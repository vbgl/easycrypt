(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcIdent
open EcParsetree
open EcEnv
open EcTypes
open EcModules
open EcFol
open EcGenRegexp
open EcSymbols

(* -------------------------------------------------------------------- *)
module Zipper = struct
  exception InvalidCPos

  module P = EcPath

  type ('a, 'state) folder =
    'a -> 'state -> instr -> 'state * instr list

  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath;                     (* path (zipper) leading to me         *)
  }

  let zipper hd tl zpr = { z_head = hd; z_tail = tl; z_path = zpr; }

  let rec zipper_of_cpos ((i, sub) : codepos) zpr s =
    let (s1, i, s2) =
      try  List.pivot_at (i-1) s.s_node
      with (Invalid_argument _ | Not_found) -> raise InvalidCPos
    in
    match sub with
    | None -> zipper s1 (i::s2) zpr
    | Some (b, sub) -> begin
      match i.i_node, b with
      | Swhile (e, sw), 0 ->
          zipper_of_cpos sub (ZWhile (e, ((s1, s2), zpr))) sw
      | Sif (e, ifs1, ifs2), 0 ->
          zipper_of_cpos sub (ZIfThen (e, ((s1, s2), zpr), ifs2)) ifs1
      | Sif (e, ifs1, ifs2), 1 ->
          zipper_of_cpos sub (ZIfElse (e, ifs1, ((s1, s2), zpr))) ifs2
      | _ -> raise InvalidCPos
    end

  let zipper_of_cpos cpos s = zipper_of_cpos cpos ZTop s

  let rec zip i ((hd, tl), ip) =
    let s = stmt (List.rev_append hd (List.ocons i tl)) in

    match ip with
    | ZTop -> s
    | ZWhile  (e, sp)     -> zip (Some (i_while (e, s))) sp
    | ZIfThen (e, sp, se) -> zip (Some (i_if (e, s, se))) sp
    | ZIfElse (e, se, sp) -> zip (Some (i_if (e, se, s))) sp

  let zip zpr = zip None ((zpr.z_head, zpr.z_tail), zpr.z_path)

  let after ~strict zpr =
    let rec doit acc ip =
      match ip with
      | ZTop                          -> acc
      | ZWhile  (_, ((_, is), ip))    -> doit (is :: acc) ip
      | ZIfThen (_, ((_, is), ip), _) -> doit (is :: acc) ip
      | ZIfElse (_, _, ((_, is), ip)) -> doit (is :: acc) ip
    in

    let after =
      match zpr.z_tail, strict with
      | []     , _     -> doit [[]] zpr.z_path
      | is     , false -> doit [is] zpr.z_path
      | _ :: is, true  -> doit [is] zpr.z_path
    in
      List.rev after

  let rec fold env cpos f state s =
    let zpr = zipper_of_cpos cpos s in

      match zpr.z_tail with
      | []      -> raise InvalidCPos
      | i :: tl -> begin
          match f env state i with
          | (state', [i']) when i == i' && state == state' -> (state, s)
          | (state', si  ) -> (state', zip { zpr with z_tail = si @ tl })
      end
end

(* -------------------------------------------------------------------- *)
type 'a evmap = {
  ev_map   : ('a option) Mid.t;
  ev_unset : int;
}

module EV = struct
  let empty : 'a evmap = {
    ev_map   = Mid.empty;
    ev_unset = 0;
  }

  let add (x : ident) (m : 'a evmap) =
    let chg = function Some _ -> assert false | None -> Some None in
    let map = Mid.change chg x m.ev_map in
    { ev_map = map; ev_unset = m.ev_unset + 1; }

  let mem (x : ident) (m : 'a evmap) =
    EcUtils.is_some (Mid.find_opt x m.ev_map)

  let set (x : ident) (v : 'a) (m : 'a evmap) =
    let chg = function
      | None | Some (Some _) -> assert false
      | Some None -> Some (Some v)
    in
      { ev_map = Mid.change chg x m.ev_map; ev_unset = m.ev_unset - 1; }

  let get (x : ident) (m : 'a evmap) =
    match Mid.find_opt x m.ev_map with
    | None          -> None
    | Some None     -> Some `Unset
    | Some (Some a) -> Some (`Set a)

  let isset (x : ident) (m : 'a evmap) =
    match get x m with
    | Some (`Set _) -> true
    | _ -> false

  let doget (x : ident) (m : 'a evmap) =
    match get x m with
    | Some (`Set a) -> a
    | _ -> assert false

  let of_idents (ids : ident list) : 'a evmap =
    List.fold_left ((^~) add) empty ids

  let fold (f : ident -> 'a -> 'b -> 'b) ev state =
    Mid.fold
      (fun x t s -> match t with Some t -> f x t s | None -> s)
      ev.ev_map state

  let filled (m : 'a evmap) = (m.ev_unset = 0)
end

(* -------------------------------------------------------------------- *)
type mevmap = {
  evm_form : form            evmap;
  evm_mem  : EcMemory.memory evmap;
  evm_mod  : EcPath.mpath    evmap;
}

(* -------------------------------------------------------------------- *)
module MEV = struct
  type item = [
    | `Form of form
    | `Mem  of EcMemory.memory
    | `Mod  of EcPath.mpath
  ]

  type kind = [ `Form | `Mem | `Mod ]

  let empty : mevmap = {
    evm_form = EV.empty;
    evm_mem  = EV.empty;
    evm_mod  = EV.empty;
  }

  let of_idents ids k =
    match k with
    | `Form -> { empty with evm_form = EV.of_idents ids }
    | `Mem  -> { empty with evm_mem  = EV.of_idents ids }
    | `Mod  -> { empty with evm_mod  = EV.of_idents ids }

  let add x k m =
    match k with
    | `Form -> { m with evm_form = EV.add x m.evm_form }
    | `Mem  -> { m with evm_mem  = EV.add x m.evm_mem  }
    | `Mod  -> { m with evm_mod  = EV.add x m.evm_mod  }

  let mem x k m =
    match k with
    | `Form -> EV.mem x m.evm_form
    | `Mem  -> EV.mem x m.evm_mem
    | `Mod  -> EV.mem x m.evm_mod

  let set x v m =
    match v with
    | `Form v -> { m with evm_form = EV.set x v m.evm_form }
    | `Mem  v -> { m with evm_mem  = EV.set x v m.evm_mem  }
    | `Mod  v -> { m with evm_mod  = EV.set x v m.evm_mod  }

  let get x k m =
    let tx f = function `Unset -> `Unset | `Set x -> `Set (f x) in

    match k with
    | `Form -> omap (tx (fun x -> `Form x)) (EV.get x m.evm_form)
    | `Mem  -> omap (tx (fun x -> `Mem  x)) (EV.get x m.evm_mem )
    | `Mod  -> omap (tx (fun x -> `Mod  x)) (EV.get x m.evm_mod )

  let isset x k m =
    match k with
    | `Form -> EV.isset x m.evm_form
    | `Mem  -> EV.isset x m.evm_mem
    | `Mod  -> EV.isset x m.evm_mod

  let filled m =
       EV.filled m.evm_form
    && EV.filled m.evm_mem
    && EV.filled m.evm_mod

  let fold (f : _ -> item -> _ -> _) m v =
    let v = EV.fold (fun x k v -> f x (`Form k) v) m.evm_form v in
    let v = EV.fold (fun x k v -> f x (`Mem  k) v) m.evm_mem  v in
    let v = EV.fold (fun x k v -> f x (`Mod  k) v) m.evm_mod  v in
    v

  let assubst ue ev =
    let tysubst = { ty_subst_id with ts_u = EcUnify.UniEnv.assubst ue } in
    let subst = Fsubst.f_subst_init ~sty:tysubst () in
    let subst = EV.fold (fun x m s -> Fsubst.f_bind_mem s x m) ev.evm_mem subst in
    let subst = EV.fold (fun x m s -> Fsubst.f_bind_mod s x m) ev.evm_mod subst in
    let seen  = ref Sid.empty in

    let rec for_ident x binding subst =
      if Sid.mem x !seen then subst else begin
        seen := Sid.add x !seen;
        match binding with None -> subst | Some f ->
          let subst =
            Mid.fold2_inter (fun x bdx _ -> for_ident x bdx)
            ev.evm_form.ev_map f.f_fv subst in
          Fsubst.f_bind_local subst x (Fsubst.f_subst subst f)
        end
    in

    Mid.fold_left
      (fun acc x bd -> for_ident x bd acc)
      subst ev.evm_form.ev_map
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta  : bool;
  fm_conv   : bool;
  fm_horder : bool;
}

let fmsearch =
  { fm_delta  = false;
    fm_conv   = false;
    fm_horder = true ; }

let fmrigid = {
    fm_delta  = false;
    fm_conv   = true ;
    fm_horder = true ; }

let fmdelta = {
    fm_delta  = true ;
    fm_conv   = true ;
    fm_horder = true ; }

let fmnotation = {
    fm_delta  = false;
    fm_conv   = false;
    fm_horder = false; }

(* -------------------------------------------------------------------- *)
(* Rigid unification *)
let f_match_core opts hyps (ue, ev) ~ptn subject =
  let ue  = EcUnify.UniEnv.copy ue in
  let ev  = ref ev in

  let iscvar = function
    | { f_node = Flocal x } -> is_none (EV.get x !ev.evm_form)
    | _ -> false
  in

  let conv =
    match opts.fm_conv with
    | true  -> EcReduction.is_conv hyps
    | false -> EcReduction.is_alpha_eq hyps
  in

  let rec doit env ((subst, mxs) as ilc) ptn subject =
    let failure =
      let oue, oev = (EcUnify.UniEnv.copy ue, !ev) in
      fun () ->
        EcUnify.UniEnv.restore ~dst:ue ~src:oue; ev := oev;
        raise MatchFailure
    in

    let default () =
      if opts.fm_conv then begin
        let subject = Fsubst.f_subst subst subject in
        let ptn = Fsubst.f_subst (MEV.assubst ue !ev) ptn in
          if not (conv ptn subject) then
            failure ()
      end else failure ()
    in

    try
      match ptn.f_node, subject.f_node with
      | Flocal x1, Flocal x2 when Mid.mem x1 mxs -> begin
          if not (id_equal (oget (Mid.find_opt x1 mxs)) x2) then
            failure ();
          try  EcUnify.unify env ue ptn.f_ty subject.f_ty
          with EcUnify.UnificationFailure _ -> failure ()
      end

      | Flocal x1, Flocal x2 when id_equal x1 x2 -> begin
          try  EcUnify.unify env ue ptn.f_ty subject.f_ty
          with EcUnify.UnificationFailure _ -> failure ()
      end

      | Flocal x, _ -> begin
          match EV.get x !ev.evm_form with
          | None ->
              raise MatchFailure

          | Some `Unset ->
              let ssbj = Fsubst.f_subst subst subject in
              let ssbj = Fsubst.f_subst (MEV.assubst ue !ev) ssbj in
              if not (Mid.set_disjoint mxs ssbj.f_fv) then
                raise MatchFailure;
              begin
                try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                with EcUnify.UnificationFailure _ -> failure ();
              end;
              ev := { !ev with evm_form = EV.set x ssbj !ev.evm_form }

          | Some (`Set a) -> begin
              let ssbj = Fsubst.f_subst subst subject in

              if not (conv ssbj a) then
                let ssbj = Fsubst.f_subst (MEV.assubst ue !ev) subject in
                if not (conv ssbj a) then
                  doit env ilc a ssbj
                else
                  try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                  with EcUnify.UnificationFailure _ -> failure ()
              else
                try  EcUnify.unify env ue ptn.f_ty subject.f_ty
                with EcUnify.UnificationFailure _ -> failure ()
          end
      end

      | Fapp (f1, fs1), _ -> begin
        try
          match subject.f_node with
          | Fapp (f2, fs2) -> begin
              try  doit_args env ilc (f1::fs1) (f2::fs2)
              with MatchFailure when opts.fm_conv  ->
                let rptn = f_betared ptn in
                if   (ptn.f_tag <> rptn.f_tag)
                then doit env ilc rptn subject
                else failure ()
          end
          | _ -> failure ()

        with MatchFailure when opts.fm_horder ->
          match f1.f_node with
          | Flocal f when
                  not (Mid.mem f mxs)
               && (EV.get f !ev.evm_form = Some `Unset)
               && List.for_all iscvar fs1
            ->

            let oargs = List.map destr_local fs1 in

            if not (List.is_unique ~eq:id_equal oargs) then
              failure ();

            let xsubst, bindings =
              List.map_fold
                (fun xsubst x ->
                   let x, xty = (destr_local x, x.f_ty) in
                   let nx = EcIdent.fresh x in
                   let xsubst =
                     Mid.find_opt x mxs
                       |> omap (fun y -> Fsubst.f_bind_rename xsubst y nx xty)
                       |> odfl xsubst
                   in (xsubst, (nx, GTty xty)))
                Fsubst.f_subst_id fs1 in

            let ssbj = Fsubst.f_subst xsubst subject in
            let ssbj = Fsubst.f_subst  subst ssbj in

            if not (Mid.set_disjoint mxs ssbj.f_fv) then
              failure ();

            begin
              let fty = toarrow (List.map f_ty fs1) ssbj.f_ty in

              try  EcUnify.unify env ue f1.f_ty fty
              with EcUnify.UnificationFailure _ -> failure ();
            end;

            let ssbj = f_lambda bindings ssbj in

            ev := { !ev with evm_form = EV.set f ssbj !ev.evm_form }

          | _ -> default ()
      end

      | Fquant (b1, q1, f1), Fquant (b2, q2, f2) when b1 = b2 ->
          let n1, n2 = List.length q1, List.length q2 in
          let q1, r1 = List.split_at (min n1 n2) q1 in
          let q2, r2 = List.split_at (min n1 n2) q2 in
          let (env, subst, mxs) = doit_bindings env (subst, mxs) q1 q2 in
          doit env (subst, mxs) (f_quant b1 r1 f1) (f_quant b2 r2 f2)

      | Fquant _, Fquant _ ->
          failure ();

      | Fpvar (pv1, m1), Fpvar (pv2, m2) ->
          let pv1 = EcEnv.NormMp.norm_pvar env pv1 in
          let pv2 = EcEnv.NormMp.norm_pvar env pv2 in
            if not (EcTypes.pv_equal pv1 pv2) then
              failure ();
            doit_mem env mxs m1 m2

      | Fif (c1, t1, e1), Fif (c2, t2, e2) ->
          List.iter2 (doit env ilc) [c1; t1; e1] [c2; t2; e2]

      | Fmatch (b1, fs1, ty1), Fmatch (b2, fs2, ty2) -> begin
          (try  EcUnify.unify env ue ty1 ty2
           with EcUnify.UnificationFailure _ -> failure ());
          if List.length fs1 <> List.length fs2 then
            failure ();
          List.iter2 (doit env ilc) (b1 :: fs1) (b2 :: fs2)
        end

      | Fint i1, Fint i2 ->
          if not (EcBigInt.equal i1 i2) then failure ();

      | Fglob (mp1, me1), Fglob (mp2, me2) ->
          let mp1 = EcEnv.NormMp.norm_mpath env mp1 in
          let mp2 = EcEnv.NormMp.norm_mpath env mp2 in
            if not (EcPath.m_equal mp1 mp2) then
              failure ();
            doit_mem env mxs me1 me2

      | Ftuple fs1, Ftuple fs2 ->
          if List.length fs1 <> List.length fs2 then
            failure ();
          List.iter2 (doit env ilc) fs1 fs2

      | Fop (op1, tys1), Fop (op2, tys2) -> begin
          if not (EcPath.p_equal op1 op2) then
            failure ();
          try  List.iter2 (EcUnify.unify env ue) tys1 tys2
          with EcUnify.UnificationFailure _ -> failure ();
      end

      | _, _ -> default ()

    with MatchFailure when opts.fm_delta ->
      match fst_map f_node (destr_app ptn),
            fst_map f_node (destr_app subject)
      with
      | (Fop (op1, tys1), args1), (Fop (op2, tys2), args2) -> begin
          try
            if not (EcPath.p_equal op1 op2) then
              failure ();
            try
              List.iter2 (EcUnify.unify env ue) tys1 tys2;
              doit_args env ilc args1 args2
            with EcUnify.UnificationFailure _ -> failure ()
          with MatchFailure ->
            if EcEnv.Op.reducible env op1 then
              doit_reduce env ((doit env ilc)^~ subject) ptn.f_ty op1 tys1 args1
            else if EcEnv.Op.reducible env op2 then
              doit_reduce env (doit env ilc ptn) subject.f_ty op2 tys2 args2
            else
              failure ()
      end

      | (Flocal x1, args1), _ when LDecl.can_unfold x1 hyps ->
          doit_lreduce env ((doit env ilc)^~ subject) ptn.f_ty x1 args1

      | _, (Flocal x2, args2) when LDecl.can_unfold x2 hyps ->
          doit_lreduce env (doit env ilc ptn) subject.f_ty x2 args2

      | (Fop (op1, tys1), args1), _ when EcEnv.Op.reducible env op1 ->
          doit_reduce env ((doit env ilc)^~ subject) ptn.f_ty op1 tys1 args1

      | _, (Fop (op2, tys2), args2) when EcEnv.Op.reducible env op2 ->
          doit_reduce env (doit env ilc ptn) subject.f_ty op2 tys2 args2

      | _, _ -> failure ()

  and doit_args env ilc fs1 fs2 =
    if List.length fs1 <> List.length fs2 then
      raise MatchFailure;
    List.iter2 (doit env ilc) fs1 fs2

  and doit_reduce env cb ty op tys args =
    let reduced =
      try  f_app (EcEnv.Op.reduce env op tys) args ty
      with NotReducible -> raise MatchFailure in
    cb (odfl reduced (EcReduction.h_red_opt EcReduction.beta_red hyps reduced))

  and doit_lreduce _env cb ty x args =
    let reduced =
      try  f_app (LDecl.unfold x hyps) args ty
      with LookupFailure _ -> raise MatchFailure in
    cb (odfl reduced (EcReduction.h_red_opt EcReduction.beta_red hyps reduced))

  and doit_mem _env mxs m1 m2 =
    match EV.get m1 !ev.evm_mem with
    | None ->
        if not (EcMemory.mem_equal m1 m2) then
          raise MatchFailure

    | Some `Unset ->
        if Mid.mem m2 mxs then
          raise MatchFailure;
        ev := { !ev with evm_mem = EV.set m1 m2 !ev.evm_mem }

    | Some (`Set m1) ->
        if not (EcMemory.mem_equal m1 m2) then
          raise MatchFailure

  and doit_bindings env (subst, mxs) q1 q2 =
    let doit_binding (env, subst, mxs) (x1, gty1) (x2, gty2) =
      let gty2 = Fsubst.gty_subst subst gty2 in

      assert (not (Mid.mem x1 mxs) && not (Mid.mem x2 mxs));

      let env, subst =
        match gty1, gty2 with
        | GTty ty1, GTty ty2 ->
            begin
              try  EcUnify.unify env ue ty1 ty2
              with EcUnify.UnificationFailure _ -> raise MatchFailure
            end;

            let subst =
              if   id_equal x1 x2
              then subst
              else Fsubst.f_bind_rename subst x2 x1 ty2

            and env = EcEnv.Var.bind_local x1 ty1 env in

            (env, subst)

        | GTmem None, GTmem None ->
            (env, subst)

        | GTmem (Some m1), GTmem (Some m2) ->
            let xp1 = EcMemory.lmt_xpath m1 in
            let xp2 = EcMemory.lmt_xpath m2 in
            let m1  = EcMemory.lmt_bindings m1 in
            let m2  = EcMemory.lmt_bindings m2 in

            if not (EcPath.x_equal xp1 xp2) then
              raise MatchFailure;
            if not (
              try
                EcSymbols.Msym.equal
                  (fun (p1,ty1) (p2,ty2) ->
                    if p1 <> p2 then raise MatchFailure;
                    EcUnify.unify env ue ty1 ty2; true)
                  m1 m2
              with EcUnify.UnificationFailure _ -> raise MatchFailure)
            then
              raise MatchFailure;

            let subst =
              if   id_equal x1 x2
              then subst
              else Fsubst.f_bind_mem subst x2 x1
            in (env, subst)

        | GTmodty (p1, r1), GTmodty (p2, r2) ->
            if not (ModTy.mod_type_equiv env p1 p2) then
              raise MatchFailure;
            if not (NormMp.equal_restr env r1 r2) then
              raise MatchFailure;

            let subst =
              if   id_equal x1 x2
              then subst
              else Fsubst.f_bind_mod subst x2 (EcPath.mident x1)

            and env = EcEnv.Mod.bind_local x1 p1 r1 env in

            (env, subst)

        | _, _ -> raise MatchFailure
      in
        (env, subst, Mid.add x1 x2 mxs)
    in
      List.fold_left2 doit_binding (env, subst, mxs) q1 q2

  in
    doit (EcEnv.LDecl.toenv hyps) (Fsubst.f_subst_id, Mid.empty) ptn subject;
    (ue, !ev)

let f_match opts hyps (ue, ev) ~ptn subject =
  let (ue, ev) = f_match_core opts hyps (ue, ev) ~ptn subject in
    if not (MEV.filled ev) then
      raise MatchFailure;
    let clue =
      try  EcUnify.UniEnv.close ue
      with EcUnify.UninstanciateUni -> raise MatchFailure
    in
      (ue, clue, ev)

(* -------------------------------------------------------------------- *)
type ptnpos = [`Select of int | `Sub of ptnpos] Mint.t
type occ    = [`Inclusive | `Exclusive] * Sint.t

exception InvalidPosition
exception InvalidOccurence

module FPosition = struct
  type select = [`Accept of int | `Continue]

  (* ------------------------------------------------------------------ *)
  let empty : ptnpos = Mint.empty

  (* ------------------------------------------------------------------ *)
  let is_empty (p : ptnpos) = Mint.is_empty p

  (* ------------------------------------------------------------------ *)
  let rec tostring (p : ptnpos) =
    let items = Mint.bindings p in
    let items =
      List.map
        (fun (i, p) -> Printf.sprintf "%d[%s]" i (tostring1 p))
        items
    in
      String.concat ", " items

  (* ------------------------------------------------------------------ *)
  and tostring1 = function
    | `Select i when i < 0 -> "-"
    | `Select i -> Printf.sprintf "-(%d)" i
    | `Sub p -> tostring p

  (* ------------------------------------------------------------------ *)
  let occurences =
    let rec doit1 n p =
      match p with
      | `Select _ -> n+1
      | `Sub p    -> doit n p

    and doit n (ps : ptnpos) =
      Mint.fold (fun _ p n -> doit1 n p) ps n

    in
      fun p -> doit 0 p

  (* ------------------------------------------------------------------ *)
  let filter ((mode, s) : occ) =
    let rec doit1 n p =
      match p with
      | `Select _ -> begin
        match mode with
        | `Inclusive -> (n+1, if Sint.mem n s then Some p else None  )
        | `Exclusive -> (n+1, if Sint.mem n s then None   else Some p)
      end

      | `Sub p  -> begin
          match doit n p with
          | (n, sub) when Mint.is_empty sub -> (n, None)
          | (n, sub) -> (n, Some (`Sub sub))
      end

    and doit n (ps : ptnpos) =
      Mint.mapi_filter_fold (fun _ p n -> doit1 n p) ps n

    in
      fun p -> snd (doit 1 p)

  (* ------------------------------------------------------------------ *)
  let is_occurences_valid o cpos =
    let (min, max) = (Sint.min_elt o, Sint.max_elt o) in
      not (min < 1 || max > occurences cpos)

  (* ------------------------------------------------------------------ *)
  let select ?o test =
    let rec doit1 ctxt pos fp =
      match test ctxt fp with
      | `Accept i -> Some (`Select i)
      | `Continue -> begin
        let subp =
          match fp.f_node with
          | Fif    (c, f1, f2) -> doit pos (`WithCtxt (ctxt, [c; f1; f2]))
          | Fapp   (f, fs)     -> doit pos (`WithCtxt (ctxt, f :: fs))
          | Ftuple fs          -> doit pos (`WithCtxt (ctxt, fs))

          | Fmatch (b, fs, _) ->
               doit pos (`WithCtxt (ctxt, b :: fs))

          | Fquant (_, b, f) ->
              let xs   = List.pmap (function (x, GTty _) -> Some x | _ -> None) b in
              let ctxt = List.fold_left ((^~) Sid.add) ctxt xs in
              doit pos (`WithCtxt (ctxt, [f]))

          | Flet (lp, f1, f2) ->
              let subctxt = List.fold_left ((^~) Sid.add) ctxt (lp_ids lp) in
              doit pos (`WithSubCtxt [(ctxt, f1); (subctxt, f2)])

          | Fproj (f, _) ->
              doit pos (`WithCtxt (ctxt, [f]))

          | Fpr pr ->
              let subctxt = Sid.add pr.pr_mem ctxt in
              doit pos (`WithSubCtxt [(ctxt, pr.pr_args); (subctxt, pr.pr_event)])

          | FhoareF hs ->
              doit pos (`WithCtxt (Sid.add EcFol.mhr ctxt, [hs.hf_pr; hs.hf_po]))

          | FbdHoareF hs ->
              let subctxt = Sid.add EcFol.mhr ctxt in
              doit pos (`WithSubCtxt ([(subctxt, hs.bhf_pr);
                                       (subctxt, hs.bhf_po);
                                       (   ctxt, hs.bhf_bd)]))

          | FequivF es ->
              let ctxt = Sid.add EcFol.mleft  ctxt in
              let ctxt = Sid.add EcFol.mright ctxt in
              doit pos (`WithCtxt (ctxt, [es.ef_pr; es.ef_po]))

          | _ -> None
        in
          omap (fun p -> `Sub p) subp
      end

    and doit pos fps =
      let fps =
        match fps with
        | `WithCtxt (ctxt, fps) ->
            List.mapi
              (fun i fp ->
                doit1 ctxt (i::pos) fp |> omap (fun p -> (i, p)))
              fps

        | `WithSubCtxt fps ->
            List.mapi
              (fun i (ctxt, fp) ->
                doit1 ctxt (i::pos) fp |> omap (fun p -> (i, p)))
              fps
      in

      let fps = List.pmap identity fps in
        match fps with
        | [] -> None
        | _  -> Some (Mint.of_list fps)

    in
      fun fp ->
        let cpos =
          match doit [] (`WithCtxt (Sid.empty, [fp])) with
          | None   -> Mint.empty
          | Some p -> p
        in
          match o with
          | None   -> cpos
          | Some o ->
            if not (is_occurences_valid (snd o) cpos) then
              raise InvalidOccurence;
            filter o cpos

  (* ------------------------------------------------------------------ *)
  let select_form ?(xconv = `Conv) hyps o p target =
    let na = List.length (snd (EcFol.destr_app p)) in
    let test _ tp =
      let (tp, ti) =
        match tp.f_node with
        | Fapp (h, hargs) when List.length hargs > na ->
            let (a1, a2) = List.takedrop na hargs in
              (f_app h a1 (toarrow (List.map f_ty a2) tp.f_ty), na)
        | _ -> (tp, -1)
      in
      if EcReduction.xconv xconv hyps p tp then `Accept ti else `Continue

    in select ?o test target

  (* ------------------------------------------------------------------ *)
  let map (p : ptnpos) (tx : form -> form) (f : form) =
    let rec doit1 p fp =
      match p with
      | `Select i when i < 0 -> tx fp

      | `Select i -> begin
          let (f, fs) = EcFol.destr_app fp in
            if List.length fs < i then raise InvalidPosition;
            let (fs1, fs2) = List.takedrop i fs in
            let f' = f_app f fs1 (toarrow (List.map f_ty fs2) fp.f_ty) in
              f_app (tx f') fs2 fp.f_ty
        end

      | `Sub p    -> begin
          match fp.f_node with
          | Flocal _ -> raise InvalidPosition
          | Fpvar  _ -> raise InvalidPosition
          | Fglob  _ -> raise InvalidPosition
          | Fop    _ -> raise InvalidPosition
          | Fint   _ -> raise InvalidPosition

          | Fquant (q, b, f) ->
              let f' = as_seq1 (doit p [f]) in
              FSmart.f_quant (fp, (q, b, f)) (q, b, f')

          | Fif (c, f1, f2)  ->
              let (c', f1', f2') = as_seq3 (doit p [c; f1; f2]) in
              FSmart.f_if (fp, (c, f1, f2)) (c', f1', f2')

          | Fmatch (b, fs, ty) ->
              let bfs = doit p (b :: fs) in
              FSmart.f_match (fp, (b, fs, ty)) (List.hd bfs, List.tl bfs, ty)

          | Fapp (f, fs) -> begin
              match doit p (f :: fs) with
              | [] -> assert false
              | f' :: fs' ->
                FSmart.f_app (fp, (f, fs, fp.f_ty)) (f', fs', fp.f_ty)
          end

          | Ftuple fs ->
              let fs' = doit p fs in
              FSmart.f_tuple (fp, fs) fs'

          | Fproj (f, i) ->
              FSmart.f_proj (fp, (f, fp.f_ty)) (as_seq1 (doit p [f]), fp.f_ty) i

          | Flet (lv, f1, f2) ->
              let (f1', f2') = as_seq2 (doit p [f1; f2]) in
              FSmart.f_let (fp, (lv, f1, f2)) (lv, f1', f2')

          | Fpr pr ->
              let (args', event') = as_seq2 (doit p [pr.pr_args; pr.pr_event]) in
              f_pr pr.pr_mem pr.pr_fun args' event'

          | FhoareF hf ->
              let (hf_pr, hf_po) = as_seq2 (doit p [hf.hf_pr; hf.hf_po]) in
              f_hoareF_r { hf with hf_pr; hf_po; }

          | FbdHoareF hf ->
              let sub = doit p [hf.bhf_pr; hf.bhf_po; hf.bhf_bd] in
              let (bhf_pr, bhf_po, bhf_bd) = as_seq3 sub in
              f_bdHoareF_r { hf with bhf_pr; bhf_po; bhf_bd; }

          | FequivF ef ->
              let (ef_pr, ef_po) = as_seq2 (doit p [ef.ef_pr; ef.ef_po]) in
              f_equivF_r { ef with ef_pr; ef_po; }

          | FhoareS   _ -> raise InvalidPosition
          | FbdHoareS _ -> raise InvalidPosition
          | FequivS   _ -> raise InvalidPosition
          | FeagerF   _ -> raise InvalidPosition
      end

    and doit ps fps =
      match Mint.is_empty ps with
      | true  -> fps
      | false ->
          let imin = fst (Mint.min_binding ps)
          and imax = fst (Mint.max_binding ps) in
          if imin < 0 || imax >= List.length fps then
            raise InvalidPosition;
          let fps = List.mapi (fun i x -> (x, Mint.find_opt i ps)) fps in
          let fps = List.map (function (f, None) -> f | (f, Some p) -> doit1 p f) fps in
            fps

    in
      as_seq1 (doit p [f])

  (* ------------------------------------------------------------------ *)
  let topattern ?x (p : ptnpos) (f : form) =
    let x = match x with None -> EcIdent.create "_p" | Some x -> x in
    let tx fp = f_local x fp.f_ty in (x, map p tx f)
end

(* -------------------------------------------------------------------- *)
type cptenv = CPTEnv of f_subst

let can_concretize ev ue =
  EcUnify.UniEnv.closed ue && MEV.filled ev

(* -------------------------------------------------------------------------- *)
type regexp_instr = regexp1_instr gen_regexp

and regexp1_instr =
  | RAssign    (*of lvalue * expr*)
  | RSample    (*of lvalue * expr*)
  | RCall      (*of lvalue option * EcPath.xpath * expr list*)
  | RIf        of (*expr *) regexp_instr * regexp_instr
  | RWhile     of (*expr *) regexp_instr


module RegexpBaseInstr = struct
  open Zipper

  type regexp = regexp_instr
  type regexp1 = regexp1_instr

  type pos  = int
  type path = int list

  type subject = instr list

  type engine  = {
    e_zipper : zipper;
    e_pos    : pos;
    e_path   : pos list;
  }

  let mkengine (s : subject) = {
    e_zipper = zipper [] s ZTop;
    e_pos    = 0;
    e_path   = [];
  }

  let position (e : engine) =
    e.e_pos

  let at_start (e : engine) =
    List.is_empty e.e_zipper.z_head

  let at_end (e : engine) =
    List.is_empty e.e_zipper.z_tail

  let path (e : engine) =
    e.e_pos :: e.e_path

  let eat_option (f : 'a -> 'a -> unit) (x : 'a option) (xn : 'a option) =
    match x, xn with
    | None  , Some _ -> raise NoMatch
    | Some _, None   -> raise NoMatch
    | None  , None   -> ()
    | Some x, Some y -> f x y

  let eat_list (f : 'a -> 'a -> unit) (x : 'a list) (xn : 'a list) =
    try  List.iter2 f x xn
    with Invalid_argument _ -> raise NoMatch (* FIXME *)

  let eat_lvalue (lv : lvalue) (lvn : lvalue) =
    if not (lv_equal lv lvn) then raise NoMatch

  let eat_expr (e : expr) (en : expr) =
    if not (e_equal e en) then raise NoMatch

  let eat_xpath (f : EcPath.xpath) (fn : EcPath.xpath) =
    if not (EcPath.x_equal f fn) then raise NoMatch

  let rec eat_base (eng : engine) (r : regexp1) =
    let z = eng.e_zipper in

    match z.z_tail with
    | [] -> raise NoMatch

    | i :: tail -> begin
       match (i.i_node,r) with
       | Sasgn _, RAssign
       | Srnd  _, RSample
       | Scall _, RCall   -> (eat eng, [])

       | Sif (e, st, sf), RIf (stn, sfn) -> begin
           let e_t = mkengine st.s_node in
           let e_t =
             let zp = ZIfThen (e, ((z.z_head, tail), z.z_path), sf) in
             let zp = { e_t.e_zipper with z_path = zp; } in
             { e_t with e_path = 0 :: eng.e_pos :: eng.e_path; e_zipper = zp; } in

           let e_f = mkengine sf.s_node in
           let e_f =
             let zp = ZIfElse (e, st, ((z.z_head, tail), z.z_path)) in
             let zp = { e_f.e_zipper with z_path = zp; } in
             { e_f with e_path = 1 :: eng.e_pos :: eng.e_path; e_zipper = zp; } in

           (eat eng, [(e_t, stn); (e_f, sfn)])
         end

       | Swhile (e, s), RWhile sn -> begin
            let es = mkengine s.s_node in
            let es =
              let zp = ZWhile (e, ((z.z_head, tail), z.z_path)) in
              let zp = { es.e_zipper with z_path = zp; } in
              { es with e_path = 0 :: eng.e_pos :: eng.e_path; e_zipper = zp; }  in

            (eat eng, [(es, sn)])
         end

       | _, _ -> raise NoMatch
     end

  and eat (e : engine) = {
    e with e_zipper = zip_eat e.e_zipper;
           e_pos    = e.e_pos + 1;
  }

  and zip_eat (z : zipper) =
    match z.z_tail with
    | []        -> raise NoMatch
    | i :: tail -> zipper (i :: z.z_head) tail z.z_path

  let extract (e : engine) ((lo, hi) : pos * pos) =
    if hi <= lo then [] else

    let s = List.rev_append e.e_zipper.z_head e.e_zipper.z_tail in
    List.of_enum (List.enum s |> Enum.skip lo |> Enum.take (hi-lo))

  let rec next_zipper (z : zipper) =
    match z.z_tail with
    | i :: tail ->
       begin match i.i_node with
       | Sif (e, stmttrue, stmtfalse) ->
          let z = (i::z.z_head, tail), z.z_path in
          let path = ZIfThen (e, z, stmtfalse) in
          let z' = zipper [] stmttrue.s_node path in
          Some z'

       | Swhile (e, block) ->
          let z = (i::z.z_head, tail), z.z_path in
          let path = ZWhile (e, z) in
          let z' = zipper [] block.s_node path in
          Some z'

       | Sasgn _ | Srnd _ | Scall _ | _ ->
          Some { z with z_head = i :: z.z_head ; z_tail = tail }
       end

    | [] ->
       match z.z_path with
       | ZTop -> None

       | ZWhile (_e, ((head, tail), path)) ->
          let z' = zipper head tail path in
          next_zipper z'

       | ZIfThen (e, father, stmtfalse) ->
          let stmttrue = stmt (List.rev z.z_head) in
          let z' = zipper [] stmtfalse.s_node (ZIfElse (e, stmttrue, father)) in
          next_zipper z'

       | ZIfElse (_e, _stmttrue, ((head, tail), path)) ->
          let z' = zipper head tail path in
          next_zipper z'

  let next (e : engine) =
    next_zipper e.e_zipper |> omap (fun z ->
      { e with e_zipper = z; e_pos = List.length z.z_head })
end

module RegexpStmt = EcGenRegexp.Regexp(RegexpBaseInstr)


(* -------------------------------------------------------------------------- *)

type 'a gen_named =
  | Anything
  | Base     of 'a
  | Named    of 'a gen_named * symbol
  (* | Subterm  of 'a gen_named *)

module type BaseNamed = sig
  type base
  type engine
  type named1
  type pos

  type interval =
    | Son     of pos
    (* | Between of pos * pos *)

  type matches = base Mstr.t

  type named = named1 gen_named

  val mkengine    : base -> engine
  val eat_down    : engine -> engine
  val eat_next    : engine -> engine
  val eat_up      : engine -> engine
  val eat         : engine -> engine
  val eat_base    : engine -> named1 -> engine * (pos * named) list
  val position    : engine -> pos
  val goto        : engine -> pos -> engine
  (* add_match can raise the exception : CannotUnify *)
  val add_match   : engine -> interval -> symbol -> matches -> engine
  val get_matches : engine -> matches
end


(* ---------------------------------------------------------------------- *)
exception NoMatches
exception CannotUnify
exception NoNext

module Named(B : BaseNamed) = struct
  include B

  (* ------------------------------------------------------------------ *)
  type continuation  = Cont of (continuation1 * continuation) Lazy.t
   and matchr        = engine * continuation
   and continuation1 = [
     | `Result of engine
     | `Named  of engine * named
   ]

  (* ------------------------------------------------------------------ *)
  let no_continuation =
    Cont (Lazy.from_fun (fun () -> raise NoMatches))

  (* ------------------------------------------------------------------ *)
  let single_continuation (ctn : continuation1) =
    Cont (Lazy.from_val (ctn, no_continuation))

  (* ------------------------------------------------------------------ *)
  let single_mr (e : engine) : matchr =
    (e, no_continuation)

  (* ------------------------------------------------------------------ *)
  let rec search (e : engine) (pattern : named) : matchr =
    match pattern with
    | Anything   ->
       (eat_next e, no_continuation)

    | Base b1 ->
       let (e1, aux) = eat_base e b1 in
       let e2 = List.fold_left search_sub e1 aux in
       (e2, no_continuation)

    | Named (p1, name) ->
       let decorate res =
         let start = position e in
         (* let end_  = position res in *)
         add_match res (Son (start)) name (get_matches res)
       in apply1_on_mr decorate (search e p1)

    (* | Subterm p1 -> *)
    (*    let search_p1 eng = search eng p1 in *)



  and search_sub (e : engine) ((p,named) : pos * named) =
    let init_pos = position e in
    let e = goto e p in
    let mr = next_mr e in
    goto (fst (apply_on_mr (fun eng -> search eng named) mr)) init_pos


  (* ------------------------------------------------------------------ *)
  and continuation_of_mr (e, ctn) : continuation =
    Cont (Lazy.from_val (`Result e, ctn))

  (* ------------------------------------------------------------------ *)
  and chain_continuation (Cont ctn1) (Cont ctn2) =
    Cont (Lazy.from_fun (fun () ->
      try
        let (x, ctn1) = Lazy.force ctn1 in
        (x, chain_continuation ctn1 (Cont ctn2))
      with NoMatches -> Lazy.force ctn2))

  (* ------------------------------------------------------------------ *)
  and force_continuation (Cont (lazy (ctn1, ctn))) : matchr =
    match ctn1 with
    | `Result e -> (e, ctn)
    | `Named (e, n) ->
        try
          let (e, ectn) = search e n in
          (e, chain_continuation ectn ctn)
        with NoMatches -> force_continuation ctn

  (* ------------------------------------------------------------------ *)
  and apply_on_continuation f ctn =
    Cont (Lazy.from_fun (fun () ->
      let e, ctn = apply_on_mr f (force_continuation ctn) in
      (`Result e, ctn)))

  (* ------------------------------------------------------------------ *)
  and apply_on_mr (f : engine -> matchr) ((e, ctn) : matchr) : matchr =
    try  chain_mr (f e) (apply_on_continuation f ctn)
    with NoMatches -> apply_on_mr f (force_continuation ctn)

  (* ------------------------------------------------------------------ *)
  and chain_mr ((e, ctn1) : matchr) (ctn2 : continuation) =
    (e, chain_continuation ctn1 ctn2)

  (* ------------------------------------------------------------------ *)
  and apply1_on_continuation f (ctn : continuation) : continuation =
    apply_on_continuation (fun e -> (f e, no_continuation)) ctn

  (* ------------------------------------------------------------------ *)
  and apply1_on_mr f (mr : matchr) : matchr =
    apply_on_mr (fun e -> (f e, no_continuation)) mr

  (* ------------------------------------------------------------------ *)
  and next_continuation (e : engine) : continuation =
    let next () : continuation1 * continuation =
      let e = eat e in
      (`Result e, next_continuation e)
    in Cont (Lazy.from_fun next)

  (* ------------------------------------------------------------------ *)
  and next_mr (e : engine) : matchr =
    (e, next_continuation e)

  (* ------------------------------------------------------------------ *)
  let search (pattern : named) (b : base) =
    let mr = next_mr (mkengine b) in
    try  Some (get_matches (fst (apply_on_mr (fun e -> search e pattern) mr)))
    with NoMatches -> None

end

(* -------------------------------------------------------------------------- *)
module BaseBindingsNamed : sig
  include BaseNamed with type base = bindings
end = struct

  type base = bindings

  type engine = {
      e_before : bindings ;
      e_after  : bindings ;
      e_map    : base Mstr.t ;
    }

  type named1 = binding
  type named = named1 gen_named

  type pos = int

  type interval =
    | Son     of pos
    (* | Between of pos * pos *)

  type matches = base Mstr.t

  let mkengine (b : base) = { e_before = [] ;
                              e_after  = b ;
                              e_map    = Mstr.empty;
                            }

  let eat_down (_e : engine) = raise NoNext

  let eat_next (e : engine) = match e.e_after with
    | [] -> raise NoNext
    | a :: after -> { e with e_before = (a::e.e_before) ; e_after = after }

  let eat_up (_e : engine) = raise NoNext

  let eat = eat_next

  let b1_equal (x1, ty1) (x2, ty2) =
    EcIdent.id_equal x1 x2 && gty_equal ty1 ty2

  let eat_base (e : engine) (b1 : named1) = match e.e_after with
    | [] -> raise NoNext
    | b2 :: after ->
       if (b1_equal b1 b2)
       then { e with e_before = b2::e.e_before;
                     e_after = after
            }, []
       else raise NoNext

  let position (e : engine) = List.length e.e_before

  let goto (e : engine) pos =
    let rec aux bef aft i = match i,bef,aft with
      | 0,_,_                 -> (bef,aft)
      | _,[],_     when i < 0 -> raise NoNext
      | _,a::bef,_ when i < 0 -> aux bef (a::aft) (i+1)
      | _,_,[]                -> raise NoNext
      | _,_,a::aft            -> aux (a::bef) aft (i-1)
    in let bef,aft = aux e.e_before e.e_after (pos - List.length e.e_before) in
       { e with e_before = bef; e_after = aft }

  let add (name : symbol) (x : base) (map : matches) =
    match Mstr.find_opt name map with
    | None   -> Mstr.add name x map
    | Some y -> if (try List.all2 b1_equal x y with
                    | Invalid_argument _ -> false)
                then map
                else raise CannotUnify

  let add_match (e : engine) (i : interval) (name : symbol) (map : matches) =
    match i with
    | Son index -> begin
        let e' = goto e index in
        match e'.e_after with
        | [] -> raise NoNext
        | a :: _after -> { e with e_map = add name [a] map }
      end
    (* | Between (i1, i2) -> begin *)
    (*     let e1 = goto e i1 in *)
    (*     let rec aux acc l i = match i,l with *)
    (*       | 0, _           -> acc *)
    (*       | _,_ when i < 0 -> raise NoNext *)
    (*       | _,[]           -> raise NoNext *)
    (*       | _, a::rest     -> aux (a::acc) rest (i-1) *)
    (*     in let l = aux [] e1.e_after (i2 - i1) in *)
    (*        { e with e_map = add name (List.rev l) map } *)
    (*   end *)

  let get_matches (e : engine) = e.e_map

end

(* -------------------------------------------------------------------------- *)
module BindingsNamed = Named(BaseBindingsNamed)



(* -------------------------------------------------------------------------- *)
module type Basic = sig
  type base
  val base_equal : base -> base -> bool
end

(* -------------------------------------------------------------------------- *)
module BasicNamed(B : Basic) : BaseNamed = struct
  type base = B.base
  type named1 = base
  type named = named1 gen_named
  type matches = base Mstr.t
  type pos = int
  type engine = {
      e_base : base ;
      e_map  : matches ;
    }
  type interval = Son of pos

  (* val mkengine : base -> engine *)
  let mkengine (b : base) = { e_base = b ; e_map = Mstr.empty ; }

  (* val eat_down : engine -> engine *)
  let eat_down (_e : engine) = raise NoNext

  (* val eat_next : engine -> engine *)
  let eat_next (_e : engine) = raise NoNext

  (* val eat_up : engine -> engine *)
  let eat_up (_e : engine) = raise NoNext

  (* val eat : engine -> engine *)
  let eat (_e : engine) = raise NoNext

  (* val eat_base : engine -> named1 -> engine * (pos * named) list *)
  let eat_base (e : engine) (x : named1) =
    if (B.base_equal e.e_base x) then e, []
    else raise NoMatches

  (* val position : engine -> pos *)
  let position (_e : engine) = 1

  (* val goto : engine -> pos -> engine *)
  let goto (e : engine) (i : int) = if i = 1 then e else raise NoNext

  let add (name : symbol) (b : base) (map : matches) =
    match Mstr.find_opt name map with
    | None -> Mstr.add name b map
    | Some b2 -> if (B.base_equal b b2) then map
                  else raise CannotUnify

  (* val add_match : engine -> interval -> EcSymbols.symbol -> engine *)
  let add_match (e : engine) (i : interval) (name : EcSymbols.symbol) (map : matches) =
    let map = match i with
      | Son 1 -> add name e.e_base map
      | Son _ -> raise CannotUnify
      (* | Between (1,1) -> add name e.e_id map *)
      (* | Between _ -> raise CannotUnify *)
    in { e with e_map = map }

  (* val get_matches : engine -> matches *)
  let get_matches (e : engine) = e.e_map

end

(* -------------------------------------------------------------------------- *)
module BaseIdentNamed = struct

  type base = EcIdent.t
  type named1 = EcIdent.t
  type pos = int
  type engine = {
      e_id : base ;
      e_map : base Mstr.t;
    }

  type interval =
    | Son of pos
    (* | Between of pos * pos *)

  type matches = base EcMaps.Mstr.t
  type named = named1 gen_named

  (* val mkengine : base -> engine *)
  let mkengine (b : base) = { e_id = b ; e_map = Mstr.empty ; }

  (* val eat_down : engine -> engine *)
  let eat_down (_e : engine) = raise NoNext

  (* val eat_next : engine -> engine *)
  let eat_next (_e : engine) = raise NoNext

  (* val eat_up : engine -> engine *)
  let eat_up (_e : engine) = raise NoNext

  (* val eat : engine -> engine *)
  let eat (_e : engine) = raise NoNext

  (* val eat_base : engine -> named1 -> engine * (pos * named) list *)
  let eat_base (e : engine) (x : named1) =
    if (EcIdent.id_equal e.e_id x) then e, []
    else raise NoMatches

  (* val position : engine -> pos *)
  let position (_e : engine) = 1

  (* val goto : engine -> pos -> engine *)
  let goto (e : engine) (i : int) = if i = 1 then e else raise NoNext

  let add (name : symbol) (id : EcIdent.t) (map : matches) =
    match Mstr.find_opt name map with
    | None -> Mstr.add name id map
    | Some id2 -> if (EcIdent.id_equal id id2) then map
                  else raise CannotUnify

  (* val add_match : engine -> interval -> EcSymbols.symbol -> engine *)
  let add_match (e : engine) (i : interval) (name : EcSymbols.symbol) (map : matches) =
    let map = match i with
      | Son 1 -> add name e.e_id map
      | Son _ -> raise CannotUnify
      (* | Between (1,1) -> add name e.e_id map *)
      (* | Between _ -> raise CannotUnify *)
    in { e with e_map = map }

  (* val get_matches : engine -> matches *)
  let get_matches (e : engine) = e.e_map

end


(* -------------------------------------------------------------------------- *)
module IdentNamed : sig

  type named = BaseIdentNamed.named
  type base = BaseIdentNamed.base
  type matches = base Mstr.t
  type interval = BaseIdentNamed.interval

  val search : named -> base -> matches option
end = Named(BaseIdentNamed)


(* -------------------------------------------------------------------------- *)
module BasePvarNamed : sig
  include BaseNamed
  type pvar = EcTypes.prog_var * EcMemory.memory
  val create_base : pvar -> base
end = struct
  type pvar = EcTypes.prog_var * EcMemory.memory

  type base = pvar (* FIXME : get it more complex to be able to enter
                      in functors of in module arguments, etc... *)

  type named1 = pvar

  type pos = int

  type interval = | Son of pos
                  (* | Between of pos * pos *)

  type matches = base EcMaps.Mstr.t

  type named = named1 gen_named

  type engine = {
      e_pvar : base ;
      e_map  : matches ;
    }


  (* val create_base : pvar -> base *)
  let create_base (p : pvar) : base = p

  (* val mkengine : base -> engine *)
  let mkengine (b : base) = {
      e_pvar = b ;
      e_map = Mstr.empty ;
    }

  (* val eat_down : engine -> engine *)
  let eat_down (_e : engine) = raise NoNext

  (* val eat_next : engine -> engine *)
  let eat_next (_e : engine) = raise NoNext

  (* val eat_up : engine -> engine *)
  let eat_up (_e : engine) = raise NoNext

  (* val eat : engine -> engine *)
  let eat (_e : engine) = raise NoNext

  let pvar_equal ((pvar1,mem1) : named1) ((pvar2,mem2) : named1) =
    pv_equal pvar1 pvar2 && EcMemory.mem_equal mem1 mem2

  (* val eat_base : engine -> named1 -> engine * (pos * named) list *)
  let eat_base (e : engine) (pvar : named1) =
    if (pvar_equal pvar e.e_pvar) then e, []
    else raise NoMatches

  (* val position : engine -> pos *)
  let position (_e : engine) = 1

  (* val goto : engine -> pos -> engine *)
  let goto (e : engine) (i : int) = if i = 1 then e else raise NoNext

  let add (name : symbol) (id : base) (map : matches) =
    match Mstr.find_opt name map with
    | None -> Mstr.add name id map
    | Some id2 -> if (pvar_equal id id2) then map
                  else raise CannotUnify

  (* val add_match : engine -> interval -> EcSymbols.symbol -> engine *)
  let add_match (e : engine) (i : interval) (name : EcSymbols.symbol) (map : matches) =
    let map = match i with
      | Son 1 -> add name e.e_pvar map
      | Son _ -> raise CannotUnify
      (* | Between (1,1) -> add name e.e_pvar map *)
      (* | Between _ -> raise CannotUnify *)
    in { e with e_map = map }

  (* val get_matches : engine -> matches *)
  let get_matches (e : engine) = e.e_map


end

(* -------------------------------------------------------------------------- *)
module PvarNamed : sig

  type named = BasePvarNamed.named
  type base = BasePvarNamed.base
  type matches = base Mstr.t
  type interval = BasePvarNamed.interval

  val search : named -> base -> matches option
end = Named(BasePvarNamed)




(* -------------------------------------------------------------------------- *)
module BasePglobNamed : sig
  include BaseNamed
  type pglob = EcPath.mpath * EcMemory.memory
  val create_base : pglob -> base
end = struct

  type pglob = EcPath.mpath * EcMemory.memory

  type base = pglob (* FIXME : get it more complex to be able to enter
                      in functors of in module arguments, etc... *)

  type named1 = pglob

  type pos = int

  type interval = | Son of pos
                  (* | Between of pos * pos *)

  type matches = base EcMaps.Mstr.t

  type named = named1 gen_named

  type engine = {
      e_pglob : base ;
      e_map  : matches ;
    }


  (* val create_base : pglob -> base *)
  let create_base (p : pglob) : base = p

  (* val mkengine : base -> engine *)
  let mkengine (b : base) = {
      e_pglob = b ;
      e_map = Mstr.empty ;
    }

  (* val eat_down : engine -> engine *)
  let eat_down (_e : engine) = raise NoNext

  (* val eat_next : engine -> engine *)
  let eat_next (_e : engine) = raise NoNext

  (* val eat_up : engine -> engine *)
  let eat_up (_e : engine) = raise NoNext

  (* val eat : engine -> engine *)
  let eat (_e : engine) = raise NoNext

  let pglob_equal ((pglob1,mem1) : named1) ((pglob2,mem2) : named1) =
    EcPath.m_equal pglob1 pglob2 && EcMemory.mem_equal mem1 mem2

  (* val eat_base : engine -> named1 -> engine * (pos * named) list *)
  let eat_base (e : engine) (pglob : named1) =
    if (pglob_equal pglob e.e_pglob) then e, []
    else raise NoMatches

  (* val position : engine -> pos *)
  let position (_e : engine) = 1

  (* val goto : engine -> pos -> engine *)
  let goto (e : engine) (i : int) = if i = 1 then e else raise NoNext

  let add (name : symbol) (id : base) (map : matches) =
    match Mstr.find_opt name map with
    | None -> Mstr.add name id map
    | Some id2 -> if (pglob_equal id id2) then map
                  else raise CannotUnify

  (* val add_match : engine -> interval -> EcSymbols.symbol -> engine *)
  let add_match (e : engine) (i : interval) (name : EcSymbols.symbol) (map : matches) =
    let map = match i with
      | Son 1 -> add name e.e_pglob map
      | Son _ -> raise CannotUnify
      (* | Between (1,1) -> add name e.e_pglob map *)
      (* | Between _ -> raise CannotUnify *)
    in { e with e_map = map }

  (* val get_matches : engine -> matches *)
  let get_matches (e : engine) = e.e_map


end

(* -------------------------------------------------------------------------- *)
module PglobNamed = Named(BasePglobNamed)



(* -------------------------------------------------------------------------- *)
module BaseOpNamed = struct

  type op = EcPath.path * ty list

  type base = op (* FIXME : get it more complex to be able to enter
                      in functors of in module arguments, etc... *)

  type named1 = op

  type pos = int

  type interval = | Son of pos
                  (* | Between of pos * pos *)

  type matches = base EcMaps.Mstr.t

  type named = named1 gen_named

  type engine = {
      e_op : base ;
      e_map  : matches ;
    }


  (* val create_base : op -> base *)
  let create_base (p : op) : base = p

  (* val mkengine : base -> engine *)
  let mkengine (b : base) = {
      e_op = b ;
      e_map = Mstr.empty ;
    }

  (* val eat_down : engine -> engine *)
  let eat_down (_e : engine) = raise NoNext

  (* val eat_next : engine -> engine *)
  let eat_next (_e : engine) = raise NoNext

  (* val eat_up : engine -> engine *)
  let eat_up (_e : engine) = raise NoNext

  (* val eat : engine -> engine *)
  let eat (_e : engine) = raise NoNext

  let op_equal ((op1,lty1) : named1) ((op2,lty2) : named1) =
    try EcPath.p_equal op1 op2 && List.all2 ty_equal lty1 lty2 with
    | Invalid_argument _ -> false

  (* val eat_base : engine -> named1 -> engine * (pos * named) list *)
  let eat_base (e : engine) (op : named1) =
    if (op_equal op e.e_op) then e, []
    else raise NoMatches

  (* val position : engine -> pos *)
  let position (_e : engine) = 1

  (* val goto : engine -> pos -> engine *)
  let goto (e : engine) (i : int) = if i = 1 then e else raise NoNext

  let add (name : symbol) (id : base) (map : matches) =
    match Mstr.find_opt name map with
    | None -> Mstr.add name id map
    | Some id2 -> if (op_equal id id2) then map
                  else raise CannotUnify

  (* val add_match : engine -> interval -> EcSymbols.symbol -> engine *)
  let add_match (e : engine) (i : interval) (name : EcSymbols.symbol) (map : matches) =
    let map = match i with
      | Son 1 -> add name e.e_op map
      | Son _ -> raise CannotUnify
      (* | Between (1,1) -> add name e.e_op map *)
      (* | Between _ -> raise CannotUnify *)
    in { e with e_map = map }

  (* val get_matches : engine -> matches *)
  let get_matches (e : engine) = e.e_map


end

(* -------------------------------------------------------------------------- *)
module OpNamed = Named(BaseOpNamed)



(* -------------------------------------------------------------------------- *)
module BaseFPattern = struct

  type pattern = pattern1 gen_named

  and pattern1 =
    | Pquant  of quantif * BindingsNamed.named * pattern
    | Pif     of pattern * pattern * pattern
    | Pmatch  of pattern * pattern list
    | Plet    of lpattern * pattern * pattern
    | Pint    of EcBigInt.zint
    | Plocal  of IdentNamed.named
    | Ppvar   of PvarNamed.named
    | Pglob   of PglobNamed.named
    | Pop     of OpNamed.named
    | Papp    of pattern * pattern list
    | Ptuple  of pattern list
    | Pproj   of pattern * int

    (* | FhoareF of hoareF (\* $hr / $hr *\) *)
    (* | FhoareS of hoareS *)

    (* | FbdHoareF of bdHoareF (\* $hr / $hr *\) *)
    (* | FbdHoareS of bdHoareS *)

    (* | FequivF of equivF (\* $left,$right / $left,$right *\) *)
    (* | FequivS of equivS *)

    (* | FeagerF of eagerF *)

    | Ppr of EcMemory.memory * EcPath.xpath * pattern * pattern


  type base = form

  type matches = base Mstr.t

  type pos = int list

  type interval =
    | Son     of pos
    (* | Between of pos * pos *)

  type named1 = pattern1

  type named = pattern

  type pat_zipper =
    | PZEnd
    | PZTop
    | PZquant    of quantif * bindings                * pat_zipper
    | PZifcond   of form * form                       * pat_zipper
    | PZifthen   of form * form                       * pat_zipper
    | PZifelse   of form * form                       * pat_zipper
    | PZmatch1   of form list * ty                    * pat_zipper
    | PZmatch2   of form * form list * form list * ty * pat_zipper
    | PZlet1     of lpattern * form                   * pat_zipper
    | PZlet2     of lpattern * form                   * pat_zipper
    | PZappOp    of form list * ty                    * pat_zipper
    | PZappArgs  of form * form list * form list * ty * pat_zipper
    | PZtuple    of form list * form list             * pat_zipper
    | PZproj     of int * ty                          * pat_zipper
    | PZprArgs   of EcMemory.memory * EcPath.xpath * form
                                                      * pat_zipper
    | PZprEvent  of EcMemory.memory * EcPath.xpath * form
                                                      * pat_zipper


  type engine = {
      e_current   : form;
      e_context   : pat_zipper;
      e_map       : matches;
      e_pos       : pos;
    }

  (* ---------------------------------------------------------------------- *)

  (* val mkengine    : base -> engine *)
  let mkengine (f : form) : engine = { e_current = f ;
                                       e_context = PZTop ;
                                       e_map     = Mstr.empty ;
                                       e_pos     = [] ;
                                      }

  let go_down (e : engine) : engine = match e.e_current.f_node with
    | Fquant (quant,binds,f) ->
       { e with e_current = f ;
                e_context = PZquant (quant,binds,e.e_context) ;
                e_pos = 0 :: e.e_pos;
       }
    | Fif (cond,f1,f2) ->
       { e with e_context = PZifcond (f1,f2,e.e_context);
                e_current = cond;
                e_pos = 0 :: e.e_pos;
       }
    | Fmatch (f,f_list,typ) ->
       { e with e_current = f;
                e_context = PZmatch1 (f_list,typ,e.e_context);
                e_pos = 0 :: e.e_pos;
       }
    | Flet (lval,f1,f2) ->
       { e with e_current = f1;
                e_context = PZlet1 (lval,f2,e.e_context);
                e_pos = 0 :: e.e_pos;
       }
    | Fint _ -> raise NoNext
    | Flocal _ -> raise NoNext
    | Fpvar _ -> raise NoNext
    | Fglob _ -> raise NoNext
    | Fop _ -> raise NoNext
    | Fapp (op,args) ->
       { e with e_current = op;
                e_context = PZappOp (args,op.f_ty,e.e_context);
                e_pos = 0 :: e.e_pos;
       }
    | Ftuple [] -> raise NoNext
    | Ftuple (f :: after) ->
       { e with e_current = f;
                e_context = PZtuple ([],after,e.e_context);
                e_pos = 0 :: e.e_pos;
       }
    | Fproj (f,i) ->
       { e with e_current = f;
                e_context = PZproj (i,f.f_ty,e.e_context);
                e_pos = 0 :: e.e_pos;
       }
    | Fpr pr ->
       { e with e_current = pr.pr_args ;
                e_context = PZprArgs (pr.pr_mem, pr.pr_fun, pr.pr_event, e.e_context) ;
                e_pos = 0 :: e.e_pos ;
       }

    | (FhoareF _
      | FhoareS _
      | FbdHoareF _
      | FbdHoareS _
      | FequivF _
      | FequivS _
      | FeagerF _) -> raise NoMatches

  let go_up (e : engine) : engine = match e.e_context with
    | PZEnd -> raise NoNext
    | PZTop -> { e with e_context = PZEnd }
    | PZquant (quant,binds,context) ->
       { e with e_current = f_quant quant binds e.e_current ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZifcond (f1,f2,context) ->
       { e with e_current = f_if e.e_current f1 f2 ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZifthen (cond,f2,context) ->
       { e with e_current = f_if cond e.e_current f2 ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZifelse (cond,f1,context) ->
       { e with e_current = f_if cond f1 e.e_current ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZmatch1 (fs,typ,context) ->
       let f_match  b  fs ty = mk_form (Fmatch (b, fs, ty)) ty in
       { e with e_current = f_match e.e_current fs typ ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZmatch2 (f,before,after,typ,context) ->
       let f_match  b  fs ty = mk_form (Fmatch (b, fs, ty)) ty in
       let fs = List.rev_append before (e.e_current :: after) in
       { e with e_current = f_match f fs typ ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZlet1 (lval,f2,context) ->
       { e with e_current = f_let lval e.e_current f2 ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZlet2 (lval,f1,context) ->
       { e with e_current = f_let lval f1 e.e_current ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZappOp (args,typ,context) ->
       { e with e_current = f_app e.e_current args typ ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZappArgs (op,before,after,typ,context) ->
       let args = List.rev_append before (e.e_current :: after) in
       { e with e_current = f_app op args typ ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZtuple (before,after,context) ->
       let tuple = List.rev_append before (e.e_current :: after) in
       { e with e_current = f_tuple tuple ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }
    | PZproj (i,typ,context) ->
       { e with e_current = f_proj e.e_current i typ ;
                e_context = context ;
                e_pos = List.tl e.e_pos;
       }

    | PZprArgs (mem, proc, event, context) ->
       { e with e_current = f_pr mem proc e.e_current event ;
                e_context = context ;
                e_pos = List.tl e.e_pos ;
       }

    | PZprEvent (mem, proc, args, context) ->
       { e with e_current = f_pr mem proc args e.e_current ;
                e_context = context ;
                e_pos = List.tl e.e_pos ;
       }

  let go_next (e : engine) : engine = match e.e_context with
    | PZTop -> { e with e_context = PZEnd }
    | PZEnd -> raise NoNext
    | PZquant _ -> raise NoNext
    | PZifcond (f1,f2,context) ->
       { e with e_current = f1 ;
                e_context = PZifthen (e.e_current,f2,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZifthen (cond,f2,context) ->
       { e with e_current = f2 ;
                e_context = PZifelse (cond,e.e_current,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZifelse _ -> raise NoNext
    | PZmatch1 ([],_,_) -> raise NoNext
    | PZmatch1 (f::after,typ,context) ->
       { e with e_current = f ;
                e_context = PZmatch2 (e.e_current,[],after,typ,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZmatch2 (_,_,[],_,_) -> raise NoNext
    | PZmatch2 (op,before,f::after,typ,context) ->
       { e with e_current = f ;
                e_context = PZmatch2 (op,(e.e_current::before),after,typ,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZlet1 (lval,f2,context) ->
       { e with e_current = f2 ;
                e_context = PZlet2 (lval,e.e_current,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZlet2 _ -> raise NoNext
    | PZappOp ([],_,_) -> raise NoNext
    | PZappOp (f::after,typ,context) ->
       { e with e_current = f ;
                e_context = PZappArgs (e.e_current,[],after,typ,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZappArgs (_,_,[],_,_) -> raise NoNext
    | PZappArgs (op,before,f::after,typ,context) ->
       { e with e_current = f ;
                e_context = PZappArgs (op,e.e_current::before,after,typ,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZtuple (_,[],_) -> raise NoNext
    | PZtuple (before,f::after,context) ->
       { e with e_current = f ;
                e_context = PZtuple (e.e_current::before,after,context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos;
       }
    | PZproj _ -> raise NoNext
    | PZprArgs (mem, proc, event, context) ->
       { e with e_current = event ;
                e_context = PZprEvent (mem, proc, e.e_current, context) ;
                e_pos = (1 + List.hd e.e_pos) :: List.tl e.e_pos ;
       }
    | PZprEvent _ -> raise NoNext



  (* val eat_down    : engine -> engine *)
  let rec eat_down (e : engine) =
    try go_down e with
    | NoNext -> eat_next e

  (* val eat_next    : engine -> engine *)
  and eat_next (e : engine) =
    try go_next e with
    | NoNext -> let e' = try go_up e with
                         | NoNext -> raise NoMatches in
                eat_next e'
  (* val eat_up      : engine -> engine *)
  let eat_up = go_up

  (* val eat         : engine -> engine *)
  let eat e = eat_next e

  let rec zip_pos (acc : pos) (p : pat_zipper) = match p with
    | PZEnd -> acc
    | PZTop -> acc
    | PZquant (_,_,context) -> zip_pos (0 :: acc) context
    | PZifcond (_,_,context) -> zip_pos (0 :: acc) context
    | PZifthen (_,_,context) -> zip_pos (1 :: acc) context
    | PZifelse (_,_,context) -> zip_pos (2 :: acc) context
    | PZmatch1 (_,_,context) -> zip_pos (0 :: acc) context
    | PZmatch2 (_,before,_,_,context) ->
       zip_pos ((1 + List.length before) :: acc) context
    | PZlet1 (_,_,context) -> zip_pos (0 :: acc) context
    | PZlet2 (_,_,context) -> zip_pos (1 :: acc) context
    | PZappOp (_,_,context) -> zip_pos (0 :: acc) context
    | PZappArgs (_,before,_,_,context) ->
       zip_pos ((1 + List.length before) :: acc) context
    | PZtuple (before,_,context) ->
       zip_pos (List.length before :: acc) context
    | PZproj (_,_,context) -> zip_pos (0 :: acc) context
    | PZprArgs (_,_,_,context) -> zip_pos (0 :: acc) context
    | PZprEvent (_,_,_,context) -> zip_pos (1 :: acc) context

  (* val position    : engine -> pos *)
  let position (e : engine) : pos = e.e_pos

  (* let print_pos (p : pos) = *)
  (*   let s_pos = String.concat " :: " (List.map string_of_int p) in *)
  (*   raise  (Invalid_argument s_pos) *)

  (* val goto        : engine -> pos -> engine *)
  let goto_prefixe (e : engine) (p : pos) =
    let rec aux eng (l1 : pos) (l2 : pos) = match l1,l2 with
      | [], _ ->
         (List.fold_left (fun a _ -> go_up a) eng l2, [])
      | _, [] -> eng, l1
      | i1::rest1, i2::rest2 when i1 = i2 -> aux eng rest1 rest2
      | _::_, _::_  ->
         (List.fold_left (fun a _ -> go_up a) eng l2, l1)
    in aux e (List.rev p) (List.rev e.e_pos)

  let goto (e : engine) (p : pos) =
    let (eng, p) = goto_prefixe e p in
    let f (e : engine) (n : int) =
      let rec go_next_n_times e n =
        if (n <= 0) then e
        else let e' = go_next e in
             go_next_n_times e' (n-1) in
      let e' = go_down e in
      go_next_n_times e' n in
    List.fold_left f eng p

  (* (\* add_match can raise the exception : CannotUnify *\) *)
  let add_son (e : engine) (p : pos) (name : symbol) (map : matches) =
    let eng = goto e p in
    let f1 = eng.e_current in
    let map = match Mstr.find_opt name map with
      | None -> Mstr.add name f1 map
      | Some f2 -> if f_equal f1 f2 then map
                   else raise CannotUnify
    in { e with e_map = map }


  (* val add_match   : engine -> interval -> symbol -> engine *)
  let add_match (e : engine) (i : interval) (name : symbol) (map : matches) =
    match i with
    | Son p -> add_son e p name map
    (* | Between (i1,i2) -> if (List.all2 (=) i1 i2) then add_son e i1 name map *)
                          (* else raise CannotUnify *)

  (* val get_matches : engine -> matches *)
  let get_matches (e : engine) = e.e_map


  (* val eat_base    : engine -> named1 -> engine * (pos * named) list *)
  let eat_base (e : engine) (pat : pattern1) =
    match e.e_current.f_node, pat with
    | Fquant (q1,b1,_), Pquant (q2,b2_named,pat2) ->
       let map_opt q1 q2 = match q1,q2 with
         | Lforall,Lforall | Lexists,Lexists | Llambda,Llambda ->
            BindingsNamed.search b2_named b1
         | Lforall, (Lexists | Llambda)
           | Lexists, (Lforall | Llambda)
           | Llambda, (Lforall | Lexists) -> None in
       begin match map_opt q1 q2 with
       | None -> raise NoMatches
       | Some _map -> (* FIXME : get back this map to merge it with e.e_map *)
          (go_down e, [0::e.e_pos, pat2])
       end
    | Fif _, Pif (cond2,p1,p2) ->
       (e, [(0::e.e_pos,cond2) ; (1::e.e_pos,p1) ; (2::e.e_pos,p2)])

    | Fmatch _, Pmatch (p,pl) ->
       let f (i : int) (pat : pattern) = (i :: e.e_pos, pat) in
       (e, List.mapi f (p::pl))

    | Fapp _, Papp (pop,pargs)->
       let f (i : int) (pat : pattern) = (i :: e.e_pos, pat) in
       (e, List.mapi f (pop::pargs))

    | Ftuple _, Ptuple ptuple ->
       let f (i : int) (pat : pattern) = (i :: e.e_pos, pat) in
       (e, List.mapi f ptuple)

    | Flet (lval1,_,_), Plet (lval2, p1, p2) ->
       if (lp_equal lval1 lval2) then
         (e, [(0::e.e_pos,p1) ; (1::e.e_pos,p2)])
       else raise NoMatches

    | Fint i, Pint j -> if i = j then (eat_next e, [])
                        else raise NoMatches

    | Fproj (_,i), Pproj (p,j) ->
       if i = j then (eat_next e, [0::e.e_pos, p])
       else raise NoMatches

    | Flocal id, Plocal id_named -> begin
        match IdentNamed.search id_named id with
        | None -> raise NoMatches
        | Some _map -> (* FIXME : get back this map to merge it with e.e_map *)
           (eat e, [])
      end

    | Fpvar (pvar,mem), Ppvar pvar_named -> begin
        match PvarNamed.search
                pvar_named
                (BasePvarNamed.create_base (pvar,mem))
        with
        | None -> raise NoMatches
        | Some _map -> (* FIXME : get back this map to merge it with e.e_map *)
           (eat e, [])
      end

    | Fglob (module_name,mem), Pglob pglob_named -> begin
        match PglobNamed.search
                pglob_named
                (BasePglobNamed.create_base (module_name,mem))
        with
        | None -> raise NoMatches
        | Some _map -> (* FIXME : get back this map to merge it with e.e_map *)
           (eat e, [])
      end

    | Fop (op,typ_list), Pop op_named -> begin
        match OpNamed.search
                op_named
                (BaseOpNamed.create_base (op,typ_list))
        with
        | None -> raise NoMatches
        | Some _map -> (* FIXME : get back this map to merge it with e.e_map *)
           (eat e, [])
      end

    | (Fpr pr, Ppr (mem, proc, args, event)) ->
       if (EcMemory.mem_equal pr.pr_mem mem && EcPath.x_equal pr.pr_fun proc)
       then (eat_down e, List.mapi (fun i a -> (i::e.e_pos, a)) [args;event])
       else raise NoMatches


    | ((FhoareF _|FhoareS _|FbdHoareF _|FbdHoareS _|FequivF _|FequivS _
        |FeagerF _|Fpr _),
       (Pquant _ |Pif _ |Pmatch _ |Plet _ |Pint _ |Plocal _ |Ppvar _
        |Pglob _ |Pop _ |Papp _ |Ptuple _|Pproj _|Ppr _))
      | (Fop (_, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Plocal _|Ppvar _|Pglob _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Fglob (_, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Plocal _|Ppvar _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Fpvar (_, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Plocal _|Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Flocal _,
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Ppvar _|Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Fint _,
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Plocal _|Ppvar _|Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Flet (_, _, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Pint _|Plocal _|Ppr _
          |Ppvar _|Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Fmatch (_, _, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Plet (_, _, _)|Pint _|Plocal _|Ppr _
          |Ppvar _|Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Fif (_, _, _),
         (Pquant (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Pint _|Plocal _|Ppr _
          |Ppvar _|Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)))
      | (Fquant (_, _, _),
         (Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Pint _|Plocal _|Ppvar _
          |Pglob _|Pop _|Papp (_, _)|Ptuple _|Pproj (_, _)|Ppr _))
      | (Ftuple _,
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Plocal _|Ppvar _|Pglob _|Pop _|Papp (_, _)|Pproj (_, _)))
      | (Fapp (_, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Plocal _|Ppvar _|Pglob _|Pop _|Ptuple _|Pproj (_, _)))
      | (Fproj (_, _),
         (Pquant (_, _, _)|Pif (_, _, _)|Pmatch (_, _)|Plet (_, _, _)|Ppr _
          |Pint _|Plocal _|Ppvar _|Pglob _|Pop _|Papp (_, _)|Ptuple _))
      -> raise NoMatches


end

(* -------------------------------------------------------------------------- *)
module FormPattern = Named(BaseFPattern)


(* module ZipperFormula = struct *)

(*   type zipper_hole = *)
(*     | ZFTop *)
(*     | ZFtuple        of pformula list * pfomula list                * zipper_hole *)
(*     | ZFside         of symbol located                              * zipper_hole *)
(*     | ZFappOp        of pformula list                               * zipper_hole *)
(*     | ZFappArgs      of pformula * pformula list * pformula list    * zipper_hole *)
(*     | ZFifCond       of pformula * pformula                         * zipper_hole *)
(*     | ZFifThen       of pformula * pformula                         * zipper_hole *)
(*     | ZFifElse       of pformula * pformula                         * zipper_hole *)
(*     | ZFlet1         of plpattern * pty option * pformula           * zipper_hole *)
(*     | ZFlet2         of plpattern * (pformula * pty option)         * zipper_hole *)
(*     | ZFforall       of pgtybindings                                * zipper_hole *)
(*     | ZFexists       of pgtybindings                                * zipper_hole *)
(*     | ZFlambda       of ptybindings                                 * zipper_hole *)
(*     | ZFrecord       of pformula rfield * pformula rfield list * *)
(*                           pformula rfield list                      * zipper_hole *)
(*     | ZFproj         of pqsymbol                                    * zipper_hole *)
(*     | ZFproji        of int                                         * zipper_hole *)
(*     | ZFeqf          of pformula list * pformula list               * zipper_hole *)
(*     | ZFscope        of pqsymbol                                    * zipper_hole *)

(*     | ZFhoareFpre    of pgamepath * pformula                        * zipper_hole *)
(*     | ZFhoareFpost   of pformula * pgamepath                        * zipper_hole *)
(*     | ZFequivFpre    of (pgamepath * pgamepath) * pformula          * zipper_hole *)
(*     | ZFequivFpost   of pformula * (pgamepath * pgamepath)          * zipper_hole *)
(*     | ZFeagerFpre    of (pstmt * pgamepath * pgamepath * pstmt) * pformula *)
(*                                                                     * zipper_hole *)
(*     | ZFeagerFpost   of pformula * (pstmt * pgamepath * pgamepath * pstmt) *)
(*                                                                     * zipper_hole *)
(*     | ZFprobArgs     of pgamepath * (pformula list * pformula list) * *)
(*                           pmemory * pformula                        * zipper_hole *)
(*     | ZFprobRes      of pgamepath * (pformula list) * pmemory       * zipper_hole *)
(*     | ZFBDhoareFpre  of pgamepath * pformula * phoarecmp * pformula * zipper_hole *)
(*     | ZFBDhoareFpost of pformula * pgamepath * phoarecmp * pformula * zipper_hole *)
(*     | ZFBDhoareFcond of pformula * pgamepath * pformula * phoarecmp * zipper_hole *)

(* end *)

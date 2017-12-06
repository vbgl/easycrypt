open EcUtils
open EcModules
open EcPath
open EcFol
open EcTypes
open EcIdent
open EcGenRegexp
open EcMatching
open EcFMatching
open FPattern
open EcMaps
open EcEnv
open EcCoreGoal


module M = Map.Make(struct
  type t = xpath
  let compare = x_compare
end)

let quantif_of_equantif = function
  | `EExists -> Lexists
  | `EForall -> Lforall
  | `ELambda -> Llambda

type name =
  | Ident of ident
  | Args  of xpath * expr list

type names = name M.t

let get_name pv names = match M.find_opt pv.pv_name names with
  | None -> EcIdent.create (String.concat " " ["prog_var";":";EcPath.tostring pv.pv_name.x_sub])
  | Some (Ident name) -> name
  | Some _ -> raise (Invalid_argument "wrong name that collide with adversary's call's arguments")

let rec lvalue_to_pattern (names : names) (lv : lvalue) = match lv with
  | LvVar (pv,ty) ->
     let p,names = match pv.pv_kind with
       | PVglob -> Pobject (Oform (f_pvar pv ty mhr)), names
       | PVloc  ->
          let name = get_name pv names in
          Pnamed (Panything, name), (M.add pv.pv_name (Ident name) names)
     in names, p

  | LvTuple tuple ->
     let names, tuple =
       List.map_fold lvalue_to_pattern names (List.map (fun x -> LvVar x) tuple) in
     names, Ptuple tuple

  | LvMap _ ->
     raise (Invalid_argument "lvalue_to_form used with LvMap")

let rec expr_to_pattern (names : names) (e : expr) = match e.e_node with
  | Eint i    -> names, Pobject (Oform (f_int i))
  | Elocal id -> names, Pobject (Oform (f_local id e.e_ty))
  | Evar pv   ->
     let name = get_name pv names in
     (M.add pv.pv_name (Ident name) names), Pnamed (Panything, name)

  | Eop (op,lty) -> names, Pobject (Oform (f_op op lty e.e_ty))

  | Eapp (e1,el) ->
     let names, p1 = expr_to_pattern names e1 in
     let names, pl = List.map_fold expr_to_pattern names el in
     if List.for_all (function | Pobject (Oform _) -> true | _ -> false) (p1::pl)
     then names,
          Pobject (Oform (form_of_expr mhr e))
     else names, Papp (p1,pl)
  | Equant (q,b,e1) ->
     let names, p1 = expr_to_pattern names e1 in
     let p = match p1 with
       | Pobject (Oform _) -> Pobject (Oform (form_of_expr mhr e))
       | _ -> Pquant ((quantif_of_equantif q),(List.map  (fun (x,y) -> x, GTty y) b),p1) in
     names, p
  | Elet _ -> names, Pobject (Oform (form_of_expr mhr e)) (* FIXME *)
  | Etuple tuple ->
     let names, ptuple = List.map_fold expr_to_pattern names tuple in
     if List.for_all (function | Pobject (Oform _) -> true | _ -> false) ptuple
     then names,
          Pobject (Oform (form_of_expr mhr e))
     else names, Ptuple ptuple

  | Eif (e1,e2,e3) ->
     let names, p = match List.map_fold expr_to_pattern names [e1;e2;e3] with
       | names, (Pobject (Oform _))::(Pobject (Oform _))::(Pobject (Oform _))::[] ->
          names, Pobject (Oform (form_of_expr mhr e))
       | names, p1::p2::p3::[] ->
          names, Pif (p1,p2,p3)
       | _ -> assert false
     in names, p
  | Ematch _ -> names, Pobject (Oform (form_of_expr mhr e))
  | Eproj (e1,i) ->
     let names, p = match expr_to_pattern names e1 with
       | names, Pobject (Oform _) -> names, Pobject (Oform (form_of_expr mhr e))
       | names, p -> names, Pproj (p,i)
     in names, p



(* (\* -------------------------------------------------------------------- *\) *)
(* let lv_subst m lv f = *)
(*   match lv with *)
(*   | LvVar _ -> lv,m,f *)
(*   | LvTuple _ -> lv,m,f *)
(*   | LvMap((p,tys),pv,e,ty) -> *)
(*     let set = f_op p tys (toarrow [ty; e.e_ty; f.f_ty] ty) in *)
(*     let f   = f_app set [f_pvar pv ty m; form_of_expr m e; f] ty in *)
(*     LvVar(pv,ty), m, f *)

let stmt_to_pattern (s1 : stmt) =
  let rec aux_instr (names : names) (i : instr) = match i.i_node with
    | Sasgn (lv,e) ->
       let names, p2 = expr_to_pattern names e in
       let names, p1 = lvalue_to_pattern names lv in
       names, Base (RAssign (p1,p2))
    | Srnd (lv,e) ->
       let names, p2 = expr_to_pattern names e in
       let names, p1 = lvalue_to_pattern names lv in
       names, Base (RSample (p1,p2))
    | Scall (xopt, xp, e) ->
       let names, p =
         match xp.x_top.m_top with
         | `Local id -> (* FIXME : add the treatment of module arguments *)
            (M.add xp (Args (xp,e)) names), Named (Repeat (Any, (None, None), `Greedy),
                          String.concat " " [EcIdent.tostring id;"body"])
         | `Concrete _ ->
            let names, p1 = match xopt with
              | None -> names, Panything
              | Some lv -> lvalue_to_pattern names lv in
            let p2 = Pxpath xp in
            let names, p3 = List.map_fold expr_to_pattern names e in
            names, Base (RCall (p1,p2,Ptuple p3))
       in names, p
    | Sif (e,s1,s2) ->
       let names, p1 = expr_to_pattern names e in
       let names, p2 = List.map_fold aux_instr names s1.s_node in
       let names, p3 = List.map_fold aux_instr names s2.s_node in
       names, Base (RIf (p1,Seq p2,Seq p3))

    | Swhile (e,s1) ->
       let names, p1 = expr_to_pattern names e in
       let names, p2 = List.map_fold aux_instr names s1.s_node in
       names, Base (RWhile (p1,Seq p2))

    | _ -> raise (Invalid_argument "assert of abstract value in statement when processed in stmt_to_pattern")
  in
  let names = M.empty in
  let names, s = List.map_fold aux_instr names s1.s_node in
  (* let s = (Anchor Start)::s @ [Anchor End] in *)
  names, Seq s

let abstract_locals args adv s =
  let rec instr_abstract_local (i : int) (arg : expr) (instr : instr) = match instr.i_node with
    | Sasgn (lv,e) ->
       let lv = lv_abstract_local i arg lv in
       let e = expr_abstract_local i arg e in
       i_asgn (lv,e)
    | Srnd (lv,e) ->
       let lv = lv_abstract_local i arg lv in
       let e = expr_abstract_local i arg e in
       i_rnd (lv,e)
    | Scall (xopt,xp,args) ->
       let xopt = omap (lv_abstract_local i arg) xopt in
       let args = List.map (expr_abstract_local i arg) args in
       i_call (xopt,xp,args)
    | Sif (e,s1,s2) ->
       let e = expr_abstract_local i arg e in
       let s1 = stmt_abstract_local s1 i arg in
       let s2 = stmt_abstract_local s2 i arg in
       i_if (e,s1,s2)
    | Swhile (e,s) ->
       let e = expr_abstract_local i arg e in
       let s = stmt_abstract_local s i arg in
       i_while (e,s)
    | _ -> raise (Invalid_argument "assert or abstract in instr_abstract_local")

  and expr_abstract_local i arg e =
    if e_equal e arg then
      e_proj (e_var (pv_arg adv) e.e_ty) i e.e_ty
    else
      let aux = expr_abstract_local i arg in
      match e.e_node with
      | Eint _
      | Elocal _
      | Evar _ | Eop _ -> e
      | Equant (q,b,e) -> e_quantif q b (aux e)
      | Eapp (e1,le) -> e_app (aux e1) (List.map aux le) e.e_ty
      | Elet (lp,e1,e2) -> e_let lp (aux e1) (aux e2)
      | Etuple tuple -> e_tuple (List.map aux tuple)
      | Eif (e1,e2,e3) -> e_if (aux e1) (aux e2) (aux e3)
      | Ematch (e1,el,ty) -> e_match (aux e1) (List.map aux el) ty
      | Eproj (e1,j) -> e_proj (aux e1) j e.e_ty

  and lv_abstract_local _ arg lv = match lv with
    | LvVar (pv1,ty) ->
       let lv = match arg.e_node with
         | Evar pv2 when pv_equal pv1 pv2 ->
            LvVar (pv_arg adv,ty)
         | _ -> lv
       in lv

    | LvTuple _ -> lv

    | LvMap _ -> lv


  and stmt_abstract_local (s : stmt) (i : int) (arg : expr) =
    stmt (List.map (instr_abstract_local i arg) s.s_node)

  and stmt_abstract_args args s =
    List.fold_lefti stmt_abstract_local s args

  in stmt_abstract_args args s



let find_instance (s1 : stmt) (s2 : stmt) (hyps : LDecl.hyps) =
  let names, pattern = stmt_to_pattern s1 in
  match RegexpStmt.search pattern s2.s_node hyps with
  | None -> raise (Invalid_argument "No matches")
  | Some (mvars,minstrs) ->
     let var_names = M.values names in
     let aux acc = function
       | Ident _id -> acc
       | Args (e,adv) -> e,adv in
     let adv,args = List.fold_left aux (xpath (mpath (`Local (EcIdent.create "A")) []) (psymbol "A"),[])  var_names in
     let minstrs =
       Mstr.map (fun s -> (abstract_locals args adv (stmt s)).s_node) minstrs in

     names,mvars,minstrs



let try_instance (tc1 : tcenv1) : tcenv =
  let env = FApi.tc1_env tc1 in
  let fmt = Format.std_formatter in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let _ =
    try
      let f = FApi.tc1_goal tc1 in
      let s1,s2 = match f.f_node with
        | FequivS s -> s.es_sl, s.es_sr
        | _ -> raise (Invalid_argument "Not an equivalence between statements in try_instance.") in
      let h = FApi.tc1_hyps tc1 in
      let names,mvars,minstrs = find_instance s1 s2 h in

      let print_stmt x =  Format.fprintf fmt "%a\n" (EcPrinting.pp_stmt ppe) x in
      let print_instrs n i =
        let _ = Format.fprintf fmt "with name \"%a\" :\n" (EcPrinting.pp_local ppe) (EcIdent.create n) in
        print_stmt (stmt i)
      in

      let print_tobject = function
        | (Omem m,_) ->
           Format.fprintf fmt "%a\n" (EcPrinting.pp_local ppe) m
        | Oform f,_ ->
           Format.fprintf fmt "%a\n" (EcPrinting.pp_form ppe) f
        | _,_ -> ()
      in

      let print_vars n o =
        let _ = Format.fprintf fmt "with name \"%a\" :\n" (EcPrinting.pp_local ppe) n in
        let _ = print_tobject o in
        () in

      let print_names pv n = match n with
        | Ident id ->
           let _ = Format.fprintf fmt "Local variable \"%a\" is " (EcPrinting.pp_funname ppe) pv in
           Format.fprintf fmt "named \"%a\".\n" (EcPrinting.pp_local ppe) id
        | Args (_,arg) ->
           let _ = Format.fprintf fmt "Adversary \"%a\"'s arguments are " (EcPrinting.pp_funname ppe) pv in
           List.iter (Format.fprintf fmt "\"%a\"\n" (EcPrinting.pp_form ppe)) (List.map (form_of_expr mhr) arg)
      in

      let _ =
        Format.fprintf fmt "%a :\n" (EcPrinting.pp_local ppe) (EcIdent.create "Local variables") in
      let _ = M.iter print_names names in
      let _ =
        Format.fprintf fmt "%a :\n" (EcPrinting.pp_local ppe) (EcIdent.create "Named sub-formules") in
      let _ = Mid.iter print_vars mvars in
      let _ =
        Format.fprintf fmt "%a :\n" (EcPrinting.pp_local ppe) (EcIdent.create "Adversary's body") in
      let _ = Mstr.iter print_instrs minstrs in
      ()
    with
    | Invalid_argument s ->
       Format.fprintf
         fmt "%a\n" (EcPrinting.pp_form ppe)
         (EcFol.f_local (EcIdent.create (String.concat "\n" ["there_is_no_map";s])) EcTypes.tint)
  in (!@) tc1

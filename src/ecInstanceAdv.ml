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

let replace_pvar_by_pvar_in_expr pv1 pv2 e =
  let rec aux e =
    match e.e_node with
    | Eint _
      | Elocal _
      | Eop _ -> e
    | Equant (q,b,e) -> e_quantif q b (aux e)
    | Eapp (e1,le) -> e_app (aux e1) (List.map aux le) e.e_ty
    | Elet (lp,e1,e2) -> e_let lp (aux e1) (aux e2)
    | Etuple tuple -> e_tuple (List.map aux tuple)
    | Eif (e1,e2,e3) -> e_if (aux e1) (aux e2) (aux e3)
    | Ematch (e1,el,ty) -> e_match (aux e1) (List.map aux el) ty
    | Eproj (e1,j) -> e_proj (aux e1) j e.e_ty
    | Evar pv -> if pv_equal pv1 pv then e_var pv2 e.e_ty else e
  in aux e



let replace_pvar_in_expr (pv1 : prog_var) (e2 : expr) (e : expr) =
  match e2.e_node with
  | Evar pv2 -> replace_pvar_by_pvar_in_expr pv1 pv2 e
  | _ ->
     let rec aux e =
       match e.e_node with
       | Eint _
         | Elocal _
         | Eop _ -> e
       | Equant (q,b,e) -> e_quantif q b (aux e)
       | Eapp (e1,le) -> e_app (aux e1) (List.map aux le) e.e_ty
       | Elet (lp,e1,e2) -> e_let lp (aux e1) (aux e2)
       | Etuple tuple -> e_tuple (List.map aux tuple)
       | Eif (e1,e2,e3) -> e_if (aux e1) (aux e2) (aux e3)
       | Ematch (e1,el,ty) -> e_match (aux e1) (List.map aux el) ty
       | Eproj (e1,j) -> e_proj (aux e1) j e.e_ty
       | Evar pv -> if pv_equal pv1 pv then e2 else e
     in aux e


let replace_expr_in_expr (e1 : expr) (e2 : expr) (e : expr) (h : LDecl.hyps) =
  match e1.e_node with
  | Evar pv -> replace_pvar_in_expr pv e2 e
  | _ ->
     let f1 = form_of_expr mhr e1 in
     let rec aux e =
       let f = form_of_expr mhr e in
       if (EcReduction.is_conv h f1 f) then e2
       else
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
     in aux e



let replace_pvar_in_lvalue (pv1 : prog_var) (pv2 : prog_var) (lv : lvalue) =
  match lv with
  | LvVar (pv,ty) when pv_equal pv1 pv -> LvVar (pv2,ty)
  | LvVar _ -> lv
  | LvTuple tuple ->
     LvTuple (List.map (fun (x,t) -> if pv_equal x pv1 then (pv2,t) else (x,t)) tuple)
  | LvMap ((a,b),pv,e,t) ->
     let pv = if pv_equal pv1 pv then pv2 else pv in
     let e = replace_pvar_in_expr pv1 (e_var pv2 t) e in
     LvMap ((a,b),pv,e,t)


(* (\* -------------------------------------------------------------------- *\) *)
(* let lv_subst m lv f = *)
(*   match lv with *)
(*   | LvVar _ -> lv,m,f *)
(*   | LvTuple _ -> lv,m,f *)
(*   | LvMap((p,tys),pv,e,ty) -> *)
(*     let set = f_op p tys (toarrow [ty; e.e_ty; f.f_ty] ty) in *)
(*     let f   = f_app set [f_pvar pv ty m; form_of_expr m e; f] ty in *)
(*     LvVar(pv,ty), m, f *)

let harmonize_lv_e ((lv,e) : lvalue * expr) = match lv with
  | LvMap ((p,tys),pv,e',ty) ->
     let set = e_op p tys (toarrow [ty;e'.e_ty;e.e_ty] ty) in
     let e = e_app set [e_var pv ty; e'; e] ty in
     (LvVar (pv,ty),e)
  | _ -> (lv,e)


let rec replace_expr_in_lv_e (e1 : expr) (e2 : expr) ((lv,e) : lvalue * expr) (h : LDecl.hyps) =
  match e1.e_node, e2.e_node,lv with
  | Evar pv1, Evar pv2,_ ->
     let lv = replace_pvar_in_lvalue pv1 pv2 lv in
     let e = replace_pvar_in_expr pv1 e2 e in
     (lv,e)

  | _,_,LvMap _ ->
     replace_expr_in_lv_e e1 e2 (harmonize_lv_e (lv,e)) h
  | _,_,_ ->
     let e = replace_expr_in_expr e1 e2 e h in
     (lv,e)


let rec instr_abstract_local (e1 : expr) (e2 : expr) h (instr : instr) =
  match instr.i_node with
  | Sasgn (lv,e) ->
     i_asgn (replace_expr_in_lv_e e1 e2 (lv,e) h)
  | Srnd (lv,e) ->
     i_rnd (replace_expr_in_lv_e e1 e2 (lv,e) h)
  | Scall (optlv,xp,args) ->
     i_call (optlv,xp,List.map (fun x -> replace_expr_in_expr e1 e2 x h) args)
  | Sif (e,s1,s2) ->
     let e = replace_expr_in_expr e1 e2 e h in
     let s1 = stmt_abstract_local e1 e2 h s1.s_node in
     let s2 = stmt_abstract_local e1 e2 h s2.s_node in
     i_if (e,stmt s1,stmt s2)
  | Swhile (e,s) ->
     let e = replace_expr_in_expr e1 e2 e h in
     let s = stmt_abstract_local e1 e2 h s.s_node in
     i_while (e,stmt s)
  | _ -> raise (Invalid_argument "assert or abstract in instr_abstract_local")

and stmt_abstract_local e1 e2 h (s : instr list) : instr list =
  List.map (instr_abstract_local e1 e2 h) s


let abstract_args args adv (s : instr list) h =
  match args with
  | [] -> s
  | [arg] ->
     stmt_abstract_local arg (e_var (pv_arg adv) arg.e_ty) h s
  | _ ->
     let arg i e = e_proj (e_var (pv_arg adv) e.e_ty) i (e_ty (e_tuple args)) in
     List.fold_lefti (fun s i e ->
         stmt_abstract_local e (arg i e) h s) s args

let rec instr_abstract_pv pv1 pv2 i =
  match i.i_node with
  | Sasgn (lv,e) ->
     let lv = replace_pvar_in_lvalue pv1 pv2 lv in
     let e = replace_pvar_by_pvar_in_expr pv1 pv2 e in
     i_asgn (lv,e)
  | Srnd (lv,e) ->
     let lv = replace_pvar_in_lvalue pv1 pv2 lv in
     let e = replace_pvar_by_pvar_in_expr pv1 pv2 e in
     i_rnd (lv,e)
  | Scall (optlv,xp,args) ->
     let optlv = omap (replace_pvar_in_lvalue pv1 pv2) optlv in
     i_call (optlv,xp,List.map (replace_pvar_by_pvar_in_expr pv1 pv2) args)
  | Sif (e,s1,s2) ->
     let e = replace_pvar_by_pvar_in_expr pv1 pv2 e in
     let s1 = stmt_abstract_pv pv1 pv2 s1.s_node in
     let s2 = stmt_abstract_pv pv1 pv2 s2.s_node in
     i_if (e,stmt s1,stmt s2)
  | Swhile (e,s) ->
     let e = replace_pvar_by_pvar_in_expr pv1 pv2 e in
     let s = stmt_abstract_pv pv1 pv2 s.s_node in
     i_while (e,stmt s)
  | _ -> raise (Invalid_argument "assert or abstract in instr_abstract_pv")

and stmt_abstract_pv pv1 pv2 =
  List.map (instr_abstract_pv pv1 pv2)

let stmt_abstract_pv_form x y s = match y with
  | (Oform f,binds) when Mid.is_empty binds -> begin
      match f.f_node with
      | Fpvar (pv,_) -> stmt_abstract_pv pv x s
      | _ -> raise (Invalid_argument "stmt_abstract_pv_form : meta-name matched with a non-prog_var")
    end
  | (Oform _,_) -> raise (Invalid_argument "stmt_abstract_pv_form : binds not empty")
  | _ -> raise (Invalid_argument "stmt_abstract_pv_form : not a formula")


let rec get_args adv = function
  | [] -> []
  | [arg] -> [arg,(pv_arg adv).pv_name]
  | args -> List.map (fun x -> x,(pv_arg adv).pv_name) args

let find_instance (s1 : stmt) (s2 : stmt) (hyps : LDecl.hyps) =
  let names, pattern = stmt_to_pattern s1 in
  match RegexpStmt.search pattern s2.s_node hyps with
  | None -> raise (Invalid_argument "No matches")
  | Some (mvars,minstrs) ->
     let var_names = M.bindings names in
     let aux (acc1,acc2) = function
       | pv,Ident id -> (acc1,(pv,id)::acc2)
       | _,Args (e,adv) -> ((e,adv),acc2) in
     let (adv,args),var_names =
       List.fold_left aux ((xpath (mpath (`Local (EcIdent.create "A")) []) (psymbol "A"),[]),[]) var_names in
     let var_binds = List.map (fun (p,id) -> (pv p PVloc,Mid.find id mvars)) var_names in
     let minstrs =
       Mstr.map (fun s ->
           List.fold_left (fun s (x,y) -> stmt_abstract_pv_form x y s) s var_binds)
                minstrs in
     let minstrs =
       Mstr.map (fun s -> abstract_args args adv s hyps) minstrs in
     let args = get_args adv args in
     names,mvars,minstrs,args


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
      let names,mvars,minstrs,args = find_instance s1 s2 h in

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

      let print_args (arg,pv) =
        let _ = Format.fprintf fmt "Argument \"%a\" is set as " (EcPrinting.pp_funname ppe) pv in
        Format.fprintf fmt "%a\n" (EcPrinting.pp_form ppe) (form_of_expr mhr arg)
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
      let _ = List.iter print_args args in
      ()
    with
    | Invalid_argument s ->
       Format.fprintf
         fmt "%a\n" (EcPrinting.pp_form ppe)
         (EcFol.f_local (EcIdent.create (String.concat "\n" ["there_is_no_map";s])) EcTypes.tint)
  in (!@) tc1

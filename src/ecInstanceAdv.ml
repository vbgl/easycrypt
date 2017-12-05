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
  | Args  of expr list

type names = name M.t


let rec lvalue_to_pattern (names : names) (lv : lvalue) = match lv with
  | LvVar (pv,ty) ->
     let p,names = match pv.pv_kind with
       | PVglob -> Pobject (Oform (f_pvar pv ty mhr)), names
       | PVloc  ->
          let name = match M.find_opt pv.pv_name names with
            | None -> EcIdent.create (String.concat " " ["prog_var";":";EcPath.tostring pv.pv_name.x_sub])
            | Some (Ident name) -> name
            | Some _ -> raise (Invalid_argument "wrong name that collide with adversary's call's arguments") in
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
     let name = match M.find_opt pv.pv_name names with
       | None -> EcIdent.create (String.concat " " ["prog_var";":";EcPath.tostring pv.pv_name.x_sub])
       | Some (Ident name) -> name
       | Some _ -> raise (Invalid_argument "wrong name that collide with adversary's call's arguments") in
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
       let names, p1 = lvalue_to_pattern names lv in
       let names, p2 = expr_to_pattern names e in
       names, Base (RAssign (p1,p2))
    | Srnd (lv,e) ->
       let names, p1 = lvalue_to_pattern names lv in
       let names, p2 = expr_to_pattern names e in
       names, Base (RSample (p1,p2))
    | Scall (xopt, xp, e) ->
       let names, p =
         match xp.x_top.m_top with
         | `Local id ->
            (M.add xp (Args e) names), Named (Repeat (Any, (None, None), `Greedy),
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
  names, Seq s


let find_instance (s1 : stmt) (s2 : stmt) (hyps : LDecl.hyps) =
  let _names, pattern = stmt_to_pattern s1 in
  match RegexpStmt.search pattern s2.s_node hyps with
  | None -> None
  | Some (mvars,minstrs) -> Some (mvars, minstrs)

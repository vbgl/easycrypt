(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcModules
open EcLowPhlGoal


(* FIXME move this *)
let p_not env p1 = 
  let x,ty,p1 = get_lambda1 env p1 in
  f_lambda [x,GTty ty] (f_not p1)

let p_imp env p1 p2 = 
  let x,ty,p1 = get_lambda1 env p1 in
  f_lambda [x,GTty ty] (f_imp p1 (f_app_simpl p2 [f_local x ty] tbool))

let p_and env p1 p2 = 
  let x,ty,p1 = get_lambda1 env p1 in
  f_lambda [x,GTty ty] (f_and p1 (f_app_simpl p2 [f_local x ty] tbool))

let p_forall_imp env p1 p2 = 
  f_pred2forall env (p_imp env p1 p2)

(*
(* -------------------------------------------------------------------- *)
let lmd_app (id,mt) ((id',mt'), body as f) =
  
   assert (EcMemory.mt_equal mt mt');
   if EcIdent.id_equal id id' then f
   else 
     let body =  Fsubst.f_subst_mem id' mt id body in
     (id,mt), body
*)

(* -------------------------------------------------------------------- *)
let oplus ty mu mu1 mu2 f =
  let is_mu (id,_) = EcIdent.id_equal id mu in
  let check_mu1mu2 (id,_) =
    assert (not (EcIdent.id_equal id mu1));
    assert (not (EcIdent.id_equal id mu2)) in
  let check_binding b =
    if is_mu b then true else (check_mu1mu2 b; false) in
  
  let check_pattern = function
    | LSymbol b -> check_binding b
    | LTuple bs -> List.exists check_binding bs
    | LRecord(_,bs) ->
      List.exists
        (fun (id,ty) -> if id = None then false else check_binding (oget id,ty))
        bs in

  let mu1 = f_local mu1 ty in
  let mu2 = f_local mu2 ty in

  let rec aux f = 
    match f.f_node with
    | Fapp({f_node = Fop(op, _)} as muf, [ff; {f_node = Flocal mu'}]) 
        when EcIdent.id_equal mu mu' &&
          EcPath.p_equal op EcCoreLib.CI_Distr.p_muf ->
      let ff = aux ff in
      let domu mu = f_app muf [ff;mu] f.f_ty in
      f_real_add (domu mu1) (domu mu2)

    | Flocal mu' -> assert (not (EcIdent.id_equal mu mu')); f

    | Fquant(q,b,f1) ->
      if List.exists check_binding b then f
      else f_quant q b (aux f1)
    | Flet (lp,f1,f2) ->
      let f1 = aux f1 in
      if check_pattern lp then f_let lp f1 f2
      else f_let lp f1 (aux f2)
    | FhoareF   _ | FhoareS   _
    | FbdHoareF _ | FbdHoareS _
    | FequivF   _ | FequivS   _
    | FeagerF   _ | Fpr       _
    | FmuhoareF _ | FmuhoareS _ -> assert false (* can be implemented *)
    | _ -> f_map (fun ty -> ty) aux f in

  aux f

(* -------------------------------------------------------------------- *)
let do_on_mu env onld ?mt' f =

  let mu, ty, f = get_lambda1 env f in
  let mt = EcUnify.destr_tdmem env ty in
  let tmt' = tmem (odfl mt mt') in
  let loc_mu = f_local mu (tdistr tmt') in 
 
  let check_binding (id,_) = EcIdent.id_equal id mu in

  let check_pattern = function
    | LSymbol b -> check_binding b
    | LTuple bs -> List.exists check_binding bs
    | LRecord(_,bs) ->
      List.exists
        (fun (id,ty) -> if id = None then false else check_binding (oget id,ty))
        bs in
 
  let rec aux f =
    if Mid.mem mu f.f_fv then
      match f.f_node with
      | Fapp({f_node = Fop(op, _)}, [f1; {f_node = Flocal mu'}]) 
          when EcIdent.id_equal mu mu' &&
          EcPath.p_equal op EcCoreLib.CI_Distr.p_muf ->
        let f1 = aux f1 in
        f_muf_ty tmt' (onld f1) loc_mu
 
      | Flocal mu' -> assert (not (EcIdent.id_equal mu mu')); f

      | Fquant(q,b,f1) ->
        if List.exists check_binding b then f
        else f_quant q b (aux f1)
      | Flet (lp,f1,f2) ->
        let f1 = aux f1 in
        if check_pattern lp then f_let lp f1 f2
        else f_let lp f1 (aux f2)
      | FhoareF   _ | FhoareS   _
      | FbdHoareF _ | FbdHoareS _
      | FequivF   _ | FequivS   _
      | FeagerF   _ | Fpr       _
      | FmuhoareF _ | FmuhoareS _ -> assert false (* can be implemented *)
      | _ -> f_map (fun ty -> ty) aux f
    else f
  in

  f_lambda [ mu, GTty (tdistr tmt')] (aux f)
  
let get_lambda1_mem env f = 
  let m, mty, f = get_lambda1 env f in
  let mt = EcUnify.destr_tmem env mty in
  m, mt, f
 
let mu_restr env pos b f = 
  let ldm_restr f =
    let m, mt, f = get_lambda1_mem env f in
    let b = form_of_expr (Some (m,mt)) b in
    let b = if pos then b else f_not b in
    f_lambda [m,gtmem mt] (f_real_mul (f_real_of_bool b) f) in
  do_on_mu env ldm_restr f

let curly env b f1 f2 = 
    p_and env (mu_restr env true b f1) (mu_restr env false b f2) 

(* -------------------------------------------------------------------- *)
exception NoWpMuhoare

let rec pt_muhoare_i env m i f =
  match i.i_node with
  | Sasgn (lv,e) ->
    let let1 = lv_subst m lv (form_of_expr (Some m) e) in
    mk_let_of_lv_substs env ([let1],f)
  | Srnd (lv,d) ->
    let ty_distr = d.e_ty in
    let ty = EcUnify.destr_tdistr env ty_distr in
    let x_id  = EcIdent.create (symbol_of_lv lv ^ "_") in
    let x = f_local x_id ty in
    let fun_ = f_lambda [x_id, GTty ty] (subst_form_lv env m lv x f) in
    f_muf_ty ty fun_ (form_of_expr (Some m) d)

  | Sif(b,s1,s2) ->
    let f1 = pt_muhoare env m s1 f in
    let f2 = pt_muhoare env m s2 f in
    let b = form_of_expr (Some m) b in
    let rb = f_real_of_bool b in
    let rnb = f_real_of_bool (f_not b) in
    f_real_add (f_real_mul rb f1) (f_real_mul rnb f2)
  | _ -> raise NoWpMuhoare

and pt_muhoare env m s f =
  List.fold_right (pt_muhoare_i env m) s.s_node f

(* -------------------------------------------------------------------- *)
let wp_muhoare env s po =
  let onld f = 
    let m, mt, f = get_lambda1_mem env f in
    f_lambda [m, gtmem mt] (pt_muhoare env (m,mt) s f) in
  do_on_mu env onld po

(* -------------------------------------------------------------------- *)
let wp_ret env mt' pvres e po = 
  let onld f = 
    let m, mt, f = get_lambda1_mem env f in
    let mmt = (m,mt) in
    let let1 = lv_subst mmt (LvVar (pvres, e.e_ty)) (form_of_expr (Some mmt) e) in
    let f = (mk_let_of_lv_substs env ([let1],f)) in
    (* this is realy durty ... *)
    let subst = Fsubst.f_subst_mem m mt' m in
    f_lambda [m, gtmem mt'] (subst f) in
  do_on_mu env onld ~mt' po

(* -------------------------------------------------------------------- *)
let wp_pre env mt' f fs pr = 
  let gmt' = gtmem mt' in
  let onld = 
    match fs.fs_anames with
    | None -> 
      fun f ->
        let m,_,f = get_lambda1_mem env f in 
        f_lambda [m,gmt'] (Fsubst.f_subst_mem m mt' m f)

    | Some lv ->
      fun f1 ->
        let m,mt,f1 = get_lambda1_mem env f1 in
        let v = List.map (fun v -> f_pvloc f v (f_mem (m,mt))) lv in
        let tv = (f_tuple v) in
        let let1 = lv_subst (m,mt) (LvVar (pv_arg f, tv.f_ty)) tv in
        let f1 = mk_let_of_lv_substs env ([let1],f1) in
        f_lambda [m, gmt'] (Fsubst.f_subst_mem m mt' m f1) in
  do_on_mu env onld ~mt' pr

(* -------------------------------------------------------------------- *)
let max_wp s =
  let rec aux_i i =
    match i.i_node with
    | Sasgn _ -> true
    | Srnd _ -> true
    | Sif (_,s1,s2) -> aux s1 = 0 && aux s2 = 0
    | _  -> false
  and aux_s s =
    match s with
    | i::s when aux_i i -> aux_s s
    | _ -> List.length s
  and aux s = aux_s (List.rev s.s_node) in
  aux s

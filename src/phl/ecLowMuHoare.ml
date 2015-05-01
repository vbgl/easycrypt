open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcModules
open EcLowPhlGoal

let ldm_app (id,mt) ((id',mt'), body as f) = 
   assert (EcMemory.mt_equal mt mt');
   if EcIdent.id_equal id id' then f
   else 
     let body =  Fsubst.f_subst_mem id' id body in
     (id,mt), body

let ldm_imp (b,f1) f2 =
  let _, f2 = ldm_app b f2 in
  b, f_imp f1 f2

let ldm_forall_imp f1 f2 = f_forall_distr (ldm_imp f1 f2)

let oplus mu mu1 mu2 f =
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
    
  let rec aux f = 
    match f.f_node with
    | Fintegr {ig_fo = ldm; ig_mu = mu'} ->
      let ldm = aux_ldm ldm in
      if EcIdent.id_equal mu mu' then
        f_real_add (f_integr ldm mu1) (f_integr ldm mu2) 
      else f_integr ldm mu'
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

  and aux_ldm (b,f1 as f) = if check_binding b then f else (b,aux f1) in

  aux f

let do_on_mu onld mu f = 

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
      | Fintegr {ig_fo = ldm; ig_mu = mu'} ->
        let ldm = aux_ldm ldm in
        if EcIdent.id_equal mu mu' then f_integr (onld ldm) mu 
        else f_integr ldm mu'
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

  and aux_ldm (b,f1 as f) = if check_binding b then f else (b,aux f1) in

  aux f
  
  

let mu_restr mu pos b f = 
  let ldm_restr ((m,mt), f) =
    let b = form_of_expr m b in
    let b = if pos then b else f_not b in
    (m,mt), f_real_mul (f_real_of_bool b) f in
  do_on_mu ldm_restr mu f

let curly b ((mu,mt),f1) f2 = 
  let _, f2 = ldm_app (mu,mt) f2 in
  (mu,mt), f_and (mu_restr mu true b f1) (mu_restr mu false b f2) 

exception NoWpMuhoare 

let rec pt_muhoare_i env m i f =  
  match i.i_node with
  | Sasgn (lv,e) ->
    let let1 = lv_subst m lv (form_of_expr m e) in
    mk_let_of_lv_substs env ([let1],f)
  | Srnd (lv,d) ->
    let ty_distr = d.e_ty in
    let ty = proj_distr_ty env ty_distr in
    let x_id  = EcIdent.create (symbol_of_lv lv ^ "_") in
    let x = f_local x_id ty in
    let fun_ = f_lambda [x_id, GTty ty] (subst_form_lv env m lv x f) in
    f_muf ty fun_ (form_of_expr m d) 

  | Sif(b,s1,s2) ->
    let f1 = pt_muhoare env m s1 f in
    let f2 = pt_muhoare env m s2 f in
    let b = form_of_expr m b in
    let rb = f_real_of_bool b in
    let rnb = f_real_of_bool (f_not b) in
    f_real_add (f_real_mul rb f1) (f_real_mul rnb f2)
  | _ -> raise NoWpMuhoare

and pt_muhoare env m s f =
  List.fold_right (pt_muhoare_i env m) s.s_node f 

let wp_muhoare env s ((mu,mt), po) =
  let onld ((m,mt),f) = (m,mt), pt_muhoare env m s f in
  ((mu,mt), do_on_mu onld mu po)

let wp_ret env mt' pvres e ((mu,_), po) = 
  let onld ((m,_), f) = 
    let let1 = lv_subst m (LvVar (pvres, e.e_ty)) (form_of_expr m e) in
    (m,mt'), mk_let_of_lv_substs env ([let1],f) in
  (mu,mt'), do_on_mu onld mu po

let wp_pre env mt' f fs ((mu,_), pr) = 
  let onld = 
    match fs.fs_anames with
    | None -> fun ((m,_), f) -> ((m,mt'), f)
    | Some lv ->
      fun ((m,_), f1) ->
        let v = List.map (fun v -> f_pvloc f v m) lv in
        let tv = (f_tuple v) in
        let let1 = lv_subst m (LvVar (pv_arg f, tv.f_ty)) tv in
        (m, mt'), mk_let_of_lv_substs env ([let1],f1) in
  (mu,mt'), do_on_mu onld mu pr

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


    


  



  

 
  
  
    

    
    
    
    

      


      
    






  




open EcUtils
open EcIdent
open EcPath
open EcTypes
open EcModules
open EcFol
open EcBaseLogic
open EcEnv
(* -------------------------------------------------------------------- *)     
exception IncompatibleType of ty * ty
exception IncompatibleForm of form * form * form * form

module PE = EcPrinting.EcDebugPP (* FIXME *)

let _ = EcPexception.register (fun fmt exn ->
  match exn with
  | IncompatibleForm(f1,f2,f3,f4) ->
    Format.fprintf fmt "the formula %a is not compatible with %a, since %a is not compatible with %a" PE.pp_form f1 PE.pp_form f2 PE.pp_form f3 PE.pp_form f4
  | _ -> raise exn)
      
let rec equal_type env t1 t2 = 
  match t1.ty_node, t2.ty_node with
  | Tunivar uid1, Tunivar uid2 -> EcUidgen.uid_equal uid1 uid2
      
  | Tvar i1, Tvar i2 -> i1 = i2
  | Ttuple lt1, Ttuple lt2 ->
      List.for_all2 (equal_type env) lt1 lt2
  | Tfun(t1,t2), Tfun(t1',t2') ->
      equal_type env t1 t1' && equal_type env t2 t2'
  | Tconstr(p1,lt1), Tconstr(p2,lt2) when EcPath.p_equal p1 p2 ->
      List.for_all2 (equal_type env) lt1 lt2 || 
      (Ty.defined p1 env &&
       equal_type env (Ty.unfold p1 lt1 env) (Ty.unfold p2 lt2 env))
  | Tconstr(p1,lt1), _ when Ty.defined p1 env ->
      equal_type env (Ty.unfold p1 lt1 env) t2
  | _, Tconstr(p2,lt2) when Ty.defined p2 env ->
      equal_type env t1 (Ty.unfold p2 lt2 env)
  | _, _ -> false
  
let check_type env t1 t2 = 
  if not (equal_type env t1 t2) then raise (IncompatibleType(t1,t2))

let rec destr_tfun env tf = 
  match tf.ty_node with
  | Tfun(ty1,ty2) -> ty1, ty2
  | Tconstr(p,tys) when Ty.defined p env ->
      destr_tfun env (Ty.unfold p tys env) 
  | _ -> assert false 

let rec ty_fun_app env tf targs = 
  match targs with
  | [] -> tf
  | t1 :: targs ->
      let dom,codom = destr_tfun env tf in
      check_type env dom t1;
      ty_fun_app env codom targs

(* TODO : can be good to also add unfolding of globals and locals *)

let pv_equal_norm env p1 p2 = 
  pv_equal p1 p2 || 
  (p1.pv_kind = p2.pv_kind &&
   EcPath.m_equal 
     (Mod.unfold_mod_path env p1.pv_name) (Mod.unfold_mod_path env p2.pv_name))

let m_equal_norm env p1 p2 = 
  EcPath.m_equal p1 p2 || 
  EcPath.m_equal (Mod.unfold_mod_path env p1) (Mod.unfold_mod_path env p2)

let e_equal_norm env e1 e2 =
  let find alpha id = try Mid.find id alpha with _ -> id in
  let check_lpattern alpha lp1 lp2 = 
    match lp1, lp2 with
    | LSymbol (id1,_), LSymbol (id2,_) -> Mid.add id1 id2 alpha
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
        List.fold_left2 (fun alpha (id1,_) (id2,_) -> Mid.add id1 id2 alpha) 
          alpha lid1 lid2
    | _, _ -> raise Not_found in
  let rec aux alpha e1 e2 = 
    match e1.e_node, e2.e_node with
    | Eint   i1, Eint   i2 -> i1 = i2
    | Elocal id1, Elocal id2 -> EcIdent.id_equal (find alpha id1) id2
    | Evar   p1, Evar   p2 -> pv_equal_norm env p1 p2
    | Eop(o1,ty1), Eop(o2,ty2) -> 
        p_equal o1 o2 && List.all2 (equal_type env) ty1 ty2

    | Eapp(f1,args1), Eapp(f2,args2) ->
        aux alpha f1 f2 &&
        List.all2 (aux alpha) args1 args2
    | Elet(p1,f1',g1), Elet(p2,f2',g2) ->
        aux alpha f1' f2' &&
        (try aux (check_lpattern alpha p1 p2) g1 g2 with Not_found -> false)
    | Etuple args1, Etuple args2 -> List.all2 (aux alpha) args1 args2
    | Eif (a1,b1,c1), Eif(a2,b2,c2) ->
        aux alpha a1 a2 && aux alpha b1 b2 && aux alpha c1 c2 
    | _, _ -> false in
  aux Mid.empty e1 e2

let lv_equal_norm env lv1 lv2 = 
  match lv1, lv2 with
  | LvVar(p1,_), LvVar(p2,_) -> pv_equal_norm env p1 p2
  | LvTuple p1, LvTuple p2 ->
      List.all2 (fun (p1,_) (p2,_) -> pv_equal_norm env p1 p2) p1 p2
  | LvMap((m1,ty1),p1,e1,_), LvMap((m2,ty2),p2,e2,_) -> 
      p_equal m1 m2 &&
      List.all2 (equal_type env) ty1 ty2 &&
      pv_equal_norm env p1 p2 && e_equal_norm env e1 e2 
  | _, _ -> false 

let rec s_equal_norm env s1 s2 = 
  s_equal s1 s2 || 
  List.all2 (i_equal_norm env) s1.s_node s2.s_node

and i_equal_norm env i1 i2 = 
  i_equal i1 i2 || 
  match i1.i_node, i2.i_node with
  | Sasgn(lv1,e1), Sasgn(lv2,e2) -> 
      lv_equal_norm env lv1 lv2 && e_equal_norm env e1 e2
  | Srnd(lv1,e1), Srnd(lv2,e2) -> 
      lv_equal_norm env lv1 lv2 && e_equal_norm env e1 e2
  | Scall(lv1, f1, e1), Scall(lv2,f2,e2) ->
      oall2 (lv_equal_norm env) lv1 lv2 &&
      m_equal_norm env f1 f2 &&
      List.all2 (e_equal_norm env) e1 e2
  | Sif (a1,b1,c1), Sif(a2,b2,c2) ->
      e_equal_norm env a1 a2 
        && s_equal_norm env b1 b2 
        && s_equal_norm env c1 c2 
  | Swhile(a1,b1), Swhile(a2,b2) ->
      e_equal_norm env a1 a2 && s_equal_norm env b1 b2 
  | Sassert a1, Sassert a2 ->
      e_equal_norm env a1 a2 
  | _, _ -> false

type reduction_info = {
  beta    : bool;
  delta_p : Sp.t option;   (* None means all *)
  delta_h : Sid.t option;  (* None means all *)
  zeta    : bool;   (* remove let *)
  iota    : bool;   (* remove case *)
  logic   : bool;   (* perform logical simplification *)
}

let full_red = {
  beta    = true;
  delta_p = None;
  delta_h = None;
  zeta    = true;
  iota    = true;
  logic   = true;
}
  
  
let no_red = {
  beta    = false;
  delta_p = Some Sp.empty;
  delta_h = Some Sid.empty;
  zeta    = false;
  iota    = false;
  logic   = false;
} 

let beta_red = { no_red with beta = true }
let betaiota_red = { no_red with beta = true; iota = true }

let reducible_local ri hyps x =
  match ri.delta_h with
  | None -> LDecl.reducible_var x hyps 
  | Some s when Sid.mem x s -> LDecl.reducible_var x hyps
  | _ -> false

let reduce_local ri hyps x  = 
  match ri.delta_h with
  | None -> LDecl.reduce_var x hyps 
  | Some s when Sid.mem x s -> LDecl.reduce_var x hyps 
  | _ -> raise NotReducible

let reducible_op ri env p =
  match ri.delta_p with
  | None -> Op.reducible env p 
  | Some s when Sp.mem p s -> Op.reducible env p 
  | _ -> false

let reduce_op ri env p tys =
  match ri.delta_p with
  | None -> Op.reduce env p tys 
  | Some s when Sp.mem p s -> Op.reduce env p tys 
  | _ -> raise NotReducible

let is_cbool f = (f_equal f f_true || f_equal f f_false)
  
let rec is_head_reducible ri env hyps f =
  match f.f_node with
  | Flocal x -> reducible_local ri hyps x 
  | Flet(LSymbol _, _, _) -> ri.zeta
  | Flet(LTuple _, {f_node = Ftuple _}, _) -> ri.iota
  | Flet(_, e1, _) -> is_head_reducible ri env hyps e1
  | Fapp({f_node = Fquant(Llambda,_,_)}, _) -> ri.beta
  | Fapp({f_node = Fop(p,_)}, args) when ri.logic && is_logical_op p ->
    List.exists (fun f -> is_cbool f || is_head_reducible ri env hyps f) args
  | Fapp(f,_) -> is_head_reducible ri env hyps f
  | Fop(p,_) -> reducible_op ri env p 
  | Fif(f1,_,_) -> (ri.iota && is_cbool f1) || is_head_reducible ri env hyps f1
  | _ -> false 
      
let rec h_red ri env hyps f = 
  match f.f_node with
  | Flocal x -> reduce_local ri hyps x 
  | Flet(LSymbol(x,_), e1, e2) when ri.zeta ->
    let s = bind_local f_subst_id x e1 in
    f_subst s e2
  | Flet(LTuple ids, { f_node = Ftuple es }, e2) when ri.iota ->
    let s = 
      List.fold_left2 (fun s (x,_) e1 -> bind_local s x e1) f_subst_id ids es in
    f_subst s e2
  | Flet(lp,f1,f2) -> f_let lp (h_red ri env hyps f1) f2 
  | Fapp({f_node = Fquant(Llambda,bd,body)}, args) when ri.beta -> 
    let nbd = List.length bd in
    let na  = List.length args in
    let args, ext_a =
      if nbd < na then List.take_n nbd args 
      else args, [] in
    let bd, ext_bd = 
      if na < nbd then List.take_n na bd 
      else bd, [] in
    let s = 
      List.fold_left2 (fun s (x,_) e1 -> bind_local s x e1) f_subst_id bd args in
    let f' = f_subst s (f_lambda ext_bd body) in
    f_app f' ext_a f.f_ty
  | Fapp({f_node = Fop(p,_)} as fo, args) when ri.logic && is_logical_op p ->
    if List.exists is_cbool args then
      match op_kind p, args with
      | OK_not  , [f] -> f_not_simpl f
      | OK_and b, [f1;f2] ->
        if b then f_anda_simpl f1 f2 else f_and_simpl f1 f2
      | OK_or b , [f1;f2] ->
        if b then f_ora_simpl f1 f2 else f_or_simpl f1 f2
      | OK_imp  , [f1;f2] -> f_imp_simpl f1 f2 
      | OK_iff  , [f1;f2] -> f_iff_simpl f1 f2 
      | OK_eq   , [f1;f2] -> f_eq_simpl f1 f2 
      | _                 -> assert false 
    else 
      let rec aux args = 
        match args with
        | [] -> raise NotReducible
        | a :: args ->
          try h_red ri env hyps a :: args with NotReducible -> a :: aux args in
      f_app fo (aux args) f.f_ty
  | Fapp(f1,args) ->
    f_app (h_red ri env hyps f1) args f.f_ty
  | Fop(p,tys) -> reduce_op ri env p tys
  | Fif(f1,f2,f3) when ri.iota ->
    if f_equal f1 f_true then f2 
    else if f_equal f1 f_false then f3 
    else f_if (h_red ri env hyps f1) f2 f3 
  | _ -> raise NotReducible 
  
let check_alpha_equal ri env hyps f1 f2 = 
  let error f1' f2' = raise (IncompatibleForm(f1,f2,f1',f2')) in
  let find alpha id = try Mid.find id alpha with _ -> id in
  let check_lpattern f1 f2 alpha lp1 lp2 = 
    match lp1, lp2 with
    | LSymbol (id1,_), LSymbol (id2,_) -> Mid.add id1 id2 alpha
    | LTuple lid1, LTuple lid2 when List.length lid1 = List.length lid2 ->
        List.fold_left2 (fun alpha (id1,_) (id2,_) -> Mid.add id1 id2 alpha) 
          alpha lid1 lid2
    | _, _ -> error f1 f2 in
  let check_binding f1 f2 alpha bd1 bd2 =
    let check_one alpha (x1,ty1) (x2,ty2) =
      let tyok =
        match ty1, ty2 with
        | GTty    ty1, GTty ty2   -> equal_type env ty1 ty2
        | GTmodty p1 , GTmodty p2 -> ModTy.mod_type_equiv env p1 p2
        | GTmem      , GTmem      -> true
        | _          , _          -> false
      in
        if   tyok
        then Mid.add x1 x2 alpha
        else error f1 f2
    in
      List.fold_left2 check_one alpha bd1 bd2 in

  let rec aux1 alpha f1 f2 = 
    if Mid.is_empty alpha && f_equal f1 f2 then () 
    else match f1.f_node, f2.f_node with

    | Fquant(q1,bd1,f1'), Fquant(q2,bd2,f2') when 
        q1 = q2 && List.length bd1 = List.length bd2 ->
          let alpha = check_binding f1 f2 alpha bd1 bd2 in
          aux alpha f1' f2'

    | Fif(a1,b1,c1), Fif(a2,b2,c2) ->
        aux alpha a1 a2; aux alpha b1 b2; aux alpha c1 c2

    | Flet(p1,f1',g1), Flet(p2,f2',g2) ->
        aux alpha f1' f2';
        let alpha = check_lpattern f1 f2 alpha p1 p2 in
        aux alpha g1 g2

    | Fint i1, Fint i2 when i1 = i2 -> ()

    | Flocal id1, Flocal id2 when EcIdent.id_equal (find alpha id1) id2 -> ()

    | Fpvar(p1,m1), Fpvar(p2,m2) when 
        EcIdent.id_equal m1 m2 && pv_equal_norm env p1 p2  -> ()

    | Fop(p1, ty1), Fop(p2, ty2) when EcPath.p_equal p1 p2 &&
        List.all2 (equal_type env) ty1 ty2 -> () 

    | Fapp(f1',args1), Fapp(f2',args2) when List.length args1 = List.length args2 ->
      aux alpha f1' f2';
      List.iter2 (aux alpha) args1 args2

    | Ftuple args1, Ftuple args2 when List.length args1 = List.length args2 ->
        List.iter2 (aux alpha) args1 args2

    | FhoareF hf1, FhoareF hf2 when m_equal_norm env hf1.hf_f hf2.hf_f ->
        aux alpha hf1.hf_pre hf2.hf_pre;
        aux alpha hf1.hf_post hf2.hf_post

    | FhoareS hs1, FhoareS hs2 when s_equal_norm env hs1.hs_s hs2.hs_s -> 
        (* FIXME should check the memenv *)
        aux alpha hs1.hs_pre  hs1.hs_pre;
        aux alpha hs1.hs_post hs2.hs_post

    | FequivF ef1, FequivF ef2 
      when m_equal_norm env ef1.eqf_fl ef2.eqf_fl && 
           m_equal_norm env ef1.eqf_fr ef2.eqf_fr ->
        aux alpha ef1.eqf_pre  ef2.eqf_pre;
        aux alpha ef1.eqf_post ef2.eqf_post

    | FequivS es1, FequivS es2 
      when s_equal_norm env es1.eqs_sl es2.eqs_sl && 
           s_equal_norm env es1.eqs_sr es2.eqs_sr ->
        (* FIXME should check the memenv *)
        aux alpha es1.eqs_pre  es2.eqs_pre;
        aux alpha es1.eqs_post es2.eqs_post

    | Fpr(m1,p1,args1,f1'), Fpr(m2,p2,args2,f2') 
      when EcIdent.id_equal (find alpha m1) m2 &&
           m_equal_norm env p1 p2 &&  
           List.length args1 = List.length args2 ->
        List.iter2 (aux alpha) args1 args2;
        aux alpha f1' f2'

    | _, _ -> error f1 f2
  and aux alpha f1 f2 = 
    try aux1 alpha f1 f2 
    with e ->
      if is_head_reducible ri env hyps f1 then
        aux alpha (h_red ri env hyps f1) f2
      else if is_head_reducible ri env hyps f2 then
        aux alpha f1 (h_red ri env hyps f2) 
      else raise e
  in
  aux Mid.empty f1 f2

let check_alpha_eq = check_alpha_equal no_red
let check_conv     = check_alpha_equal full_red

let is_alpha_eq env hyps f1 f2 = 
  try check_alpha_eq env hyps f1 f2; true
  with _ -> false

let is_conv env hyps f1 f2 = 
  try check_conv env hyps f1 f2; true
  with _ -> false

let rec simplify ri env hyps f = 
  let f' = try h_red ri env hyps f with NotReducible -> f in
  if f == f' then f_map (fun ty -> ty) (simplify ri env hyps) f
  else simplify ri env hyps f'



  


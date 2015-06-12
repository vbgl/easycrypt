(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcModules
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal
open EcLowMuHoare
module Sx  = EcPath.Sx
module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let while_info env e s = 
  let rec i_info (w,r,c) i = 
    match i.i_node with
    | Sasgn(lp, e) | Srnd(lp, e) ->
        let r = e_read_r env (EcPV.lp_read_r env r lp) e in
        let w = lp_write_r env w lp in
        (w, r, c)

    | Sif (e, s1, s2) ->
        let r = e_read_r env r e in s_info (s_info (w, r, c) s1) s2

    | Swhile(e,s) ->
        let r = e_read_r env r e in s_info (w, r, c) s

    | Scall(lp,f,es) ->
        let r = List.fold_left (e_read_r env) r es in
        let r = match lp with None -> r | Some lp -> lp_read_r  env r lp in
        let w = match lp with None -> w | Some lp -> lp_write_r env w lp in
        let f = EcEnv.NormMp.norm_xfun env f in
        (w, r, Sx.add f c)
  
    | Sassert e ->
        (w, e_read_r env r e, c)

    | Sabstract id ->
      let add_pv x (pv,ty) = PV.add env pv ty x in 
      let us = EcEnv.AbsStmt.byid id env in
      let w = List.fold_left add_pv w us.EcBaseLogic.aus_writes in
      let r = List.fold_left add_pv r us.EcBaseLogic.aus_reads in
      let c = List.fold_left (fun c f -> Sx.add f c) c us.EcBaseLogic.aus_calls in
      (w, r, c)

  and s_info info s = List.fold_left i_info info s.s_node in

  let (w,r,c) = s_info (PV.empty, EcPV.e_read env e, Sx.empty) s in

  { EcBaseLogic.aus_reads  = fst (PV.elements r);
    EcBaseLogic.aus_writes = fst (PV.elements w);
    EcBaseLogic.aus_calls  = Sx.elements c; }

(* -------------------------------------------------------------------- *)
let t_hoare_while_r inv tc =
  let env = FApi.tc1_env tc in
  let hs = tc1_as_hoareS tc in
  let (e, c), s = tc1_last_while tc hs.hs_s in
  let m = EcMemory.memory hs.hs_m in
  let e = form_of_expr (Some hs.hs_m) e in
  (* the body preserves the invariant *)
  let b_pre  = f_and_simpl inv e in
  let b_post = inv in
  let b_concl = f_hoareS hs.hs_m b_pre c b_post in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] hs.hs_po in
  let modi = s_write env c in
  let post = generalize_mod env (f_mem hs.hs_m) modi post in
  let post = f_and_simpl inv post in
  let concl = f_hoareS_r { hs with hs_s = s; hs_po=post} in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_while_r inv vrnt tc =
  let env = FApi.tc1_env tc in
  let bhs = tc1_as_bdhoareS tc in
  let (e, c), s = tc1_last_while tc bhs.bhs_s in
  let m = EcMemory.memory bhs.bhs_m in
  let e = form_of_expr (Some bhs.bhs_m) e in
  (* the body preserves the invariant *)
  let k_id = EcIdent.create "z" in
  let k = f_local k_id tint in
  let vrnt_eq_k = f_eq vrnt k in
  let vrnt_lt_k = f_int_lt vrnt k in
  let b_pre  = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
  let b_post = f_and_simpl inv vrnt_lt_k in
  let b_concl = f_bdHoareS_r
    { bhs with
        bhs_pr  = b_pre; bhs_s  = c; bhs_po = b_post;
        bhs_cmp = FHeq ; bhs_bd = f_r1}
  in
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  (* the wp of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] bhs.bhs_po in
  let term_condition = f_imps_simpl [inv;f_int_le vrnt f_i0] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env (f_mem bhs.bhs_m) modi post in
  let post = f_and_simpl inv post in
  let concl = f_bdHoareS_r { bhs with bhs_s = s; bhs_po=post} in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_while_rev_r inv tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let bhs = tc1_as_bdhoareS tc in

  if bhs.bhs_cmp <> FHle then
    tc_error !!tc "only judgments with an upper-bounded are supported";

  let b_pre  = bhs.bhs_pr in
  let b_post = bhs.bhs_po in
  let mem    = bhs.bhs_m in
  let bound  = bhs.bhs_bd in

  let (lp_guard_exp, lp_body), rem_s = tc1_last_while tc bhs.bhs_s in
  let lp_guard = form_of_expr (Some mem) lp_guard_exp in

  let w_u   = while_info env lp_guard_exp lp_body in
  let w     = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  (* 1. Sub-goal *)
  let body_concl =
    let while_s  = EcModules.stmt [EcModules.i_abstract w] in
    let while_s' = EcModules.i_if (lp_guard_exp, while_s, EcModules.stmt []) in
    let while_s' = EcModules.stmt [while_s'] in
    let unfolded_while_s = EcModules.s_seq lp_body while_s' in
    let while_jgmt = f_bdHoareS_r {bhs with bhs_pr=inv ; bhs_s=while_s'; } in
    let unfolded_while_jgmt = f_bdHoareS_r
      { bhs with bhs_pr = f_and inv lp_guard; bhs_s = unfolded_while_s; }
    in
      f_imp while_jgmt unfolded_while_jgmt
  in

  (* 2. Sub-goal *)
  let rem_concl =
    let modi = s_write env lp_body in
    let term_post = f_imp
      (f_and inv (f_and (f_not lp_guard) b_post))
      (f_eq bound f_r1) in
    let term_post = generalize_mod env (f_mem mem) modi term_post in
    let term_post = f_and inv term_post in
    f_hoareS mem b_pre rem_s term_post
  in

  FApi.xmutate1_hyps tc `While [(hyps', body_concl); (hyps, rem_concl)]

(* -------------------------------------------------------------------- *)
let t_bdhoare_while_rev_geq_r inv vrnt k eps tc =
  let env, hyps, _ = FApi.tc1_eflat tc in

  let bhs    = tc1_as_bdhoareS tc in
  let b_pre  = bhs.bhs_pr in
  let b_post = bhs.bhs_po in
  let mem    = bhs.bhs_m in

  let (lp_guard_exp, lp_body), rem_s = tc1_last_while tc bhs.bhs_s in

  if not (List.is_empty rem_s.s_node) then
    tc_error !!tc  "only single loop statements are accepted";

  let lp_guard = form_of_expr (Some mem) lp_guard_exp in
  let bound    = bhs.bhs_bd in
  let modi     = s_write env lp_body in

  (* 1. Pre-invariant *)
  let pre_inv_concl = f_forall_mems [mem] (f_imp b_pre inv) in

  (* 2. Pre-bound *)
  let pre_bound_concl =
    let term_post = [b_pre; f_not lp_guard; f_not b_post] in
    let term_post = f_imps term_post (f_eq bound f_r0) in
    let term_post = generalize_mod env (f_mem mem) modi term_post in
      f_forall_mems [mem] term_post
  in

  (* 3. Term-invariant *)
  let inv_term_concl =
    let concl = f_imp (f_int_le vrnt f_i0) (f_not lp_guard) in
    let concl = f_and (f_int_le vrnt k) concl in
    let concl = f_imp inv concl in
      f_forall_mems [mem] (generalize_mod env (f_mem mem) modi concl)
  in

  (* 4. Vrnt conclusion *)
  let vrnt_concl =
    let k_id = EcIdent.create "z" in
    let k    = f_local k_id tint in
    let vrnt_eq_k = f_eq vrnt k in
    let vrnt_lt_k = f_int_lt vrnt k in
      f_and
        (f_forall_mems [mem] (f_imp inv (f_real_lt f_r0 eps)))
        (f_forall_simpl [(k_id,GTty tint)]
           (f_bdHoareS_r { bhs with
             bhs_pr  = f_ands [inv;lp_guard;vrnt_eq_k];
             bhs_po  = vrnt_lt_k;
             bhs_s   = lp_body;
             bhs_cmp = FHge;
             bhs_bd  = eps }))
  in

  (* 5. Out invariant *)
  let inv_concl =
    f_bdHoareS_r { bhs with
      bhs_pr  = f_and inv lp_guard;
      bhs_po  = inv;
      bhs_s   = lp_body;
      bhs_cmp = FHeq;
      bhs_bd  = f_r1; }
  in

  (* 6. Out body *)
  let w_u = while_info env lp_guard_exp lp_body in
  let w   = EcEnv.LDecl.fresh_id hyps "w" in
  let hyps' = EcEnv.LDecl.add_local w (EcBaseLogic.LD_abs_st w_u) hyps in

  let body_concl =
    let while_s1 = EcModules.stmt [EcModules.i_abstract w] in
    let while_s2 = EcModules.i_if (lp_guard_exp, while_s1, EcModules.stmt []) in
    let while_s2 = EcModules.stmt [while_s2] in

    let unfolded_while_s = EcModules.s_seq lp_body while_s2 in
    let while_jgmt = f_bdHoareS_r { bhs with bhs_pr=inv; bhs_s=while_s2; } in
    let unfolded_while_jgmt = f_bdHoareS_r
      { bhs with bhs_pr=f_and inv lp_guard; bhs_s=unfolded_while_s; }
    in
    f_imp while_jgmt unfolded_while_jgmt
  in

  FApi.xmutate1_hyps tc `While
    [(hyps , pre_inv_concl  );
     (hyps , pre_bound_concl);
     (hyps , inv_term_concl );
     (hyps', body_concl     );
     (hyps , inv_concl      );
     (hyps , vrnt_concl     )]

(* -------------------------------------------------------------------- *)
let t_equiv_while_disj_r side vrnt inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let s, m_side, m_other =
    match side with
    | `Left  -> es.es_sl, es.es_ml, es.es_mr
    | `Right -> es.es_sr, es.es_mr, es.es_ml in
  let (e, c), s = tc1_last_while tc s in
  let e = form_of_expr (Some m_side) e in

  (* 1. The body preserves the invariant and the variant decreases. *)
  let k_id = EcIdent.create "z" in
  let k    = f_local k_id tint in

  let vrnt_eq_k = f_eq vrnt k in
  let vrnt_lt_k = f_int_lt vrnt k in

  let m_other' = (EcIdent.create "&m", EcMemory.memtype m_other) in

  let smem = Fsubst.f_subst_id in
  let smem = Fsubst.f_bind_mem smem (EcMemory.memory m_side) (snd m_side) mhr in
  let smem = Fsubst.f_bind_mem smem (EcMemory.memory m_other) (snd m_other) (EcMemory.memory m_other') in

  let b_pre   = f_and_simpl (f_and_simpl inv e) vrnt_eq_k in
  let b_pre   = Fsubst.f_subst smem b_pre in
  let b_post  = f_and_simpl inv vrnt_lt_k in
  let b_post  = Fsubst.f_subst smem b_post in
  let b_concl = f_bdHoareS (mhr, EcMemory.memtype m_side) b_pre c b_post FHeq f_r1 in
  let b_concl = f_forall_simpl [(k_id,GTty tint)] b_concl in
  let b_concl = f_forall_mems [m_other'] b_concl in

  (* 2. WP of the while *)
  let post = f_imps_simpl [f_not_simpl e; inv] es.es_po in
  let term_condition = f_imps_simpl [inv;f_int_le vrnt f_i0] (f_not_simpl e) in
  let post = f_and term_condition post in
  let modi = s_write env c in
  let post = generalize_mod env (f_mem m_side) modi post in
  let post = f_and_simpl inv post in
  let concl =
    match side with
    | `Left  -> f_equivS_r { es with es_sl = s; es_po=post; }
    | `Right -> f_equivS_r { es with es_sr = s; es_po=post; }
  in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
let t_equiv_while_r inv tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let (el, cl), sl = tc1_last_while tc es.es_sl in
  let (er, cr), sr = tc1_last_while tc es.es_sr in
  let ml = EcMemory.memory es.es_ml in
  let mr = EcMemory.memory es.es_mr in
  let el = form_of_expr (Some es.es_ml) el in
  let er = form_of_expr (Some es.es_mr) er in
  let sync_cond = f_iff_simpl el er in

  (* 1. The body preserves the invariant *)
  let b_pre  = f_ands_simpl [inv; el] er in
  let b_post = f_and_simpl inv sync_cond in
  let b_concl = f_equivS es.es_ml es.es_mr b_pre cl cr b_post in

  (* 2. WP of the while *)
  let post = f_imps_simpl [f_not_simpl el;f_not_simpl er; inv] es.es_po in
  let modil = s_write env cl in
  let modir = s_write env cr in
  let post = generalize_mod env (f_mem es.es_mr) modir post in
  let post = generalize_mod env (f_mem es.es_ml) modil post in
  let post = f_and_simpl b_post post in
  let concl = f_equivS_r { es with es_sl = sl; es_sr = sr; es_po = post; } in

  FApi.xmutate1 tc `While [b_concl; concl]

(* -------------------------------------------------------------------- *)
(* Rule : WHILE-G1 *)
let t_muhoare_while (inv : form) tc =
  (* FIXME: check the type of inv *)
  let env = FApi.tc1_env tc in
  let mus = tc1_as_muhoareS tc in
  let (e, c), s = tc1_last_while tc mus.muh_s in

  let enot = e_op EcCoreLib.CI_Bool.p_not [] (toarrow [tbool] tbool) in
  let ne   = e_app enot [e] tbool in

  let cond1 = f_muhoareS inv (s_if (e, c, s_empty)) inv in
(*let cond2 = f_muhoareS inv (s_assert ne) mus.muh_po in *)
  let cond2 = p_forall_imp env inv (mu_restr env false e mus.muh_po) in
  let cond3 = f_muhoareS mus.muh_pr s inv in

  FApi.xmutate1 tc `While [cond1; cond2; cond3]

(* Rule : WHILE-RWB *)

let muhoare_while_pre env inv v kK =
  let (mu,mt), inv = open_mu_binding env inv in
  let tmt = tmem mt in
  let v   = f_app_simpl v [f_local mhr tmt] tint in
  let bounded  = 
    f_square (mhr, tmt) (f_and (f_int_le f_i0 v) (f_int_le v kK)) mu in 
  close_mu_binding (mu,mt) (f_and inv bounded) 

let muhoare_while_post env inv b = 
  let (mu,mt), inv = open_mu_binding env inv in
  let tmt = tmem mt in
  let nb = f_not (form_of_expr (Some (mhr, mt)) b) in
  close_mu_binding (mu,mt) (f_and inv (f_square (mhr, tmt) nb mu))

let t_low_muhoare_while_bounded_r inv v kK q tc = 
  (* TODO check type of 
      inv : mem -> bool
      v   : mem -> int
      kK  : int
      q   : real *)
  let env,hyps, _ = FApi.tc1_eflat tc in
  let mus = tc1_as_muhoareS tc in
  let (e, c), s = tc1_last_while tc mus.muh_s in
  if not (s_equal s s_empty) then
    tc_error !!tc "low_muhoare_while_bounded: the statement should be a single while instruction";
  let pr = muhoare_while_pre env inv v kK in
  if not (EcReduction.is_conv hyps mus.muh_pr pr) then
    tc_error !!tc "low_muhoare_while_bounded:invalid pre-condition";
  let po = muhoare_while_post env inv e in
  if not (EcReduction.is_conv hyps mus.muh_po po) then
    tc_error !!tc "low_muhoare_while_bounded:invalid post-condition";
  (* Generating the sub goal *)

  (* condition on the body *)
  let (mu,mt),inv = open_mu_binding env inv in 
  let tmt = tmem mt in
  let v   = f_app_simpl v [f_local mhr tmt] tint in
  let vk  = EcIdent.create "k" in
  let k   = f_local vk tint in
  let le  = f_and (f_int_le f_i0 v) (f_int_le v kK) in
  let pr1 = f_square (mhr, tmt) (f_and (f_eq v k) le) mu in
  let pr  = close_mu_binding (mu,mt) (f_and inv pr1) in
  let po1 = f_real_le q (f_muf_b2r (mhr,tmt) 
                           (f_or (f_eq v f_i0) (f_int_lt v k)) mu) in
  let po2 = f_square (mhr, tmt) le mu in
  let po  = close_mu_binding (mu,mt) (f_ands [inv; po1;po2]) in
  let cond1 = 
    f_forall [(vk, GTty tint)] (f_muhoareS pr (s_if (e, c, s_empty)) po) in
  let cond2 = 
    f_forall [(vk, GTty tint); (mu,GTty (tdistr tmt)) ]
      (f_imp 
         inv 
         (f_imp 
            (f_square (mhr,tmt) (f_eq v f_i0) mu)
            (f_square (mhr,tmt) (f_not (form_of_expr (Some (mhr,mt)) e)) mu)))
  in
  let cond3 = f_real_lt f_r0 q in
  FApi.xmutate1 tc `While [cond3; cond2; cond1]

let t_low_muhoare_while_bounded = FApi.t_low4 "muhoare-while-bound" t_low_muhoare_while_bounded_r
 
(* FIXME: improve it such that we can apply it at any position *) 
let t_muhoare_while_bounded inv v kK q tc =
  let env = FApi.tc1_env tc in
  let mus = tc1_as_muhoareS tc in
  let (e, _), s = tc1_last_while tc mus.muh_s in
  let pr = muhoare_while_pre env inv v kK in
  let po = muhoare_while_post env inv e in
  let t_app i p tc =
    FApi.t_rotate `Left 1 (EcPhlApp.t_muhoare_app i p tc) in

  (EcPhlConseq.t_muhoareS_conseq mus.muh_pr po @+ [
    t_logic_trivial;
    t_id;
    t_app (List.length s.s_node) pr @+ [ 
      t_low_muhoare_while_bounded inv v kK q;
      t_id
    ] 
  ]) tc

(* Rule : WHILE-RWU *)

(* -------------------------------------------------------------------- *)
let t_hoare_while           = FApi.t_low1 "hoare-while"   t_hoare_while_r
let t_bdhoare_while         = FApi.t_low2 "bdhoare-while" t_bdhoare_while_r
let t_bdhoare_while_rev_geq = FApi.t_low4 "bdhoare-while" t_bdhoare_while_rev_geq_r
let t_bdhoare_while_rev     = FApi.t_low1 "bdhoare-while" t_bdhoare_while_rev_r
let t_equiv_while           = FApi.t_low1 "equiv-while"   t_equiv_while_r
let t_equiv_while_disj      = FApi.t_low3 "equiv-while"   t_equiv_while_disj_r
let t_muhoare_while         = FApi.t_low1 "muhoare-while" t_muhoare_while

(* -------------------------------------------------------------------- *)
let process_while side winfos tc =
  let { EcParsetree.wh_inv  = phi ;
        EcParsetree.wh_vrnt = vrnt;
        EcParsetree.wh_bds  = bds ; } = winfos in

  match (FApi.tc1_goal tc).f_node with
  | FhoareS _ -> begin
      match vrnt with
      | None -> t_hoare_while (TTC.tc1_process_phl_formula tc phi) tc
      | _    -> tc_error !!tc "invalid arguments"
    end

  | FbdHoareS _ -> begin
      match vrnt, bds with
      | Some vrnt, None ->
          t_bdhoare_while
            (TTC.tc1_process_phl_formula tc phi)
            (TTC.tc1_process_phl_form tc tint vrnt)
            tc

      | Some vrnt, Some (k, eps) ->
        t_bdhoare_while_rev_geq
          (TTC.tc1_process_phl_formula tc phi)
          (TTC.tc1_process_phl_form    tc tint vrnt)
          (TTC.tc1_process_phl_form    tc tint k)
          (TTC.tc1_process_phl_form    tc treal eps)
          tc

      | None, None ->
          t_bdhoare_while_rev (TTC.tc1_process_phl_formula tc phi) tc

      | None, Some _ -> tc_error !!tc "invalid arguments"
  end

  | FequivS _ -> begin
      match side, vrnt with
      | None, None ->
          t_equiv_while (TTC.tc1_process_prhl_formula tc phi) tc

      | Some side, Some vrnt ->
          t_equiv_while_disj side
            (TTC.tc1_process_prhl_form    tc tint vrnt)
            (TTC.tc1_process_prhl_formula tc phi)
            tc

      | _ -> tc_error !!tc "invalid arguments"
  end

  | FmuhoareS _ -> 
    if side <> None then 
      tc_error !!tc "invalid arguments";
    let (_,mt) as mumt,f = TTC.tc1_process_phl_ld_formula tc phi in
    let inv = close_mu_binding mumt f in
    begin match vrnt, bds with
    | None, None ->
      t_muhoare_while inv tc
        
    | Some v, Some(kK, q) ->
      let q = TTC.tc1_process_form tc treal q in
      let kK = TTC.tc1_process_form tc tint kK in
      let env,hyps,_ = FApi.tc1_eflat tc in
      let v = (* FIXME: improve this *)
        let ue = TTC.unienv_of_hyps hyps in
        let mmt = mhr, mt in
        let env = EcEnv.Memory.push_active mmt env in
        let f = 
          try 
            let ff = EcTyping.trans_form env ue v tint in
            EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff
          with EcUnify.UninstanciateUni ->
            EcTyping.tyerror v.EcLocation.pl_loc
              env EcTyping.FreeTypeVariables in
        f_lambda [mhr, GTty (tmem mt)] f in
      t_muhoare_while_bounded inv v kK q tc
        
    | _ -> tc_error !!tc "invalid arguments"
    end

  | _ -> tc_error !!tc "invalid goal shape"

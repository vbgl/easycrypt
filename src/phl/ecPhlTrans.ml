(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcParsetree
open EcTypes
open EcFol
open EcEnv
open EcPV
open EcMatching
open EcTransMatching
open EcModules
open EcMaps

open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
module Low = struct
  (* ------------------------------------------------------------------ *)
  let transitivity_side_cond hyps prml prmr poml pomr p q p1 q1 pomt p2 q2 =
    let env = LDecl.toenv hyps in
    let cond1 =
      let fv1 = PV.fv env mright p1 in
      let fv2 = PV.fv env mleft  p2 in
      let fv  = PV.union fv1 fv2 in
      let elts, glob = PV.ntr_elements fv in
      let bd, s = generalize_subst env mhr elts glob in
      let s1 = PVM.of_mpv s mright in
      let s2 = PVM.of_mpv s mleft in
      let concl = f_and (PVM.subst env s1 p1) (PVM.subst env s2 p2) in
      f_forall_mems [prml;prmr] (f_imp p (f_exists bd concl)) in
    let cond2 =
      let m2 = LDecl.fresh_id hyps "&m" in
      let q1 = Fsubst.f_subst_mem mright m2 q1 in
      let q2 = Fsubst.f_subst_mem mleft  m2 q2 in
      f_forall_mems [poml;(m2,pomt);pomr] (f_imps [q1;q2] q) in
    (cond1, cond2)

  (* ------------------------------------------------------------------ *)
  let t_equivS_trans_r (mt, c2) (p1, q1) (p2, q2) tc =
    let hyps = FApi.tc1_hyps tc in
    let es = tc1_as_equivS tc in
    let m1, m3 = es.es_ml, es.es_mr in
    let cond1, cond2 =
      transitivity_side_cond hyps
        m1 m3 m1 m3 es.es_pr es.es_po p1 q1 mt p2 q2 in
    let cond3 =
      f_equivS_r { es with
        es_mr = (mright,mt);
        es_sr = c2;
        es_pr = p1;
        es_po = q1;
      } in
    let cond4 =
      f_equivS_r { es with
        es_ml = (mleft, mt);
        es_sl = c2;
        es_pr = p2;
        es_po = q2;
      } in

     FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]

  (* ------------------------------------------------------------------ *)
  let t_equivF_trans_r f (p1, q1) (p2, q2) tc =
    let env, hyps, _ = FApi.tc1_eflat tc in
    let ef = tc1_as_equivF tc in
    let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
    let (_, pomt) = snd (Fun.hoareF_memenv f env) in
    let cond1, cond2 =
      transitivity_side_cond
        hyps prml prmr poml pomr
        ef.ef_pr ef.ef_po p1 q1 pomt p2 q2 in
    let cond3 = f_equivF p1 ef.ef_fl f q1 in
    let cond4 = f_equivF p2 f ef.ef_fr q2 in

    FApi.xmutate1 tc `Trans [cond1; cond2; cond3; cond4]
end

(* -------------------------------------------------------------------- *)
let t_equivS_trans = FApi.t_low3 "equiv-trans" Low.t_equivS_trans_r
let t_equivF_trans = FApi.t_low3 "equiv-trans" Low.t_equivF_trans_r

(* -------------------------------------------------------------------- *)
let process_replace_stmt s p c p1 q1 p2 q2 tc =
  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_equivS tc in
  let ct = match oget s with `Left -> es.es_sl | `Right -> es.es_sr in
  let mt = snd (match oget s with `Left -> es.es_ml | `Right -> es.es_mr) in
  (* Translation of the stmt *)
  let regexpstmt = trans_block p in
  let map = match RegexpStmt.search regexpstmt ct.s_node with
    | None -> Mstr.empty
    | Some m -> m in
  let p1, q1 =
    let hyps = LDecl.push_all [es.es_ml; (mright, mt)] hyps in
    TTC.pf_process_form !!tc hyps tbool p1,
    TTC.pf_process_form !!tc hyps tbool q1 in
  let p2, q2 =
    let hyps = LDecl.push_all [(mleft, mt); es.es_mr] hyps in
    TTC.pf_process_form !!tc hyps tbool p2,
    TTC.pf_process_form !!tc hyps tbool q2 in
  let c = TTC.tc1_process_prhl_stmt tc (oget s) ~map c in
  t_equivS_trans (mt, c) (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_trans_stmt s c p1 q1 p2 q2 tc =
  let hyps = FApi.tc1_hyps tc in
  let es = tc1_as_equivS tc in
  let mt = snd (match oget s with `Left -> es.es_ml | `Right -> es.es_mr) in
  let p1, q1 =
    let hyps = LDecl.push_all [es.es_ml; (mright, mt)] hyps in
    TTC.pf_process_form !!tc hyps tbool p1,
    TTC.pf_process_form !!tc hyps tbool q1 in
  let p2, q2 =
    let hyps = LDecl.push_all [(mleft, mt); es.es_mr] hyps in
    TTC.pf_process_form !!tc hyps tbool p2,
    TTC.pf_process_form !!tc hyps tbool q2 in
  (* Translation of the stmt *)
  let c = TTC.tc1_process_prhl_stmt tc (oget s) c in
  t_equivS_trans (mt,c) (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_trans_fun f p1 q1 p2 q2 tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let ef = tc1_as_equivF tc in
  let f = EcTyping.trans_gamepath env f in
  let (_, prmt), (_, pomt) = Fun.hoareF_memenv f env in
  let (prml, prmr), (poml, pomr) = Fun.equivF_memenv ef.ef_fl ef.ef_fr env in
  let process ml mr fo =
    TTC.pf_process_form !!tc (LDecl.push_all [ml; mr] hyps) tbool fo in
  let p1 = process prml (mright, prmt) p1 in
  let q1 = process poml (mright, pomt) q1 in
  let p2 = process (mleft,prmt) prmr p2 in
  let q2 = process (mleft,pomt) pomr q2 in
  t_equivF_trans f (p1, q1) (p2, q2) tc

(* -------------------------------------------------------------------- *)
let process_equiv_trans (tk, p1, q1, p2, q2) g =
  match tk with
  | TKfun f -> process_trans_fun f p1 q1 p2 q2 g
  | TKstmt (s, c) -> process_trans_stmt s c p1 q1 p2 q2 g
  | TKparsedStmt (s, p, c) -> process_replace_stmt s p c p1 q1 p2 q2 g

(* -------------------------------------------------------------------- *)
let tuplify env (m1, m2) f =
  let fv = PV.union (PV.fv env m1 f) (PV.fv env m2 f) in
  let felts, fglob = PV.ntr_elements fv in

  let ty1 = (List.map snd felts) in
  let ty2 = (List.map (fun x -> tglob x) fglob) in
  let tty = ttuple (ty1 @ ty2) in

  let t1  = EcIdent.create "t1" in
  let t2  = EcIdent.create "t2" in
  let ft1 = f_local t1 tty in
  let ft2 = f_local t2 tty in

  let subst = PVM.empty in

  let theproj =
    if   (List.length ty1 + List.length ty2 <= 1)
    then fun f _ _  -> f
    else fun f i ty  -> f_proj f i ty
  in

  let subst =
    List.fold_lefti (fun subst i (pv, ty) ->
      let ft1 = theproj ft1 i ty in
      let ft2 = theproj ft2 i ty in
      let subst = PVM.add env pv m1 ft1 subst in
      let subst = PVM.add env pv m2 ft2 subst in
      subst) subst felts
  in

  let subst =
    let n = List.length felts in
    List.fold_lefti (fun subst i gv ->
      let ft1 = theproj ft1 (i+n) (tglob gv) in
      let ft2 = theproj ft2 (i+n) (tglob gv) in
      let subst = PVM.add_glob env gv m1 ft1 subst in
      let subst = PVM.add_glob env gv m2 ft2 subst in
      subst) subst fglob
  in

  ((t1, t2), (felts, fglob), PVM.subst env subst f)

(* -------------------------------------------------------------------- *)
let t_esp_trans phi' tc =
  let es = tc1_as_espS tc in
  let env, _, _ = FApi.tc1_eflat tc in

  begin
    let sl = es.esps_sl in
    let sr = es.esps_sr in

    if not (EcReduction.EqTest.for_stmt ~norm:true env sl sr) then
      tc_error !!tc "left/right programs must be equal"
  end;

  let mk_linear =
    let f_linear =
      f_op EcCoreLib.CI_Momemtum.p_linear []
        (toarrow [toarrow [treal] treal] tbool) in
    fun f -> f_app f_linear [f] tbool
  in

  let po_trans =
    let m1 = EcIdent.create "&1" in
    let m2 = EcIdent.create "&2" in
    let m3 = EcIdent.create "&3" in

    let s1 = Fsubst.f_subst_id in
    let s1 = Fsubst.f_bind_mem s1 (fst es.esps_ml) m1 in
    let s1 = Fsubst.f_bind_mem s1 (fst es.esps_mr) m2 in

    let s2 = Fsubst.f_subst_id in
    let s2 = Fsubst.f_bind_mem s2 (fst es.esps_ml) m2 in
    let s2 = Fsubst.f_bind_mem s2 (fst es.esps_mr) m3 in

    let s = Fsubst.f_subst_id in
    let s = Fsubst.f_bind_mem s (fst es.esps_ml) m1 in
    let s = Fsubst.f_bind_mem s (fst es.esps_mr) m3 in

    let po1 = Fsubst.f_subst s1 (fst es.esps_po) in
    let po2 = Fsubst.f_subst s2 (fst es.esps_po) in
    let po  = Fsubst.f_subst s  (fst es.esps_po) in

    f_forall_mems
      [(m1, snd es.esps_ml); (m2, None); (m3, snd es.esps_mr)]
      (f_imp (f_and po1 po2) po)
  in

  let ti_ineq =
    let m1 = EcIdent.create "&1" in
    let m2 = EcIdent.create "&2" in
    let m3 = EcIdent.create "&3" in

    let s1 = Fsubst.f_subst_id in
    let s1 = Fsubst.f_bind_mem s1 (fst es.esps_ml) m1 in
    let s1 = Fsubst.f_bind_mem s1 (fst es.esps_mr) m2 in

    let s2 = Fsubst.f_subst_id in
    let s2 = Fsubst.f_bind_mem s2 (fst es.esps_ml) m2 in
    let s2 = Fsubst.f_bind_mem s2 (fst es.esps_mr) m3 in

    let s = Fsubst.f_subst_id in
    let s = Fsubst.f_bind_mem s (fst es.esps_ml) m1 in
    let s = Fsubst.f_bind_mem s (fst es.esps_mr) m3 in

    let d1 = Fsubst.f_subst s1 (snd es.esps_po) in
    let d2 = Fsubst.f_subst s2 (snd es.esps_po) in
    let d  = Fsubst.f_subst s  (snd es.esps_po) in

    f_forall_mems
      [(m1, snd es.esps_ml); (m2, None); (m3, snd es.esps_mr)]
      (f_real_le (f_real_add d1 d2) d)
  in

  let mk_d (m1, m2) form =
    let ((t1, t2), (pv, gl), form) = tuplify env (m1, m2) form in

    let a1 = List.map (fun (pv, ty) -> f_pvar pv ty m1) pv in
    let a2 = List.map (fun (pv, ty) -> f_pvar pv ty m2) pv in

    let g1 = List.map (fun g -> f_glob g m1) gl in
    let g2 = List.map (fun g -> f_glob g m2) gl in

    let arg1 = f_tuple (a1 @ g1) in
    let arg2 = f_tuple (a2 @ g2) in

    let f_dpath =
      let fty = toarrow [arg1.f_ty; arg2.f_ty] tbool in
      let fty = toarrow [fty; arg1.f_ty; arg2.f_ty] tint in
      f_op EcCoreLib.CI_Momemtum.p_dpath [arg1.f_ty] fty in

    let d = f_lambda [(t1, GTty arg1.f_ty); (t2, GTty arg2.f_ty)] form in
    let d = f_app f_dpath [d; arg1; arg2] tint in
    let d = f_real_of_int d in

    d
  in

  let ds = mk_d (fst es.esps_ml, fst es.esps_mr)
                (f_and (fst es.esps_pr) phi') in

  let dpr = mk_d (fst es.esps_ml, fst es.esps_mr) phi' in

  let eq_d =
    f_forall_mems
      [es.esps_ml; es.esps_mr]
      (f_imp (fst es.esps_pr) (f_eq ds (snd es.esps_pr)))
  in

  let is_refl_trans_closed =
    let (m1 as old1, _mem1) = es.esps_ml in
    let (m2 as old2, _mem2) = es.esps_mr in

    let ((t1, t2), (pv, gl), phi') = tuplify env (m1, m2) phi' in

    let m1 = EcIdent.fresh m1 in
    let m2 = EcIdent.fresh m2 in

    let phi' =
      let subst = Fsubst.f_subst_id in
      let subst = Fsubst.f_bind_mem subst old1 m1 in
      let subst = Fsubst.f_bind_mem subst old2 m2 in
      Fsubst.f_subst subst phi'
    in

    let tty = ttuple ((List.map snd pv) @ (List.map tglob gl)) in

    let a1 = EcIdent.fresh t1 in
    let a2 = EcIdent.fresh t2 in

    let f_closure =
      let fty = toarrow [tty; tty] tbool in
      let fty = toarrow [fty; tty; tty] tbool in
      f_op EcCoreLib.CI_Momemtum.p_dclosure [tty] fty in

    let concl = f_lambda [(t1, GTty tty); (t2, GTty tty)] phi' in
    let concl = f_app f_closure [concl] (toarrow [tty; tty] tbool) in
    let concl = f_app concl [f_local a1 tty; f_local a2 tty] tbool in
    let concl = f_forall [(a1, GTty tty); (a2, GTty tty)] concl in

    concl
  in

  let concl0 =
    let fv = EcPV.s_read env es.esps_sl in
    let fv = EcPV.PV.elements fv in

    let eq1 =
      f_ands (List.map (fun (pv, ty) ->
        f_eq (f_pvar pv ty (fst es.esps_ml))
             (f_pvar pv ty (fst es.esps_mr)))
        (fst fv))
    and eq2 =
      f_ands (List.map (fun mp ->
        f_eq (f_glob mp (fst es.esps_ml))
             (f_glob mp (fst es.esps_mr)))
        (snd fv))
    in

    f_espS es.esps_ml es.esps_mr
      (f_ands [fst es.esps_pr; eq1; eq2], f_r0)
      es.esps_sl es.esps_sr es.esps_po
      (f_lambda [EcIdent.create "_", GTty treal] f_r0)
  in

  let concl1 =
    f_espS es.esps_ml es.esps_mr
      (f_and (fst es.esps_pr) phi', ds) es.esps_sl es.esps_sr es.esps_po
      es.esps_f
  in

  FApi.t_last
    (fun tc ->
       FApi.xmutate1 tc `Trans
         [mk_linear es.esps_f; po_trans; ti_ineq;
          is_refl_trans_closed; eq_d; concl0; concl1])
    (EcPhlConseq.t_espS_conseq
       f_r1 es.esps_f (fst es.esps_pr, dpr) es.esps_po tc)

(* -------------------------------------------------------------------- *)
let process_esp_trans phi' tc =
  let _    = tc1_as_espS tc in
  let phi' = TTC.tc1_process_prhl_formula tc phi' in

  t_esp_trans phi' tc

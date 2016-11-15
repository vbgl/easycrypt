(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcParsetree
open EcTypes
open EcModules
open EcFol

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let t_hoare_app_r i phi tc =
  let hs = tc1_as_hoareS tc in
  let s1, s2 = s_split i hs.hs_s in
  let a = f_hoareS_r { hs with hs_s = stmt s1; hs_po = phi }  in
  let b = f_hoareS_r { hs with hs_pr = phi; hs_s = stmt s2 } in
  FApi.xmutate1 tc `HlApp [a; b]

let t_hoare_app = FApi.t_low2 "hoare-app" t_hoare_app_r

(* -------------------------------------------------------------------- *)
let t_bdhoare_app_r_low i (phi, pR, f1, f2, g1, g2) tc =
  let bhs = tc1_as_bdhoareS tc in
  let s1, s2 = s_split i bhs.bhs_s in
  let s1, s2 = stmt s1, stmt s2 in
  let nR = f_not pR in
  let cond_phi = f_hoareS bhs.bhs_m bhs.bhs_pr s1 phi in
  let condf1 = f_bdHoareS_r { bhs with bhs_s = s1; bhs_po = pR; bhs_bd = f1; } in
  let condg1 = f_bdHoareS_r { bhs with bhs_s = s1; bhs_po = nR; bhs_bd = g1; } in
  let condf2 = f_bdHoareS_r
    { bhs with bhs_s = s2; bhs_pr = f_and_simpl phi pR; bhs_bd = f2; } in
  let condg2 = f_bdHoareS_r
    { bhs with bhs_s = s2; bhs_pr = f_and_simpl phi nR; bhs_bd = g2; } in
  let bd =
    (f_real_add_simpl (f_real_mul_simpl f1 f2) (f_real_mul_simpl g1 g2)) in
  let condbd =
    match bhs.bhs_cmp with
    | FHle -> f_real_le bd bhs.bhs_bd
    | FHeq -> f_eq bd bhs.bhs_bd
    | FHge -> f_real_le bhs.bhs_bd bd in
  let condbd = f_imp bhs.bhs_pr condbd in
  let (ir1, ir2) = EcIdent.create "r", EcIdent.create "r" in
  let (r1 , r2 ) = f_local ir1 treal, f_local ir2 treal in
  let condnm =
    let eqs = f_and (f_eq f2 r1) (f_eq g2 r2) in
    f_forall
      [(ir1, GTty treal); (ir2, GTty treal)]
      (f_hoareS bhs.bhs_m (f_and bhs.bhs_pr eqs) s1 eqs) in
  let conds = [f_forall_mems [bhs.bhs_m] condbd; condnm] in
  let conds =
    if   f_equal g1 f_r0
    then condg1 :: conds
    else if   f_equal g2 f_r0
         then condg2 :: conds
         else condg1 :: condg2 :: conds in

  let conds =
    if   f_equal f1 f_r0
    then condf1 :: conds
    else if   f_equal f2 f_r0
         then condf2 :: conds
         else condf1 :: condf2 :: conds in

  let conds = cond_phi :: conds in

  FApi.xmutate1 tc `HlApp conds

(* -------------------------------------------------------------------- *)
let t_bdhoare_app_r i info tc =
  let tactic tc =
    let hs  = tc1_as_hoareS tc in
    let tt1 = EcPhlConseq.t_hoareS_conseq_nm hs.hs_pr f_true in
    let tt2 = EcHiGoal.process_trivial in
    FApi.t_seqs [tt1; tt2; t_fail] tc
  in

  FApi.t_last
    (FApi.t_try (t_intros_s_seq (`Symbol ["_"; "_"]) tactic))
    (t_bdhoare_app_r_low i info tc)

let t_bdhoare_app = FApi.t_low2 "bdhoare-app" t_bdhoare_app_r

(* -------------------------------------------------------------------- *)
let t_equiv_app (i, j) phi tc =
  let es = tc1_as_equivS tc in
  let sl1,sl2 = s_split i es.es_sl in
  let sr1,sr2 = s_split j es.es_sr in
  let a = f_equivS_r {es with es_sl=stmt sl1; es_sr=stmt sr1; es_po=phi} in
  let b = f_equivS_r {es with es_pr=phi; es_sl=stmt sl2; es_sr=stmt sr2} in

  FApi.xmutate1 tc `HlApp [a; b]

let t_equiv_app_onesided side i pre post tc =
  let env = FApi.tc1_env tc in
  let es = tc1_as_equivS tc in
  let m, s, s' =
    match side with
    | `Left  -> es.es_ml, es.es_sl, es.es_sr
    | `Right -> es.es_mr, es.es_sr, es.es_sl
  in
  let ij =
    match side with
    | `Left  -> (i, List.length s'. s_node)
    | `Right -> (List.length s'. s_node, i) in
  let _s1, s2 = s_split i s in

  let modi = EcPV.s_write env (EcModules.stmt s2) in
  let subst = Fsubst.f_subst_mem mhr (fst m) in
  let p' = subst pre and q' = subst post in
  let r = f_and p' (generalize_mod env (fst m) modi (f_imp q' es.es_po)) in
  FApi.t_seqsub (t_equiv_app ij r)
    [t_id; (* s1 ~ s' : pr ==> r *)
     FApi.t_seqsub (EcPhlConseq.t_equivS_conseq_nm p' q')
       [(* r => forall mod, post => post' *) t_logic_trivial;
        (* r => p' *) t_logic_trivial;
        (* s1 ~ [] : p' ==> q' *) EcPhlConseq.t_equivS_conseq_bd side pre post
       ]
    ] tc

(* -------------------------------------------------------------------- *)
let t_esp_app (i, j) (f1, f2) phi tc =
  let es = tc1_as_espS tc in
  let sl1,sl2 = s_split i es.esps_sl in
  let sr1,sr2 = s_split j es.esps_sr in

  let a = f_espS_r { es with
      esps_sl = stmt sl1; esps_sr = stmt sr1;
      esps_po = phi     ; esps_f  = f1      ; } in

  let b = f_espS_r { es with
      esps_pr = phi     ; esps_sl = stmt sl2;
      esps_sr = stmt sr2; esps_f  = f2      ; } in

  let pf  x = f_app es.esps_f [x] treal in
  let pf1 x = f_app f1 [x] treal in
  let pf2 x = f_app f2 [x] treal in
  let lr  x = f_local x treal in

  let eqf =
    let x = EcIdent.create "x" in
    f_forall [(x, GTty treal)]
       (f_eq (pf (lr x)) (pf2 (pf1 (lr x)))) in

  let aff =
    let f_affine =
      f_op EcCoreLib.CI_Distr.p_affine []
        (toarrow [toarrow [treal] treal] tbool) in
    f_app f_affine [f2] tbool in

  FApi.xmutate1 tc `HlApp [a; b; eqf; aff]

(* -------------------------------------------------------------------- *)
let process_phl_bd_info dir bd_info tc =
  match bd_info with
  | PAppNone ->
      let hs = tc1_as_bdhoareS tc in
      let f1, f2 =
         match dir with
        | Backs -> hs.bhs_bd, f_r1
        | Fwds  -> f_r1, hs.bhs_bd
      in `Phl (f_true, f1, f2, f_r0, f_r1)

  | PAppSingle f ->
      let hs = tc1_as_bdhoareS tc in
      let f  = TTC.tc1_process_Xhl_form tc treal f in
      let f1, f2 =
        match dir with
        | Backs  -> (f_real_div hs.bhs_bd f, f)
        | Fwds   -> (f, f_real_div hs.bhs_bd f)
      in
      `Phl (f_true, f1, f2, f_r0, f_r1)

  | PAppMult (phi, f1, f2, g1, g2) ->
      let phi =
        phi |> omap (TTC.tc1_process_Xhl_formula tc)
            |> odfl f_true in

      let check_0 f =
        if not (f_equal f f_r0) then
          tc_error !!tc "the formula must be 0%%r" in

      let process_f (f1,f2) =
        match f1, f2 with
        | None, None -> assert false

        | Some fp, None ->
            let f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f; (f, f_r1)

        | None, Some fp ->
            let f = TTC.tc1_process_Xhl_form tc treal fp in
            reloc fp.pl_loc check_0 f; (f_r1, f)

        | Some f1, Some f2 ->
            (TTC.tc1_process_Xhl_form tc treal f1,
             TTC.tc1_process_Xhl_form tc treal f2)
      in

      let f1, f2 = process_f (f1, f2) in
      let g1, g2 = process_f (g1, g2) in

      `Phl (phi, f1, f2, g1, g2)

  | PAppEsp ((f1, f2), d) ->
        let f1 = TTC.tc1_process_form tc (tfun treal treal) f1 in
        let f2 = TTC.tc1_process_form tc (tfun treal treal) f2 in
        let d  = TTC.tc1_process_prhl_form tc treal d in

      let f1, f2 =
         match dir with Backs -> (f1, f2) | Fwds  -> (f2, f1)
      in `Esp ((f1, f2), d)

(* -------------------------------------------------------------------- *)
let process_app (side, dir, k, phi, bd_info) tc =
  let concl = FApi.tc1_goal tc in

  let get_single phi =
    match phi with
    | Single phi -> phi
    | Double _   -> tc_error !!tc "seq: a single formula is expected" in

  let check_side side =
    if EcUtils.is_some side then
      tc_error !!tc "seq: no side information expected" in

  match k, bd_info with
  | Single i, PAppNone when is_hoareS concl ->
    check_side side;
    let phi = TTC.tc1_process_Xhl_formula tc (get_single phi) in
    t_hoare_app i phi tc

  | Single i, PAppNone when is_equivS concl ->
    let pre, post =
      match phi with
      | Single _ -> tc_error !!tc "seq onsided: a pre and a post is expected"
      | Double (pre, post) ->
        TTC.tc1_process_Xhl_formula ?side tc pre,
        TTC.tc1_process_Xhl_formula ?side tc post in
    let side =
      match side with
      | None -> tc_error !!tc "seq onsided: side information expected"
      | Some side -> side in
    t_equiv_app_onesided side i pre post tc

  | Single i, _ when is_bdHoareS concl ->
      let pia = TTC.tc1_process_Xhl_formula tc (get_single phi) in
      let (ra, f1, f2, f3, f4) =
        match process_phl_bd_info dir bd_info tc with
        | `Phl info -> info | _ -> tc_error !!tc "invalid bound"
      in t_bdhoare_app i (ra, pia, f1, f2, f3, f4) tc

  | Double (i, j), PAppNone when is_equivS concl ->
      let phi = TTC.tc1_process_prhl_formula tc (get_single phi) in
      t_equiv_app (i, j) phi tc

  | Double (i, j), _ when is_espS concl ->
      let phi = TTC.tc1_process_prhl_formula tc (get_single phi) in
      let ((f1, f2), d) =
        match process_phl_bd_info dir bd_info tc with
        | `Esp info -> info | _ -> tc_error !!tc "invalid momentum spec"
      in t_esp_app (i, j) (f1, f2) (phi, d) tc

  | Single _, PAppNone
  | Double _, PAppNone ->
      tc_error !!tc "invalid `position' parameter"

  | _, _ ->
      tc_error !!tc "optional bound parameter not supported"

(* -------------------------------------------------------------------- *)
let t_pcase (f0, f1, f2, d, p1, p2, e, phi, i, j) tc =

  let es = tc1_as_espS tc in
  let sl1,sl2 = s_split i es.esps_sl in
  let sr1,sr2 = s_split j es.esps_sr in

  let sl1 = stmt sl1 in
  let a = f_espS_r { es with
      esps_sl = sl1; esps_sr = stmt sr1;
      esps_po = phi, d; esps_f  = f0      ; } in

  let fe = Fsubst.f_subst_mem mhr (fst es.esps_ml) e in

  let b = f_espS_r { es with
      esps_pr = f_and phi fe, d ;
      esps_sl = stmt sl2; esps_sr = stmt sr2;
      esps_f  = f1; } in

  let c = f_espS_r { es with
      esps_pr = f_and phi (f_not fe), d ;
      esps_sl = stmt sl2; esps_sr = stmt sr2;
      esps_f  = f2; } in

  let f =
    let x = EcIdent.create "x" in
    let fx = f_local x treal in
    let f0x = f_app f0 [fx] treal in
    let fm fi pi x = f_real_mul pi (f_app fi [x] treal) in
    f_lambda [x, gtty treal]
      (f_real_add (fm f1 p1 f0x) (fm f2 p2 f0x)) in

  let hyps = FApi.tc1_hyps tc in
  EcReduction.check_conv hyps f es.esps_f;

  let pre = Fsubst.f_subst_mem (fst es.esps_ml) mhr (fst es.esps_pr) in
  let side1 =
    f_forall_mems [es.esps_mr]
      (f_bdHoareS (mhr, snd es.esps_ml) pre sl1 e FHle p1) in
  let side2 =
    f_forall_mems [es.esps_mr]
      (f_bdHoareS (mhr, snd es.esps_ml) pre sl1 (f_not e) FHle p2) in

  let f_affine =
    f_op EcCoreLib.CI_Distr.p_affine []
      (toarrow [toarrow [treal] treal] tbool) in
  let mk_affine f =
    f_app f_affine [f] tbool in
  FApi.xmutate1 tc `PCASE [mk_affine f1; mk_affine f2;side1; side2; a; b; c]

(* -------------------------------------------------------------------- *)
let process_pcase (info, i, j) tc =
  let (f0, f1, f2, d, p1, p2, e, phi) = info in
  let es = tc1_as_espS tc in
  let f0 = TTC.tc1_process_form tc (tfun treal treal) f0 in
  let f1 = TTC.tc1_process_form tc (tfun treal treal) f1 in
  let f2 = TTC.tc1_process_form tc (tfun treal treal) f2 in
  let d  = TTC.tc1_process_prhl_form tc treal d in
  let phi = TTC.tc1_process_prhl_form tc tbool phi in
  let p1 = TTC.tc1_process_form tc treal p1 in
  let p2 = TTC.tc1_process_form tc treal p2 in
  let e  =
    let hyps = FApi.tc1_hyps tc in
    let hyps = EcEnv.LDecl.push_active (mhr, snd es.esps_ml) hyps in
    TTC.pf_process_form !!tc hyps tbool e in
  t_pcase (f0, f1, f2, d, p1, p2, e, phi, i, j) tc

(* -------------------------------------------------------------------- *)
let t_pcase3 (f0, f1, f2, f3, d, p1, p2, p3, e1, e2, phi, i, j) tc =
  let es = tc1_as_espS tc in
  let sl1,sl2 = s_split i es.esps_sl in
  let sr1,sr2 = s_split j es.esps_sr in

  let sl1 = stmt sl1 in
  let a = f_espS_r { es with
      esps_sl = sl1; esps_sr = stmt sr1;
      esps_po = phi, d; esps_f = f0; } in

  let fe1 = Fsubst.f_subst_mem mhr (fst es.esps_ml) e1 in
  let fe2 = Fsubst.f_subst_mem mhr (fst es.esps_ml) e2 in

  let b = f_espS_r { es with
      esps_pr = f_and phi fe1, d ;
      esps_sl = stmt sl2; esps_sr = stmt sr2;
      esps_f  = f1; } in

  let c = f_espS_r { es with
      esps_pr = f_and phi fe2, d ;
      esps_sl = stmt sl2; esps_sr = stmt sr2;
      esps_f  = f2; } in

  let d = f_espS_r { es with
      esps_pr = f_and phi (f_not (f_and fe1 fe2)), d ;
      esps_sl = stmt sl2; esps_sr = stmt sr2;
      esps_f  = f3; } in

  let f =
    let x = EcIdent.create "x" in
    let fx = f_local x treal in
    let f0x = f_app f0 [fx] treal in
    let fm fi pi x = f_real_mul pi (f_app fi [x] treal) in
    f_lambda [x, gtty treal]
      (f_real_add
         (f_real_add (fm f1 p1 f0x) (fm f2 p2 f0x))
         (fm f3 p3 f0x)) in

  let hyps = FApi.tc1_hyps tc in
  EcReduction.check_conv hyps f es.esps_f;

  let pre = Fsubst.f_subst_mem (fst es.esps_ml) mhr (fst es.esps_pr) in
  let side1 =
    f_forall_mems [es.esps_mr]
      (f_bdHoareS (mhr, snd es.esps_ml) pre sl1 e1 FHle p1) in
  let side2 =
    f_forall_mems [es.esps_mr]
      (f_bdHoareS (mhr, snd es.esps_ml) pre sl1 e2 FHle p2) in
  let side3 =
    f_forall_mems [es.esps_mr]
      (f_bdHoareS (mhr, snd es.esps_ml) pre sl1 (f_not (f_and e1 e2)) FHle p3) in

  let f_affine =
    f_op EcCoreLib.CI_Distr.p_affine []
      (toarrow [toarrow [treal] treal] tbool) in
  let mk_affine f =
    f_app f_affine [f] tbool in
  FApi.xmutate1 tc `PCASE3
    [mk_affine f1; mk_affine f2; mk_affine f3;
     side1; side2; side3; a; b; c; d]

(* -------------------------------------------------------------------- *)
let process_pcase3 (info, i, j) tc =
  let (f0, f1, f2, f3, d, p1, p2, p3, e1, e2, phi) = info in
  let es = tc1_as_espS tc in
  let f0 = TTC.tc1_process_form tc (tfun treal treal) f0 in
  let f1 = TTC.tc1_process_form tc (tfun treal treal) f1 in
  let f2 = TTC.tc1_process_form tc (tfun treal treal) f2 in
  let f3 = TTC.tc1_process_form tc (tfun treal treal) f3 in
  let d  = TTC.tc1_process_prhl_form tc treal d in
  let phi = TTC.tc1_process_prhl_form tc tbool phi in
  let p1 = TTC.tc1_process_form tc treal p1 in
  let p2 = TTC.tc1_process_form tc treal p2 in
  let p3 = TTC.tc1_process_form tc treal p3 in
  let e1  =
    let hyps = FApi.tc1_hyps tc in
    let hyps = EcEnv.LDecl.push_active (mhr, snd es.esps_ml) hyps in
    TTC.pf_process_form !!tc hyps tbool e1 in
  let e2  =
    let hyps = FApi.tc1_hyps tc in
    let hyps = EcEnv.LDecl.push_active (mhr, snd es.esps_ml) hyps in
    TTC.pf_process_form !!tc hyps tbool e2 in
  t_pcase3 (f0, f1, f2, f3, d, p1, p2, p3, e1, e2, phi, i, j) tc

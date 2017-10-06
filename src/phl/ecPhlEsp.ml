(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcModules
open EcFol
open EcCoreGoal
open EcLowPhlGoal

module TTC = EcProofTyping

(* -------------------------------------------------------------------- *)
let process_esp_mult distr norm tc =
  let env, hyps, _ = FApi.tc1_eflat tc in
  let esp = tc1_as_espS tc in

  let distr = TTC.pf_process_exp !!tc hyps `InProc None distr in
  let norm  = TTC.pf_process_exp !!tc hyps `InProc None norm  in

  let error = fun () -> tc_error !!tc "invalid arguments" in

  let ty =
    let ue = EcUnify.UniEnv.create None in
    let v1 = EcUnify.UniEnv.fresh ue in
    let v2 = EcUnify.UniEnv.fresh ue in

    begin try
      EcUnify.unify env ue distr.e_ty (tfun v1 (tdistr v2))
    with EcUnify.UnificationFailure _ -> error () end;

    let map = EcUnify.UniEnv.assubst ue in
    let v1 = Tuni.offun map v1 in
    let v2 = Tuni.offun map v2 in

    if not (EcReduction.EqTest.for_type env v1 v2) then error ();

    if not (EcReduction.EqTest.for_type env
              norm.e_ty (toarrow [v1; v1] treal)) then error ();
    v1
  in

  let r1, m1 = tc1_first_rnd tc esp.esps_sl in
  let r2, m2 = tc1_first_rnd tc esp.esps_sr in

  if not (List.is_empty m1.s_node && List.is_empty m2.s_node) then
    error ();

  match r1, r2 with
  | (LvVar (x1, _), { e_node = Eapp (d1, [a1]) }),
    (LvVar (x2, _), { e_node = Eapp (d2, [a2]) }) ->
    begin
      if not (EcReduction.EqTest.for_expr env d1 distr) then error ();
      if not (EcReduction.EqTest.for_expr env d2 distr) then error ();

      let idfun =
        let x = EcIdent.create "x" in
        f_lambda [x, GTty treal] (f_local x treal)
      in

      let dpr =
        f_app (form_of_expr (fst esp.esps_ml) norm)
              [form_of_expr (fst esp.esps_ml) a1;
               form_of_expr (fst esp.esps_mr) a2] treal in
      let dpo =
        f_app (form_of_expr (fst esp.esps_mr) norm)
              [f_pvar x1 ty (fst esp.esps_ml);
               f_pvar x2 ty (fst esp.esps_mr)] treal in

      FApi.t_last
        (fun tc -> FApi.xmutate1 tc `Mult [])
        (EcPhlConseq.t_espS_conseq
           f_r1 idfun (f_true, dpr) (f_true, dpo) tc)
    end

  | _ -> error ()

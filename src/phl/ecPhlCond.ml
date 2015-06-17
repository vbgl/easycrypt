(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcEnv

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

module Sid = EcIdent.Sid

(* -------------------------------------------------------------------- *)
module LowInternal = struct
 let t_gen_cond side e tc =
   let hyps  = FApi.tc1_hyps tc in
   let fresh = ["m"; "m"; "_"; "_"; "_"] in
   let fresh = LDecl.fresh_ids hyps fresh in

   let m1,m2,h,h1,h2 = as_seq5 fresh in
   let t_introm = if is_none side then t_id else t_intros_i [m1] in

   let t_sub b tc =
     FApi.t_on1seq 0
       (EcPhlRCond.t_rcond side b 1)
       (FApi.t_seqs
           [t_introm; EcPhlSkip.t_skip; t_intros_i [m2;h];
            FApi.t_or
              (FApi.t_seqs [t_elim_hyp h;
                            t_intros_i [h1;h2];
                            t_apply_hyp h2])
              (t_apply_hyp h)])
       tc
   in

   FApi.t_seqsub (EcPhlCase.t_hl_case e) [t_sub true; t_sub false] tc
end

(* -------------------------------------------------------------------- *)
(* mix of the if rule + conseq rule + seq rule *)

let t_muhoare_cond pr1 po1 pr2 po2 tc = 
  let env = FApi.tc1_env tc in
  let muh = tc1_as_muhoareS tc in 
  let (e,s1,s2), s = tc1_last_if tc muh.muh_s in
  (* FIXME: ensure that pr1 po1 pr2 po2 have the expected type *)
  let concl1 = f_muhoareS_r {muh_pr = pr1; muh_s = s1; muh_po = po1;} in
  let concl2 = f_muhoareS_r {muh_pr = pr2; muh_s = s2; muh_po = po2;} in
  let concl3 = 
    let mu,ty,po = get_lambda1 env muh.muh_po in
    let mu1 = EcIdent.create "mu1" in
    let mu2 = EcIdent.create "mu2" in
     
    f_forall [(mu1,GTty ty); (mu2,GTty ty)]
      (f_imp (f_app_simpl po1 [f_local mu1 ty] tbool)
         (f_imp (f_app_simpl po2 [f_local mu2 ty] tbool)
            (EcLowMuHoare.oplus ty mu mu1 mu2 po))) in
  
  let po = EcLowMuHoare.curly env e pr1 pr2 in
  let concl4 = f_muhoareS_r { muh with muh_s = s; muh_po = po } in

  FApi.xmutate1 tc `Conseq [concl1; concl2; concl3; concl4 ]

(* -------------------------------------------------------------------- *)
let t_hoare_cond tc =
  let hs = tc1_as_hoareS tc in
  let (e,_,_) = fst (tc1_first_if tc hs.hs_s) in
  LowInternal.t_gen_cond None (form_of_expr (Some hs.hs_m) e) tc

(* -------------------------------------------------------------------- *)
let t_bdhoare_cond tc =
  let bhs = tc1_as_bdhoareS tc in
  let (e,_,_) = fst (tc1_first_if tc bhs.bhs_s) in
  LowInternal.t_gen_cond None (form_of_expr (Some bhs.bhs_m) e) tc

(* -------------------------------------------------------------------- *)
let rec t_equiv_cond side tc =
  let hyps = FApi.tc1_hyps tc in
  let es   = tc1_as_equivS tc in

  match side with
  | Some s ->
      let e =
        match s with
        | `Left ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sl) in
          form_of_expr (Some es.es_ml) e
        | `Right ->
          let (e,_,_) = fst (tc1_first_if tc es.es_sr) in
          form_of_expr (Some es.es_mr) e
      in LowInternal.t_gen_cond side e tc

  | None ->
      let el,_,_ = fst (tc1_first_if tc es.es_sl) in
      let er,_,_ = fst (tc1_first_if tc es.es_sr) in
      let el     = form_of_expr (Some es.es_ml) el in
      let er     = form_of_expr (Some es.es_mr) er in
      let fiff   =
        f_forall_mems
          [es.es_ml;es.es_mr]
          (f_imp es.es_pr (f_iff el er)) in

      let fresh = ["hiff";"m1";"m2";"h";"h";"h"] in
      let fresh = LDecl.fresh_ids hyps fresh in

      let hiff,m1,m2,h,h1,h2 = as_seq6 fresh in

      let t_aux =
        let rwpt = { pt_head = PTLocal hiff;
                     pt_args = [pamemory (m1,snd es.es_ml); pamemory (m2, snd es.es_mr); 
                                PASub None]; } in


        FApi.t_seqs [t_intros_i [m1]    ; EcPhlSkip.t_skip;
                     t_intros_i [m2; h] ; t_elim_hyp h;
                     t_intros_i [h1; h2];
                     FApi.t_seqsub
                       (t_rewrite rwpt (`RtoL, None))
                       [t_apply_hyp h1; t_apply_hyp h2]]
      in
        FApi.t_on1seq 1 (t_cut fiff)
          (t_intros_i_seq [hiff]
             (FApi.t_seqsub
                (t_equiv_cond (Some `Left))
                [FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond `Right true  1)
                   [t_aux; t_clear hiff];
                 FApi.t_seqsub
                   (EcPhlRCond.Low.t_equiv_rcond `Right false 1)
                   [t_aux; t_clear hiff]]))
          tc

let process_muhoare_cond ((pr1, po1),(pr2,po2)) tc =
  let doit (mumt,f) = close_mu_binding mumt f in
  let pr1 = EcProofTyping.tc1_process_phl_ld_formula tc pr1 in
  let po1 = EcProofTyping.tc1_process_phl_ld_formula tc po1 in
  let pr2 = EcProofTyping.tc1_process_phl_ld_formula tc pr2 in
  let po2 = EcProofTyping.tc1_process_phl_ld_formula tc po2 in
  t_muhoare_cond (doit pr1) (doit po1) (doit pr2) (doit po2) tc  
 
let t_muhoare_cond_det tc = 
  let hs = tc1_as_muhoareS tc in
  let env = FApi.tc1_env tc in
  let (e,_,_) = fst (tc1_first_if tc hs.muh_s) in
  let (mu,mt),pr = open_mu_binding env hs.muh_pr in
  let fe = form_of_expr (Some (mhr,mt)) e in
  let tmt = tmem mt in
  let se = f_square (mhr,tmt) fe mu in
  let sne = f_square (mhr,tmt) (f_not fe) mu in
  let pr1 = close_mu_binding (mu,mt) (f_and pr (f_or se sne)) in
  let prt = close_mu_binding (mu,mt) (f_and pr se) in
  let prf = close_mu_binding (mu,mt) (f_and pr sne) in

  let se = close_mu_binding (mu,mt) se in

  let t_branch b = 
    let pr = if b then prt else prf in
    let lconseq = 
      if b then EcCoreLib.CI_Logic.p_muhoare_if_conseq_t 
      else EcCoreLib.CI_Logic.p_muhoare_if_conseq_f in
    let l_and = EcCoreLib.CI_Logic.p_and_proj_r in

    EcPhlConseq.t_muhoareS_conseq pr hs.muh_po @+ [
      t_intros_s (`Symbol ["_"]) @!  EcHiGoal.t_apply_prept (`UG lconseq) ;
      t_logic_trivial;
      EcPhlRCond.t_rcond None b 1 @+ [
        EcPhlSkip.t_skip @! t_intros_s (`Symbol ["_"]) @! 
          EcHiGoal.t_apply_prept (`UG l_and); 
        t_id
      ]
    ] in
  let mu = EcIdent.create "mu" in
  let lpre = EcCoreLib.CI_Logic.p_muhoare_if_conseq_pre in
   
  (EcPhlConseq.t_muhoareS_conseq pr1 hs.muh_po @+ [
    t_intro_i mu @! 
      EcHiGoal.t_apply_prept (`UG lpre) @!
      t_generalize_hyp ~clear:true mu;
    t_logic_trivial;
    EcPhlCase.t_hl_case se @+ [
      t_branch true;
      t_branch false 
    ]
  ]) tc
  
(* -------------------------------------------------------------------- *)
let process_cond info tc =
  let default_if i s = ofdfl (fun _ -> tc1_pos_last_if tc s) i in
  
  match info with
  | `MuHoare info -> process_muhoare_cond info tc 
  | `Head side ->
    t_hS_or_bhS_or_eS ~th:t_hoare_cond ~tbh:t_bdhoare_cond ~te:(t_equiv_cond side) ~tmuh:t_muhoare_cond_det tc 

  | `Seq (side, i1, i2, f) -> 
    let es = tc1_as_equivS tc in
    let f  = EcProofTyping.tc1_process_prhl_formula tc f in
    let n1 = default_if i1 es.es_sl in
    let n2 = default_if i2 es.es_sr in
    FApi.t_seqsub (EcPhlApp.t_equiv_app (n1,n2) f)
      [ t_id; t_equiv_cond side ] tc

  | `SeqOne (s, i, f1, f2) -> 
    let es = tc1_as_equivS tc in
    let n = default_if i (match s with `Left -> es.es_sl | `Right -> es.es_sr) in
    let f1 = EcProofTyping.tc1_process_phl_formula ~side:s tc f1 in
    let f2 = EcProofTyping.tc1_process_phl_formula ~side:s tc f2 in
    FApi.t_seqsub
      (EcPhlApp.t_equiv_app_onesided s n f1 f2)
      [ t_id; t_bdhoare_cond] tc

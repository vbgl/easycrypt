(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let destr_square env p = 
  let (mu, mt), p = open_mu_binding env p in

  let check_mu f = 
    match f.f_node with
    | Flocal mu' when EcIdent.id_equal mu mu' -> ()
    | _  -> EcUtils.destr_error "check_mu" in

  try
    let f, f0 = destr_eq p in

    if not (f_equal f0 f_r0) then EcUtils.destr_error "f_r0" else
  
    let f =
      let f, fmu =
        destr_app2_eq ~name:"muf" EcCoreLib.CI_Distr.p_muf f
      in check_mu fmu; f in

    let fbody = f_app_simpl f [f_local mhr (EcTypes.tmem mt)] EcTypes.treal in
    let p = destr_not (destr_app1_eq ~name:"b2r" EcCoreLib.CI_Real.p_b2r fbody) in
  
    (mt, p)

  with EcUtils.DestrError _ ->
    raise (EcUtils.DestrError "phl-square")

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS_r tc =
  let bhs = tc1_as_bdhoareS tc in
  if not (bhs.bhs_cmp = FHeq && f_equal bhs.bhs_bd f_r0) then
    tc_error !!tc "%s" "bound must be equal to 0%r";
  let concl = f_hoareS bhs.bhs_m bhs.bhs_pr bhs.bhs_s (f_not bhs.bhs_po) in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareF_r tc =
  let bhf = tc1_as_bdhoareF tc in
  if not (bhf.bhf_cmp = FHeq && f_equal bhf.bhf_bd f_r0) then
    tc_error !!tc "%s" "bound must be equal to 0%r";
  let concl = f_hoareF bhf.bhf_pr bhf.bhf_f (f_not bhf.bhf_po) in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareS_r tc =
  let hs = tc1_as_hoareS tc in
  let concl = f_bdHoareS hs.hs_m hs.hs_pr hs.hs_s (f_not hs.hs_po) FHeq f_r0 in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_bdhoare_of_hoareF_r tc =
  let hf = tc1_as_hoareF tc in
  let concl = f_bdHoareF hf.hf_pr hf.hf_f (f_not hf.hf_po) FHeq f_r0 in
  FApi.xmutate1 tc `ViewBdHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_muhoareS_r tc =
  let muh = tc1_as_muhoareS tc in
  let env = FApi.tc1_env tc in
  let mt, pr = 
    try  destr_square env muh.muh_pr 
    with EcUtils.DestrError _ -> tc_error !!tc "pre must be a square" in
  let _, po = 
    try  destr_square env muh.muh_po 
    with EcUtils.DestrError _ -> tc_error !!tc "post must be a square" in
  let concl = f_hoareS (mhr, mt) pr muh.muh_s po in
  FApi.xmutate1 tc `ViewmuHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_muhoareF_r tc =
  let muh = tc1_as_muhoareF tc in
  let env = FApi.tc1_env tc in
  let _, pr = 
    try  destr_square env muh.muhf_pr 
    with EcUtils.DestrError _ -> tc_error !!tc "pre must be a square" in
  let _ , po = 
    try destr_square env muh.muhf_po 
    with EcUtils.DestrError _ -> tc_error !!tc "post must be a square" in
  let concl = f_hoareF pr muh.muhf_f po in
  FApi.xmutate1 tc `ViewmuHoare [concl]

(* -------------------------------------------------------------------- *)
let t_hoare_of_bdhoareS = FApi.t_low0 "hoare-bdhoareS" t_hoare_of_bdhoareS_r
let t_hoare_of_bdhoareF = FApi.t_low0 "hoare-bdhoareF" t_hoare_of_bdhoareF_r
let t_bdhoare_of_hoareS = FApi.t_low0 "bdhoare-hoareS" t_bdhoare_of_hoareS_r
let t_bdhoare_of_hoareF = FApi.t_low0 "bdhoare-hoareF" t_bdhoare_of_hoareF_r
let t_hoare_of_muhoareS = FApi.t_low0 "hoare-muhoareS" t_hoare_of_muhoareS_r
let t_hoare_of_muhoareF = FApi.t_low0 "hoare-muhoareF" t_hoare_of_muhoareF_r

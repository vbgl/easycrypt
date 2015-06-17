(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal
open EcLowMuHoare
(* --------------------------------------------------------------------- *)
let t_hoare_case_r f tc =
  let hs = tc1_as_hoareS tc in
  let concl1 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr f } in
  let concl2 = f_hoareS_r { hs with hs_pr = f_and_simpl hs.hs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_bdhoare_case_r f tc =
  let bhs = tc1_as_bdhoareS tc in
  let concl1 = f_bdHoareS_r
    { bhs with bhs_pr = f_and_simpl bhs.bhs_pr f } in
  let concl2 = f_bdHoareS_r
    { bhs with bhs_pr = f_and_simpl bhs.bhs_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_equiv_case_r f tc =
  let es = tc1_as_equivS tc in
  let concl1 = f_equivS_r { es with es_pr = f_and es.es_pr f } in
  let concl2 = f_equivS_r { es with es_pr = f_and es.es_pr (f_not f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_muhoare_case_r f tc = 
  let muh = tc1_as_muhoareS tc in
  let env = FApi.tc1_env tc in
  let concl1 = f_muhoareS_r { muh with muh_pr = p_and env muh.muh_pr f } in
  let concl2 = 
    f_muhoareS_r { muh with muh_pr = p_and env muh.muh_pr (p_not env f) } in
  FApi.xmutate1 tc (`HlCase f) [concl1; concl2]

(* --------------------------------------------------------------------- *)
let t_hoare_case   = FApi.t_low1 "hoare-case"   t_hoare_case_r
let t_bdhoare_case = FApi.t_low1 "bdhoare-case" t_bdhoare_case_r
let t_equiv_case   = FApi.t_low1 "equiv-case"   t_equiv_case_r
let t_muhoare_case = FApi.t_low1 "muhoare-case" t_muhoare_case_r
(* --------------------------------------------------------------------- *)
let t_hl_case_r f tc =
  t_hS_or_bhS_or_eS
    ~th:(t_hoare_case f)
    ~tbh:(t_bdhoare_case f)
    ~te:(t_equiv_case f)
    ~tmuh:(t_muhoare_case f) 

    tc

(* -------------------------------------------------------------------- *)
let t_hl_case = FApi.t_low1 "hl-case" t_hl_case_r

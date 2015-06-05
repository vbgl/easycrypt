(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(*-------------------------------------------------------------------- *)
open EcFol
open EcCoreGoal
open EcLowPhlGoal

(*-------------------------------------------------------------------- *)
let build_sym (ml,mtl) (mr, mtr) =
  (* FIXME *)
  let s = Fsubst.f_subst_id in
  let s = Fsubst.f_bind_mem s ml mtl mr in
  let s = Fsubst.f_bind_mem s mr mtr ml in
  let s = Fsubst.f_subst s in
  s 

(*-------------------------------------------------------------------- *)
let t_equivF_sym tc =
  let ef    = tc1_as_equivF tc in
  let ((_,mtl1),(_,mtr1)), ((_,mtl2),(_,mtr2)) =
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr (FApi.tc1_env tc) in
  let pr = build_sym (mleft, mtl1) (mright, mtr1) ef.ef_pr in
  let po = build_sym (mleft, mtl2) (mright, mtr2) ef.ef_po in
  let cond  = f_equivF pr ef.ef_fr ef.ef_fl po in
  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equivS_sym tc =
  let es    = tc1_as_equivS tc in
  let s = build_sym es.es_ml es.es_mr in
  let pr, po = s es.es_pr, s es.es_po in
  let cond  = f_equivS_r {
    es_ml = fst es.es_ml, snd es.es_mr;
    es_mr = fst es.es_mr, snd es.es_ml;
    es_sl = es.es_sr;
    es_sr = es.es_sl;
    es_pr = pr;
    es_po = po; } in

  FApi.xmutate1 tc `EquivSym [cond]

(*-------------------------------------------------------------------- *)
let t_equiv_sym tc =
  match (FApi.tc1_goal tc).f_node with
  | FequivF _ -> t_equivF_sym tc
  | FequivS _ -> t_equivS_sym tc
  | _ -> tc_error_noXhl ~kinds:[`Equiv `Any] !!tc

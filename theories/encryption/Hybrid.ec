(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore List Finite Distr DInterval.
require (*--*) Means StdOrder.
(*---*) import StdBigop.Bigreal.BRA.

type input.
type output.
type inleaks.
type outleaks.
type outputA.

(* -------------------------------------------------------------------- *)
(* Wrappers for counting *)

module Count = {
  var c : int

  proc init () : unit = {
    c <- 0;
  }

  proc incr () : unit = {
    c <- c + 1;
  }
}.

module type Adv = {
  proc main() : outputA
}.

module AdvCount (A : Adv) = {
  proc main() : outputA = {
    var r : outputA;

    Count.init();
    r <@ A.main();
    return r;
  }
}.

module type Orcl = {
  proc orcl(m : input) : output
}.

module OrclCount (O : Orcl) = {
  proc orcl(m : input) : output = {
    var r : output;

    r <@ O.orcl(m);
    Count.incr();
    return r;
  }
}.

(* -------------------------------------------------------------------- *)
(* Hybrid oracles and games *)

op q : { int | 0 < q } as q_pos.

module type AdvOrcl (O : Orcl) = {
  include Adv
}.

module type Orclb = {
  proc leaks (il : inleaks) : outleaks
  proc orclL (m : input) : output
  proc orclR (m : input) : output
}.

module L (Ob : Orclb) : Orcl = {
  proc orcl = Ob.orclL
}.

module R (Ob : Orclb) : Orcl = {
  proc orcl = Ob.orclR
}.

module type AdvOrclb (Ob : Orclb) (O : Orcl) = {
  include Adv
}.

module Orcln (A : AdvOrcl) (O : Orcl) = AdvCount(A(OrclCount(O))).
module Ln (Ob : Orclb) (A : AdvOrclb) = Orcln(A(Ob), L(Ob)).
module Rn (Ob : Orclb) (A : AdvOrclb) = Orcln(A(Ob), R(Ob)).

(* Hybrid oracle:
   Use left oracle for queries < l0,
   oracle O for queries = l0, and
   right oracle for queries > l0. *)
module HybOrcl (Ob : Orclb) (O : Orcl) = {
  var l, l0 : int

  proc orcl(m:input):output = {
    var r : output;

    if   (l0 < l) r <@ Ob.orclL(m);
    elif (l0 = l) r <@ O.orcl(m);
    else          r <@ Ob.orclR(m);
    l <- l + 1;
    return r;
  }
}.

(* Hybrid game: Adversary has access to
   leaks, left, right, and hybrid oracle *)
module HybGame (A:AdvOrclb) (Ob:Orclb) (O:Orcl) = {
  proc main() : outputA = {
    var r : outputA;

    HybOrcl.l0 <$ [0..q-1];
    HybOrcl.l  <- 0;
    r <@ A(Ob, HybOrcl(Ob, O)).main();
    return r;
  }
}.

clone import Means as M with
  type input <- int,
  type output <- outputA,
    op d <- [0..q-1].

(* -------------------------------------------------------------------- *)
(* Prove that it is equivalent to consider n or 1 calls to the oracle *)
section.

  declare module Ob : Orclb    {Count,HybOrcl}.
  declare module A  : AdvOrclb {Count,HybOrcl,Ob}.

  axiom losslessL: islossless Ob.leaks.
  axiom losslessOb1: islossless Ob.orclL.
  axiom losslessOb2: islossless Ob.orclR.
  axiom losslessA (Ob0 <: Orclb {A}) (LR <: Orcl {A}):
    islossless LR.orcl =>
    islossless Ob0.leaks => islossless Ob0.orclL => islossless Ob0.orclR =>
    islossless A(Ob0, LR).main.

  (* Hybrid game where index is fixed, not sampled *)
  local module HybGameFixed (O : Orcl) = {
    proc work(x : int) : outputA = {
      var r : outputA;

      HybOrcl.l <- 0;
      HybOrcl.l0 <- x;
      r <@ A(Ob, HybOrcl(Ob, O)).main();
      return r;
    }
  }.

  local equiv Obleaks : Ob.leaks ~ Ob.leaks : ={il,glob Ob} ==> ={res,glob Ob}.
  proof. by proc true. qed.

  local equiv Oborcl1 : Ob.orclL ~ Ob.orclL : ={m,glob Ob} ==> ={res,glob Ob}.
  proof. by proc true. qed.

  local equiv Oborcl2 : Ob.orclR ~ Ob.orclR : ={m,glob Ob} ==> ={res,glob Ob}.
  proof. by proc true. qed.

  local lemma GLB_WL &m (p:glob A -> glob Ob -> int -> outputA -> bool):
      Pr[Ln(Ob,HybGame(A)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1]
    = Pr[Rand(HybGameFixed(L(Ob))).main() @ &m : p (glob A) (glob Ob) HybOrcl.l (snd res)].
  proof.
  byequiv (: ={glob A, glob Ob}
             ==>    ={glob A, glob Ob,glob HybOrcl}
                 /\ res{1} = snd res{2}
                 /\ Count.c{1} <= 1)=> //.
  proc.
  inline {1} HybGame(A, Ob, OrclCount(L(Ob))).main.
  inline {2} HybGameFixed(L(Ob)).work.
  wp; call (:    ={glob Ob, glob HybOrcl}
              /\ Count.c{1} = (HybOrcl.l0{1} < HybOrcl.l{1}) ? 1 : 0).
  + proc; wp.
    if=> //.
    + by call Oborcl1; auto=> /#.
    if=> //.
    + inline {1} OrclCount(L(Ob)).orcl Count.incr.
      by wp; call Oborcl1; auto=> /#.
    by call Oborcl2; auto=> /#.
  + by conseq Obleaks.
  + by conseq Oborcl1.
  + by conseq Oborcl2.
  swap {1} 1 2; inline {1} Count.init.
  by auto=> /> l0 /supp_dinter /#.
  qed.

  local lemma GRB_WR &m (p:glob A -> glob Ob -> int -> outputA -> bool):
      Pr[Rn(Ob,HybGame(A)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1]
    = Pr[Rand(HybGameFixed(R(Ob))).main() @ &m : p (glob A) (glob Ob) HybOrcl.l (snd res)].
  proof.
  byequiv (: ={glob A, glob Ob}
             ==>    ={glob A, glob Ob, glob HybOrcl}
                 /\ res{1} = snd res{2}
                 /\ Count.c{1} <= 1)=> //.
  proc.
  inline {1} HybGame(A, Ob, OrclCount(R(Ob))).main.
  inline {2} HybGameFixed(R(Ob)).work.
  wp; call (:    ={glob Ob, glob HybGame}
              /\ Count.c{1} = (HybOrcl.l0{1} < HybOrcl.l{1}) ? 1 : 0).
  + proc; wp.
    if=> //.
    + by call Oborcl1; auto=> /#.
    if=> //.
    + inline {1} OrclCount(R(Ob)).orcl Count.incr.
      by wp; call Oborcl2; auto=> /#.
    by call Oborcl2; auto=> /#.
  + by conseq Obleaks.
  + by conseq Oborcl1.
  + by conseq Oborcl2.
  swap {1} 1 2; inline {1} Count.init.
  by auto=> /> l0 /supp_dinter /#.
  qed.

  local lemma WL0_GLA &m (p:glob A -> glob Ob -> int -> outputA -> bool):
      Pr[HybGameFixed(L(Ob)).work(0) @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q]
    = Pr[Ln(Ob,A).main() @ &m : p (glob A) (glob Ob) Count.c res /\ Count.c <= q ].
  proof.
  byequiv (:    ={glob A, glob Ob}
             /\ x{1} = 0
             ==>    (HybOrcl.l{1} <= q) = (Count.c{2} <= q)
                 /\ (   Count.c{2} <= q
                     =>    ={glob A, glob Ob,res}
                        /\ HybOrcl.l{1} = Count.c{2}))=> // [|/#].
  proc.
  call (: q < Count.c
        ,    ={glob Ob}
          /\ HybOrcl.l0{1} = 0
          /\ HybOrcl.l{1} = Count.c{2}
          /\ 0 <= HybOrcl.l{1}
        ,    HybOrcl.l0{1} = 0
          /\ q < HybOrcl.l{1}).
  + by apply losslessA.
  + proc; inline {2} Count.incr; wp.
    if{1}.
    + by call Oborcl1; auto=> /#.
    rcondt {1} 1; first by auto=> /#.
    by wp; call Oborcl1; auto=> /#.
  + move=> _ _; proc.
    rcondt 1; first by auto; smt(q_pos).
    by wp; call losslessOb1; auto=> /#.
  + by move=> &1; proc; inline Count.incr; wp; call losslessOb1; auto=> /#.
  + by conseq Obleaks.
  + by move=> _ _; conseq losslessL.
  + by move=> &1; conseq losslessL.
  + by conseq Oborcl1.
  + by move=> _ _; conseq losslessOb1.
  + by move=> &1; conseq losslessOb1.
  + by conseq Oborcl2.
  + by move=> _ _; conseq losslessOb2.
  + by move=> &1; conseq losslessOb2.
  by inline {2} Count.init; auto=> /#.
  qed.

  local lemma WRq_GRA &m (p:glob A -> glob Ob -> int -> outputA -> bool):
      Pr[HybGameFixed(R(Ob)).work((q-1)) @ &m :  p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q]
    = Pr[Rn(Ob,A).main() @ &m :  p (glob A) (glob Ob) Count.c res /\ Count.c <= q ].
  proof.
  byequiv (:    ={glob A, glob Ob}
             /\ x{1} = q - 1
             ==>    (HybOrcl.l{1} <= q) = (Count.c{2} <= q)
                 /\ (   Count.c{2} <= q
                     =>    ={glob A, glob Ob, res}
                        /\ HybOrcl.l{1} = Count.c{2}))=> // [|/#].
  proc.
  call (: q < Count.c
        ,    ={glob Ob}
          /\ HybOrcl.l0{1} = q - 1
          /\ HybOrcl.l{1} = Count.c{2}
          /\ 0 <= HybOrcl.l{1}
        ,    HybOrcl.l0{1} = q - 1
          /\ q < HybOrcl.l{1}).
  + by apply losslessA.
  + proc; inline {2} Count.incr; wp.
    if{1}.
    + by call {1} losslessOb1; call {2} losslessOb2; auto=> /#.
    if{1}.
    + by wp; call Oborcl2; auto=> /#.
    by call Oborcl2; auto=> /#.
  + move=> _ _; proc.
    rcondt 1; first by auto=> /#.
    by wp; call losslessOb1; auto=> /#.
  + by move=> &1; proc; inline Count.incr; wp; call losslessOb2; auto=> /#.
  + by conseq Obleaks.
  + by move=> _ _; conseq losslessL.
  + by move=> &1; conseq losslessL.
  + by conseq Oborcl1.
  + by move=> _ _; conseq losslessOb1.
  + by move=> &1; conseq losslessOb1.
  + by conseq Oborcl2.
  + by move=> _ _; conseq losslessOb2.
  + by move=> &1; conseq losslessOb2.
  by inline {2} Count.init; auto=> /#.
  qed.

  local lemma WLR_shift &m v (p:glob A -> glob Ob -> int -> outputA -> bool):
       1 <= v <= q - 1
    =>   Pr[HybGameFixed(L(Ob)).work(v) @ &m: p (glob A) (glob Ob) HybOrcl.l res]
       = Pr[HybGameFixed(R(Ob)).work((v-1)) @ &m : p (glob A) (glob Ob) HybOrcl.l res].
  proof.
  move=> Hv.
  byequiv (:    ={glob A, glob Ob}
             /\ x{1} = v
             /\ x{2} = v - 1
             ==>    ={glob A, glob Ob, HybOrcl.l, res})=> //.
  proc.
  call (: ={glob Ob, HybOrcl.l} /\ HybOrcl.l0{1} = v /\ HybOrcl.l0{2} = v - 1).
  + proc.
    if{1}.
    + by rcondt{2} 1; [ | wp; call Oborcl1 ]; auto=> /#.
    if{1}.
    + by rcondt{2} 1; [ | wp; call Oborcl1 ]; auto=> /#.
    rcondf{2} 1; first by auto=> /#.
    by if{2}; wp; call Oborcl2; wp.
  + by conseq Obleaks.
  + by conseq Oborcl1.
  + by conseq Oborcl2.
  by wp.
  qed.

  lemma Hybrid &m (p:glob A -> glob Ob -> int -> outputA -> bool):
    let p' = fun ga ge l r, p ga ge l r /\ l <= q in
        Pr[Ln(Ob,HybGame(A)).main() @ &m : p' (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1]
      - Pr[Rn(Ob,HybGame(A)).main() @ &m : p' (glob A) (glob Ob) HybOrcl.l res /\ Count.c <= 1]
    = 1%r/q%r * (  Pr[Ln(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res]
                 - Pr[Rn(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res]).
  proof.
  move=> p';rewrite (GLB_WL &m p') (GRB_WR &m p').
  simplify p'; rewrite -(WL0_GLA &m p) -(WRq_GRA &m p).
  have Hint : forall x, support [0..q - 1] x <=> mem (List.Iota.iota_ 0 q) x.
    by move=> x; rewrite !List.Iota.mem_iota  supp_dinter; smt.
  have Hfin: is_finite (support [0..q - 1]).
    rewrite is_finiteE; exists (range 0 q).
    by rewrite range_uniq=> /= x; rewrite mem_range supp_dinter=> /#.
  have Huni : forall (x : int), x \in [0..q - 1] => mu1 [0..q - 1] x = 1%r / q%r.
    by move=> x Hx; rewrite dinter1E /=; smt(supp_dinter).
  pose ev :=
    fun (_j:int) (g:glob HybGameFixed(L(Ob))) (r:outputA),
      let (l,l0,ga,ge) = g in p ga ge l r /\ l <= q.
  have := M.Mean_uni (HybGameFixed(L(Ob))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
  have := M.Mean_uni (HybGameFixed(R(Ob))) &m ev (1%r/q%r) _ _ => //; simplify ev => ->.
  have supp_range: perm_eq (to_seq (support [0..q - 1])) (range 0 q).
  + apply: uniq_perm_eq.
    + exact: uniq_to_seq.
    + exact: range_uniq.
    by move=> x; rewrite mem_to_seq // supp_dinter mem_range /#.
  rewrite !(eq_big_perm _ _ _ _ supp_range) {1}range_ltn 1:q_pos big_cons {1}/predT /=.
  have {6}->: q = q - 1 + 1 by smt().
  rewrite rangeSr 1:#smt:(q_pos) big_rcons {2}/predT /=.
  fieldeq; 1:smt(q_pos).
  rewrite RField.mulNr -RField.mulrN -RField.mulrDr.
  rewrite (big_reindex _ _ (fun x=> x - 1) (fun x=> x + 1) (range 0 (q - 1))) //.
  have ->: (transpose Int.(+) 1) = ((+) 1).
  + by apply: fun_ext=> x /#.
  have ->: predT \o transpose Int.(+) (-1) = predT.
  + by apply: fun_ext=> x.
  rewrite /(\o) //= -(range_addl 0 q 1) /= sumrB /=.
  rewrite (eq_big_seq _ (fun _=> 0%r)) //.
  + move=> n /mem_range /andaE [] ge1_q n_lt_q /=.
    by rewrite (WLR_shift &m n p' _) 1:/# /p'.
  rewrite big_const count_predT size_range.
  rewrite (: max 0 (q - 1) = q - 1) 1:#smt:(q_pos).
  have: (0 <= q - 1) by smt(q_pos).
  elim: (q - 1)=> //= => [|n ge0_n ih].
  + by rewrite iter0.
  by rewrite iterS.
  qed.
end section.

(* -------------------------------------------------------------------- *)
(* Simplified variant: Assume that A calls the oracle at most q times. *)
section.
  declare module Ob : Orclb    {Count,HybOrcl}.
  declare module A  : AdvOrclb {Count,HybOrcl,Ob}.

  axiom A_call : forall (O <: Orcl{Count,A}), hoare [ Orcln(A(Ob), O).main : true ==> Count.c <= q ].

  axiom losslessL: islossless Ob.leaks.
  axiom losslessOb1: islossless Ob.orclL.
  axiom losslessOb2: islossless Ob.orclR.
  axiom losslessA (Ob0 <: Orclb{A}) (LR <: Orcl{A}):
    islossless LR.orcl =>
    islossless Ob0.leaks => islossless Ob0.orclL => islossless Ob0.orclR =>
    islossless A(Ob0, LR).main.

  local module Al = Orcln(A(Ob),HybOrcl(Ob,L(Ob))).

  local module Bl = {
    proc main() : outputA = {
      var r : outputA;

      HybOrcl.l0 <$ [0..q-1];
      HybOrcl.l  <- 0;
      r <@ Al.main();
      return r;
    }
  }.

  local module Ar = Orcln(A(Ob),HybOrcl(Ob,R(Ob))).

  local module Br = {
    proc main() : outputA = {
      var r : outputA;

      HybOrcl.l0 <$ [0..q-1];
      HybOrcl.l  <- 0;
      r <@ Ar.main();
      return r;
    }
  }.

  local equiv B_Bl : HybGame(A,Ob,L(Ob)).main ~ Bl.main :
     ={glob A, glob Ob} ==>
     ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} = HybOrcl.l{2} /\ Count.c{2} <= q.
  proof.
  conseq (:  ={glob A, glob Ob} ==> ={glob A, glob Ob, glob HybOrcl, res})
         _
         (: true ==> Count.c = HybOrcl.l /\ Count.c <= q).
  + conseq (: true ==> Count.c = HybOrcl.l) (: true ==> Count.c <= q).
    + by proc; call (A_call (<: HybOrcl(Ob,L(Ob))))=> //.
    proc; inline *; wp; call (: Count.c = HybOrcl.l).
    + by proc; inline *; wp; conseq (: _ ==> true).
    + by conseq (: _ ==> true).
    + by conseq (: _ ==> true).
    + by conseq (: _ ==> true).
    by wp.
  proc; inline Al.main; wp; call (: ={glob Ob, glob HybOrcl}).
  + proc; inline *; wp; sp; if=> //.
    + by call (: true).
    by if=> //; wp; call (: true).
  + by proc (={glob HybOrcl}).
  + by proc (={glob HybOrcl}).
  + by proc (={glob HybOrcl}).
  by inline *; auto.
  qed.

  local equiv B_Br : HybGame(A,Ob,R(Ob)).main ~ Br.main :
     ={glob A, glob Ob} ==>
     ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} = HybOrcl.l{2} /\ Count.c{2} <= q.
  proof.
  conseq (: ={glob A, glob Ob} ==> ={glob A, glob Ob, glob HybOrcl, res})
         _
         (: true ==> Count.c = HybOrcl.l /\ Count.c <= q).
  + conseq (: true ==> Count.c = HybOrcl.l) (: true ==> Count.c <= q).
    + by proc; call (A_call (<: HybOrcl(Ob,R(Ob)))).
    proc; inline *; wp; call (: Count.c = HybOrcl.l).
    + by proc; inline *; wp; conseq (: _ ==> true).
    + by conseq (: _ ==> true).
    + by conseq (: _ ==> true).
    + by conseq (: _ ==> true).
    by wp.
  proc; inline Ar.main; wp; call (: ={glob Ob, glob HybOrcl}).
  + proc; inline *; wp; sp; if=> //.
    + by call (: true).
    by if=> //; wp; call (: true).
  + by proc (={glob HybOrcl}).
  + by proc (={glob HybOrcl}).
  + by proc (={glob HybOrcl}).
  by inline *; auto.
  qed.

  local lemma Pr_Bl &m (p:glob A -> glob Ob -> int -> outputA -> bool):
       Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res]
     = Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
  proof.
  have ->:
      Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res]
    = Pr[Bl.main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
  + by byequiv B_Bl.
  apply eq_sym.
  by byequiv B_Bl.
  qed.

  local lemma Pr_Br &m (p:glob A -> glob Ob -> int -> outputA -> bool):
       Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res]
     = Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
  proof.
  have ->:
      Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res]
    = Pr[Br.main() @ &m : p (glob A) (glob Ob) HybOrcl.l res /\ HybOrcl.l <= q].
  + by byequiv B_Br.
  apply eq_sym.
  by byequiv B_Br.
  qed.

  lemma Hybrid_restr &m (p:glob A -> glob Ob -> int -> outputA -> bool):
        Pr[HybGame(A,Ob,L(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res]
      - Pr[HybGame(A,Ob,R(Ob)).main() @ &m : p (glob A) (glob Ob) HybOrcl.l res]
    = 1%r/q%r * (  Pr[Ln(Ob,A).main() @ &m : p (glob A) (glob Ob) Count.c res]
                 - Pr[Rn(Ob,A).main() @ &m : p (glob A) (glob Ob) Count.c res]).
  proof.
  pose p' := fun ga ge l r, p ga ge l r /\ l <= q.
  have ->:   Pr[Ln(Ob,A).main() @ &m : p  (glob A) (glob Ob) Count.c res]
           = Pr[Ln(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res].
  + byequiv (: ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res} /\ Count.c{1} <= q)=> [| |@/p'] //=.
    conseq (: ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res}) (: true ==> Count.c <= q).
    + exact/(A_call (<: L(Ob))).
    by sim.
  have ->:   Pr[Rn(Ob,A).main() @ &m : p  (glob A) (glob Ob) Count.c res]
           = Pr[Rn(Ob,A).main() @ &m : p' (glob A) (glob Ob) Count.c res].
  + byequiv (: ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res} /\ Count.c{1} <= q)=> [| |@/p'] //=.
    conseq (: ={glob A, glob Ob} ==> ={glob A, glob Ob, Count.c, res}) (: true ==> Count.c <= q).
    + exact/(A_call (<: R(Ob))).
    by sim.
  rewrite (Pr_Bl &m p) (Pr_Br &m p).
  have /= H := Hybrid Ob A losslessL losslessOb1 losslessOb2 losslessA &m p.
  rewrite /p' -H.
  congr.
  + byequiv (: ={glob A, glob Ob} ==> ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} <= 1)=> //.
    proc; inline *; wp.
    call (: ={glob Ob, glob HybOrcl} /\ (if HybOrcl.l <= HybOrcl.l0 then Count.c = 0 else Count.c =1){2}).
    + proc; inline *; wp.
      if=> //.
      + by call (: ={glob HybOrcl}); auto=> /#.
      if=> //.
      + by wp; call (: ={glob HybOrcl}); auto=> /#.
      by call (: ={glob HybOrcl}); auto=> /#.
    + by conseq (: _ ==> ={res,glob Ob})=> //; sim.
    + by conseq (: _ ==> ={res,glob Ob})=> //; sim.
    + by conseq (: _ ==> ={res,glob Ob})=> //; sim.
    by auto=> /> l0 /supp_dinter /#.
  congr.
  byequiv (: ={glob A, glob Ob} ==> ={glob A, glob Ob, glob HybOrcl, res} /\ Count.c{2} <= 1)=> //.
  proc; inline *; wp.
  call (: ={glob Ob, glob HybOrcl} /\ (if HybOrcl.l <= HybOrcl.l0 then Count.c = 0 else Count.c =1){2}).
  + proc; inline *; wp.
    if=> //.
    + by call (: ={glob HybOrcl}); auto=> /#.
    if=> //.
    + by wp; call (: ={glob HybOrcl}); auto=> /#.
    by call (: ={glob HybOrcl}); auto=> /#.
  + by conseq (: _ ==> ={res, glob Ob})=> //; sim.
  + by conseq (: _ ==> ={res, glob Ob})=> //; sim.
  + by conseq (: _ ==> ={res, glob Ob})=> //; sim.
  by auto=> /> l0 /supp_dinter /#.
  qed.
end section.

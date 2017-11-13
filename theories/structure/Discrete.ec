(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Ring StdRing StdOrder List.
(*---*) import IntID IntOrder.

pragma -oldip.

(* -------------------------------------------------------------------- *)
pred enumerate ['a] (C : int -> 'a option) (E : 'a -> bool) =
     (forall i j x, C i = Some x => C j = Some x => i = j)
  /\ (forall x, E x => exists i, 0 <= i /\ C i = Some x).

(* -------------------------------------------------------------------- *)
lemma eq_enumerate ['a] E1 E2 (C : int -> 'a option) :
  (forall x, E1 x = E2 x) => enumerate C E1 => enumerate C E2.
proof. by move/fun_ext=> ->. qed.

(* -------------------------------------------------------------------- *)
op countable ['a] (E : 'a -> bool) =
  exists (C : int -> 'a option),
    forall x, E x => exists i, C i = Some x.

(* -------------------------------------------------------------------- *)
lemma L (n1 p1 n2 p2 : int) :
     0 < n1 => 0 < p1
  => 0 < n2 => 0 < p2
  => exp 2 n1 * exp 3 p1 = exp 2 n2 * exp 3 p2
  => n1 = n2 /\ p1 = p2.
proof.
move=> gt0_n1 gt0_p1 gt0_n2 gt0_p2; case: (n1 = n2) => /= [<-|neq_n].
(* FIXME: move/ieexprIn fails *)
+ have h/h{h} := mulfI (exp 2 n1) _; 1: by rewrite expf_eq0 //.
  by have h := ieexprIn 3 _ _ p1 p2 _ _ => //; apply/ltzW.
pose x1 := exp 3 p1; pose x2 := exp 3 p2.
have {gt0_p1 gt0_p2} [o1 o2] : odd x1 /\ odd x2 by rewrite !oddX // odd3.
(* FIXME: wlog *)
(* FIXME: display of pose is not well indented *)
pose P n1 n2 x1 x2 :=
     0 < n1 => 0 < n2 => n1 <> n2 => odd x1 => odd x2
  => exp 2 n1 * x1 <> exp 2 n2 * x2.
move: x1 x2 gt0_n1 gt0_n2 neq_n o1 o2.
move=> {p1 p2} x1 x2; rewrite -/(P n1 n2 x1 x2).
have: (forall n1 n2 x1 x2, (n1 <= n2)%Int => P n1 n2 x1 x2) => P n1 n2 x1 x2.
+ move=> ih; case: (lez_total n1 n2); first by move/ih; apply.
  by move=> h @/P *; rewrite eq_sym &(ih) 1?eq_sym.
apply=> {n1 n2 x1 x2} n1 n2 x1 x2 le_n gt0_n1 gt0_n2 neq_n o1 o2.
have lt_n: n1 < n2 by rewrite ltr_neqAle le_n.
rewrite (_ : n2 = n1 + (n2 - n1)) 1:#ring exprD ?subr_ge0 1?ltrW //.
apply/negP; rewrite -mulrA; have h/h := mulfI (exp 2 n1) _.
+ by rewrite expf_eq0.
by move/(congr1 odd); rewrite oddM oddX ?subr_gt0 // odd2 !(o1, o2).
qed.

(* -------------------------------------------------------------------- *)
op cunion (C1 C2 : int -> 'a option) : (int -> 'a option).

(* -------------------------------------------------------------------- *)
axiom cunion_enum (C1 C2 : int -> 'a option) E1 E2 :
  enumerate C1 E1 => enumerate C2 E2 =>
    enumerate (cunion C1 C2) (predU E1 E2).

(* -------------------------------------------------------------------- *)
op cunions (Cs : (int -> 'a option) list) =
  foldr cunion (fun x => None) Cs.

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
op enumerate ['a] (C : int -> 'a option) (E : 'a -> bool) =
     (forall i j x, C i = Some x => C j = Some x => i = j)
  /\ (forall x, E x => exists i, 0 <= i /\ C i = Some x).

(* -------------------------------------------------------------------- *)
op cenum ['a] (p : 'a -> bool) =
  choiceb (fun f => enumerate f p) (fun _ => None).

(* -------------------------------------------------------------------- *)
lemma nosmt eq_enumerate ['a] E1 E2 (C : int -> 'a option) :
  (forall x, E1 x = E2 x) => enumerate C E1 => enumerate C E2.
proof. by move/fun_ext=> ->. qed.

(* -------------------------------------------------------------------- *)
op countable ['a] (E : 'a -> bool) =
  exists (C : int -> 'a option),
    forall x, E x => exists i, C i = Some x.

abbrev countableT ['a] = countable predT<:'a>.

(* -------------------------------------------------------------------- *)
op int2nat (i : int) : int =
  if 0 <= i then 2 * i else -2 * i + 1.

lemma inj_int2nat : injective int2nat.
proof.
move=> x y @/int2nat; case: (0 <= y); case: (0 <= x) => hx hy.
+ by apply: mulfI.
+ by move/(congr1 odd); rewrite oddS oddN !oddM odd2.
+ by move/(congr1 odd); rewrite oddS oddN !oddM odd2.
+ by move/addIr; rewrite -!mulNr &(mulfI) oppr_eq0.
qed.

lemma ge0_int2nat x : 0 <= int2nat x by smt().

(* -------------------------------------------------------------------- *)
lemma cnt_int : countableT<:int>.
proof. by exists (fun i => Some i) => i _; exists i. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt countableP ['a] (E : 'a -> bool) :
  (exists f, enumerate f E) <=> countable E.
proof.
split; case=> C => [[h1 h2]|h].
+ by exists C => x /h2 [i] [_ <-]; exists i.
pose P i x := exists j, i = int2nat j /\ C j = Some x.
pose Q i x := P i x /\ i = minz (transpose P x).
pose R i x := odflt false (omap (Q i) x).
pose f i   := choiceb (R i) None.
have eqR: forall i x1 x2, R i x1 => R i x2 => x1 = x2.
+ move=> i [|x1] [|x2] @/R //= [+ _] [+ _] -[j1 [-> h1]] [j2 [+ h2]].
  by move/inj_int2nat=> <<-; move: h1 h2 => ->.
have fQ: forall k x, f k = Some x => Q k x.
+ move=> k x; case: (exists x0, R k x0); last first.
  - by rewrite negb_exists /= => /choiceb_dfl @/f ->.
  move/(choicebP _ None); rewrite -/(f _) /= => + fkE.
  by rewrite fkE /R.
exists f; split=> [i j x fiE fjE|x /h {h} [i hi]].
+ by move/fQ: fjE; move/fQ: fiE => [h1 ->] [h2 ->].
exists (minz (transpose P x)); rewrite ge0_argmin /=.
have hP: P (minz (transpose P x)) x.
+ apply/(@argminP idfun (transpose P x) (int2nat i)) => @/idfun /=.
  * by apply/ge0_int2nat. * by exists i.
have hR: R (minz (transpose P x)) (Some x) by done.
have h: exists x', R (minz (transpose P x)) x' by exists (Some x).
have /= {h} := choicebP _ None h; rewrite -/(f _) => h.
by move: h hR; apply/eqR.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt countable_inj ['a] (p : 'a -> bool) :
  countable p => exists (f : 'a -> int), (* FIXME: (...) should not be mandatory *)
    forall x y, p x => p y => f x = f y => x = y.
proof.
case=> C hC; exists (fun x => choiceb (fun i => C i = Some x) 0) => /=.
move=> x y px py; have hx := hC x px; have hy := hC y py => {hC px py} h.
have /= := choicebP _ 0 hy; have /= := choicebP _ 0 hx => {hx hy}.
by rewrite -h => ->.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt inj_cond_countable ['a 'b] (f : 'a -> 'b) pb pa :
     countable<:'b> pb
  => (forall x y, pa x => pa y => f x = f y => x = y)
  => (forall x, pa x => pb (f x))
  => countable<:'a> pa.
proof.
case/countable_inj=> [C hC] inj_fp okf.
pose P i x := pa x /\ C (f x) = i.
exists (fun i => Some (choiceb (P i) witness)) => /=.
move=> x pax; have h: exists i, P (C (f x)) i by exists x.
exists (C (f x)); case/(choicebP (P (C (f x))) witness): h.
move=> hpa; have h1 := okf _ pax; have h2 := okf _ hpa.
by move/(hC _ _ h2 h1)/(inj_fp _ _ hpa pax).
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt inj_condL_countable ['a 'b] (f : 'a -> 'b) p :
     countableT<:'b>
  => (forall x y, p x => p y => f x = f y => x = y)
  => countable<:'a> p.
proof. by apply/inj_cond_countable. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt inj_countable ['a] (f : 'a -> int) (p : 'a -> bool) :
     (forall x y, p x => p y => f x = f y => x = y)
  => countable p.
proof. by apply/inj_condL_countable/cnt_int. qed.

(* -------------------------------------------------------------------- *)
theory IntPair.
  lemma FTA23 (n1 p1 n2 p2 : int) :
       0 <= n1 => 0 <= p1
    => 0 <= n2 => 0 <= p2
    => exp 2 n1 * exp 3 p1 = exp 2 n2 * exp 3 p2
    => n1 = n2 /\ p1 = p2.
  proof.
  move=> ge0_n1 ge0_p1 ge0_n2 ge0_p2; case: (n1 = n2) => /= [<-|neq_n].
  (* FIXME: move/ieexprIn fails *)
  + have h/h{h} := mulfI (exp 2 n1) _; 1: by rewrite expf_eq0 //.
    by have h := ieexprIn 3 _ _ p1 p2 _ _ => //; apply/ltzW.
  pose x1 := exp 3 p1; pose x2 := exp 3 p2.
  have {ge0_p1 ge0_p2} [o1 o2] : odd x1 /\ odd x2 by rewrite !oddX // odd3.
  (* FIXME: wlog *)
  (* FIXME: display of pose is not well indented *)
  pose P n1 n2 x1 x2 :=
       0 <= n1 => 0 <= n2 => n1 <> n2 => odd x1 => odd x2
    => exp 2 n1 * x1 <> exp 2 n2 * x2.
  move: x1 x2 ge0_n1 ge0_n2 neq_n o1 o2.
  move=> {p1 p2} x1 x2; rewrite -/(P n1 n2 x1 x2).
  have: (forall n1 n2 x1 x2, (n1 <= n2)%Int => P n1 n2 x1 x2) => P n1 n2 x1 x2.
  + move=> ih; case: (lez_total n1 n2); first by move/ih; apply.
    by move=> h @/P *; rewrite eq_sym &(ih) 1?eq_sym.
  apply=> {n1 n2 x1 x2} n1 n2 x1 x2 le_n ge0_n1 ge0_n2 neq_n o1 o2.
  have lt_n: n1 < n2 by rewrite ltr_neqAle le_n.
  rewrite (_ : n2 = n1 + (n2 - n1)) 1:#ring exprD ?subr_ge0 //.
  apply/negP; rewrite -mulrA; have h/h := mulfI (exp 2 n1) _.
  + by rewrite expf_eq0.
  by move/(congr1 odd); rewrite oddM poddX ?subr_gt0 // odd2 !(o1, o2).
  qed.

  op encode (xy : int * int) =
    exp 2 (int2nat xy.`1) * exp 3 (int2nat xy.`2).

  lemma inj_encode : injective encode.
  proof.
  case=> [x1 y1] [x2 y2] @/encode /=; rewrite andabP.
  rewrite -(inj_eq _ inj_int2nat x1) -(inj_eq _ inj_int2nat y1).
  by apply/FTA23; apply/ge0_int2nat.
  qed.

  lemma countable : countableT<:int * int>.
  (* FIXME: type argument of countableT not shown *)
  proof.
  by apply/(@inj_countable encode)=> xy1 xy2 _ _; apply/inj_encode.
  qed.
end IntPair.

(* -------------------------------------------------------------------- *)
theory IntTuple.
  op encode (s : int list) =
    with s = []     => 0
    with s = x :: s => IntPair.encode (x, encode s).

  lemma inj_encode s1 s2 :
    size s1 = size s2 => encode s1 = encode s2 => s1 = s2.
  proof.
  elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //=; try by rewrite addz_neq0 ?size_ge0.
  by move/addzI => /ih {ih}ih /IntPair.inj_encode [-> /ih ->].
  qed.

  lemma countable n : countable<:int list> (fun s => size s = n).
  proof.
  by apply/(@inj_countable encode) => /= s1 s2 <- /eq_sym; apply/inj_encode.
  qed.
end IntTuple.

(* -------------------------------------------------------------------- *)
theory IntList.
  op encode (s : int list) =
    IntPair.encode (size s, IntTuple.encode s).

  lemma inj_encode : injective encode.
  proof.
  (* FIXME: unfolding encode should not be necessary *)
  (* FIXME: unfolding encode should not unfold IntPair.encode *)
  move=> s1 s2 @/IntList.encode /IntPair.inj_encode [].
  by apply/IntTuple.inj_encode.
  qed.

  lemma countable : countableT<:int list>.
  proof.
  by apply/(@inj_countable encode)=> s1 s2 _ _; apply/inj_encode.
  qed.
end IntList.

(* -------------------------------------------------------------------- *)
lemma cnt_unit p : countable<:unit> p.
proof. by apply/(@inj_countable (fun _ => 0)). qed.

(* -------------------------------------------------------------------- *)
lemma cnt_bool p : countable<:bool> p.
proof. by apply/(@inj_countable b2i) => -[] -[]. qed.

(* -------------------------------------------------------------------- *)
lemma cnt_prod_cond ['a 'b] pa pb :
     countable<:'a> pa
  => countable <:'b> pb
  => countable (fun (xy : _ * _) => pa xy.`1 /\ pb xy.`2).
proof.
case/countable_inj=> CA hA; case/countable_inj=> CB hB.
pose f (xy : _ * _) := (CA xy.`1, CB xy.`2).
apply/(@inj_condL_countable f) => /=; 1: by apply/IntPair.countable.
case=> [x1 x2] [y1 y2] /= [hax hbx] [hay hby] [] /= hx hy.
by rewrite (hA _ _ hax hay) // (hB _ _ hbx hby).
qed.

(* -------------------------------------------------------------------- *)
lemma cnt_prod ['a 'b] :
  countableT<:'a> => countableT<:'b> => countableT<:'a * 'b>.
proof. by apply/cnt_prod_cond. qed.

(* -------------------------------------------------------------------- *)
lemma cnt_list_cond ['a] (p : 'a -> bool) :
  countable p => countable (all p).
proof.
case/countable_inj=> C h; pose f s := map C s.
apply/(@inj_condL_countable f); 1: by apply/IntList.countable.
by apply/in_inj_map.
qed.

(* -------------------------------------------------------------------- *)
lemma cnt_list ['a] : countableT<:'a> => countableT<:'a list>.
proof.
move/cnt_list_cond; suff ->//: all predT<:'a> = predT.
by apply/fun_ext=> s; rewrite all_predT.
qed.

(* -------------------------------------------------------------------- *)
lemma cnt_option ['a] : countableT<:'a> => countableT<:'a option>.
proof.
move=> h; pose f x := odflt [] (omap (fun y => [<:'a> y]) x).
by apply(@inj_condL_countable f) => [|[|x] [|y]] //; apply/cnt_list.
qed.

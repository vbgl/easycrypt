(* -------------------------------------------------------------------- *)
require import Option Bool Fun ExtEq Finite Int IntExtra List.
require (*--*) Monoid Ring Subtype.

pragma -oldip.

(* -------------------------------------------------------------------- *)
abstract theory MonAlg.
type M, R.

clone import Monoid as ZM with type t <- M.
clone import Ring.IDomain as ZR with type t <- R.

clear [ZR.* ZR.AddMonoid.* ZR.MulMonoid.*].

(* -------------------------------------------------------------------- *)
type monalg.

pred qnull (C : M -> R) = is_finite (fun x => C x <> zeror).

lemma qnullP (C : M -> R) : qnull C <=>
  (exists s, forall x, C x <> zeror => x \in s).
proof.                          (* FIXME: move to Finite *)
split=> [qC|]; pose F := fun x => C x <> zeror.
+ by exists (Finite.to_seq F) => x nz_Cx; apply/Finite.mem_to_seq.
case=> s x_in_s; exists (undup (filter F s)).
rewrite undup_uniq /= => x; rewrite mem_undup mem_filter /F.
by rewrite -eq_iff; apply/andb_idr/x_in_s.
qed.

(* -------------------------------------------------------------------- *)
clone Subtype as Supp with
  type T <- (M -> R), type sT <- monalg, pred P C <- qnull C.

(* -------------------------------------------------------------------- *)
op monalg0 = Supp.insubd (fun _ => zeror).

op mkmonalg (C : M -> R) = odflt monalg0 (Supp.insub C).
op mcoeff (m : monalg) = Supp.val m.

(* -------------------------------------------------------------------- *)
lemma monalg_eqE m1 m2 : (m1 = m2) <=>
  (forall x, mcoeff m1 x = mcoeff m2 x).
proof.
split=> [->//|eq]; apply/Supp.val_inj.
by apply/ExtEq.fun_ext=> x; rewrite eq.
qed.

(* -------------------------------------------------------------------- *)
op support (m : monalg) = Finite.to_seq (fun x => mcoeff m x <> zeror).

lemma supportP (m : monalg) z : z \in support m <=> mcoeff m z <> zeror.
proof. by apply/mem_to_seq/Supp.valP. qed.

lemma supportPn (m : monalg) z : !(z \in support m) <=> mcoeff m z = zeror.
proof. by rewrite -iff_negb /= supportP. qed.

(* -------------------------------------------------------------------- *)
lemma mcoeff0 z : mcoeff monalg0 z = zeror.
proof. by rewrite Supp.insubdK //; exists []. qed.

hint rewrite mcoeff : mcoeff0.

(* -------------------------------------------------------------------- *)
lemma mcoeffE C z : qnull C => mcoeff (mkmonalg C) z = C z.
proof.
move=> qC; case: (Supp.insubP C) => // {qC} |> m.
by rewrite /mcoeff /mkmonalg => _ ->.
qed.

(* -------------------------------------------------------------------- *)
op [-] (m : monalg) = mkmonalg (fun x => - mcoeff m x).
op (+) (m1 m2 : monalg) = mkmonalg (fun x => mcoeff m1 x + mcoeff m2 x).

(* -------------------------------------------------------------------- *)
lemma moppE m x : mcoeff (- m) x = - mcoeff m x.
proof.
rewrite mcoeffE // qnullP; exists (support m) => /=.
by move=> {x}x; rewrite oppr_eq0 => /supportP.
qed.

hint rewrite mcoeff : moppE.

(* -------------------------------------------------------------------- *)
lemma maddE m1 m2 x : mcoeff (m1 + m2) x = mcoeff m1 x + mcoeff m2 x.
proof.
rewrite mcoeffE // qnullP; exists (support m1 ++ support m2) => /=.
move=> {x}x; apply/absurd=> /=; rewrite mem_cat -nor; case.
by move=> /supportPn-> /supportPn->; rewrite addr0.
qed.

hint rewrite mcoeff : maddE.

(* -------------------------------------------------------------------- *)
clone Ring.ZModule as MAZM with
  type t     <- monalg,
    op zeror <- monalg0,
    op [-]   <- ([-]),
    op (+)   <- (+)
  proof *.

realize addrA.
proof. by move=> m n p; apply/monalg_eqE=> x; rewrite !mcoeff addrA. qed.

realize addrC.
proof. by move=> m p; apply/monalg_eqE=> x; rewrite !mcoeff addrC. qed.

realize add0r.
proof. by move=> m; apply/monalg_eqE=> x; rewrite !mcoeff add0r. qed.

realize addNr.
proof. by move=> m; apply/monalg_eqE=> x; rewrite !mcoeff addNr. qed.
end MonAlg.

(* -------------------------------------------------------------------- *)
abstract theory MPoly.
type vars, monom.

(* -------------------------------------------------------------------- *)
pred qmonom (M : vars -> int) =
  (forall x, 0 <= M x) /\ is_finite (fun x => M x <> 0).

(* -------------------------------------------------------------------- *)
lemma qmonomP (M : vars -> int) : qmonom M <=>
  (forall i, 0 <= M i) /\ (exists s, forall i, M i <> 0 => i \in s).
proof.                          (* FIXME: move to Finite *)
split=> [[pM qM]|]; pose F := fun i => M i <> 0.
+ split=> [i|]; first by rewrite pM.
  by exists (Finite.to_seq F) => x nz_Mx; apply/Finite.mem_to_seq.
case=> pM [s x_in_s]; split=> //; exists (undup (filter F s)).
rewrite undup_uniq /= => x; rewrite mem_undup mem_filter /F.
by rewrite -eq_iff; apply/andb_idr/x_in_s.
qed.

(* -------------------------------------------------------------------- *)
clone Subtype as Monom with
  type T <- (vars -> int), type sT <- monom, pred P M <- qmonom M.

(* -------------------------------------------------------------------- *)
op monom1 = Monom.insubd (fun _ => 0).

op mkmonom (M : vars -> int) = odflt monom1 (Monom.insub M).
op mpow (M : monom) i = Monom.val M i.

lemma mpow_ge0 (M : monom) i : 0 <= mpow M i.
proof. by have [] := Monom.valP M => + _; apply. qed.

lemma mpow_fin (M : monom) : is_finite (fun i => mpow M i <> 0).
proof. by have [] := Monom.valP M. qed.

hint exact : mpow_ge0 mpow_fin.

(* -------------------------------------------------------------------- *)
lemma mpow1 i : mpow monom1 i = 0.
proof. by rewrite Monom.insubdK //; exists []. qed.

hint rewrite mpow : mpow1.

(* -------------------------------------------------------------------- *)
lemma mpowE M i : qmonom M => mpow (mkmonom M) i = M i.
proof.
move=> qM; case: (Monom.insubP M) => // {qM} |> m.
by rewrite /mpow /mkmonom => _ ->.
qed.

(* -------------------------------------------------------------------- *)
op ( ** ) (M1 M2 : monom) =
  mkmonom (fun i => mpow M1 i + mpow M2 i).

lemma mpowM (M1 M2 : monom) i :
  mpow (M1 ** M2) i = mpow M1 i + mpow M2 i.
proof.
rewrite mpowE // qmonomP => /=; split=> [{i} i|].
+ by rewrite addz_ge0.
pose s1 := Finite.to_seq (fun x => mpow M1 x <> 0).
pose s2 := Finite.to_seq (fun x => mpow M2 x <> 0).
exists (s1 ++ s2) => {i}i; apply/absurd=> /=; rewrite mem_cat -nor.
by rewrite !mem_to_seq //=; case=> -> ->.
qed.

hint rewrite mpow : mpowM.

(* -------------------------------------------------------------------- *)
lemma monom_eqE M1 M2 : (M1 = M2) <=>
  (forall x, mpow M1 x = mpow M2 x).
proof.
split=> [->//|eq]; apply/Monom.val_inj.
by apply/ExtEq.fun_ext=> x; rewrite eq.
qed.

(* -------------------------------------------------------------------- *)
clone Monoid as MonomMonoid with
  type t   <- monom,
    op idm <- monom1,
    op (+) <- ( ** )
  proof *.

realize Axioms.addmA.
proof. by move=> M N P; apply/monom_eqE=> x; rewrite !mpow addzA. qed.

realize Axioms.addmC.
proof. by move=> M N; apply/monom_eqE=> x; rewrite !mpow addzC. qed.

realize Axioms.add0m.
proof. by move=> M; apply/monom_eqE=> x; rewrite !mpow. qed.

clear [MonomMonoid.Axioms.*].   (* FIXME: do not work?! *)

(* -------------------------------------------------------------------- *)
type mpoly.

clone include MonAlg with
  type   M      <- monom,
  type   monalg <- mpoly,
    op   ZM.idm <- monom1,
    op   ZM.(+) <- ( ** )
  rename "monalg" as "mpoly"
  proof   ZM.Axioms.*.

realize ZM.Axioms.addmA by exact MonomMonoid.addmA.
realize ZM.Axioms.addmC by exact MonomMonoid.addmC.
realize ZM.Axioms.add0m by exact MonomMonoid.add0m.
end MPoly.

print MPoly.

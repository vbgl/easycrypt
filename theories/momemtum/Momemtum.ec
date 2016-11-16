(* -------------------------------------------------------------------- *)
require import Int IntExtra Real RealExtra List.
require export Fun FunExt.

op path ['a] (e : 'a -> 'a -> bool) x p =
  with p = [] => true
  with p = y :: p' => e x y /\ path e y p'.

op pathn ['a] (e : 'a -> 'a -> bool) n x y =
  exists s, size s = n /\ path e x s /\ last x s = y.

op dclosure ['a] (e : 'a -> 'a -> bool) x y =
  exists n, pathn e n x y.

op dpath ['a] (e : 'a -> 'a -> bool) x y =
  choiceb (fun n =>
    pathn e n x y /\ forall k, k < n => !pathn e n x y)
    (-1).

(* -------------------------------------------------------------------- *)
inductive affine (f : real -> real) =
| Affine a b of (0%r <= a) & (0%r <= b) & (forall x, f x = a*x + b).
      
inductive linear (f : real -> real) =
| Linear a of (0%r <= a) & (forall x, f x = a*x).

lemma linear_affine f : linear f => affine f.
proof. by case=> a ge0_a eqf; apply/(Affine _ a 0%r). qed.

lemma idfun_affine : affine idfun.
proof. by apply/(Affine _ 1%r 0%r). qed.

lemma comp_affine f1 f2 :
  affine f1 => affine f2 => affine (f1 \o f2).
proof.
case=> [a1 b1 ge0_a1 ge0_b1 Heq1] [a2 b2 ge0_a2 geo_b2 Heq2].
by apply/(Affine _ (a1 * a2) (a1 * b2 + b1)) => /#.
qed.
  
lemma bigo_affine f N:
 (forall n, 0 <= n < N => affine (f n)) => affine (bigo N f).
proof.
elim/natind: N.
+ by move=> n Hn Hf; rewrite bigo0 ?idfun_affine.
by move=> n Hn Hrec Hf; rewrite bigoS ?comp_affine=> /#.
qed.

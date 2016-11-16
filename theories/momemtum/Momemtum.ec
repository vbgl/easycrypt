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
pred affine (f : real -> real) = 
   exists a b, forall x, f x = a*x + b.
      
pred linear : (real -> real).

lemma idfun_affine : affine idfun.
proof. by exists 1%r 0%r. qed.

lemma comp_affine (f1 f2:real -> real) :
  affine f1 => affine f2 => affine (f1 \o f2).
proof.
  move=> [a1 b1 Heq1] [a2 b2 Heq2].
  exists (a1 * a2) (a1 * b2 + b1) => /#.
qed.
  
lemma bigo_affine f N:
 (forall n, 0 <= n < N => affine (f n)) => affine (bigo N f).
proof.
elim/natind: N.
+ by move=> n Hn Hf; rewrite bigo0 ?idfun_affine.
by move=> n Hn Hrec Hf; rewrite bigoS ?comp_affine=> /#.
qed.


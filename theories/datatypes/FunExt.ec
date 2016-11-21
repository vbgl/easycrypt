(* -------------------------------------------------------------------- *)
require import Int IntExtra Fun List.

(* -------------------------------------------------------------------- *)
op bigo n (f : int -> real -> real) =
  foldr (fun n f1 => f n \o f1) idfun (range 0 n).

lemma bigo0 N f : N <= 0 => bigo N f = idfun.
proof. by move=> HN;rewrite /bigo range_geq. qed.

lemma bigo_comp N f1 (f2 : real -> real) :
  bigo N f1 \o f2 = foldr (fun n f2 => f1 n \o f2) f2 (range 0 N).
proof.
rewrite /bigo; have ->//: forall f3, 
    foldr
       (fun (n : int) (f2 : real -> real) => f1 n \o f2) f3
       (range 0 N) \o f2
  = foldr (fun (n : int) (f2: real -> real) => f1 n \o f2) (f3 \o f2) (range 0 N).
elim/natind: N f2 => [n Hn | n Hn Hrec].
+ by move=> f2 idfun;rewrite range_geq.
by move=> f2 f3; rewrite rangeSr // -cats1 !foldr_cat /= Hrec.
qed.

lemma bigoS N f : 0 <= N => bigo (N + 1) f = bigo N f \o f N.
proof.
by move=> HN;rewrite /bigo rangeSr // -cats1 foldr_cat /= bigo_comp.
qed.

(* -------------------------------------------------------------------- *)
require import AllCore List Real.

(* -------------------------------------------------------------------- *)
op bigo n (f : int -> real -> real) =
  foldr (fun n f1 => f n \o f1) idfun (range 0 n).

lemma bigo0 n f : n <= 0 => bigo n f = idfun.
proof. by move=> le0_n;rewrite /bigo range_geq. qed.

lemma bigo_comp n f1 (f2 : real -> real) :
  bigo n f1 \o f2 = foldr (fun n f2 => f1 n \o f2) f2 (range 0 n).
proof.
rewrite /bigo; have ->//: forall f3, 
    foldr
       (fun (n : int) (f2 : real -> real) => f1 n \o f2) f3
       (range 0 n) \o f2
  = foldr (fun (n : int) (f2: real -> real) => f1 n \o f2) (f3 \o f2) (range 0 n).
elim/natind: n f2 => [n ge0_n | n ge0_n ih].
+ by move=> f2 idfun; rewrite range_geq.
+ by move=> f2 f3; rewrite rangeSr // -cats1 !foldr_cat /= ih.
qed.

lemma bigoS n f : 0 <= n => bigo (n + 1) f = bigo n f \o f n.
proof.
by move=> ge0_n; rewrite /bigo rangeSr // -cats1 foldr_cat /= bigo_comp.
qed.

lemma bigo_id n : bigo n (fun k => idfun) = idfun.
proof. by elim/natind: n => n ih; [rewrite bigo0 | rewrite bigoS]. qed.

lemma bigo_iter_shift (n : int) (x c : real) : 0 <= n =>
  bigo n (fun k x => x + c) = (fun x => x + n%r * c).
proof.
move=> ge0_n; apply/fun_ext => y; elim/intind: n ge0_n y => /=.
+ by move=> y; rewrite bigo0.
by move=> i ge0_i ih y; rewrite bigoS /(\o) //= ih /#.
qed.

require import Real.
require export Distr.

(* ----------------------------------------------------------------- *)

pred positive (f:'a -> real) = forall x, 0%r <= f x.

lemma add_positive (f1 f2:'a -> real) :
   positive f1 => positive f2 => positive (fun x => f1 x + f2 x)
by [].

lemma mul_positive (f1 f2:'a -> real) :
   positive f1 => positive f2 => positive (fun x => f1 x * f2 x)
by [].

(* ----------------------------------------------------------------- *)

lemma b2r_positive (f:'a -> bool): positive (fun x => b2r (f x))
by [].

lemma b2r_true : b2r true = 1%r
by [].

lemma b2r_1 (b:bool): b2r b = 1%r <=> b
by [].

lemma b2r_false : b2r false = 0%r
by [].

lemma b2r_0 (b:bool): b2r b = 0%r <=> !b 
by [].

lemma b2r_not (b:bool): b2r (!b) = 1%r - b2r b
by [].

lemma b2r_and (b1 b2: bool): b2r(b1 /\ b2) = b2r b1 * b2r b2
by [].

lemma b2r_or (b1 b2:bool): 
    b2r (b1 \/ b2) = b2r b1 + b2r b2 - b2r b1 * b2r b2
by [].

lemma b2r_if b1 b2 b3 : b2r (if b1 then b2 else b3) = b2r b1 * b2r b2 + b2r (!b1) * b2r b3
by [].

lemma b2r_imp b1 b2 : b2r (b1 => b2) = 1%r - b2r b1 + b2r b1 * b2r b2
by [].

lemma nosmt absurd_and_n (b:bool) : !(b /\ !b)
by [].

lemma add_b2r_pn b : b2r b + b2r (!b) = 1%r
by [].

lemma add_b2r_np (b:bool) : b2r (!b) + b2r b = 1%r
by [].

(* ---------------------------------------------------------------------------- *)
(* FIXME this should be the definition                                          *)

axiom nosmt muf_le_compat (f1 f2:'a -> real) (d:'a distr) :
  (forall x, in_supp x d => f1 x <= f2 x) =>
  $[f1 | d] <= $[f2 | d].

(* TODO mu should be defined in term of muf *)
axiom muf_b2r (P: 'a -> bool) (d:'a distr) : 
  mu d P = $[fun a => b2r (P a) | d].

(* FIXME: need to add restriction on f1 f2 *)
axiom muf_add (f1 f2:'a -> real) (d:'a distr):
  $[fun x => f1 x + f2 x | d] = 
  $[f1 | d] + $[f2 | d].

axiom muf_opp (f : 'a -> real) (d:'a distr):
  $[ fun x => -(f x) | d] = - $[f | d].

axiom muf_mulc_l (c:real) (f:'a -> real) (d:'a distr):
  $[fun x => c * f x | d] = c * $[f | d].

(* TODO this seem provable *)
axiom nosmt muf_pos_0 (d :'a distr) (f:'a -> real) : 
  positive f => 
  $[ f | d] = 0%r <=> (forall x, in_supp x d => f x = 0%r).

(* ------------------------------------------------------------------------- *)

lemma nosmt muf_eq_compat (f1 f2:'a -> real) (d:'a distr) :
  (forall x, in_supp x d => f1 x = f2 x) =>
  $[f1 | d] = $[f2 | d].
proof.
  move=> Hf; cut := muf_le_compat <:'a>;smt.
qed.

lemma muf_congr (f1 f2: 'a -> real) (d1 d2:'a distr): 
  d1 = d2 =>
  (forall a, f1 a = f2 a) =>
  $[f1 | d1] = $[f2 | d2].
proof. by move=> -> Hf;congr; rewrite -fun_ext. qed.

lemma muf_sub (f1 f2:'a -> real) (d:'a distr):
  $[fun x => f1 x - (f2 x) | d] = $[f1 | d] - $[f2 | d].
proof.
  cut -> : $[f1 | d] - $[f2 | d] = $[f1 | d] + - $[f2 | d] by ringeq.
  rewrite -muf_opp -muf_add;apply muf_congr => //= x;ringeq.
qed.

lemma muf_mulc_r (c:real) (f:'a -> real) (d:'a distr):
  $[fun x => f x * c | d] = $[f | d] * c.
proof.
  rewrite (Real.Comm.Comm (muf f d)) -muf_mulc_l;apply muf_congr => //= x;ringeq.
qed.

lemma muf_c (c:real) (d:'a distr) : 
   $[fun x => c | d] = c * $[fun x => 1%r | d].
proof. by rewrite -muf_mulc_l. qed.

lemma muf_c_ll (c:real) (d:'a distr) : 
  $[fun x => 1%r | d] = 1%r => 
  $[fun x => c | d] = c.
proof. by move=> Hll;rewrite muf_c Hll. qed.

lemma muf_0 (d:'a distr) :
  $[fun x => 0%r | d] = 0%r.
proof. by rewrite muf_c. qed.

lemma muf_positive (f:'a -> 'b -> real) (d:'a -> 'b distr): 
   (forall (x:'a), positive (f x)) =>
   positive (fun (x:'a) => $[ f x | d x]).
proof.
  move=> Hf x. 
  rewrite - (muf_0 (d x)); apply muf_le_compat => /= b _; apply Hf.
qed.

lemma muf_0_f0 (f:'a -> real) (d: 'a distr):
   (forall a, in_supp a d => f a = 0%r) => $[f | d] = 0%r.
proof.
  move=> Hf;rewrite -(muf_c 0%r d);apply muf_eq_compat;apply Hf.
qed.

(* ----------------------------------------------------------------- *)

lemma square_supp (p:'a -> bool) (d :'a distr): 
  $@[p | d] <=> (forall x, in_supp x d => p x).
proof. by rewrite muf_pos_0 1:smt /= b2r_0. qed.

lemma nosmt square_and (d :'a distr) (p1 p2:'a -> bool) : 
  ($@[p1 | d] /\ $@[p2 | d]) <=> $@[fun x => p1 x /\ p2 x | d].
proof. rewrite !square_supp /=;smt. qed.

lemma nosmt square_muf_add (p:'a -> bool) (f:'a -> real) (d: 'a distr):
  $@[p | d] =>
  $[ f | d] = $[fun x => f x + b2r (!p x) | d].
proof.
  rewrite square_supp=> Hp.
  apply muf_eq_compat=> /= x Hx;rewrite (Hp _ Hx) //.
qed.

lemma nosmt square_muf_mul (p:'a -> bool) (f:'a -> real)  (d: 'a distr):
  $@[p | d] =>
  $[ f | d] = $[fun x => b2r (p x) * f x | d].
proof.
  rewrite square_supp=> Hp.
  apply muf_eq_compat=> /= x Hx;rewrite (Hp _ Hx) //.
qed.

lemma nosmt square_muf_mul_add (p:'a -> bool) (f:'a -> real)  (d: 'a distr):
  $@[p | d] =>
  $[ f | d] = $[fun x => b2r (p x) * f x + b2r (!p x)| d].
proof.
  move=> Hp; rewrite (square_muf_mul p) // (square_muf_add p) //.
qed.


(* Lemmas about known distribution *)
require import Bool.

axiom muf_dbool (f:bool -> real): 
  $[f | {0,1} ] = 1%r/2%r * f true + 1%r/2%r * f false.

lemma dbool_ll: $[fun x=> 1%r | {0,1} ] = 1%r.
proof. by rewrite muf_dbool. qed.

lemma muf_c_dbool : forall c, $[fun x => c | {0,1}] = c.
proof. by rewrite muf_c dbool_ll. qed.

(* -------------------------------------------------------------- *)

op drestr : 'a distr -> ('a -> bool) -> 'a distr.

axiom drestr_def (d:'a distr) p f: 
   $[f | drestr d p] = $[fun x => b2r (p x) * f x | d].

(* --------------------------------------------------------------- *)

op dscale : 'a distr -> 'a distr. 

axiom dscale_def (d:'a distr) f: 
   $[f | dscale d] = $[f | d] / $[fun x => 1%r | d].

(* --------------------------------------------------------------- *)
op (||) (d:'a distr) (p:'a -> bool) = dscale (drestr d p).
(* remark: $[fun x => br2 a | d || b] is Pr_d[a | b] ie Pr_d[a /\ b]/ Pr_d[b] *)

lemma dsrestr_def (d:'a distr) (p:'a -> bool) (f:'a -> real): 
    $[f | d || p] = 
       $[fun (x : 'a) => b2r (p x) * f x | d] / 
       $[fun (x : 'a) => b2r (p x) | d].
proof. rewrite /(||) dscale_def !drestr_def //. qed.

lemma dsrestr_ll (d:'a distr) (p:'a -> bool): 
    $[fun x => 1%r | d] = 1%r =>
    (exists a, in_supp a d /\ p a) => 
    $[fun x => 1%r | d || p] = 1%r.
proof.
  move=> Hll Hex.
  rewrite /(||) dscale_def drestr_def /=.    
  cut : $[fun (x : 'a) => b2r (p x) | d] <> 0%r;last by smt.
  elim Hex=> a [Hin Hp].
  cut : mu_x d a <= $[fun (x : 'a) => b2r (p x) | d]; last by smt.
  rewrite /mu_x muf_b2r;apply muf_le_compat=> /= x Hxin; smt.
qed.


(* Notation:
   $[f | d]      := muf f d
   $[@ p | d]    := mu p d := muf (fun x => b2r (p x)) d 
   #[ p | d ]    := mu p d = 0 *)


 




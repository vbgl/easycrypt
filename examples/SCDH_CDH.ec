require import Int.
require import Real.
require import FSet.
require import Option.

require import Prime_field.
require import Cyclic_group_prime.
require import Trapdoor.

print op DDH_2DDH.n.


(* This files formalizes the more efficient reduction from the *)
(* Set CDH problem to CDH based on Shoup's self-corrector. *)
(* The proof goes as follows: *)
(*  1- A reduction from Set CDH to (CDH  + Twin DDH oracle) *)
(*  2- A reduction from (CDH + Twin DDH oracle) to CDH  *)
(*  (this uses the trapdoor trick and it's formalized in Trapdoor.ec) *)

(* The proof of 1 is covered in this file and works by  *)
(* constructing an adversary against B (CDH  + Twin DDH oracle) using a  *)
(* Set CDH adversary A as follows *)

(*   B(gx gy) : group = { *)
(*     gx1 = gx *)
(*     gx2 = $dgroup; *)
(*     s1 = A.run(gx1, gy); *)
(*     s2 = A.run(gx2, gy); *)
(*     return (pick { z1 | z1 <- s1; z2 <- s2 && tddh(gx1, gx2, gy, z1 z2)}); *)
(*    } *)
   
(* clearly, the if cdh (gx1, gy) \in s1 /\ cdh (gx2, gy) \in s2 *)
(* then B wins.  *)
(* The probability of cdh (gx1, gy) \in s1 /\ cdh (gx2, gy) \in s2 is *)
(* Pr [Set_CDH : win] ^ 2. We then obtain *)

(* Pr [Set_CDH : win] ^ 2 <= Pr[CDH+TDDH : res] + 2%r/q%r *)

(* where q is the size of the group. The loss comes from eliminating *)
(* two cases in which two sampled values Zq are 0 (and things go *)
(* wrong). *)

(* From 2 we obtain  *)

(* Pr[CDH+TDDH : res] <= qO / q%r + Pr[CDH : res] *)

(* where qO is the amount of oracle calls.  *)
(* Putting everything together we obtain the following result *)
(* Pr [Set_CDH : win] ^ 2 <= Pr[CDH : res]  + ((n+1) ^ 2) / q + 2 / q *)
(* where q is the size of the group and n is the size of the Set_CDH set. *)

type group = Cyclic_group_prime.group.
type Zq = Prime_field.gf_q.

const dZq = Dgf_q.dgf_q.
const dgrp = Dgroup.dgroup.


axiom nosmt card_subset(X1 X2 : 'a FSet.set):
X1 < X2 => card X1 < card X2.

op cdh(x y : group) : group = x ^ log y. 
op ddh(x y z : group) = z = cdh x y.
op tddh(x1 x2 y z1 z2 : group) = ddh x1 y z1 /\ ddh x2 y z2.


(** Twin Diffie-Hellman problem *)
theory CDH_TDDH.
  const q2DDH : int.
  module type TDDH = {
    fun tddh(z1 z2 : group) : bool
  }.

  module type Adversary(O : TDDH) = {
    fun solve(gx1 gx2 gy:group) : group {* O.tddh}
  }.

  module CDH_TDDH (A:Adversary) = {
   var x1 : gf_q
   var x2 : gf_q
   var y : gf_q
   var c : int
   module O : TDDH = {
    fun tddh (z1 z2 : group) : bool ={
     var b : bool = false;
     if (c < q2DDH) {
      c = c + 1;
      b = tddh (g^x1) (g^x2) (g^y) z1 z2;
     }
     return (b);
    }
   }
   module AO = A(O)
    fun main() : bool = {
      var r : group;
      x1 = $dZq;
      y = $dZq;
      x2 = $dZq;
      c = 0;
      r = AO.solve(g ^ x1, g^x2, g ^ y);
      return (r = cdh (g^x1) (g^y) );
    }
  }.

end CDH_TDDH.

theory CDH.

  module type Adversary = {
    fun solve(gx gy : group) : group {*}
  }.

  module CDH (A:Adversary) = {
   fun main() : bool = {
   var r : group;
   var x, y : Zq;
    x = $dZq;
    y = $dZq;
    r = A.solve(g ^ x, g ^ y);
      return (r = cdh (g^x) (g^y) );
    }
  }.


end CDH.

print theory CDH_TDDH.
(** Set version of the Computational Diffie-Hellman problem *)

theory Set_CDH.

  const n : int.

  module type Adversary = {
    fun solve(gx:group, gy:group) : group set {*}
  }.

  module SCDH (B:Adversary) = {
    fun main() : bool = {
      var x, y : Zq;
      var s : group set;

      x = $dZq;
      y = $dZq;
      s = B.solve(g ^ x, g ^ y);
      return (mem (cdh (g ^ x) (g ^ y)) s /\ card s <= n);
    }
  }.

end Set_CDH.

clone CDH_TDDH as CDH_TDDH' with
op q2DDH <- (Set_CDH.n * Set_CDH.n) + 1.

clone DDH_2DDH as DDH_2DDH' with
op qO <- (Set_CDH.n)%Set_CDH * (Set_CDH.n)%Set_CDH + 1.


section.

declare module A : Set_CDH.Adversary {CDH_TDDH'.CDH_TDDH, DDH_2DDH'.M}.

axiom lossless : islossless A.solve.

local module G1 = {
 fun f() : bool = {
 var x, y : Zq;
 var r : group set;
  x = $dZq;
  y = $dZq;
  r = A.solve(g ^ x, g ^ y);
  return (mem (cdh (g ^ x) (g^ y)) r /\ card r <= Set_CDH.n);
 }
 
 fun main() : bool = {
  var b1 : bool;
  var b2 : bool;
  b1 = f();
  b2 = f();
  return (b1 /\ b2);
 }
}.

local lemma Pr1 &m0 &m1 :
  Pr[Set_CDH.SCDH(A).main() @ &m0 : res] = 
  Pr[G1.f() @ &m1 : res].
equiv_deno (_ : true ==> ={res}) => //.
by fun; call (_ : true); do 2! rnd; skip; progress.
save.

local lemma bd_h_f &m :
 bd_hoare [G1.f : true ==> res] =  Pr[Set_CDH.SCDH(A).main() @ &m : res].
proof.
by bypr => ? ?;  rewrite (Pr1 &m &m0).
save.

local lemma Pr2  &m:
  Pr[G1.main() @ &m : res] = Pr[Set_CDH.SCDH(A).main() @ &m : res] * 
                             Pr[Set_CDH.SCDH(A).main() @ &m : res].
proof.
pose p := Pr[Set_CDH.SCDH(A).main() @ &m : res].
bdhoare_deno (_ : true) => //.
fun.
seq 1:
 b1
 (p)
 (p)
 (1%r - p)
 0%r => //.
 call (bd_h_f &m) => //.
 call (bd_h_f &m) => //.
 hoare; call(_: true); trivial; skip; smt.
save.

local module G2 = {
 
 fun main() : bool = {
  var x1, y1 : Zq;
  var r1 : group set;
  var x2, y2 : Zq;
  var r2 : group set;
  x1 = $dZq;
  y1 = $dZq;
  r1 = A.solve(g ^ x1, g ^ y1);
  x2 = $dZq;
  y2 = $dZq;
  r2 = A.solve(g ^ x2, g ^ y2);
  return (mem (cdh (g ^ x1) (g^ y1)) r1 /\ card r1 <= Set_CDH.n /\ 
          mem (cdh (g ^ x2) (g^ y2)) r2 /\ card r2 <= Set_CDH.n);
 }
}.

local lemma Pr3 &m0 &m1 :
  Pr[G1.main() @ &m1 : res] =
  Pr[G2.main() @ &m1 : res].
proof.
 equiv_deno (_ : true ==> ={res}) => //.
 fun; inline G1.f; wp.
  call (_ : true); do 2! rnd; wp.
  call (_ : true); do 2! rnd; wp; skip; progress.
  smt.
save.

local module G3 = {
 var y1 : Zq
 fun main() : bool = {
  var x1 : Zq; 
  var r1 : group set;
  var x2, y2 : Zq;
  var v1 : Zq;
  var r2 : group set;
  x1 = $dZq;
  y1 = $dZq;
  r1 = A.solve(g ^ x1, g ^ y1);
  x2 = $dZq;
  v1 = $dZq;
  r2 = A.solve(g ^ x2, (g ^ y1) ^v1);
  return (mem (cdh (g ^ x1) (g^ y1)) r1 /\ card r1 <= Set_CDH.n /\ 
          mem (cdh (g ^ x2) ((g^ y1) ^ v1)) r2 /\ card r2 <= Set_CDH.n);
 }
}.


local lemma Pr4 &m :
  Pr[G2.main() @ &m : res] <=
  Pr[G3.main() @ &m : res ] + (1%r / q%r).
proof.
 cut <- : Pr[G3.main() @ &m : G3.y1 = gf_q0] = 1%r / q%r.
 cut hbd : bd_hoare [G3.main : true ==> G3.y1 = gf_q0] = (1%r/q%r).
 fun.
 seq 2: (G3.y1 = gf_q0) (1%r/q%r) 1%r (1%r - (1%r/q%r)) 0%r => //.
 do 2! rnd; skip; progress.
 rewrite /dZq -(Dgf_q.mu_x_def_in gf_q0) /Distr.mu_x; 
  apply Distr.mu_eq => x /=; smt.
 smt.
 call lossless; do !rnd; call lossless; skip; progress; smt.
 hoare; call (_ : true) => //;do !rnd; call (_ : true) => //. 
 by bdhoare_deno hbd.
 
 apply (Real.Trans _ (Pr[G3.main() @ &m : res \/ G3.y1 = gf_q0]) _).
 equiv_deno (_ : true ==> res{1} => res{2} \/ G3.y1{2} = gf_q0) => //.
  fun.
  seq 3 3: (={x1, r1} /\ y1{1} = G3.y1{2}).
  call (_ : true) => //.
  do! rnd; skip; progress.
  case (G3.y1{2} = gf_q0).
  conseq (_ : _ ==> G3.y1{2} = gf_q0) => //.
  call{1} lossless; call{2} lossless; rnd; rnd; skip; progress; smt.
  seq 2 2: ((={x1, r1, x2} /\ y1{1} = G3.y1{2}) /\ 
              ! G3.y1{2} = gf_q0 /\ y2{1} = (G3.y1 * v1){2}).
  rnd (lambda (x : gf_q), x / G3.y1{2})
      (lambda (x : gf_q), x * G3.y1{2}).
  rnd; skip; progress; smt.
  call (_ : true); skip; progress; smt.
 rewrite Pr mu_or; smt.
save.


(* proceed as follows *)
(* check if above can be done upto 
 G3.v <> gf_q0 instead of
 G3.y1 <> gf_q0. Use this fact to prove tjat (inv v) is well defined in (****)
 Otherwise we have another (1/q) loss

*)


local module CDH_from_SCDH (O : CDH_TDDH'.TDDH) : CDH_TDDH'.Adversary(O) = {
    var v : gf_q
    var gx1', gx2', gy' : group
    fun find_val (sres1 sres2 : group set) : group = {
      var as1, as2 : group set;
      var gz1, gz2 : group;
      var b = false;
      var ret : group option = None;
      as1 = sres1;
      while (ret = None /\ as1 <> FSet.empty) {
       gz1 = pick as1;
       as1 = rm gz1 as1;
       as2 = sres2;
       while (ret = None /\ as2 <> FSet.empty) {
        gz2 = pick as2;
        as2 = rm gz2 as2;
        b = O.tddh(gz1, gz2^ (inv v)); 
        ret = b ? Some gz1 : None;
       }
      }
     return ((ret <> None) ? proj ret : g);
     
    }
    fun solve(gx1:group, gx2: group, gy:group) : group = {
      var sres1, sres2 : group set;
      var ret : group;    
      var b : bool;
      v = $dZq;
      gx1' = gx1;
      gx2' = gx2;
      gy' = gy;
      sres1 = A.solve(gx1, gy);
      sres2 = A.solve(gx2, gy^v);
      ret = find_val(sres1, sres2);
      return ret;
     }
}.


lemma cdh_prop1 : 
forall (x y z : group)(r : gf_q) ,r <> gf_q0  => 
               ddh x (y ^ r) z = ddh x y (z^ (inv r)).
proof.
 intros => x y z r hnz.
 cut: ddh x (y ^ r) z <=> ddh x y (z ^ (inv r)); last smt.
 rewrite /ddh /cdh; progress.
 rewrite (_ : log (y ^ r) = r * log y) ?pow_mult; first smt.
 rewrite (_ : (r * log y * inv r) = (r * inv r) * log y); smt.
 cut ->: x ^ log (y ^ r) = x ^ (r * log y) by smt.
 cut ->: x ^ (r * log y) =  x ^ (log y * r) by smt.
 rewrite -pow_mult -H pow_mult gf_q_mult_comm.
 rewrite gf_q_mult_inv //.
 by rewrite -{2}(group_log_pow z) pow_mult gf_q_mult_unit group_log_pow.
save.

lemma cdh_prop2 : 
forall (x y z : group)(r : gf_q), ddh x (y ^ r) z = ddh (x^r) y z.
proof.
 intros => x y z r; rewrite /ddh.
rewrite /cdh. 
cut -> :x ^ log (y ^ r) = x ^ (r * log y) by smt.
by rewrite pow_mult.
save.


local lemma Pr5 &m :
  Pr[G3.main() @ &m : res] <= 
  Pr[CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).main() @ &m : res] + 1%r/q%r.
proof.
 cut <- : Pr[CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).main() @ &m : 
             CDH_from_SCDH.v = gf_q0 ] = 1%r / q%r.
 
 cut hbd : bd_hoare [CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).main : 
                      true ==> CDH_from_SCDH.v = gf_q0] = (1%r/q%r).
 fun.
 inline CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).AO.solve.
 swap 8 -7.
 seq 1: (CDH_from_SCDH.v = gf_q0) (1%r/q%r) 1%r (1%r - (1%r/q%r)) 0%r => //.
 rnd; wp; skip; progress.
 rewrite /dZq -(Dgf_q.mu_x_def_in gf_q0) /Distr.mu_x; 
  apply Distr.mu_eq => x /=; smt.
inline CDH_from_SCDH(CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O).find_val
       CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O.tddh.
wp; while (true) (card as1) => //.
 intros => q1.
while (true) (card as2) => //.
 intros => q2; wp; skip; progress => //; smt.
 wp; skip; progress; smt.
 wp; do! call lossless; wp; do !rnd; skip; progress; smt.
 hoare; wp.
inline CDH_from_SCDH(CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O).find_val
       CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O.tddh.
 wp; while (true).
 while (true); wp; skip; progress.
 wp; do! call (_ : true); wp; do ! rnd; skip; progress.
 bdhoare_deno hbd => //.
apply (Real.Trans _ (Pr[CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).main() @ &m : res 
                     \/ CDH_from_SCDH.v = gf_q0]) _ ).
equiv_deno (_ : true ==> (res ){1}  => (res{2} 
                \/ CDH_from_SCDH.v{2} = gf_q0{2})) => //.
fun.
inline CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).AO.solve.
wp.
seq 2 2:(x1{1} = CDH_TDDH'.CDH_TDDH.x1{2} /\ 
         G3.y1{1} = CDH_TDDH'.CDH_TDDH.y{2});first by do! rnd.
swap{1} 2 -1 .
swap{1} 3 -1 .
swap{2} 6 -4.
seq 2 2: (x1{1} = CDH_TDDH'.CDH_TDDH.x1{2} /\ G3.y1{1} =  CDH_TDDH'.CDH_TDDH.y{2} /\
          x2{1} = CDH_TDDH'.CDH_TDDH.x2{2} /\ v1{1} = CDH_from_SCDH.v{2}); sp; first by do! rnd.

seq 2 2:
 (gx1{2} = g ^ CDH_TDDH'.CDH_TDDH.x1{2} /\
  gx2{2} = g ^ CDH_TDDH'.CDH_TDDH.x2{2} /\
  gy{2} = g ^ CDH_TDDH'.CDH_TDDH.y{2} /\
  CDH_from_SCDH.gx1'{2} = gx1{2} /\
  CDH_from_SCDH.gx2'{2} = gx2{2} /\
  CDH_from_SCDH.gy'{2} = gy{2} /\
  x1{1} = CDH_TDDH'.CDH_TDDH.x1{2} /\
  G3.y1{1} = CDH_TDDH'.CDH_TDDH.y{2} /\
  x2{1} = CDH_TDDH'.CDH_TDDH.x2{2} /\ v1{1} = CDH_from_SCDH.v{2} /\
 (mem (cdh (g ^ x1{1}) (g ^ G3.y1{1})) r1{1} /\
  card r1{1} <= (Set_CDH.n)%Set_CDH /\
  mem (cdh (g ^ x2{1}) (g ^ G3.y1{1} ^ v1{1})) r2{1} /\
  card r2{1} <= (Set_CDH.n)%Set_CDH =>
 (mem (cdh (g ^ x1{1}) (g ^ G3.y1{1})) sres1{2} /\
  mem (cdh (g ^ x2{1} ^ v1{1}) (g ^ G3.y1{1})) sres2{2})) /\
  CDH_TDDH'.CDH_TDDH.c{2} = 0 /\ 
  r1{1} = sres1{2} /\
  r2{1} = sres2{2}).
do! call (_ : true); skip; progress.
generalize H1; rewrite /cdh !group_pow_log; smt.
case (mem (cdh (g ^ x1{1}) (g ^ G3.y1{1})) r1{1} /\
   card r1{1} <= (Set_CDH.n)%Set_CDH /\
   mem (cdh (g ^ x2{1}) (g ^ G3.y1{1} ^ v1{1})) r2{1} /\
   card r2{1} <= (Set_CDH.n)%Set_CDH).
case( CDH_from_SCDH.v{2} = gf_q0).
inline CDH_from_SCDH(CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O).find_val
       CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O.tddh.
 wp; while{2} (true) (card as1{2}).
 intros => ? ?.
 while (true) (card as2). 
 intros => ?; wp; skip; progress; smt.
 wp; skip; progress; smt.
 wp; skip; progress; smt.

call{2} (_ : mem (cdh (g ^ CDH_TDDH'.CDH_TDDH.x1) (g ^ CDH_TDDH'.CDH_TDDH.y)) sres1 /\  
             mem (cdh (g ^ CDH_TDDH'.CDH_TDDH.x2 ^ CDH_from_SCDH.v) (g ^ CDH_TDDH'.CDH_TDDH.y)) sres2 /\
            ! CDH_from_SCDH.v = gf_q0 /\ card sres1 <= Set_CDH.n /\ card sres2 <= Set_CDH.n /\
            CDH_TDDH'.CDH_TDDH.c = 0
                ==> 
               res = cdh (g ^ CDH_TDDH'.CDH_TDDH.x1) (g ^ CDH_TDDH'.CDH_TDDH.y)).
fun.
inline CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O.tddh.
while
((forall x, ret = None => mem x sres1 => !mem x as1 => 
  (forall y, mem y sres2 => 
!tddh (g ^ CDH_TDDH'.CDH_TDDH.x1)((g ^ CDH_TDDH'.CDH_TDDH.x2)^ CDH_from_SCDH.v) (g ^ CDH_TDDH'.CDH_TDDH.y) x y)) /\
 ! CDH_from_SCDH.v = gf_q0 /\
 (ret <> None => tddh (g ^ CDH_TDDH'.CDH_TDDH.x1) ((g ^ CDH_TDDH'.CDH_TDDH.x2) ^ CDH_from_SCDH.v) (g ^ CDH_TDDH'.CDH_TDDH.y) gz1 gz2 /\ ret = Some gz1) /\
CDH_TDDH'.CDH_TDDH.c <= ((card sres1) - (card as1)) * card sres2 /\
card as1{hr} <= card sres1{hr} /\
card sres1{hr} <= (Set_CDH.n)%Set_CDH /\
(* card as2{hr} <= card sres2{hr} /\ *)
card sres2{hr} <= (Set_CDH.n)%Set_CDH) (card as1).
 intros => q1.
while ((forall y, ret = None => mem y sres2 => !mem y as2 => 
  !tddh (g ^ CDH_TDDH'.CDH_TDDH.x1) ((g ^ CDH_TDDH'.CDH_TDDH.x2)^ CDH_from_SCDH.v) (g ^ CDH_TDDH'.CDH_TDDH.y) gz1 y) /\
       (ret <> None => tddh (g ^ CDH_TDDH'.CDH_TDDH.x1) ((g ^ CDH_TDDH'.CDH_TDDH.x2) ^ CDH_from_SCDH.v) (g ^ CDH_TDDH'.CDH_TDDH.y) gz1 gz2 /\ ret = Some gz1) /\
 ! CDH_from_SCDH.v = gf_q0 /\
CDH_TDDH'.CDH_TDDH.c <= ((card sres1) - (card as1) - 1) * (card sres2) +  ((card sres2) - card as2) /\
card as1{hr} < card sres1{hr} /\
card sres1{hr} <= (Set_CDH.n)%Set_CDH /\
card as2{hr} <= card sres2{hr} /\
card sres2{hr} <= (Set_CDH.n)%Set_CDH /\
sres1{hr} <> empty)  (card as2).
 intros => q2.
 rcondt 6.
 wp; skip; progress => //.
cut: CDH_TDDH'.CDH_TDDH.c{hr} <= (Set_CDH.n)%Set_CDH * (Set_CDH.n)%Set_CDH; last smt.
cut _:(card sres1{hr} - card as1{hr} - 1) * card sres2{hr} <=
      ((Set_CDH.n)%Set_CDH - 1) * (Set_CDH.n)%Set_CDH; last smt.
cut _: 0 < card sres1{hr} by smt.
apply (_ : forall (a b c d : int), 0 <= a <= b => 0 <= c <= d => a * c <= b * d); [smt| |smt].
case (as1{hr} = empty) => Heq; [rewrite Heq card_empty|]; smt.
wp; skip; progress.

cut: !tddh (g ^ CDH_TDDH'.CDH_TDDH.x1{hr}) (g ^ CDH_TDDH'.CDH_TDDH.x2{hr})
          (g ^ CDH_TDDH'.CDH_TDDH.y{hr}) gz1{hr}
          (pick as2{hr} ^ inv CDH_from_SCDH.v{hr}) by smt.
case (y = (pick as2{hr})); last first.
generalize H11; rewrite mem_rm; smt.
rewrite /tddh -cdh_prop1 ?cdh_prop2 => //.
smt.
cut: tddh (g ^ CDH_TDDH'.CDH_TDDH.x1{hr}) (g ^ CDH_TDDH'.CDH_TDDH.x2{hr})
          (g ^ CDH_TDDH'.CDH_TDDH.y{hr}) gz1{hr}
          (pick as2{hr} ^ inv CDH_from_SCDH.v{hr}) by smt.
intros => [? ?].
generalize H11; rewrite -cdh_prop1 // ? cdh_prop2 //.
smt.
smt.
smt.
smt.
wp; skip; progress.
 smt.
 smt.
 smt.
 smt.
 smt.
case (x = pick as1{hr}) => ?; smt.
generalize H11.
 rewrite !card_rm_in; try (by apply mem_pick).
rewrite (_ : (card sres1{hr} - (card as1{hr} - 1) - 1) = (card sres1{hr} - (card as1{hr}))); first smt.
rewrite (_ :(card sres1{hr} - (card as1{hr} - 1)) * card sres2{hr} =
            (((card sres1{hr} - (card as1{hr})) + 1)) * card sres2{hr}).
smt.
rewrite (_: (((card sres1{hr} - (card as1{hr})) + 1)) * card sres2{hr} =
            (card sres1{hr} - (card as1{hr})) * card sres2{hr} +card sres2{hr}).
smt.
intros ?.
cut : (card sres1{hr} - card as1{hr}) * card sres2{hr} +
     (card sres2{hr} - card as20) <=
      (card sres1{hr} - card as1{hr}) * card sres2{hr} + card sres2{hr}; last smt.
apply (_ : forall (a b c d : int),a <= b => c <= d => a + c <= b + d); [smt| smt |].
by case (as20 = empty); smt.
smt.
rewrite card_rm_in; try (by apply mem_pick); smt.
 wp; skip; progress.
 smt.
 smt.
generalize H7 H5; case (ret0 = None) => /= ? ?.
cut:=  H7 (cdh (g ^ CDH_TDDH'.CDH_TDDH.x1{hr}) (g ^ CDH_TDDH'.CDH_TDDH.y{hr})) _ _
          (cdh (g ^ CDH_TDDH'.CDH_TDDH.x2{hr} ^ CDH_from_SCDH.v{hr})
         (g ^ CDH_TDDH'.CDH_TDDH.y{hr})) _ => //; smt.
smt.

skip; progress; try smt.
inline CDH_from_SCDH(CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O).find_val
       CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).O.tddh.
 wp; while{2} (true) (card as1{2}).
 intros => ? ?.
 while (true) (card as2). 
 intros => ?; wp; skip; progress; smt.
 wp; skip; progress; smt.
 wp; skip; progress; smt.
 rewrite Pr mu_or; smt.
save.


lemma Conclusion &m:
exists (B <: CDH_TDDH'.Adversary {DDH_2DDH'.M,  CDH_TDDH'.CDH_TDDH}),
(Pr[Set_CDH.SCDH(A).main() @ &m : res] * Pr[Set_CDH.SCDH(A).main() @ &m : res] <=
  Pr[CDH_TDDH'.CDH_TDDH(B).main() @ &m : res] + 2%r/q%r) /\ 
(forall (O <: CDH_TDDH'.TDDH), islossless O.tddh => islossless B(O).solve).
proof.
exists CDH_from_SCDH; split.
cut: (Pr[Set_CDH.SCDH(A).main() @ &m : res] * Pr[Set_CDH.SCDH(A).main() @ &m : res] <=
  Pr[CDH_TDDH'.CDH_TDDH(CDH_from_SCDH).main() @ &m : res] + 1%r/q%r + 1%r / q%r).
rewrite -(Pr2 &m).
rewrite (Pr3 &m &m).
apply (Real.Trans _   (Pr[G3.main() @ &m : res ] + (1%r / q%r))).
apply (Pr4 &m).
cut := Pr5 &m.
smt.
smt.
intros => O H; fun.
call (_ : true ==> true).
fun.
while (true) (card as1).
intros => ?.
while (true) (card as2).
intros => ?.
wp; call H; wp; skip; smt.
wp; skip; smt.
wp; skip; smt.
do! call (lossless); wp; rnd; skip; smt.
save.

end section.

print axiom Conclusion.


section.
declare module A : CDH_TDDH'.Adversary {DDH_2DDH'.M,  CDH_TDDH'.CDH_TDDH}.
axiom isll : forall (O <: CDH_TDDH'.TDDH), islossless O.tddh => islossless A(O).solve.
(*  : forall (O <: DDH_2DDH'.O{A}), islossless O.check => islossless A(O).solve. *)
print theory DDH_2DDH'.
print theory CDH_TDDH'.

require import List.

print module type DDH_2DDH.O.

(* 
module O'(O : DDH_2DDH.O) : CDH_TDDH'.TDDH = {
   var gx1 : group
   var gx2 : group
   var gy : group
    fun tddh (z1 z2 : group) : bool ={
     var b : bool;
     b = O.check(gx2, z1, z2, gy);
     return (b);
   }
}.
*)

local module B (O : DDH_2DDH.O) : DDH_2DDH.Adv(O) ={
   var gx1 : group
   var gx2 : group
   var gy : group
   module O' : CDH_TDDH'.TDDH = {
    fun tddh (z1 z2 : group) : bool ={
     var b : bool;
     b = O.check(gx2, z1, z2, gy);
     return (b);
    }
   }
  module AO = A (O')
  fun run (X : group, X_i : group list, Y : group) : group = {
   var r : group;
   gx1 = X;
   gx2 = hd X_i;
   gy = Y;

   r = AO.solve(X, hd X_i, Y);
   return r;
  }
 }.

require import Cyclic_group_prime.
require import FMap. import OptionGet.

lemma Conc2 &m : exists (B' <: DDH_2DDH.Adv {DDH_2DDH'.M}),
(Pr[CDH_TDDH'.CDH_TDDH(A).main() @ &m : res] =
Pr[DDH_2DDH'.TDDH_Win(B').main() @ &m : res] )/\ forall (O <: DDH_2DDH'.O{B'}), islossless O.check => islossless B'(O).run.
exists B; split.
equiv_deno (_ : true ==> ={res}) => //.
fun.
inline  DDH_2DDH'.TDDH_Win(B).AT.run.
sp.
rcondt{2} 4.
intros => ?; wp; do! rnd; skip; progress.
rcondf{2} 8.
intros => ?; wp; rnd; wp; do! rnd; wp; skip; progress.
wp.
call (_ :
g ^ CDH_TDDH'.CDH_TDDH.x1{1} =  DDH_2DDH'.M.gx{2} /\
DDH_2DDH'.M.gx{2} = B.gx1{2} /\
g ^ CDH_TDDH'.CDH_TDDH.y{1} = DDH_2DDH'.M.gy{2} /\
DDH_2DDH'.M.gy{2} = B.gy{2} /\
dom DDH_2DDH'.M.gx_i_rs{2} = add (g ^ CDH_TDDH'.CDH_TDDH.x2{1}) FSet.empty /\
g ^ CDH_TDDH'.CDH_TDDH.x2{1} = B.gx2{2} /\
CDH_TDDH'.CDH_TDDH.c{1} = DDH_2DDH'.M.cO{2}).
fun.
inline DDH_2DDH'.TDDH_Win(B).TD.check.
sp 1 5.
if.
progress.
by rewrite /in_dom H mem_add.
wp; skip; progress.
rewrite /tddh /ddh /cdh // rw_eq_iff; progress; smt.
wp; skip; progress.
wp.
rnd (lambda u, g ^ u)(lambda (u : group), log u). 
wp.
rnd (lambda u, g ^ u)(lambda (u : group), log u). 
rnd (lambda u, g ^ u)(lambda (u : group), log u). 
skip; progress; smt. 

intros => O H.
fun.
call (isll (<:B(O).O') _).
by (fun; call H => //).
by wp.
save.

end section.

section.

declare module A : DDH_2DDH'.Adv'.

print theory  DDH_2DDH'.
print theory  CDH.

local module B : CDH.Adversary ={
  fun solve (gx : group, gy : group) : group = {
   var r : group;
   r = A.run(gx, gy);
   return r;
  }
 }.

lemma Conc3 &m:
exists (B <: CDH.Adversary),
Pr[DDH_2DDH'.Win(A).main() @ &m : res] = 
Pr[CDH.CDH(B).main() @ &m : res].
exists B.
equiv_deno (_ : true ==> ={res}) => //.
fun.
inline B.solve.
wp.
call (_: true).
wp.
rnd (lambda (u : group), log u)(lambda u, g ^ u). 
rnd (lambda (u : group), log u)(lambda u, g ^ u). 
wp; skip; progress; smt.
save.

end section.

print axiom Conclusion.

print axiom Conc2.

section.

declare module A : Set_CDH.Adversary{CDH_TDDH'.CDH_TDDH, DDH_2DDH'.M}. 
axiom ll_a :
islossless A.solve.

lemma Koblitz &m :
exists (B <: CDH.Adversary),
        (Pr[Set_CDH.SCDH(A).main() @ &m : res] ^ 2 <=
        Pr[CDH.CDH(B).main() @ &m : res] +
        ((Set_CDH.n)%Set_CDH * (Set_CDH.n)%Set_CDH + 1)%r * (1%r / q%r) + 2%r / q%r).
cut [B [hB hB']] := Conclusion A _ &m; first by apply ll_a.
cut [C [hC hC']] := Conc2 B _ &m => //.
cut [D hD] := DDH_2DDH'.Conclusion C _ &m => //.
cut [E hE] := Conc3 D &m .
exists E.
smt.
save.        

end section.

print axiom Koblitz.
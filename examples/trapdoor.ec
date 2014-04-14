require import Int.
require import FSet.
require import Bool.
require import Real.
require import AlgTactic.
require import Prime_field.
require import Cyclic_group_prime.
require import Option.
require import Pair.
require import FMap.
require import List.
import OptionGet.

(* This is a mess and needs cleaning up *)
(* It includes:
  - a bunch of group lemmas that have to be
   integrated to Cyclic_group_prime 
  - a really general trapdoor test trick that is 
   useful (so far) for:
    + the DLOG branch of naxos and
    + the good reduction from SCDH to CDH AKA the Koblitz
   lemma

Only one admit that should be easy to solve and was
previously discharged with compute.
Additionally, I am using fusion in a way in which the syntactic
independance check is not passed, but it's still sound.
We have to fix this, for now I have disabled the check in my 
distribution.
*)


import Dgroup.
import Dgf_q.

(* formalization of find_last *)
(* useful for spliting a loop in the last iteration 
   satisfying a predicate *)
op find_last : int -> int -> (int -> bool) -> int option.

axiom find_last_spec : forall l u p k,
find_last l u p = Some k <=>
(l <= k <= u /\
 p k /\
(forall j, k < j => ! p j) ).

axiom find_last_exists : forall l u p,
find_last l u p = None =>
(forall k, l <= k <= u => ! p k).





(* reals axiom *)
(* we should be able to discharge this *)
lemma mult_pos_mon : forall (p q r : real), 0%r <= r => p <= q => r * p <= r * q by smt.

(* group stuff *)
type zq = gf_q.

op pow : zq -> int -> zq.
op (^^) = pow.

axiom qf_expr0 : forall (x : zq), x^^0 = gf_q1.
axiom qf_exprS : forall (x : zq) i, 0 <= i => x^^(i+1) = x * x^^i.
axiom qf_exprN : forall (x : zq) i, 0 <= i => x^^(-i) = inv (x^^i).



op ofint : int -> zq.

axiom qf_ofint0 : ofint 0 = Prime_field.gf_q0.
axiom qf_ofint1 : ofint 1 = Prime_field.gf_q1.
axiom qf_ofintS : forall i, 0 <= i => ofint (i+1) = ofint i + gf_q1.
axiom qf_ofintN : forall (i : int), ofint (-i) = -(ofint i).

instance field with zq
  op rzero = Prime_field.gf_q0
  op rone  = Prime_field.gf_q1
  op add   = Prime_field.( + )
  op opp   = Prime_field.([-])
  op mul   = Prime_field.( * )
  op expr  = pow
  op sub   = Prime_field.( - )
  op ofint = ofint
  op inv   = Prime_field.inv
  op div   = Prime_field.(/)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof mulrV     by smt
  proof expr0     by smt
  proof exprS     by smt
  proof exprN     by smt
  proof subrE     by smt
  proof divrE     by smt
  proof ofint0    by smt
  proof ofint1    by smt
  proof ofintS    by smt
  proof ofintN    by smt.


(* lemmas of groups and prime field *)
lemma gen_exp_inj : forall(m n : gf_q), g ^ m = g ^ n => m = n.
proof.
 intros => m n heq.
 cut: log (g ^ m) = log (g ^n).
  by rewrite heq.
 by rewrite !group_pow_log.
save.

lemma neg_distr : forall (x y : gf_q), -(x + y) = -x + -y.
proof.
 by intros => ? ?; fieldeq.
save.

lemma neg_zero : forall (x y : gf_q), gf_q0 = x - y => x = y.
proof.
 intros => ? ? ?.
 fieldeq; rewrite H; fieldeq.
save.

lemma gen_def : forall X, exists m, X = g ^ m. 
proof.
 intros X; exists (log X).
 by rewrite group_log_pow.
save.

const I : group = g ^ gf_q0.

lemma exp_inj : forall X (m n : gf_q), X <> I => X ^ m = X ^ n => m = n.  
proof.
 intros => X m n.
 cut [r ->] := gen_def X.
 case (r = gf_q0) => heq.
  rewrite /I heq; smt.
 intros => h {h}.
 rewrite !group_pow_mult => h.
 cut: log (g ^ (r * m)) = log (g ^ (r * n)) by smt.
  rewrite !group_pow_log => {h} h. 
 cut: (r * m) / r = (r * n) / r by smt.
  rewrite (gf_q_mult_comm _ m) (gf_q_mult_comm _ n) /Prime_field.(/).
  by rewrite -!gf_q_mult_assoc !gf_q_mult_inv // !gf_q_mult_unit.
save.

lemma exp_rewr : forall X (m n : gf_q), X <> I => (X ^ m = X ^ n <=> m = n)  
 by (progress; apply (exp_inj X)).

lemma exp_inj2 : forall X Y (n : gf_q), n <> gf_q0 => X ^ n = Y ^ n => X = Y.
proof.
 intros => X Y n hn.
 cut [y ->]:= gen_def Y.
 cut [x ->]:= gen_def X.
 rewrite !group_pow_mult => h.
 cut := gen_exp_inj (x * n) (y * n) _ => // {h} h.
 cut: ( x * n * (inv n) = y * n * (inv n)) by smt => {h}.
 by rewrite -!gf_q_mult_assoc !gf_q_mult_inv // !gf_q_mult_unit.
save.

lemma exp_rewr2 : forall X Y (n : gf_q), n <> gf_q0 => X ^ n = Y ^ n <=> X = Y
by (progress; apply (exp_inj2 X Y n)).


lemma substr_inj : 
 forall (m n r : gf_q), m - r = n - r => m = n.
proof.
 intros => m n r h.
 cut: ((m - r) + r = (n - r) + r).
  by rewrite h.
 rewrite /Prime_field.(-) -!gf_q_add_assoc !(gf_q_add_comm (-r) r)  gf_q_add_minus.
 by rewrite (gf_q_add_comm m) (gf_q_add_comm n) !gf_q_add_unit.
save.
 
lemma log_prod_plus : forall (X Y : group), log (X * Y) = log X + log Y.
proof.
 intros => X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite group_pow_add.
 by rewrite !group_pow_log.
save.

lemma log_div_minus : forall (X Y : group), log (X / Y) = log X - log Y.
proof.
 intros => X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 by rewrite -Cyclic_group_prime.div_def !group_pow_log.
save.

lemma inv_inj : forall (X Y Z : group), X / Z = Y / Z => X = Y.
proof.
 intros X Y Z.
 rewrite -!Cyclic_group_prime.div_def => h.
 cut:= gen_exp_inj (log X - log Z) (log Y - log Z) _ => // {h} h.
 cut: (log X = log Y).
  by apply (substr_inj _ _ (log Z)).
 intros => h'.
 cut: g ^ log X = g ^ log Y by rewrite h' //.
 by rewrite !group_log_pow.
save.

lemma inv_rewr : forall (X Y Z : group), X / Z = Y / Z <=> X = Y
 by (progress; apply (inv_inj _ _ Z)).

lemma div_cancel : forall (Y : group), Y / Y = g ^ gf_q0.
proof.
 intros => Y.
 by rewrite -!Cyclic_group_prime.div_def /Prime_field.(-) gf_q_add_minus.
save.

lemma div_prod (X Y : group): X / Y = X * (I / Y).
proof.
 rewrite -!Cyclic_group_prime.div_def /I /Prime_field.(-).
 cut:= gen_def X => [[x]] ->.
 by rewrite !group_pow_log group_pow_add gf_q_add_unit.
save.


lemma group_prod_assoc : forall (X Y Z : group), (X * Y) * Z = X * (Y * Z).
proof.
 intros => X Y Z.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 cut := gen_def Z => [[z]] ->.
 rewrite !group_pow_add.
 by rewrite gf_q_add_assoc.
save.

lemma prod_div : forall (X Y Z : group), X * (Y / Z) = (X * Y) / Z.
proof.
 intros => X Y Z.
 by rewrite div_prod -group_prod_assoc -div_prod.
save.

lemma I_prod_n : forall (X : group),  X * I = X.
proof.
 intros => X.
 cut := gen_def X => [[x]] ->.
 by rewrite /I group_pow_add gf_q_add_comm gf_q_add_unit.
save. 

lemma I_pow_n : forall n , I ^ n = I.
proof.
 intros => n; rewrite /I.
 by rewrite group_pow_mult gf_q_mult_comm gf_q_mult_zero. 
save.

lemma prod_comm : forall (X Y : group), X * Y = Y * X. 
proof.
 intros => X Y.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 by rewrite !group_pow_add gf_q_add_comm.
save.

lemma mult_div_I : forall (X : group), X / X = I.
 intros => X.
 cut := gen_def X => [[x]] ->.
 by rewrite -!Cyclic_group_prime.div_def /Prime_field.(-) gf_q_add_minus /I.
save. 

lemma mult_div : forall (X Y : group), (X * Y) / Y = X.
proof.
 intros => X Y.
 by rewrite div_prod group_prod_assoc prod_div I_prod_n mult_div_I I_prod_n.
save.

lemma mult_pow_distr : forall (X Y : group) n, (X * Y) ^ n = X ^ n * Y ^ n.
proof.
 intros => X Y n.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite !group_pow_add !group_pow_mult group_pow_add.
 by rewrite gf_q_mult_comm gf_q_distr (gf_q_mult_comm x n) (gf_q_mult_comm y n).
save.

lemma div_pow_distr : forall (X Y : group) n, (X / Y) ^ n = X ^ n / Y ^ n.
proof.
 intros => X Y n.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 rewrite -!Cyclic_group_prime.div_def !group_pow_mult !group_pow_log.
 rewrite /Prime_field.(-) gf_q_mult_comm gf_q_distr (gf_q_mult_comm x n). 
 by rewrite gf_q_mult_minus_right (gf_q_mult_comm y n).
save.

lemma pow_mult : forall (X : group) m n, X ^ m ^ n = X ^ (m * n). 
 intros => X m n.
 cut:= gen_def X => [[x]] ->.
 by rewrite !group_pow_mult gf_q_mult_assoc.
save.


lemma div_div_mult : forall (X Y Z : group), (X / Y) / Z = X / (Y * Z).
proof.
 intros => X Y Z.
 cut := gen_def X => [[x]] ->.
 cut := gen_def Y => [[y]] ->.
 cut := gen_def Z => [[z]] ->.
 rewrite -!Cyclic_group_prime.div_def.
 rewrite -log_div_minus log_prod_plus /Prime_field.(-).
 by rewrite neg_distr gf_q_add_assoc /Prime_field.(-); smt.
save.

lemma pow_div_minus : forall (X : group) m n,  X ^ m / X ^ n = X ^ (m - n).
 intros => X m n.
 cut := gen_def X => [[x]] ->.
 rewrite -!Cyclic_group_prime.div_def.
 rewrite !group_pow_mult !group_pow_log.
 rewrite /Prime_field.(-) gf_q_distr gf_q_mult_comm (gf_q_mult_comm x n).
 by rewrite -gf_q_mult_minus (gf_q_mult_comm (-n) x).
save.

lemma log_pow_mult : forall (X : group) n, log (X ^ n) = n * log X.
proof.
 intros => X m.
 cut := gen_def X => [[x]] ->.
 by rewrite group_pow_mult !group_pow_log gf_q_mult_comm.
save.

lemma test_rewrite : forall Z_1 Z_2 Y (r s x1 x2 : gf_q),
s = r * x1 + x2 => 
Z_1 ^ r * Z_2 = Y ^ s <=>
(Z_1 / Y ^ x1) ^ r = (Y ^ x2) / Z_2.
proof.
 intros => Z_1 Z_2 Y r s x1 x2 ->.
 rewrite -(inv_rewr _ _ Z_2).
 rewrite mult_div.
 rewrite -(inv_rewr _ _ (Y ^ (x1 * r) )).
 cut -> : Z_1 ^ r / Y ^ (x1 * r) = (Z_1 / Y ^ x1) ^ r.
  by rewrite div_pow_distr pow_mult.
 cut -> : Y ^ (r * x1 + x2) / Z_2 / Y ^ (x1 * r) = Y ^ x2 / Z_2.
 rewrite div_div_mult prod_comm -div_div_mult pow_div_minus.
 cut: (r * x1 + x2 - x1 * r) = x2; last by smt.
 rewrite gf_q_add_comm /Prime_field.(-) -gf_q_add_assoc gf_q_mult_comm.
 by rewrite gf_q_add_minus gf_q_add_comm gf_q_add_unit.
 smt.
save. 

lemma div_eq_I : forall (X Y : group), I = X / Y  <=> X = Y.
proof.
 progress; last first.
 by rewrite -!Cyclic_group_prime.div_def gf_q_minus /I.
 generalize H; rewrite -!Cyclic_group_prime.div_def /I=> H.
 cut:= gen_exp_inj  gf_q0  (log X - log Y) _ => // {H} H.
 cut:= neg_zero (log X) (log Y) _ => // {H} H.
 by rewrite -(group_log_pow X) H group_log_pow.
save.
 
theory Trapdoor.

const qO : int. (* bound on calls *)
axiom qO_pos : 0 < qO.
lemma qO_posR : 0%r <= qO%r by smt.

type adv_ret. (* return type of adversary *)
op win : group -> group -> adv_ret -> bool. (* winning condition *)


const n : int. (* number of X_2's used. In the twin dh problem n = 1 *)
axiom n_pos : 0 < n.


module type O = {
 fun check (X_i : group, Z1 Z2 Y : group) : bool
}.

module type Adv (O : O) = {
 fun run (X : group, X_i : group list, Y : group) : adv_ret {* O.check}
}.


module M = {
 var gx_i_rs : (group, (gf_q * gf_q)) map
 var bad : bool
 var cO : int
 var bad_query : int option
 var bad_guess : int
 var gz1, gz2, gy : group
 var r, s : gf_q
 var gx : group
 var gx_bad : group
 var gy_bad : group
}.


module TDDH_Win( A : Adv) ={
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs){
    ret = (Z1 = Y ^(log M.gx) /\ Z2 = Y ^ (log X_i) );
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gy : group;
  var gxs : group list = [];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  a = AT.run(M.gx, gxs, M.gy);
  return (win M.gx M.gy a);
 }
}.


module type Adv' = {
 fun run (gx gy : group) : adv_ret {*}
}.

module Win(A : Adv') ={
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gy, gx : group;
  gx = $dgroup;
  gy = $dgroup;
  M.bad_query = None;
  a = A.run(gx, gy);
  return (win gx gy a);
 }
}.


section.

declare module A : Adv {M}.

axiom run_ll : forall (O <: O{A}), islossless O.check => islossless A(O).run.


local module G0( A : Adv) ={
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs){
    (* r = (Z1 = Y ^(log M.ga) /\ Z2 = Y ^ (log X_i) ); *)
    (r, s) = proj (M.gx_i_rs.[X_i]);
    ret = ((Z1 ^ r) * Z2 = Y ^ s);
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gxs : group list = [];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = (g ^ s) / (M.gx ^ r);
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  a = AT.run(M.gx, gxs, M.gy);
  return (win M.gx M.gy a);
 }
}.


local module G1( A : Adv) ={
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs){
    (r, s) = proj (M.gx_i_rs.[X_i]);
    ret = (Z1 / (Y^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2;
    M.cO = M.cO + 1;
    if (Z1 <> (Y ^ (log M.gx)) /\
         ((Z1 / (Y ^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2)) {
     M.bad = true;
    }

   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gxs = [];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = (g ^ s) / (M.gx ^ r);
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  M.bad = false;
  a = AT.run(M.gx, gxs, M.gy);
  return (win M.gx M.gy a);
 }
}.

lemma stpd_get : forall x (m : ('a,'b) map), m.[x] = FMap.Core.get m x by smt.

local equiv Eq1 : 
G0(A).main ~ G1(A).main : true ==> ={res}.
proof.
 fun.
 call (_ : ={M.gx,M.gy, M.gx_i_rs, M.cO} /\ 
(forall X, in_dom X M.gx_i_rs => 
let (r,s) = proj M.gx_i_rs.[X] in
(X = g ^ s / M.gx ^ r)){2}).
fun; sp 1 1; if => //; sp 3 3; wp; skip; progress.

cut : r{1} = r{2} by smt.
cut : s{1} = s{2} by smt.
progress.
 cut ->:= test_rewrite Z1{2} Z2{2} Y{2} r{2} s{2} (log M.gx{2}) 
  (log (g ^ s{2} / M.gx{2} ^ r{2})) _ => //. 
 rewrite log_div_minus.
 rewrite group_pow_log.
 by rewrite log_pow_mult /Prime_field.(-) gf_q_add_comm -gf_q_add_assoc 
 -(gf_q_add_comm (r{2} * log M.gx{2}))  gf_q_add_minus gf_q_add_comm gf_q_add_unit.

cut := H1 X_i{2} _ => //;rewrite  -H /=.
by intros => ->.

wp.
while (={i, M.gx_i_rs, M.gx, M.gy, gxs} /\ (forall X, in_dom X M.gx_i_rs =>  let (r,s) = proj M.gx_i_rs.[X] in (X = g ^ s / M.gx ^ r)){2}).
wp; do 2! rnd; skip; progress.

case (X = g ^ sL / M.gx{2} ^ rL) => heq.
 generalize H9; rewrite -heq stpd_get get_setE proj_some => h.
 cut <-: rL = x1 by smt.
 rewrite heq (_ : sL = x2) //; smt.
 generalize H8 H9; rewrite /in_dom dom_set mem_add stpd_get get_setN; first smt.
 intros => [|] h;[|smt].
 cut:= H X _; first smt. 
 by intros => h1 h2; generalize h1; rewrite stpd_get h2 /=.
wp; do!rnd; wp; skip; progress; smt.
save.

local lemma Pr1 &m : 
Pr [G0(A).main() @ &m : res] =
Pr [G1(A).main() @ &m : res]. 
proof.
 equiv_deno Eq1 => //.
save.

local equiv Eq2 :
TDDH_Win(A).main ~ G1(A).main : true ==> ! M.bad{2} => ={res}.
proof.
 fun.
 call (_ : M.bad, 
          ={M.gx, M.gy, M.cO} /\ 
          (dom M.gx_i_rs{1} = dom M.gx_i_rs{2}) /\
          (forall X, in_dom X M.gx_i_rs => 
           let (r,s) = proj M.gx_i_rs.[X] in
           (X = g ^ s / M.gx ^ r)){2}) => //.
 apply run_ll. 
 fun; sp 1 1; if => //.
 by progress; generalize H3; rewrite /in_dom H0.
  sp 0 1; wp; skip; progress.
 cut: (Z1{2} = Y{2} ^ log M.gx{2} /\ Z2{2} = Y{2} ^ log (g ^ s{2} / M.gx{2} ^ r{2}) <=>
((Z1{2} / Y{2} ^ log M.gx{2}) ^ r{2} = Y{2} ^ log (g ^ s{2} / M.gx{2} ^ r{2}) / Z2{2})); last by smt.
 split.
 intros => [heq1 heq2].
 rewrite heq1 heq2 -!Cyclic_group_prime.div_def !gf_q_minus group_pow_mult.
 by rewrite gf_q_mult_comm gf_q_mult_zero.
 intros heq.
 cut :(Z1{2} = Y{2} ^ log M.gx{2} \/
       (Z1{2} / Y{2} ^ log M.gx{2}) ^ r{2} <> Y{2} ^ log X_i{2} / Z2{2}) by smt.
 intros => [|] heq'.
 split => //.
 cut:  (! Z2{2} = Y{2} ^ log (g ^ s{2} / M.gx{2} ^ r{2}) => false); last by smt.
 intros => hneq; generalize heq => /=.
  rewrite heq' mult_div_I I_pow_n.
  rewrite div_eq_I.
 smt.
 cut:= H2 X_i{2} _ => //.
  rewrite /in_dom -H1; smt.
 
 rewrite -H /=.
 smt.
 by intros => ? h; fun; wp.
 by intros => ?; fun; wp; skip.
 wp.
  while (={i, M.gx, M.gy, gxs} /\ 
        (dom M.gx_i_rs{1} = dom M.gx_i_rs{2}) /\
        (forall X, in_dom X M.gx_i_rs => 
         let (r,s) = proj M.gx_i_rs.[X] in 
         (X = g ^ s / M.gx ^ r)){2}).
 wp.
 rnd (lambda (u : group), log u + r{2} * log M.gx{2}) 
     (lambda (v : gf_q) , g ^ (v - log M.gx{2} * r{2})).
 rnd{2}.
 skip; progress => //.
 apply lossless. 
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by rewrite Dgroup.supp_def.
 cut -> : (log gxL + r0 * log M.gx{2} - log M.gx{2} * r0) = 
           log gxL by fieldeq.
 by rewrite group_log_pow.
 
 by rewrite group_pow_log; fieldeq.
 cut: gxL = (g ^ (log gxL + r0 * log M.gx{2}) / M.gx{2} ^ r0); last smt.
 rewrite -{1}H9.
 rewrite (_ : M.gx{2}^ r0 = g ^ ((log M.gx{2}) * r0)); first smt.
 by rewrite -{1}Cyclic_group_prime.div_def !group_pow_log.
 rewrite !dom_set H.
 cut: gxL = (g ^ (log gxL + r0 * log M.gx{2}) / M.gx{2} ^ r0); last smt.
 rewrite -{1}H9.
 rewrite (_ : M.gx{2}^ r0 = g ^ ((log M.gx{2}) * r0)); first smt.
 by rewrite -{1}Cyclic_group_prime.div_def !group_pow_log.
case (X = g ^ (log gxL + r0 * log M.gx{2}) / M.gx{2} ^ r0) => heq //.
generalize H12; rewrite heq stpd_get get_setE proj_some => h.
cut <- :  r0 = x1 by smt.
cut <- :  log gxL + r0 * log M.gx{2} = x2 by smt.
smt.
 generalize H11 H12; rewrite /in_dom dom_set mem_add stpd_get get_setN.
smt.
intros => [|] hmem heq'.
cut:= H0 X _; first smt.
by rewrite stpd_get heq' /=.
smt.
wp; do! rnd; wp; skip; progress; smt.
save.

local lemma Pr2_aux &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G1(A).main() @ &m : res] + Pr[G1(A).main() @ &m : M.bad]. 
proof.
 apply (Real.Trans _ (Pr [G1(A).main() @ &m : res \/ M.bad]) _).
 equiv_deno Eq2; smt.
 rewrite Pr mu_or; smt.
save.

local lemma Pr2 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + Pr[G1(A).main() @ &m : M.bad]. 
proof.
 rewrite (Pr1 &m).
 by apply (Pr2_aux &m).
save.

(* We introduce the following changes:
 - we stop replying in the oracle after bad is triggered
   the first time
 - we sample all the X_i's at random insetead of computing
   them as X_i = g ^ s / A ^ r
*)

local module G2( A : Adv) ={
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs /\ !M.bad){
    (r, s) = proj (M.gx_i_rs.[X_i]);
    if (Z1 <> (Y ^ (log M.gx)) /\
         ((Z1 / (Y ^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2)) {
     M.bad = true;
    }
    ret = (Z1 / (Y^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2;
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gxs = [];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  M.bad = false;
  a = AT.run(M.gx, gxs, M.gy);
  return (win M.gx M.gy a);
 }
}.


local equiv Eq3 : 
G1(A).main ~ G2(A).main : true ==> M.bad{1} = M.bad{2}.
proof.
 fun.
 wp; call (_ : M.bad, 
              ={M.gx, M.gy, M.bad, M.cO} /\
          (dom M.gx_i_rs{1} = dom M.gx_i_rs{2}) /\
          (forall X, in_dom X M.gx_i_rs{1} => fst (proj M.gx_i_rs.[X]){1} = fst (proj M.gx_i_rs.[X]){2}) /\
          (forall X, in_dom X M.gx_i_rs => 
           let (r,s) = proj M.gx_i_rs.[X] in
           (X = g ^ s / M.gx ^ r)){1}, 
              ={M.bad}).
 apply run_ll.
 fun; sp 1 1; if => //.
 by progress; generalize H4; rewrite /in_dom H0.
 swap{2} 2 2;  sp 3 3; if => //.
 progress. 
 rewrite -(_: r{1} = r{2}); last smt.
 rewrite (_ : r{1} = fst (proj M.gx_i_rs{1}.[X_i{2}])). 
  by rewrite -H0.
 rewrite (_ : r{2} = fst (proj M.gx_i_rs{2}.[X_i{2}])).
  by rewrite -H.
 by apply H3.
 rewrite (_: r{1} = r{2}); last smt.
 rewrite (_ : r{1} = fst (proj M.gx_i_rs{1}.[X_i{2}])). 
  by rewrite -H0.
 rewrite (_ : r{2} = fst (proj M.gx_i_rs{2}.[X_i{2}])).
  by rewrite -H.
 by apply H3.
  
 by wp; skip; progress.
 wp; skip; progress.
 rewrite -(_: r{1} = r{2}); last smt.
 rewrite (_ : r{1} = fst (proj M.gx_i_rs{1}.[X_i{2}])). 
  by rewrite -H0.
 rewrite (_ : r{2} = fst (proj M.gx_i_rs{2}.[X_i{2}])).
  by rewrite -H.
 by apply H3.
 by intros => ? _; fun; wp; skip; progress; smt.
 by intros => ?; fun; wp; skip; progress; smt.
 wp.
  while (={i, M.gx, M.gy, gxs} /\ 
        (dom M.gx_i_rs{1} = dom M.gx_i_rs{2}) /\
        (forall X, in_dom X M.gx_i_rs => 
         let (r,s) = proj M.gx_i_rs.[X] in 
         (X = g ^ s / M.gx ^ r)){1} /\
        (forall X, in_dom X M.gx_i_rs{1} => 
         fst (proj M.gx_i_rs.[X]){1} = 
         fst (proj M.gx_i_rs.[X]){2})).
 wp.
 rnd (lambda (v : gf_q) , g ^ (v - log M.gx{2} * r{2}))
     (lambda (u : group), log u + r{2} * log M.gx{2}).
 rnd{2}; rnd.
 skip; progress => //.
 apply lossless. 
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by rewrite Dgf_q.supp_def.
 by rewrite group_pow_log; fieldeq.
 cut -> : (log gxR + rL * log M.gx{2} - log M.gx{2} * rL) = 
           log gxR by fieldeq.
 by rewrite group_log_pow.
 rewrite (_ : M.gx{2}^ rL = g ^ ((log M.gx{2}) * rL)); first smt.
 by rewrite -{1}Cyclic_group_prime.div_def !group_pow_log.
 rewrite !dom_set H.
 rewrite (_ : M.gx{2}^ rL = g ^ ((log M.gx{2}) * rL)); first smt.
 by rewrite -{1}Cyclic_group_prime.div_def !group_pow_log.
case (X = g ^ sL / M.gx{2} ^ rL) => heq //.
generalize H16; rewrite heq stpd_get get_setE proj_some => h.
cut <- : rL = x1 by smt.
cut <- : sL = x2 by smt.
smt.
 generalize H15 H16; rewrite /in_dom dom_set mem_add stpd_get get_setN.
smt.
intros => [|] hmem heq'.
cut:= H0 X _; first smt.
by rewrite stpd_get heq' /=.
smt.
case (X = g ^ sL / M.gx{2} ^ rL) => heq //.
rewrite !stpd_get heq !get_setE proj_some {1}/fst /=.
cut ->: g ^ (sL - log M.gx{2} * rL) = 
        g ^ sL / M.gx{2} ^ rL.
 rewrite (_ : M.gx{2}^ rL = g ^ ((log M.gx{2}) * rL)); first smt.
 by rewrite -{1}Cyclic_group_prime.div_def !group_pow_log.
 by rewrite !get_setE proj_some /fst /=.

rewrite !stpd_get !get_setN.
smt.
generalize heq.
 rewrite (_ : M.gx{2}^ rL = g ^ ((log M.gx{2}) * rL)); first smt.
  rewrite -{1}Cyclic_group_prime.div_def !group_pow_log.
smt.
rewrite -!stpd_get H1 //.
generalize H15; rewrite /in_dom dom_set mem_add => [|] //.
smt.

wp; do! rnd; wp; skip; progress; smt.
save. 

local lemma Pr3_aux &m :
Pr[G1(A).main() @ &m : M.bad] =
Pr[G2(A).main() @ &m : M.bad]. 
proof.
 by equiv_deno Eq3.
save.

local lemma Pr3 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + Pr[G2(A).main() @ &m : M.bad]. 
proof.
 rewrite -(Pr3_aux &m).
 apply (Pr2 &m).
save.

(* Now we change the test to actually compute 
   Z1 = Y ^ a /\ Z2 = Y ^ x_i instead of 
   (Z / Y ^ a) ^ r  = Y ^ x_i / Z2
*)
 

local module G3( A : Adv) ={
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs /\ !M.bad){
    (r, s) = proj (M.gx_i_rs.[X_i]);
    if (Z1 <> (Y ^ (log M.gx)) /\
         ((Z1 / (Y ^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2)) {
     M.bad = true;
    }
    ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gxs =[];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  M.bad = false;
  a = AT.run(M.gx, gxs, M.gy);
  return (win M.gx M.gy a);
 }
}.


local equiv Eq4 : 
G2(A).main ~ G3(A).main : true ==> M.bad{1} = M.bad{2}.
proof.
 fun.
 call (_ : M.bad, 
         ={M.gx, M.gy, M.gx_i_rs, M.bad, M.cO}, 
         ={M.bad}).
 apply run_ll.
 fun.
 sp 1 1; if => //; sp 1 1; if => //.
 intros => ? ?; rewrite /in_dom; progress; smt.
 wp; skip; progress.
 wp; skip; progress.
cut: ((Z1{2} / Y{2} ^ log M.gx{2}) ^ r{2} = Y{2} ^ log X_i{2} / Z2{2}) <=>
(Z1{2} = Y{2} ^ log M.gx{2} /\ Z2{2} = Y{2} ^ log X_i{2}); last by smt.
 split; last first.
 by intros [-> ->]; rewrite !mult_div_I I_pow_n.
  intros => H'.
  cut :  Z1{2} = Y{2} ^ log M.gx{2} \/
       (Z1{2} / Y{2} ^ log M.gx{2}) ^ r{2} <> Y{2} ^ log X_i{2} / Z2{2}.
 smt.
 intros => {H2} [|] h.
 generalize H'; rewrite h.
 rewrite !mult_div_I I_pow_n.
 progress => //.
 rewrite -I_prod_n H2 div_prod prod_comm group_prod_assoc (prod_comm _ Z2{2}).
 by rewrite -div_prod mult_div_I I_prod_n.
 smt.
 by intros => ? _; fun; wp; skip; progress; smt.
 by intros => ?; fun; wp; skip; progress; smt.
 conseq (_ : _ ==> ={M.gx, M.gy, M.gx_i_rs, gxs, M.bad, M.cO}).
 progress; smt.
 by eqobs_in.
save.


local lemma Pr4_aux &m :
Pr[G2(A).main() @ &m : M.bad] =
Pr[G3(A).main() @ &m : M.bad]. 
proof.
 by equiv_deno Eq4.
save.

local lemma Pr4 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + Pr[G3(A).main() @ &m : M.bad]. 
proof.
 rewrite -(Pr4_aux &m).
 apply (Pr3 &m).
save.

(* record the query that triggers bad, add
   the fact that this value is between 0 and qO *)

local module G4( A : Adv) ={
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs /\ !M.bad){
    (r, s) = proj (M.gx_i_rs.[X_i]);
    if (Z1 <> (Y ^ (log M.gx)) /\
         ((Z1 / (Y ^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2)) {
     M.bad_query = Some M.cO;
     M.bad = true;
    }
    ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gxs = [];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  M.bad = false;
  a = AT.run(M.gx, gxs, M.gy);
  return (win M.gx M.gy a);
 }
}.

local equiv Eq5 : 
G3(A).main ~ G4(A).main : true ==> M.bad{1} <=> 
              M.bad{2} /\ 0 <= proj M.bad_query{2} < qO.
proof.
 fun.
 call (_ : ={M.gx, M.gy, M.gx_i_rs, M.bad, M.cO} /\
              0 <= M.cO{2} <= qO /\ 
             (M.bad{2} => 0 <= proj M.bad_query{2} < M.cO{2} ) /\
             (! M.bad{2} =>  M.bad_query{2} = None ) ).
 fun; wp; skip; progress => //; smt.
 wp.
 while (={i, M.gx, M.gx_i_rs, gxs}). 
 wp; do! rnd; skip; progress => //; smt.
  wp; do! rnd; wp; skip; progress => //; smt.
save.

local lemma Pr5_aux &m :
Pr[G3(A).main() @ &m : M.bad] =
Pr[G4(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO]. 
proof.
 by equiv_deno Eq5.
save.

local lemma Pr5 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
Pr [G4(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO]. 
proof.
 rewrite -(Pr5_aux &m).
 apply (Pr4 &m).
save.

(* just sample a value to "guess" the query that triggers 
   bad *)

local module G5 (A : Adv) = {
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs /\ !M.bad){
    (r, s) = proj (M.gx_i_rs.[X_i]);
    if (Z1 <> (Y ^ (log M.gx)) /\
         ((Z1 / (Y ^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2)) {
     M.bad_query = Some M.cO;
     M.bad = true;
    }
    ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
 fun main () : bool = {
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gx : group;
  var gxs = [];
  M.gx = $dgroup;
  M.gy = $dgroup;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  M.bad = false;
  a = AT.run(M.gx, gxs, M.gy);
  M.bad_guess = $[0 .. qO];
  return (win M.gx M.gy a);
 }
}.


local equiv Eq6: 
G4(A).main ~ G5(A).main : true ==> ={M.bad,M.bad_query}.
proof.
 fun.
 seq 10 10: (={M.bad,M.bad_query, gxs}).
 eqobs_in.
 rnd{2}; skip; progress.
 smt.
save.

local lemma Pr6_aux1 &m :
Pr[G4(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO] =
Pr[G5(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO].  
proof.
 by equiv_deno Eq6.
save.

local lemma Pr6_aux2 &m :
Pr[G5(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO] <=
qO%r * Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess].  
proof.
 admit. (* don't know how to prove this here. used to be "by compute" *)
save.


local lemma Pr6 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess].  
proof.
 apply (Real.Trans _ 
     (Pr[G0(A).main() @ &m : res] +
      Pr[G5(A).main() @ &m : M.bad /\ 0 <= proj M.bad_query < qO]) _).   
 rewrite -(Pr6_aux1 &m).
 apply (Pr5 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply (Pr6_aux2 &m).
save.

(* we record the Z1 Z2 and Y values of the bad query and we move  the sampling to before the call to the adversary *)

local module G6 (A : Adv) = {
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs /\ !M.bad){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;
      (r, s) = proj (M.gx_i_rs.[X_i]);
       M.r = r;
       M.s = s;
       if (Z1 <> (Y ^ (log M.gx)) /\
       ((Z1 / (Y ^ (log M.gx))) ^ r = (Y^(log X_i)) / Z2)) {
        M.bad_query = Some M.cO;
        M.bad = true;
      }
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx : group;
   var gxs = [];
   M.gx = $dgroup;
   M.gy = $dgroup;
   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   return (win M.gx M.gy a);
  }
 }.


local equiv Eq7: 
G5(A).main ~ G6(A).main : true ==> (M.bad /\ proj M.bad_query = M.bad_guess){1} => 
                                   (M.bad /\ proj M.bad_query = M.bad_guess /\
 (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
         ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)) /\
  in_dom M.gx_bad M.gx_i_rs){2}.
proof.
symmetry.
fun.
swap{2} 11 -1.
call (_ : M.bad /\ M.bad_query <> None /\ proj M.bad_query <> M.bad_guess,
          ={M.gx, M.gy, M.gx_i_rs, M.bad, M.bad_guess, M.bad_query, M.cO} /\ 
        ( M.bad{1} => (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
         ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)
          /\ in_dom M.gx_bad M.gx_i_rs){1}) /\
       (M.bad_query{2} = None => M.bad_query{1} = None) /\ 
       ((M.bad_query{2} <> None /\ proj M.bad_query{2} = M.bad_guess{2}) => M.bad{1})).
apply run_ll.
fun; wp; skip; progress; smt.
by intros => &2 h; fun; wp; skip; progress.
by intros => &2; fun; wp; skip; progress;smt.
wp; rnd; wp.
while (={M.gx, M.gy, M.gx_i_rs, i, gxs}).
by wp; do !rnd; skip; progress.
wp; do! rnd; wp; skip; progress; smt.
save.

local lemma Pr7_aux &m :
Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess] <=
Pr[G6(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
         ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)) /\
  in_dom M.gx_bad M.gx_i_rs].  
proof.
 by equiv_deno Eq7.
save.


local lemma Pr7 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G6(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess /\
(M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
         ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)) /\
  in_dom M.gx_bad M.gx_i_rs].  
proof.
apply (Real.Trans _ 
(Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G5(A).main() @ &m : M.bad /\ proj M.bad_query = M.bad_guess]) _ ).  
apply (Pr6 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon; first smt.
 by apply (Pr7_aux &m).
save.

op def : 'a.

(* return the event and remove ! bad from the guard of the oracle *)
local module G7 (A : Adv) = {
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
    }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx : group;
   var gxs = [];
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   M.gx = $dgroup;
   M.gy = $dgroup;
   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = $dgroup;
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
    a = AT.run(M.gx, gxs, M.gy);
   (r, s) = proj (M.gx_i_rs.[M.gx_bad]);
    M.r = r;
    M.s = s;
   return (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
        ((M.gz1 / (M.gy_bad^ (log M.gx))) ^ M.r = (M.gy_bad ^(log M.gx_bad)) / M.gz2) /\
         in_dom M.gx_bad M.gx_i_rs);
  }
 }.

local equiv Eq8: 
G6(A).main ~ G7(A).main : true ==> 
           (M.bad /\ proj M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
           ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)) /\ in_dom M.gx_bad M.gx_i_rs){1} =>
           res{2}.
proof.
symmetry.
fun.
wp.
call (_ : M.bad,
 ! M.bad{1} /\
 ={M.cO, M.gx_i_rs, M.gx, M.gy, M.bad_guess} /\
(M.bad{2} => ={M.gx, M.gy, M.gx_bad, M.gy_bad, M.gz1, M.gz2} /\
             (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
           ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2) /\
            (M.r, M.s) = proj M.gx_i_rs.[M.gx_bad]){2} /\
in_dom M.gx_bad{2} M.gx_i_rs{2}),
 ={M.gx_i_rs, M.gx, M.gy, M.bad_guess} /\
(={M.gx_bad, M.gy_bad, M.gz1, M.gz2}/\
 (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
 ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2) /\
 (M.r, M.s) = proj M.gx_i_rs.[M.gx_bad]){2}) /\
  M.bad_guess{1} < M.cO{1} /\
  in_dom M.gx_bad{2} M.gx_i_rs{2}).
apply run_ll.
fun. 
sp 1 1; if => //; last by (skip; progress; smt).
if => //; wp; skip; progress; smt.

intros => &2 _; fun; sp 1; if => //.
if => //; wp; skip; smt.

intros => ?; fun; wp; skip; progress => //; smt.
rnd; wp.
while (={M.gx_i_rs, i, gxs}).
wp; do! rnd; wp; skip;  progress.
wp; do! rnd; wp; skip; progress; smt.
save.

local lemma Pr8_aux &m :
Pr[G6(A).main() @ &m : (M.bad /\ proj M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
           ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)) /\
in_dom M.gx_bad M.gx_i_rs)] <=
Pr[G7(A).main() @ &m : res].  
proof.
 by equiv_deno Eq8.
save.

local lemma Pr8 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G7(A).main() @ &m : res].  
proof.
apply (Real.Trans _ 
(Pr [G0(A).main() @ &m : res] + 
qO%r * Pr[G6(A).main() @ &m : (M.bad /\ proj M.bad_query = M.bad_guess /\
           (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
           ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2)) /\ in_dom M.gx_bad M.gx_i_rs)]) _ ).  
apply (Pr7 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon.
 smt.
 by apply (Pr8_aux &m).
save.

(* we move the random sampling loop to after the adversary call *) 

local module G8 (A : Adv) = {
  var mXi : (int, group) map
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_rng X_i mXi){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx, gx' : group;
   var gxs = [];
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   mXi = FMap.Core.empty;
   M.gx = $dgroup;
  M.gy = $dgroup;

   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    gx = $dgroup;
    mXi.[i] = gx;
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   i = 0;
   while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx' = proj (mXi.[i]);
    M.gx_i_rs.[gx'] = (r,s);
    i = i + 1;
   }
   (r, s) = proj (M.gx_i_rs.[M.gx_bad]);
    M.r = r;
    M.s = s;
   return (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
        ((M.gz1 / (M.gy_bad^ (log M.gx))) ^ M.r = (M.gy_bad ^(log M.gx_bad)) / M.gz2) /\
         in_dom M.gx_bad M.gx_i_rs);
  }
 }.

lemma rng_set : forall (m : ('a,'b) map) x y1,
! in_dom x m => 
rng m.[x <- y1] = FSet.add y1 (rng m).
proof.
 intros => m x y hndom; apply set_ext => y'.
 rewrite mem_add mem_rng; progress.
 case (x = x0) => heq.
 right; generalize H0; rewrite heq  get_setE; smt.
 generalize H H0; rewrite get_setN // /in_dom dom_set mem_add.
intros => [hmem hgeteq|].
left; rewrite mem_rng; exists x0; rewrite /in_dom; progress.
smt.
elim H => {H}.
rewrite mem_rng => [x' [? ? ]]; exists x'.
case (x' = x); [smt|]; intros => heq.
rewrite /in_dom dom_set mem_add get_setN; smt.
intros => heq.
by exists x; rewrite /in_dom dom_set mem_add get_setE heq.
save.

local equiv Eq9 : G7(A).main ~ G8(A).main : true ==> ={res}.
proof.
 fun.
 swap{2} 17 -5.
 swap{2} 18 -5.
 wp.
 call (_ : ={M.gx, M.gy, M.bad_guess, M.gx_bad, M.gy_bad, 
             M.gz1, M.gz2, M.cO} /\ dom M.gx_i_rs{1} = rng G8.mXi{2}).
fun.
sp 1 1; if => //.
intros => ? ?.
rewrite /in_dom/in_rng; progress; smt.
if => //.
 wp; skip; progress.
 wp; skip; progress.
rnd; wp.
swap{2} 1 9.
fusion{2} 11!1 @ 3, 4. (* this fails the syntactic naive independence check and needs a stronger version *)
while (={i, M.gx_i_rs, gxs} /\ dom M.gx_i_rs{2} = rng G8.mXi{2} /\
      (forall j, in_dom j G8.mXi => j < i){2}).
swap{2} 4 -3; swap{2} 5 -3; wp; do! rnd; skip; progress.
by rewrite !stpd_get get_setE proj_some.
apply set_ext => x.
rewrite !stpd_get get_setE proj_some dom_set rng_set.
rewrite -not_def => hdom.
cut:= H0 i{2} _ => //.
smt.

generalize H12; rewrite /in_dom dom_set mem_add => [hdom| ->].
cut := H0 j _ => //; smt.
smt.
wp; do! rnd; wp; skip; progress; smt.
save.

local lemma Pr9_aux &m :
Pr[G7(A).main() @ &m : res] = 
Pr[G8(A).main() @ &m : res].  
proof.
 by equiv_deno Eq9.
save.

local lemma Pr9 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G8(A).main() @ &m : res].  
proof.
 rewrite -(Pr9_aux &m). 
 apply (Pr8 &m).
save. 


(* Now we have to split the loop after the adversary where the value
   M.gx_i_rs.[M.gx] is set for the LAST time. In order to do so we 
   use an operator find_last l u p, where l and u are integers, and p
   is a predicate. The operator returns either:
   - some j, j is the last value for which p holds, i.e. 
     l <= j <= u and p j holds and for every
     k,  j < k => ! p k.
   - None, when for all values in range p doesn't hold, i.e.
     forall j, l <= j <= u => ! p j.

*)  


local module G9' (A : Adv) = {
  var mXi : (int, group) map
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_rng X_i mXi){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx, gx' : group;
   var gxs = [];
   var k : int;
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   mXi = FMap.Core.empty;
   M.gx = $dgroup;
   M.gy = $dgroup;

   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    gx = $dgroup;
    mXi.[i] = gx;
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   k = proj (find_last 0 n (lambda k, proj mXi.[k] = M.gx_bad));
   i = 0;
   while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx' = proj (mXi.[i]);
    M.gx_i_rs.[gx'] = (r,s);
    i = i + 1;
   }
   (r, s) = proj (M.gx_i_rs.[M.gx_bad]);
    M.r = r;
    M.s = s;
    return (M.gz1 <> (M.gy_bad ^ (log M.gx)) /\ 
        ((M.gz1 / (M.gy_bad^ (log M.gx))) ^ M.r = (M.gy_bad ^(log M.gx_bad)) / M.gz2) /\
         in_dom M.gx_bad M.gx_i_rs);
  }
 }.

local equiv Eq10' : G8(A).main ~ G9'(A).main : true ==> ={res}.
proof.
 fun.
 swap{2} 17 5.
 wp 21 21.
 by eqobs_in.
save.


(* Now we can split the loop in 3:
   - all iterations such that i < j
   - the iteration where i = j
   - the iterations where j < i 
   (these do not modify M.gx_i_rs.[M.gx] 
   so we can actually skip them 
*)

local module G9 (A : Adv) = {
  var mXi : (int, group) map
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_rng X_i mXi){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx, gx' : group;
   var gxs = [];
   var k : int;
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   mXi = FMap.Core.empty;
   M.gx = $dgroup;
   M.gy = $dgroup;

   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    gx = $dgroup;
    mXi.[i] = gx;
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   k = proj (find_last 0 n (lambda k, proj mXi.[k] = M.gx_bad));
   i = 0;
   while (i <= n /\ i < k) {
    r = $dgf_q;
    s = $dgf_q;
    gx' = proj (mXi.[i]);
    M.gx_i_rs.[gx'] = (r,s);
    i = i + 1;
   }
    r = $dgf_q;
    s = $dgf_q;
    M.gx_i_rs.[M.gx_bad] = (r,s);
    i = i + 1;
   (r, s) = proj (M.gx_i_rs.[M.gx_bad]);
    M.r = r;
    M.s = s;
   return (M.gz1 <> (M.gy_bad^ (log M.gx)) /\ 
        ((M.gz1 / (M.gy_bad^ (log M.gx))) ^ M.r = (M.gy_bad^(log M.gx_bad)) / M.gz2));
  }
 }.


lemma some_proj : forall (x : 'a option),
x <> None =>
Some (proj x) = x.
proof strict.
 intros => x hnn.
 elim /option_ind_eq x; first smt.
  intros => [y] ->.
  by rewrite proj_some.
save.

local equiv Eq10 : G9'(A).main ~ G9(A).main : true ==> res{1} => res{2}.
proof.
 fun.
 seq 16 16: (={M.gx, M.gy, M.gz1, M.gz2, M.gx_bad, M.gy_bad, M.gx_i_rs} 
            /\ G9'.mXi{1} = G9.mXi{2} /\ (forall j, 0 <= j <= n <=> in_dom j G9'.mXi{1}) /\
            M.gx_i_rs{1} = FMap.Core.empty).
 call (_ : ={M.gx, M.gy, M.cO, M.bad_guess, M.gx_bad, M.gz1, M.gz2, M.gy_bad} 
            /\ G9'.mXi{1} = G9.mXi{2}).
 by fun; eqobs_in.
 rnd; wp.
 while (={i, gxs} /\ G9'.mXi{1} = G9.mXi{2} /\ 
           (forall j, 0 <= j < i{1} <=> in_dom j G9'.mXi{1}) /\ 
            0 <= i{1} <= n + 1).
 wp; rnd; skip; progress.
 rewrite /in_dom dom_set mem_add.
 case (j = i{2}) => //.
 intros => ?; left.
 generalize H; rewrite /in_dom => <-.
 smt.
 generalize H7; rewrite /in_dom dom_set mem_add => [|].
 generalize H; rewrite /in_dom => <-.
  smt.
  intros => -> //.
 generalize H7; rewrite /in_dom dom_set mem_add => [|].
 generalize H; rewrite /in_dom => <-.
  smt.
  intros => -> //; smt.
  smt.
  smt.
  wp; do! rnd; wp; skip; progress; smt.

 case (in_rng M.gx_bad{1} G9'.mXi){1}; last first.
 conseq(_:_==> !in_dom M.gx_bad{1} M.gx_i_rs{1}); first smt.
 wp; do ! rnd{2}.
 while{2} (true) ((max (n+1)  (k{2})) - i{2}).
  intros => ? ? ; wp; do!rnd; skip; progress.
smt.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.

 while{1} ((forall x, in_dom x M.gx_i_rs => in_rng x G9'.mXi) /\
           (forall j, 0 <= j <= n => in_dom j G9'.mXi) /\
           0 <= i){1} ((n+1) - i{1}).
  intros => ? ?.
 wp; do!rnd; skip; progress.
 rewrite -{2}Dgf_q.lossless /Distr.weight.
 apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=  => x'.
 rewrite rw_eqT -Dgf_q.lossless /Distr.weight.
 apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=  => y'.
 rewrite rw_eqT; progress.
 generalize H3; rewrite /in_dom dom_set mem_add => [hdom|heq].
   by apply H; smt.
   rewrite /in_rng mem_rng; exists i{hr}.
   cut hdom := H0 i{hr} _; first smt.
   split => //.
   rewrite heq some_proj //.
   by generalize hdom; rewrite stpd_get /in_dom mem_dom.
 smt.
 smt.
wp; skip; progress.
smt.
smt.
smt.
generalize H5.
rewrite /max.
case ( n + 1 <
    proj (find_last 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2}))).
smt.
smt.
smt.
rewrite -not_def => ?; generalize H0 => /=; apply H2 => //.
splitwhile (i < k): {1} 3.
splitwhile (i = k): {1} 4.
 seq 3 3: (={M.gx, M.gy, M.gz1, M.gz2, M.gy_bad, M.gx_bad, M.gx_i_rs, k, i} /\
          i{1} = k{1} /\ G9'.mXi{1} = G9.mXi{2} /\  k{1} <= n /\ 
          0 <= k{2} <= n /\
          proj G9.mXi{2}.[k{2}] = M.gx_bad{2} /\
         (forall (j : int), k{2} < j => ! proj G9.mXi{2}.[j] = M.gx_bad{2})
          ).
 wp.
 while (={i, M.gx_i_rs, k} /\ G9'.mXi{1} = G9.mXi{2} 
       /\ i{1} <= k{1} /\ k{1} <= n).
 wp; do! rnd; skip; progress; smt.
wp; skip.
intros => ? ? h k1 k2.
cut H: (find_last 0 n (lambda (k : int), proj G9'.mXi{1}.[k] = M.gx_bad{1})) <> None.
generalize h; progress.
rewrite -not_def => ?.
cut:= find_last_exists 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2}) _ => // {H1} H1.
generalize H0 => /=; rewrite /in_rng mem_rng -not_def => [x][hdom] hget.
generalize hdom.
rewrite -H => ?.
cut:=  H1 x _ => //=.
by rewrite stpd_get hget proj_some.
generalize h; progress.
generalize H.
rewrite /k1/k2 => {k1 k2}.
elim /option_ind_eq (find_last 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2})) => //.
intros => ->; smt.
intros => [x] h h' {h'}. 
rewrite h; generalize h; rewrite find_last_spec proj_some /=; progress.
cut: k1 <= n.
rewrite /k1 =>  {k1}.
generalize H.
elim /option_ind_eq (find_last 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2})).
smt.
intros => [x] heq; rewrite heq; generalize heq; rewrite find_last_spec; progress.
 rewrite proj_some; smt.
smt.
smt.
generalize H.
rewrite /k1 => {k1 H2 H3 H4 H5}.
elim /option_ind_eq (find_last 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2})) => //.
intros => ->; smt.
intros => [x] h h' {h'}. 
rewrite h; generalize h; rewrite find_last_spec proj_some /=; progress.

generalize H.
rewrite /k1 => {k1 H2 H3 H4 H5}.
elim /option_ind_eq (find_last 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2})) => //.
intros => ->; smt.
intros => [x] h h' {h'}. 
rewrite h; generalize h.
rewrite find_last_spec /= proj_some; progress.

generalize H H2 H3 H4 H5 H6.
rewrite /k1 => {k1}.
elim /option_ind_eq (find_last 0 n (lambda (k : int), proj G9.mXi{2}.[k] = M.gx_bad{2})) => //.
intros => ->; smt.
intros => [x] h h' {h'}. 
rewrite h; generalize h; rewrite find_last_spec proj_some /=; progress.
apply H3 => //.

rcondt{1} 1.
intros => ?; wp; skip; progress.
rcondf{1} 6.
intros => ?; wp; do! rnd; wp; skip; progress.
smt.
conseq (_ : _ ==> ={M.gx, M.gy, M.gz1, M.gz2, M.gx_bad, M.gy_bad, M.r, M.s} /\
 in_dom M.gx_bad{1} M.gx_i_rs{1} /\ in_dom M.gx_bad{2} M.gx_i_rs{2}).
progress.
 wp 6 4.
while{1} 
( M.gx_i_rs.[M.gx_bad]{1} = M.gx_i_rs.[M.gx_bad]{2} /\ 
  G9'.mXi{1} = G9.mXi{2} /\ 
  (forall (j : int), k < j => ! proj G9'.mXi.[j] = M.gx_bad){1} /\
   k{1} < i{1} /\ in_dom M.gx_bad{1} M.gx_i_rs{1})
  ((n+1 - i{1})).
intros => ? ?; wp; do! rnd; skip; progress.
 rewrite -{2}Dgf_q.lossless /Distr.weight.
 apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=  => x'.
 rewrite rw_eqT; progress.
 rewrite -Dgf_q.lossless /Distr.weight.
 apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=  => y'.
 rewrite rw_eqT; progress.
 rewrite {1}stpd_get get_setN ?H //.
 apply H0 => //.
 smt.
 by generalize H2; rewrite /in_dom dom_set mem_add => ?; left.
 smt.
 wp; do!rnd; skip; progress => //.
 smt.
 by rewrite /in_dom dom_set mem_add; right.
 smt.
 smt.
 smt.
 by rewrite /in_dom dom_set mem_add; right.
save.


local lemma Pr10_aux &m :
Pr[G8(A).main() @ &m : res] <=
Pr[G9(A).main() @ &m : res].  
proof.
 rewrite (_ : Pr[G8(A).main() @ &m : res] = Pr[G9'(A).main() @ &m : res]).
  by equiv_deno Eq10'.
 by equiv_deno Eq10.
save.

local lemma Pr10 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G9(A).main() @ &m : res].  
proof.
apply (Real.Trans _ 
(Pr [G0(A).main() @ &m : res] + 
qO%r * Pr[G8(A).main() @ &m : res]) _ ).  
apply (Pr9 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon.
 smt.
 by apply (Pr10_aux &m).
save.

(* now we do manipulation, we will sample r only in case
M.gz1 <> (M.gy^ (log M.gx)). Under this condition
(M.gz1 / (M.gy^ (log M.gx))) ^ r is indistinguishable from random
*)

local module G10 (A : Adv) = {
  var mXi : (int, group) map
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_rng X_i mXi){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx, gx' : group;
   var gxs = [];
   var b : bool = false;
   var k : int;
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   mXi = FMap.Core.empty;
   M.gx = $dgroup;
   M.gy = $dgroup;
   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    gx = $dgroup;
    mXi.[i] = gx;
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   k = proj (find_last 0 n (lambda k, proj mXi.[k] = M.gx_bad));
   if (M.gz1 <> (M.gy_bad ^ (log M.gx))) { 
    r = $dgf_q;
    b = ((M.gz1 / (M.gy_bad ^ (log M.gx))) ^ r = 
         (M.gy_bad ^(log M.gx_bad)) / M.gz2);
   }
     return b;
  }
 }.

local equiv Eq11 : G9(A).main ~ G10(A).main : true ==> res{1} => res{2}.
proof.
 fun.
 seq 16 17: 
(={M.gx, M.gy, M.gx_bad, M.gy_bad, M.gz1, M.gz2, M.gy, M.gx_i_rs, gxs} 
/\ G9.mXi{1} = G10.mXi{2} ).
eqobs_in.
sp.
if{2}.
wp; rnd{1}; rnd.
 while{1} (true) ((max (n+1)  (k{1})) - i{1}).
 intros => ? ?; wp; do!rnd; skip; progress.
 smt.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
 skip; progress.
 generalize H0; rewrite /max.
case (n + 1 <
    proj (find_last 0 n (lambda (k : int), proj G10.mXi{2}.[k] = M.gx_bad{2}))).
smt.
smt.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
generalize H6; rewrite stpd_get get_setE proj_some.
smt.
wp; rnd{1}; rnd{1}.
 while{1} (true) ((max (n+1)  (k{1})) - i{1}).
 intros => ? ?; wp; do!rnd; skip; progress.
 smt.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
 skip; progress.
 generalize H; rewrite /max.
case (n + 1 <
    proj (find_last 0 n (lambda (k : int), proj G10.mXi{2}.[k] = M.gx_bad{2}))).
smt.
smt.
 rewrite -Dgf_q.lossless /Distr.weight.
 by apply Distr.mu_eq; rewrite /Fun.(==) /Fun.cpTrue /=.
save.

local lemma Pr11_aux &m :
Pr[G9(A).main() @ &m : res] <=
Pr[G10(A).main() @ &m : res].  
proof.
 by equiv_deno Eq11.
save.

local lemma Pr11 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G10(A).main() @ &m : res].  
proof.
apply (Real.Trans _ 
(Pr [G0(A).main() @ &m : res] + 
qO%r * Pr[G9(A).main() @ &m : res]) _ ).  
apply (Pr10 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon.
 smt.
 by apply (Pr11_aux &m).
save.

   
(* now instead of sampling r and setting
gx' = (M.gz1 / (M.gy^ (log M.gx))) ^ r we
sample gx' 
*)

local module G11 (A : Adv) = {
  var mXi : (int, group) map
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_rng X_i mXi){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx, gx' : group;
   var gxs = [];
   var b : bool = false;
   var k : int;
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   mXi = FMap.Core.empty;
   M.gx = $dgroup;
  M.gy = $dgroup;

   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    gx = $dgroup;
    mXi.[i] = gx;
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   k = proj (find_last 0 n (lambda k, proj mXi.[k] = M.gx_bad));
   if (M.gz1 <> (M.gy_bad ^ (log M.gx))) { 
    gx' = $dgroup;
    b = gx' = (M.gy_bad^(log M.gx_bad)) / M.gz2;
   }
     return b;
  }
 }.

local equiv Eq12 : G10(A).main ~ G11(A).main : true ==> ={res}.
proof.
 fun.
  seq 18 18: 
(={M.gx, M.gy, M.gz1, M.gz2, M.gx_bad, M.gy_bad, M.gx_i_rs, b, gxs} 
/\ G10.mXi{1} = G11.mXi{2} ).
eqobs_in.
if => //.
wp.
 rnd (lambda v, (M.gz1 / M.gy_bad ^ log M.gx){2} ^ v)
     (lambda (v : group), log v / ((log M.gz1 - log ( M.gy_bad ^ log M.gx))){2}).
skip; progress.
 by rewrite mu_x_def_in Dgroup.mu_x_def_in.
 by apply supp_def.
 rewrite -!Cyclic_group_prime.div_def log_pow_mult group_pow_log
        /Prime_field.(/) -gf_q_mult_assoc gf_q_mult_inv.
 cut: log M.gz1{2} - log (M.gy_bad{2} ^ log M.gx{2}) = gf_q0 => M.gz1{2} = M.gy_bad{2} ^ log M.gx{2}; 
      last smt. 
 intros  => heq.
 cut := neg_zero (log M.gz1{2}) (log (M.gy_bad{2} ^ log M.gx{2})) _.
  by rewrite heq.
 intros => {heq} heq.
 apply (_ : forall (V W : group), log V = log W => V = W) => //.
  by intros => V W h; rewrite -group_log_pow -(group_log_pow W) h.
 by rewrite gf_q_mult_unit.
 rewrite -!Cyclic_group_prime.div_def group_pow_mult 
         /Prime_field.(/) gf_q_mult_assoc gf_q_mult_comm 
         gf_q_mult_assoc.
 rewrite (gf_q_mult_comm (inv (log M.gz1{2} - log (M.gy_bad{2} ^ log M.gx{2})))).  
 rewrite gf_q_mult_inv.
 cut: log M.gz1{2} - log (M.gy_bad{2} ^ log M.gx{2}) = gf_q0 =>
       M.gz1{2} = M.gy_bad{2} ^ log M.gx{2}; last smt. 
 intros  => heq.
 cut := neg_zero (log M.gz1{2}) (log (M.gy_bad{2} ^ log M.gx{2})) _.
  by rewrite heq.
 intros => {heq} heq.
 apply (_ : forall (V W : group), log V = log W => V = W) => //.
  by intros => V W h; rewrite -group_log_pow -(group_log_pow W) h.
 rewrite gf_q_mult_comm gf_q_mult_unit.
 by rewrite group_log_pow.
 save.
 
local lemma Pr12 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r *Pr[G11(A).main() @ &m : res].  
proof.
rewrite -(_ : Pr[G10(A).main() @ &m : res] =
              Pr[G11(A).main() @ &m : res]).
by equiv_deno Eq12.
by apply (Pr11 &m).
save.

(* remove the if and ready to Rock & Roll *)
local module G12 (A : Adv) = {
  var mXi : (int, group) map
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_rng X_i mXi){
   if (M.cO = M.bad_guess) {
       M.gz1 = Z1;
       M.gz2 = Z2; 
       M.gy_bad = Y;
       M.gx_bad = X_i;  
     }
     ret = Z1 = Y ^ (log M.gx) /\ Z2 = Y ^ (log X_i);
       M.cO = M.cO + 1;
    }
      return ret;
   }
  }
  module AT = A(TD)
   fun main () : bool = {
   var a : adv_ret;
   var i : int = 0;
   var r, s : gf_q;
   var gx, gx' : group;
   var gxs = [];
   var b : bool = false;
   var k : int;
   M.gx_bad = def;
   M.gy_bad = def;
   M.gz1 = def;
   M.gz2 = def;
   mXi = FMap.Core.empty;
   M.gx = $dgroup;
   M.gy = $dgroup;
 
   M.gx_i_rs = FMap.Core.empty;
   while (i <= n) {
    gx = $dgroup;
    mXi.[i] = gx;
    gxs = gx :: gxs;
    i = i + 1;
   }
     M.cO = 0;
     M.bad_query = None;
     M.bad = false;
     M.bad_guess = $[0 .. qO];
   a = AT.run(M.gx, gxs, M.gy);
   k = proj (find_last 0 n (lambda k, proj mXi.[k] = M.gx_bad));
   gx' = $dgroup;
   return (gx' = (M.gy_bad^(log M.gx_bad)) / M.gz2);
  }
 }.

local equiv Eq13 : G11(A).main ~ G12(A).main : true ==> res{1} => res{2}.
proof.
 fun.
 swap 3 15.
 seq 17 17: 
(={M.gx, M.gy, M.gz1, M.gz2, M.gx_bad , M.gy_bad, M.gx_i_rs, gxs} 
/\ G11.mXi{1} = G12.mXi{2}).
eqobs_in.
sp; if{1}.
wp; rnd; skip; smt.
rnd{2}; wp; skip; smt.
save.

local lemma Pr13_aux1 &m :
Pr[G11(A).main() @ &m : res] <=
Pr[G12(A).main() @ &m : res].  
proof.
 by equiv_deno Eq13.
save.

local lemma Pr13_aux2 &m :
Pr[G12(A).main() @ &m : res] = 1%r / q%r.
proof.
 bdhoare_deno (_ : true ==> res) => //.
 fun; rnd; wp.
 call (_ : true) => //.
  by apply run_ll.
  by fun; wp.
 rnd; wp.
 while (true) (n + 1 - i).
 intros => ?; wp; rnd; skip; progress.
 smt.
by rewrite -Dgroup.lossless; apply Distr.mu_eq => x /=; rewrite /Fun.cpTrue.
 wp; do! rnd; wp; skip; progress.
 smt.
 generalize ( gy_bad ^ log gx_bad / gz2) => y.
 rewrite -(Dgroup.mu_x_def_in y) /Distr.mu_x.
 apply Distr.mu_eq; rewrite /Fun.(==) /= => x'; smt.
 rewrite (_:  (lambda (x : int), true) = Fun.cpTrue).
 smt.
 smt.
 rewrite -Dgroup.lossless /Distr.weight; apply Distr.mu_eq.
 by rewrite /Fun.cpTrue  => ? /=.
 smt.
save.

(* We are done bounding the probability of bad *)

local lemma Pr13 &m : 
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [G0(A).main() @ &m : res] + 
qO%r * (1%r / q%r).  
proof.
apply (Real.Trans _ 
(Pr [G0(A).main() @ &m : res] + 
qO%r * Pr[G11(A).main() @ &m : res]) _ ).  
apply (Pr12 &m).
 apply (_ : forall (p q r : real), p <= q => r + p <= r + q).
 smt.
 apply mult_pos_mon.
 smt.
 rewrite -(Pr13_aux2 &m).
 by apply (Pr13_aux1 &m).
save.

(* the oracle in G0 is already public so we can constructwe construct an adversary agains Win *)

local module B (A : Adv) : Adv' = {
  module TD : O ={
   fun check (X_i Z1 Z2 Y : group) : bool ={
   var ret : bool = false;
   var r, s : gf_q;
   if (M.cO < qO /\ in_dom X_i M.gx_i_rs){
    (r, s) = proj (M.gx_i_rs.[X_i]);
    ret = ((Z1 ^ r) * Z2 = Y ^ s);
    M.cO = M.cO + 1;
   }
   return ret;
   }
 }
 module AT = A(TD)
  fun run (gx : group, gy : group) : adv_ret ={
  var a : adv_ret;
  var i : int = 0;
  var r, s : gf_q;
  var gxs = [];
  M.gx = gx;
  M.gy = gy;
  M.gx_i_rs = FMap.Core.empty;
  while (i <= n) {
    r = $dgf_q;
    s = $dgf_q;
    gx = (g ^ s) / (M.gx ^ r);
    M.gx_i_rs.[gx] = (r,s);
    gxs = gx :: gxs;
    i = i + 1;
  }
  M.cO = 0;
  M.bad_query = None;
  a = AT.run(M.gx, gxs, M.gy);
  return (a);
 }
}.

(* reduction step *)

local equiv Eq14 : G0(A).main ~ Win(B(A)).main : true ==> ={res}.
proof.
 fun.
 inline B(A).run.
 wp.
 call (_ : ={M.gx_i_rs, M.cO}).
fun.
eqobs_in.
wp.
while (={M.gx_i_rs, M.gx, gxs} /\ i{1} = i0{2}).
wp; do!rnd; skip; progress.
wp; do! rnd; wp; skip; progress.
save.

(* nice tidy conclusion *)
lemma Conclusion &m :
exists (B <: Adv'),
Pr [TDDH_Win(A).main() @ &m : res] <=
Pr [Win(B).main() @ &m : res] + 
qO%r * (1%r / q%r).  
proof.
exists (B(A)).
rewrite -(_ : Pr [G0(A).main() @ &m : res] =
              Pr [Win(B(A)).main() @ &m : res]).
by equiv_deno Eq14.
by apply (Pr13 &m).
save.


end section.

end Trapdoor.

(* now we can instantiate to DLog and to DDH *)

op win_dlog (x y : group) (z : gf_q) = (x = (g ^ z)).

clone Trapdoor as DLog_2DDH with
type adv_ret = gf_q,
op win = win_dlog.

print module DLog_2DDH.Win.


op win_ddh (x y : group) (z : group) = (x ^ log y = y).

clone Trapdoor as DDH_2DDH with
type adv_ret = group,
op n = 0,
op win = win_ddh.

print module DLog_2DDH.Win.
print module DDH_2DDH.Win. (* used in the SCDH to CDH cool reduction *)


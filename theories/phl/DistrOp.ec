(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import List.
require export DistrF.
import Real Fun.

pragma +withbd.

(* -------------------------------------------------------------------- *)
lemma distr_ext (d1 d2 : 'a distr):
       (forall (f : 'a -> real), $[f | d1] = $[f | d2]) <=> d1 = d2.
proof. split=> //;apply eq_distr_ext. qed.

(* ----------------------------------------------------------------- *)
op PR (d:'a distr) (P:'a -> bool) = muf (fun x => b2r (P x)) d.
op weight (d:'a distr) = PR d predT. 

lemma PR_bounded (P:'a -> bool) (d:'a distr): 0%r <= PR d P <= 1%r.
proof. rewrite /PR -muf_b2r; smt. qed.

lemma weight_bounded (d:'a distr): 0%r <= weight d <= 1%r.
proof. rewrite /weight; apply PR_bounded. qed.

(* ----------------------------------------------------------------- *)
op dzero: 'a distr.
axiom dzero_def (f:'a->real): $[f | dzero] = 0%r.

lemma PR_dzero (P:'a -> bool): PR dzero P = 0%r.
proof. by rewrite /PR dzero_def. qed.

lemma w0_dzero (d:'a distr): weight d = 0%r <=> d = dzero.
proof.
  split => H;2:by rewrite H /weight /PR dzero_def.
  apply pw_eq => x. 
  rewrite /mu_x (muf_b2r _ dzero) dzero_def.
  cut : mu d ((=) x) <= 0%r; 2:smt.
  rewrite -H /mu_x /weight /PR muf_b2r;apply muf_le_compat=> /=.
  rewrite b2r_true=> x0 _; case (x = x0) => //.
qed.

(* ----------------------------------------------------------------- *)

op dunit : 'a -> 'a distr.
axiom dunit_def (f:'a -> real) a: $[f | dunit a] = f a.

lemma dunit_ll (a:'a) : weight (dunit a) = 1%r.
proof. by rewrite /weight /PR dunit_def. qed.

(* ----------------------------------------------------------------- *)

op dlet : 'a distr -> ('a -> 'b distr) -> 'b distr.
axiom dlet_def (d : 'a distr) (F:'a -> 'b distr) f: 
   $[f | dlet d F] = $[fun a => $[ f | F a] | d].

op dlift (F: 'a -> 'b distr) : 'a distr -> 'b distr = 
  fun d => dlet d F.

lemma nosmt dlet_d_unit (d:'a distr) : dlet d dunit = d.
proof. by apply eq_distr_ext=> f;rewrite dlet_def dunit_def. qed.

lemma nosmt dlet_unit (F:'a -> 'b distr) a : dlet (dunit a) F = F a.
proof. by apply eq_distr_ext=> f;rewrite dlet_def dunit_def. qed.

lemma dlet_dlet (d1:'a distr) (F1:'a -> 'b distr) (F2: 'b -> 'c distr):
  dlet (dlet d1 F1) F2 = dlet d1 (fun x1 => dlet (F1 x1) F2).
proof. by apply eq_distr_ext=> f;rewrite !dlet_def /= dlet_def. qed.

lemma dlet_dzero (F:'a -> 'b distr): dlet dzero F = dzero.
proof. by apply eq_distr_ext; rewrite dlet_def !dzero_def. qed.

lemma dlet_d_dzero (d:'a distr): dlet d (fun a => dzero<:'b>) = dzero.
proof. by apply eq_distr_ext; rewrite dlet_def !dzero_def muf_0. qed. 

lemma weight_dlet (d:'a distr) (F:'a -> 'b distr) : 
  weight (dlet d F) <= weight d.
proof.
  rewrite /weight /PR dlet_def;apply muf_le_compat => /= a Ha.
  rewrite -muf_b2r /predT b2r_true;smt.
qed.

(* -------------------------------------------------------------- *)
(* multiplication by a constant                                   *)
op d_compat (d:'a distr) (r:real) =  (0%r <= r <= 1%r/weight d \/ d = dzero).

lemma d_compat_inv_weight (d:'a distr): d_compat d (1%r/ weight d). 
proof.
  rewrite /d_compat; case (weight d = 0%r)=> Hw;1: by right;apply w0_dzero. 
  cut [H0w Hw1] := weight_bounded d. 
  left;split => //; smt.
qed.

lemma d_compat_1 (d:'a distr) r: 0%r <= r <= 1%r => d_compat d r.
proof. 
  rewrite /d_compat; case (weight d = 0%r);1: smt.
  cut := weight_bounded d; move:(weight d);smt.
qed.

lemma d_compat_weight (d:'a distr): d_compat d (weight d). 
proof. smt. qed.

lemma d_compat_dlet (d:'a distr) (F:'a -> 'b distr) r:
    d_compat d r => d_compat (dlet d F) r.
proof.
  rewrite /d_compat. 
  case (d = dzero); 1:by move=> ->;rewrite dlet_dzero. 
  rewrite -w0_dzero /=; cut := weight_dlet d F.
  case (dlet d F = dzero) => //.
  rewrite -w0_dzero /=; cut := weight_bounded d; cut := weight_bounded (dlet d F).
  move: (weight d) (weight (dlet d F)).
  progress. 
  admit.
qed.

op dmulc : real -> 'a distr -> 'a distr.
axiom dmulc_def (r:real) (d:'a distr) (f:'a -> real): 
  d_compat d r =>
  $[f | dmulc r d] = r * $[f | d].

lemma dmulc_dzero r : dmulc r dzero<:'a> = dzero.
proof. by apply eq_distr_ext => f;rewrite dmulc_def // dzero_def. qed.

lemma dmulc_0 (d:'a distr) : dmulc 0%r d = dzero.
proof. 
  apply eq_distr_ext => f;rewrite dmulc_def //. 
  + rewrite /d_compat. 
    case (weight d = 0%r);1: smt.
    cut := weight_bounded d; move:(weight d);smt.
  by rewrite dzero_def. 
qed.

lemma w_dmulc (d:'a distr) r: d_compat d r => weight (dmulc r d) = r * weight d.
proof. by move=> H;rewrite /weight /PR dmulc_def. qed.
 
lemma dmulcA r1 r2 (d:'a distr) : d_compat d r2 => d_compat d (r1 * r2) => 
  dmulc r1 (dmulc r2 d) = dmulc (r1 * r2) d.
proof.
  move=> Hc2 Hc12;apply eq_distr_ext => f;rewrite !dmulc_def // 2:smt.
  cut H_:= w_dmulc d _ Hc2.
  move:Hc2 Hc12;rewrite /d_compat H_ => {H_}.
  case (d = dzero) => /=;1: by move=> ->; rewrite dmulc_dzero.
  case (r2 = 0%r).
  + by move=> ->; rewrite dmulc_0.
  rewrite -w0_dzero; cut := weight_bounded d;move: (weight d) => w H1 H2 H3 H4 H5;left.
  split. smt. admit.
qed.

lemma dmulc_eq_compat (r:real) (d1 d2:'a distr) : 
   0%r < r <= 1%r/(weight d1) => 0%r < r <= 1%r/(weight d2) => 
   dmulc r d1 = dmulc r d2 <=> d1 = d2.
proof.
  move=> Hr1 Hr2; rewrite -!distr_ext !dmulc_def 1,2:smt.
  split => Hf f;cut := Hf f=> //;smt. 
qed.

lemma dmulc_eq_compat1 (r:real) (d1 d2:'a distr) : 
   0%r < r <= 1%r =>  
   dmulc r d1 = dmulc r d2 <=> d1 = d2.
proof.
  move=> Hr; rewrite -!distr_ext !dmulc_def 1,2:smt.
  split => Hf f;cut := Hf f=> //;smt. 
qed.

lemma dlet_dmulc r d (F:'a -> 'b distr):  
  d_compat d r => 
  dlet (dmulc r d) F = dmulc r (dlet d F).
proof. 
  rewrite -distr_ext => Hr f;rewrite dmulc_def; 1:by apply d_compat_dlet.
  by rewrite !dlet_def dmulc_def. 
qed.

(* -------------------------------------------------------------- *)

op drestr : 'a distr -> ('a -> bool) -> 'a distr.

axiom drestr_def (d:'a distr) p f: 
   $[f | drestr d p] = $[fun x => b2r (p x) * f x | d].

lemma drestr_dzero (p:'a -> bool) : drestr dzero p = dzero.
proof. by apply eq_distr_ext => f;rewrite drestr_def !dzero_def. qed.

(* --------------------------------------------------------------- *)

op dscale (d:'a distr) = dmulc (1%r/weight d) d. 

lemma dscale_def (d:'a distr) f: 
   $[f | dscale d] = $[f | d] / weight d.
proof. rewrite /dscale dmulc_def 2:smt; apply d_compat_inv_weight. qed.
 
(* --------------------------------------------------------------- *)
op (||) (d:'a distr) (p:'a -> bool) = dscale (drestr d p).
(* remark: $[fun x => br2 a | d || b] is Pr_d[a | b] ie Pr_d[a /\ b]/ Pr_d[b] *)

lemma dsrestr_def (d:'a distr) (p:'a -> bool) (f:'a -> real): 
    $[f | d || p] = 
       $[fun (x : 'a) => b2r (p x) * f x | d] / 
       $[fun (x : 'a) => b2r (p x) | d].
proof. by rewrite /(||) dscale_def !drestr_def /weight /PR drestr_def. qed.

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

(* ----------------------------------------------------------------- *)

op dif (p:'a -> bool) (F1 F2: 'a -> 'b distr) (a:'a) = 
  if p a then F1 a else F2 a.

lemma nosmt dif_def (d : 'a distr) p (F1 F2:'a -> 'b distr) f :
  $[f | dlet d (dif p F1 F2)] = 
  $[fun a => b2r (p a) * $[f | F1 a] + b2r (!p a) * $[f | F2 a] | d].
proof.
  rewrite /dif dlet_def -if_b2r /=.
  apply muf_congr => //= a; case (p a) => //. 
qed.

(* ------------------------------------------------------------------ *)

op ( * ) (d1:'a distr) (d2:'b distr) : ('a * 'b) distr =
  dlet d1 (fun a => dlet d2 (fun b => dunit (a, b))).

lemma dprod_def (d1:'a distr) (d2:'b distr) f:
  $[f | d1 * d2] = $[fun (a : 'a) => $[fun (a0 : 'b) => f (a, a0) | d2] | d1]. 
proof. by rewrite /( * ) dlet_def /= dlet_def /= dunit_def. qed.

lemma dprod0l (d:'b distr) : dzero<:'a> * d = dzero.
proof. by rewrite /( * ) dlet_dzero. qed.

lemma dprod0r (d:'a distr) : d * dzero<:'b> = dzero.
proof. by rewrite /( * ) dlet_dzero dlet_d_dzero. qed.

lemma dprodW (d1:'a distr) (d2:'b distr) : weight (d1 * d2) = weight d1 * weight d2.
proof.
  by rewrite /weight /( * ) /PR /predT b2r_true dlet_def /= dlet_def /= dunit_def /=
     muf_c Real.Comm.Comm.
qed.

lemma dprod_comp_r (d1:'a distr) (d2:'b distr) r: d_compat d2 r => d_compat (d1 * d2) r.
proof.
  rewrite /d_compat=> [H1 | ->];2:by rewrite dprod0r.  
  case (weight d1 = 0%r) => Hw1.
  + by right;cut := (w0_dzero d1);rewrite Hw1 /= => ->; rewrite dprod0l.
  case (weight d2 = 0%r) => Hw2.
  + by right;cut := (w0_dzero d2);rewrite Hw2 /= => ->; rewrite dprod0r.
  rewrite dprodW. left. cut := weight_bounded d1. cut := weight_bounded d2. 
  move:  (weight d1) (weight d2) H1 Hw1 Hw2. 
  admit. 
qed.

lemma dprod_comp_l (d1:'a distr) (d2:'b distr) r: d_compat d1 r => d_compat (d1 * d2) r.
proof.
  rewrite /d_compat=> [H1 | ->];2:by rewrite dprod0l.  
  case (weight d1 = 0%r) => Hw1.
  + by right;cut := (w0_dzero d1);rewrite Hw1 /= => ->; rewrite dprod0l.
  case (weight d2 = 0%r) => Hw2.
  + by right;cut := (w0_dzero d2);rewrite Hw2 /= => ->; rewrite dprod0r.
  rewrite dprodW. left. cut := weight_bounded d2. 
  move:  (weight d1) (weight d2) H1 Hw1 Hw2. 
  admit.
qed.

lemma dmulc_dprod_r r (d1:'a distr) (d2:'b distr) : 
   d_compat d2 r => 
   dmulc r (d1 * d2) = d1 * dmulc r d2.
proof.
  rewrite -distr_ext=> Hr f; rewrite dprod_def !dmulc_def // 2:dprod_def 2:muf_mulc_l //. 
  by apply dprod_comp_r.
qed.

lemma dmulc_dprod_l r (d1:'a distr) (d2:'b distr) :
   d_compat d1 r =>
   dmulc r (d1 * d2) = dmulc r d1 * d2.
proof.
  rewrite -distr_ext=> Hr f; rewrite dprod_def !dmulc_def // 2:dprod_def //. 
  by apply dprod_comp_l.
qed.

(* ------------------------------------------------------------------ *)

op (\o) (d: 'a distr) (f : 'a -> 'b) : 'b distr =
   dlet d (dunit \o f).

lemma dcomp_def (d:'a distr) (g: 'a -> 'b) (f:'b -> real): 
  $[f | d \o g] = $[f \o g | d].
proof. by rewrite /(\o) dlet_def /= dunit_def. qed.

lemma dzero_dcomp (f:'a -> 'b) : dzero \o f = dzero. 
proof. by rewrite /(\o) dlet_dzero. qed.

lemma dcomp_dunit (f:'a -> 'b) a: dunit a \o f = dunit (f a).
proof. by rewrite /(\o) dlet_unit. qed.
    
lemma dlet_dcomp (d:'a distr) (F : 'a -> 'b distr) (g:'b -> 'c):
  (dlet d F) \o g = dlet d (fun x => F x \o g).
proof. by rewrite /(\o) dlet_dlet. qed.

lemma dcomp_dmulc r d (g:'a -> 'b):  d_compat d r => 
  (dmulc r d) \o g = dmulc r (d \o g).
proof. by move=> H;rewrite /(\o) dlet_dmulc. qed.

lemma dcomp_dcomp (d:'a distr) (f1 : 'a -> 'b) (f2:'b -> 'c): 
    (d \o f1) \o f2 = d \o (f2 \o f1). 
proof. by rewrite -distr_ext /(\o) !dlet_def /= !dunit_def. qed.

lemma weight_dcomp d (g:'a -> 'b) : weight (d \o g) = weight d.
proof. by rewrite /weight /PR dcomp_def. qed.

lemma d_compat_dcomp  r d (g:'a -> 'b):  d_compat d r => d_compat (d \o g) r.
proof.
  by rewrite /d_compat;rewrite weight_dcomp => [ ] -> //; rewrite dzero_dcomp.
qed.

(* ------------------------------------------------------------------ *)
(* list of distributions to distribution of list                      *)

op dnil : 'a list distr = dunit [].

op dcons (d:'a distr) (ds:'a list distr) = 
  dlet d (fun a => dlet ds (fun (l:'a list) => dunit (a :: l))).

lemma dcons_def (d:'m distr) (ds: 'm list distr) (f:'m list -> real): 
  $[f | dcons d ds] = 
  $[fun (a : 'm) => $[fun (a0 : 'm list) => f (a :: a0) | ds] | d].
proof.
  by rewrite /dcons dlet_def /= dlet_def /= dunit_def.
qed.

op dlist (ds:'a distr list) = foldr dcons (dunit []) ds.

lemma dlist_nil : dlist<:'a> [] = dnil.
proof. by []. qed.

lemma dlist_cons (d:'a distr) (ds: 'a distr list) : dlist<:'a> (d::ds) = dcons d (dlist ds).
proof. by []. qed.

lemma ddrop1_dcons (d:'a distr) (ds:'a list distr) : 
  (dcons d ds) \o (drop 1) = dmulc (weight d) ds.
proof.
  rewrite -distr_ext /(\o) => f. 
  rewrite dlet_def dcons_def dmulc_def 1:smt /= dunit_def drop0 muf_c Real.Comm.Comm //.
qed.



































































(*




(* ----------------------------------------------------------- *)
(* try to define the logic                                     *)
(* ------------------------------------------------------------*)

pred uhoare (P : 'a -> bool) (F : 'a -> 'b distr) (Q : 'b distr -> bool) = 
  forall a, P a => Q (F a).

pred dhoare (P : 'a distr -> bool) (F : 'a -> 'b distr) (Q : 'b distr -> bool) = 
  forall d, P d => Q (dlet d F).

op f1 (a:'a) = 1%r.

(* Scale rule *)

lemma nosmt dhoare_scale (P: 'a -> bool) (F:'a -> 'b distr) (r:real) :
  dhoare (fun d => $@[P | d] /\ $[f1 | d] = 1%r) F (fun d => $[f1 | d] = 1%r) =>
  dhoare (fun d => $@[P | d] /\ $[f1 | d] = r)   F (fun d => $[f1 | d] = r).
proof.
  move=> Hll d [HP Hdf1].
  case (r= 0%r) => Hr. 
  + rewrite /dlift dlet_def.
    cut : $[fun (a : 'a) => $[f1 | F a] | d] <= $[f1 | d].
    + apply muf_le_compat;rewrite /f1 /= => x Hx. 
      cut /= := (muf_b2r (fun a => true) (F x)).
      rewrite b2r_true => <-. smt.
    cut : 0%r <= $[fun (a : 'a) => $[f1 | F a] | d];last by smt.
    + by rewrite -(muf_0 d);apply muf_le_compat=> /= x _;
         rewrite -(muf_0 (F x));apply muf_le_compat.
  cut := Hll (dscale d) _.
  + rewrite !dscale_def HP /= Hdf1. smt.
  rewrite /dlift !dlet_def dscale_def Hdf1;smt.   
qed.

(* skip rule *)
lemma nosmt dhoare_skip (P: 'a distr->bool) : dhoare P dunit P. 
proof. by rewrite /dhoare dlet_unit. qed.


(* If rule *)
import Pred.

pred curly (b:'a -> bool) (P1 P2:'a distr -> bool) (d:'a distr) = 
  P1 (drestr d b) /\ P2 (drestr d (!b)).

pred (\oplus) (P1 P2 : 'a distr -> bool) (d:'a distr) =
  exists (d1 d2:'a distr),
     (forall (f:'a -> real), $[f | d] = $[f | d1] + $[f | d2]) /\
     P1 d1 /\ P2 d2.

lemma nosmt square_restr (b:'a -> bool) (d:'a distr) : $@[b | drestr d b].
proof.
  by rewrite drestr_def /= -b2r_and absurd_and_n b2r_false muf_0.
qed.

lemma nosmt dhoare_if (P1 P2:'a distr -> bool) (Q1 Q2:'b distr -> bool) (b:'a -> bool)
   (F1 F2 : 'a -> 'b distr):
   dhoare (fun d => P1 d /\ $@[b | d]) F1 Q1 =>
   dhoare (fun d => P2 d /\ $@[!b | d]) F2 Q2 =>
   dhoare (curly b P1 P2) (dif b F1 F2) (Q1 \oplus Q2).
proof.
  move=> HF1 HF2 d [Hd1 Hd2];rewrite /curly /(\oplus) .
  exists (dlet (drestr d b) F1), (dlet (drestr d (!b)) F2);split.
  + by move=> f;rewrite /dlift dif_def !dlet_def !drestr_def /Pred.([!]) /= -muf_add.  
  split; [apply HF1 | apply HF2]; split => //;apply square_restr.
qed.

(* Sequence *)

op dseq (F1:'a -> 'b distr) (F2: 'b -> 'c distr) = 
  fun a => dlet (F1 a) F2.

lemma dseq_def (d:'a distr) (F1:'a -> 'b distr) (F2: 'b -> 'c distr) f : 
  $[f | dlet d (dseq F1 F2)] = $[fun a => $[ fun b => $[f | F2 b] | F1 a ] | d].
proof.
  by rewrite /dseq dlet_def /= dlet_def.  
qed.

lemma dseq_def2 (d:'a distr) (F1:'a -> 'b distr) (F2: 'b -> 'c distr) : 
  dlet d (dseq F1 F2) = dlet (dlet d F1) F2.
proof.
  apply eq_distr_ext=> f;by rewrite dseq_def !dlet_def.
qed.

lemma nosmt dhoare_seq (P: 'a distr -> bool) (Q:'b distr -> bool) (R: 'c distr -> bool) F1 F2:
   dhoare P F1 Q => dhoare Q F2 R => dhoare P (dseq F1 F2) R.
proof. by move=> H1 H2 d Hd;rewrite dseq_def2;apply H2; apply H1. qed.


 

   




*)
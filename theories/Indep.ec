require import NewList.
require import StdBigop.
import Int Real Fun.
require export DistrOp.

(* TODO: move this *)
lemma Rpow0 (r:real): r ^ 0 = 1%r.
proof. smt full. qed.

lemma Rpow1 (r:real): r ^ 1 = r.
proof. smt full. qed.

lemma RpowS (r:real) n: 0 <= n => r ^ (n+1) = r * r ^ n.
proof. smt full. qed.

lemma Rpow2 (r:real): r ^ 2 = r * r.
proof. by rewrite (_:2 = 1 + 1) // RpowS // Rpow1. qed.

op valid2  (l: ('a -> bool) list) (P: 'a list) = 
  with l = "[]"     , P = "[]"      => true
  with l = "[]"     , P = (::) p P' => false
  with l = (::) f l', P = "[]"      => false
  with l = (::) f l', P = (::) p P' => f p /\ valid2 l' P'.

type 'a ppred = ('a -> bool) -> bool.

lemma valid2_cat (Xs1 Xs2: 'a ppred list) (Ps1 Ps2: ('a -> bool) list): 
  valid2 Xs1 Ps1 => valid2 Xs2 Ps2 => valid2 (Xs1 ++ Xs2) (Ps1 ++ Ps2).
proof.
  move=> H1 H2;elim Xs1 Ps1 H1 => [ [ | ] | X Xs1 Hrec [ | P Ps1] ] //=.
  by progress;apply Hrec.
qed.

lemma valid2_length (Xs: 'a ppred list) (Ps: ('a -> bool) list): 
  valid2 Xs Ps => size Xs = size Ps.
proof.
  by elim: Xs Ps => [ [ | P Ps] | X Xs Hrec [ | P Ps]] //= [_ Hv];rewrite (Hrec _ Hv).
qed.

lemma valid2_nPr (Ps: ('a -> bool) list): valid2 [] Ps => Ps = [].
proof. by case Ps. qed.

lemma valid2_cPr (X:'a ppred) (Xs: 'a ppred list) (Ps: ('a -> bool) list):
   valid2 (X::Xs) Ps => exists P Ps', Ps = P :: Ps' /\ X P /\ valid2 Xs Ps'. 
proof. by case Ps => // P Ps' _;exists P, Ps'. qed.

lemma valid2_catPr (Xs1 Xs2: 'a ppred list) (Ps: ('a -> bool) list):
   valid2 (Xs1 ++ Xs2) Ps => exists Ps1 Ps2, Ps = Ps1 ++ Ps2 /\ valid2 Xs1 Ps1 /\ valid2 Xs2 Ps2.
proof.  
  elim: Xs1 Ps => /= [ Ps _ | X Xs1 Hs1 [ | P Ps] //= [_ Hv] ]; 1: by exists [], Ps.
  by have [Ps1 Ps2 [Heq [H1 H2]]] := Hs1 _ Hv;exists (P::Ps1), Ps2;rewrite Heq.
qed.




(* ------------------------------------------------------------------- *)
(* Generic definition of heterogeneous independance                    *)
(* ------------------------------------------------------------------- *)

pred hindep (d:'m distr) (L: 'm ppred list) = 
  forall (Ps : ('m -> bool) list), 
    valid2 L Ps => 
    L = [] \/
    (DistrOp.weight d)^(size Ps - 1) * PR d (fun m => BBM.big predT (fun P => P m) Ps) = 
    BRM.big predT (fun P => PR d P) Ps.

pred [\I_] (X:'m -> 'a) (P : 'm -> bool) =
  exists (P': 'a -> bool), P = P' \o X.

(* ------------------------------------------------------------------- *)
(* Independance in term of predicate                                   *)
(* ------------------------------------------------------------------- *)

pred indep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
  forall (P1:'a -> bool) (P2:'b -> bool), 
     (DistrOp.weight d) * PR d (fun m => P1 (X m) /\ P2 (Y m)) = PR d (P1 \o X) * PR d (P2 \o Y).

lemma hindep_indep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):
   hindep d [\I_ X; \I_ Y] <=> indep d X Y.
proof.
  rewrite /hindep /indep;split.
  + move=> Hind P1 P2.
    cut := Hind [P1 \o X; P2 \o Y] _.
    + by split;[exists P1 | exists P2].
    rewrite !BBM.big_consT BBM.big_nil /=.
    by rewrite !BRM.big_consT BRM.big_nil /= /(\o) Rpow1.
  move=> Hind [ | P1 [ | P2 [ | ]]];simplify valid2 => // [[[P1' H1] [P2' H2]]].
  rewrite H1 H2.
  rewrite !BBM.big_consT BBM.big_nil /=.
  rewrite !BRM.big_consT BRM.big_nil /= /(\o) Rpow1.
  apply (Hind P1' P2').
qed.

(* ------------------------------------------------------------------- *)
(* Independance in term of equality of distribution                    *)
(* ------------------------------------------------------------------- *)

op fpair (X : 'm -> 'a) (Y : 'm -> 'b) (m:'m) = (X m, Y m).

op eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
   dmulc (DistrOp.weight d) (d \o fpair X Y) = (d \o X) * (d \o Y).

lemma indep_eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):
  indep d X Y <=> eindep d X Y.
proof.
  rewrite /indep /eindep.
  cut Hc : d_compat (d \o fpair X Y) (DistrOp.weight d).
  + by apply d_compat_dcomp;apply d_compat_weight.
  split => Hind.
  + rewrite -pw_eq => [a b];rewrite /mu_x !muf_b2r dmulc_def //.
    rewrite dcomp_def /= /Fun.(\o) /fpair /= anda_and (Hind ((=) a) ((=) b)).
    by rewrite /PR dprod_def /= !dcomp_def /(\o) anda_and b2r_and muf_mulc_l muf_mulc_r.
  move=> P1 P2;rewrite /PR.
  apply (eq_trans _ ($[ (fun (p:'a * 'b) => b2r(P1 p.`1 /\ P2 p.`2)) | (d \o X) * (d \o Y)])).
  + by rewrite -Hind dmulc_def // dcomp_def.
  by rewrite dprod_def /= b2r_and muf_mulc_l muf_mulc_r !dcomp_def.
qed.

op fnil (m:'m): 'a list = [].
op flist (Xs : ('m -> 'a) list) m = map (fun Xi => Xi m) Xs.
op fcons (X:'m -> 'a) (Xs:('m -> 'a) list)  (m:'m) = X m :: flist Xs m.
op eindeps (d:'m distr) (Xs : ('m -> 'a) list) =
  dmulc ((DistrOp.weight d)^(size Xs - 1)) (d \o flist  Xs) = dlist (map ((\o) d) Xs).

lemma flist_nil : flist<:'m,'a> [] = fnil.
proof. by []. qed.

lemma flist_cons (X:'m -> 'a) (Xs: ('m -> 'a) list): flist (X::Xs) = fcons X Xs. 
proof. by []. qed.

(* ------------------------------------------------------------------- *)
(* point wize independance                                             *)
(* ------------------------------------------------------------------- *)

pred pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
  forall (a:'a) (b:'b), 
     (DistrOp.weight d) * PR d (fun m => a = X m /\ b = Y m) = 
                          PR d ((=) a \o X) * PR d ((=) b \o Y).

lemma pwindep_eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):
  pwindep d X Y <=> eindep d X Y.
proof.
  rewrite /pwindep /eindep.
  cut Hc : d_compat (d \o fpair X Y) (DistrOp.weight d).
  + by apply d_compat_dcomp;apply d_compat_weight.
  split => Hind.
  + rewrite -pw_eq => [a b];rewrite /mu_x !muf_b2r dmulc_def //.
    rewrite dcomp_def /= /Fun.(\o) /fpair /= anda_and (Hind a b).
    by rewrite /PR dprod_def /= !dcomp_def /(\o) anda_and b2r_and muf_mulc_l muf_mulc_r.
  move=> a b;rewrite /PR.
  apply (eq_trans _ ($[ (fun (p:'a * 'b) => b2r(a = p.`1 /\ b = p.`2)) | (d \o X) * (d \o Y)])).
  + by rewrite -Hind dmulc_def // dcomp_def.
  by rewrite dprod_def /= b2r_and muf_mulc_l muf_mulc_r !dcomp_def.
qed.

(* ------------------------------------------------------------------- *)
(* Equivalence of the different definitions                            *)
(* ------------------------------------------------------------------- *)

(* hindep indep eindep pwindep *)

(* hindep_indep *)

lemma hindep_eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):  
  hindep d [\I_ X;\I_ Y] <=> eindep d X Y.
proof. by rewrite hindep_indep indep_eindep. qed.

lemma hindep_pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):  
  hindep d [\I_ X;\I_ Y] <=> pwindep d X Y.
proof. by rewrite hindep_eindep pwindep_eindep. qed.

(* indep_eindep *)

lemma indep_pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):  
  indep d X Y <=> pwindep d X Y.
proof. by rewrite indep_eindep pwindep_eindep. qed.

(* pwindep_eindep *)

(* ------------------------------------------------------------------- *)

lemma hindep_perm_imp (d:'m distr) (Xs1 Xs2:'m ppred list):
  perm_eq Xs1 Xs2 => 
  hindep d Xs1 => hindep d Xs2.
proof.
  change (perm_eq Xs1 Xs2 => hindep d ([] ++ Xs1) => hindep d ([]++Xs2)).
  move=> /perm_eqP H;move: H [].  
  elim Xs1 Xs2 => [|X Xs1 ih1] Xs2 eq_s12 Xs.
  + case Xs2 eq_s12 => // i s2 h; cut := h (pred1 i); smt.
  cut r2i: mem Xs2 X by rewrite -has_pred1 has_count -eq_s12 smt.
  have/splitPr [Xs3 Xs4] ->> Hind := r2i.
  cut := ih1 (Xs3 ++ Xs4) _ (rcons Xs X) _. 
  + by move=> p; have := eq_s12 p; rewrite !count_cat /=; smt.
  + by rewrite cat_rcons.
  rewrite /hindep=> H1 Ps Hv;right.
  cut {Hv} [Ps_ Ps' [->> [Hv Hv']]] := valid2_catPr _ _ _ Hv.
  cut {Hv'} [Ps3 Ps'' [->> [Hv3 Hv']]] := valid2_catPr _ _ _ Hv'.
  cut {Hv'} [P Ps4 [->> [HP Hv4]]] := valid2_cPr _ _ _ Hv'.
  cut {H1}[ ] H:= H1 (rcons Ps_ P ++ (Ps3 ++ Ps4)) _. 
  + apply valid2_cat;1:rewrite -!cats1; apply valid2_cat => //.
  + cut : size (rcons Xs X ++ (Xs3 ++ Xs4)) <= 0 by rewrite H.
    rewrite size_cat size_rcons;smt. 
  cut Hperm : perm_eq (Ps_ ++ (Ps3 ++ P :: Ps4)) (rcons Ps_ P ++ (Ps3 ++ Ps4)).
  + by rewrite cat_rcons perm_cat2l perm_catCl /= perm_cons perm_catCl perm_eq_refl.
  rewrite (BBM.eq_big_perm _ _ _ _ Hperm) (BRM.eq_big_perm _ _ _ _ Hperm) -H;congr.
  congr;rewrite !size_cat size_rcons /=;smt.
qed.

lemma hindep_perm (d:'m distr) (Xs1 Xs2:'m ppred list):
  perm_eq Xs1 Xs2 => 
  hindep d Xs1 <=> hindep d Xs2.
proof.
  by move=> Hp;split; apply hindep_perm_imp => //;apply perm_eq_sym.
qed.

lemma LTODO : forall (x y z:real), z <> 0%r => z * x = z * y => x = y. 
proof.
  admit.
qed.

lemma hindep_cons (X:'m ppred) (d:'m distr) (Xs:'m ppred list):
  X predT => 
  hindep d (X :: Xs) => hindep d Xs.
proof.
  rewrite /hindep=> Hx Hh Ps Hv;cut := Hh (predT :: Ps) _ => //=.
  rewrite BBM.big_consT BRM.big_consT /=.
  cut ->: PR d predT = DistrOp.weight d by done.
  case (Xs = []) => // Hn.
  rewrite /predT<:'m> /= (_: 1 + size Ps - 1 = (size Ps - 1) + 1) 1:smt RpowS 1:smt. 
  case (DistrOp.weight d = 0%r).
  + rewrite w0_dzero=> -> _H{_H};rewrite !PR_dzero /=. 
    by elim: Ps Hv;1: smt; progress;rewrite BRM.big_consT.
  move=> Hw H1;apply (LTODO _ _ _ Hw);rewrite -H1;fieldeq.
qed.

lemma hindep_Icons (X:'m -> 'a) (d:'m distr) (Xs:'m ppred list):
  hindep d ((\I_ X) :: Xs) => hindep d Xs.
proof. by apply hindep_cons;exists predT. qed.

lemma hindep_cat_r (d:'m distr) (Xs1 Xs2:'m ppred list):
  all (fun X => X predT) Xs1 =>
  hindep d (Xs1 ++ Xs2) => hindep d Xs2.
proof.
  elim: Xs1 => //= X Xs1 Hrec [HX Hall] Hh; apply Hrec => //.
  apply (hindep_cons X) => //.
qed.

lemma hindep_cat_l (d:'m distr) (Xs1 Xs2:'m ppred list):
  all (fun X => X predT) Xs2 =>
  hindep d (Xs1 ++ Xs2) => hindep d Xs1.
proof.
  rewrite (hindep_perm _ _ (Xs2 ++ Xs1)) 1:perm_catCl 1:perm_eq_refl //.
  apply hindep_cat_r.
qed.

lemma indep_comp (d:'m distr) (X:'m -> 'a) (Y: 'm -> 'b) (F :'b -> 'c):
     indep d X Y => indep d X (F \o Y).
proof.
  rewrite !indep_eindep /eindep => Hi.
  apply (eq_trans _ (((d \o X) * (d \o Y)) \o (fun (p:'a * 'b) => (p.`1, F p.`2)))).
  + by rewrite -Hi dcomp_dmulc 1:smt dcomp_dcomp.
  by apply eq_distr_ext=> f;rewrite !(dprod_def, dcomp_def).
qed.

(* FIXME *)
axiom dcomp_bij (d:'a distr) (f:'a -> 'a):
  bijective f => d \o f = d.

print bijective.
lemma indep_bij_comp (d:'m distr) (X:'m -> 'a) (Y: 'm -> 'b) (f: 'a -> 'b -> 'a) :
   (exists g, forall b, bijective (fun a => f a b)) =>
   indep d X Y => indep d (fun m => f (X m) (Y m)) Y.
proof.
  move=> Hf Hi;rewrite indep_eindep /eindep.
  cut H1 : d \o (fun m => (f (X m) (Y m), Y m)) = d \o (fun m => (X m, Y m)).
    apply (eq_trans _ ((d \o fun (m : 'm) => (X m, Y m)) \o 
               (fun (p:'a*'b) => (f p.`1 p.`2, p.`2)))).
    + by rewrite dcomp_dcomp //.
    apply dcomp_bij. 
    move: Hf; rewrite /bijective /cancel /=.
    
    cut : exists g 

elim Hi.
    
 exists (fun (p:'a*'b) => 

 rewrite /bijective. 

split.
    d \o (fun m => (f (X m) (Y m), Y m)) = d \o (fun m => (X m, Y m)).
  cut -> : d \o (fun (m : 'm) => f (X m) (Y m)) = d \o X.
  + apply (eq_trans _ ((d \o (fun m => (f (X m) (Y m), Y m))) \o (fun (p:'a*'b) => p.`1))).
    + by rewrite dcomp_dcomp.
    by rewrite indep_bij // dcomp_dcomp.
  cut := Hi;rewrite indep_eindep /eindep => Hi'.
  by rewrite /fpair indep_bij.
qed.






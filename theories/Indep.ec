require import NewList.
require import StdBigop StdRing.
import Int Real Fun.
require export DistrOp.

search Real.PowerInt.( ^ ).

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

op appf (a:'a) (f:'a -> 'b) = f a.

pred hindep (d:'m distr) (L: 'm ppred list) = 
  forall (Ps : ('m -> bool) list), 
    valid2 L Ps => 
    L = [] \/
    (DistrOp.weight d)^(size Ps - 1) * PR d (fun m => BBM.big predT (appf m) Ps) = 
    BRM.big predT (PR d) Ps.

pred I_ (X:'m -> 'a) (P : 'm -> bool) =
  exists (P': 'a -> bool), P = P' \o X.

lemma valid2_Icons (X:'m -> 'a) (L: 'm ppred list) (Ps:('m -> bool) list):
  valid2 (I_ X :: L) Ps => exists (P:'a -> bool) Ps', Ps = (P \o X) :: Ps' /\ valid2 L Ps'.
proof.
  by move=> /valid2_cPr [P0 Ps' [->> [[P ->>] Hv]]]; exists P, Ps'.
qed.

lemma valid2_Imap (Xs:('m -> 'a)list) (Ps:('m -> bool) list):
  valid2 (map I_ Xs) Ps => 
    exists (Ps':('a -> bool)list), 
    Ps = map (fun i => (nth predT Ps' i) \o (nth Option.witness Xs i)) (range 0 (size Xs)).
proof.
  elim /last_ind Xs Ps=> /=;1:by move=> Ps /valid2_nPr ->>;rewrite range_geq. 
  move=> Xs X Hrec Ps; rewrite -cats1 map_cat=> 
    /valid2_catPr [Ps1 Ps2 [->> [HPs1 ]]] /= /valid2_cPr [_P _Ps [->> [[P ->>] ]]]
    /valid2_nPr ->> {_P _Ps}.
  cut [Ps' ->>]:= Hrec _ HPs1.
  rewrite size_cat /= (range_cat (size Xs) 0 (size Xs + 1)) 1,2:smt map_cat. 
  exists (Ps' ++ P :: []).
  rewrite (range_ltn (size Xs) (size Xs + 1)) 1:smt (range_geq (size Xs + 1)) //=.
  congr.
search map.  
search range.
search rcons (++).
  rewrite   

rewrite 
(P \o X) :: Ps' /\ valid2 L Ps'.
proof.
  by move=> /valid2_cPr [P0 Ps' [->> [[P ->>] Hv]]]; exists P, Ps'.
qed.


  
(* ------------------------------------------------------------------- *)
(* Independance in term of equality of distribution                    *)
(* ------------------------------------------------------------------- *)

op fpair (X : 'm -> 'a) (Y : 'm -> 'b) (m:'m) = (X m, Y m).

op eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
   dmulc (DistrOp.weight d) (d \o fpair X Y) = (d \o X) * (d \o Y).

pred eindeps (d:'m distr) (Xs : ('m -> 'a) list) = 
  Xs = [] \/
  dmulc ((DistrOp.weight d)^(size Xs - 1)) (d \o (fun m => map (appf m) Xs)) = 
     dlist (map ((\o) d) Xs).

(* ------------------------------------------------------------------- *)
(* Independance in term of predicates                                  *)
(* ------------------------------------------------------------------- *)

pred indep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
  forall (P1:'a -> bool) (P2:'b -> bool), 
     (DistrOp.weight d) * PR d (fun m => P1 (X m) /\ P2 (Y m)) = PR d (P1 \o X) * PR d (P2 \o Y).

pred indeps (d:'m distr) (Xs:'m -> int -> 'a) (k p:int) = 
   forall (Ps:int -> 'a -> bool),
      p <= k \/
      (DistrOp.weight d)^(p - k - 1) * 
      PR d (fun m => BBM.bigi predT (fun i => Ps i (Xs m i)) k p) = 
      BRM.bigi predT (fun i => PR d (fun m => Ps i (Xs m i))) k p.

(* ------------------------------------------------------------------- *)
(* Independance in term of points                                      *)
(* ------------------------------------------------------------------- *)

pred pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
  forall (a:'a) (b:'b), 
     (DistrOp.weight d) * PR d (fun m => a = X m /\ b = Y m) = 
                          PR d ((=) a \o X) * PR d ((=) b \o Y).

pred pwindeps (d:'m distr) (Xs:'m -> int -> 'a) (k p:int) = 
   forall (Ps:int -> 'a),
      p <= k \/
      (DistrOp.weight d)^(p - k - 1) * 
      PR d (fun m => BBM.bigi predT (fun i => Ps i = Xs m i) k p) = 
      BRM.bigi predT (fun i => PR d (fun m => Ps i = Xs m i)) k p.

(* ------------------------------------------------------------------- *)
(* Equivalence of the different definitions                            *)
(* ------------------------------------------------------------------- *)

lemma hindep_indep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):
   hindep d [I_ X; I_ Y] <=> indep d X Y.
proof.
  rewrite /hindep /indep;split.
  + move=> Hind P1 P2.
    cut := Hind [P1 \o X; P2 \o Y] _.
    + by split;[exists P1 | exists P2].
    rewrite !BBM.big_consT BBM.big_nil /=.
    by rewrite !BRM.big_consT BRM.big_nil /= /(\o) Power_1.
  move=> Hind [ | P1 [ | P2 [ | ]]];simplify valid2 => // [[[P1' H1] [P2' H2]]].
  rewrite H1 H2.
  rewrite !BBM.big_consT BBM.big_nil /=.
  rewrite !BRM.big_consT BRM.big_nil /= /(\o) Power_1.
  apply (Hind P1' P2').
qed.

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

lemma hindep_eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):  
  hindep d [I_ X;I_ Y] <=> eindep d X Y.
proof. by rewrite hindep_indep indep_eindep. qed.

lemma hindep_pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):  
  hindep d [I_ X;I_ Y] <=> pwindep d X Y.
proof. by rewrite hindep_eindep pwindep_eindep. qed.

lemma indep_pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b):  
  indep d X Y <=> pwindep d X Y.
proof. by rewrite indep_eindep pwindep_eindep. qed.

lemma hindep_eindeps (d:'m distr) (Xs: ('m -> 'a)list):
  hindep d (map I_ Xs) <=> eindeps d Xs.
proof.
  rewrite /hindep /eindeps.
  case (Xs = []);1:done;move=> Hn /=;split=> Hind.
  + apply pw_eq=> L;rewrite /mu_x !muf_b2r.
    cut Hpr := Hind (map (fun i m => nth (fun m => Option.witness) Xs i m =  
                                 nth Option.witness L i)
                     (range 0 (size Xs))) _.
    + cut : 0 <= 0 by done.
      move: {-1}0;move=> {Hind Hn}; elim Xs L => /=; 1: by move=> L x Hx; rewrite range_geq.
      move=> X Xs HXs L. /valid2_cPr.    
 search range. 
  + move=> -> /=.
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

(* ------------------------------------------------------------------- *)

lemma hindep_perm_imp (d:'m distr) (Xs1 Xs2:'m ppred list):
  perm_eq Xs1 Xs2 => 
  hindep d Xs1 => hindep d Xs2.
proof.
  change (perm_eq Xs1 Xs2 => hindep d ([] ++ Xs1) => hindep d ([]++Xs2)).
  move=> /perm_eqP H;move: H [].  
  elim Xs1 Xs2 => [|X Xs1 ih1] Xs2 eq_s12 Xs.
  + case Xs2 eq_s12 => // i s2 h; cut := h (pred1 i);smt.
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

lemma hindep_cons (X:'m ppred) (d:'m distr) (Xs:'m ppred list):
  X predT => 
  hindep d (X :: Xs) => hindep d Xs.
proof.
  rewrite /hindep=> Hx Hh Ps Hv;cut := Hh (predT :: Ps) _ => //=.
  rewrite BBM.big_consT BRM.big_consT /=.
  cut ->: PR d predT = DistrOp.weight d by done.
  case (Xs = []) => // Hn.
  rewrite /predT<:'m> /= (_: 1 + size Ps - 1 = (size Ps - 1) + 1);1:ringeq;rewrite Power_s 1:smt.
  case (DistrOp.weight d = 0%r).
  + rewrite w0_dzero=> -> _H{_H};rewrite !PR_dzero /=. 
    by elim: Ps Hv;1:smt; progress;rewrite BRM.big_consT PR_dzero.
  move=> Hw H1;apply (RField.mulfI _ Hw);rewrite -H1 /appf /=;fieldeq.
qed.

lemma hindep_Icons (X:'m -> 'a) (d:'m distr) (Xs:'m ppred list):
  hindep d (I_ X :: Xs) => hindep d Xs.
proof. by apply hindep_cons;exists predT. qed.

lemma hindep_cat_r (Xs1 Xs2:'m ppred list) (d:'m distr):
  all (appf predT) Xs1 =>
  hindep d (Xs1 ++ Xs2) => hindep d Xs2.
proof.
  elim: Xs1 => //= X Xs1 Hrec [HX Hall] Hh; apply Hrec => //.
  apply (hindep_cons X) => //.
qed.

lemma hindep_cat_l (Xs2 Xs1:'m ppred list) (d:'m distr):
  all (appf predT) Xs2 =>
  hindep d (Xs1 ++ Xs2) => hindep d Xs1.
proof.
  rewrite (hindep_perm _ _ (Xs2 ++ Xs1)) 1:perm_catCl 1:perm_eq_refl //.
  apply hindep_cat_r.
qed.

lemma all_I_predT (Xs:('m -> 'a)list): all (appf predT) (map I_ Xs).
proof.
  by rewrite /appf /=;elim Xs => //= X Xs Hrec;split=> //;exists predT.
qed.

lemma hindep_Icat_r (Xs1:('m -> 'a)list) (Xs2:'m ppred list) (d:'m distr):
  hindep d ( map I_ Xs1 ++ Xs2) => hindep d Xs2.
proof. apply hindep_cat_r;apply all_I_predT. qed.

lemma hindep_Icat_l (Xs2:('m -> 'a)list) (Xs1:'m ppred list) (d:'m distr):
  hindep d (Xs1 ++ map I_ Xs2) => hindep d Xs1.
proof. apply hindep_cat_l;apply all_I_predT. qed.

lemma indep_comp (d:'m distr) (X:'m -> 'a) (Y: 'm -> 'b) (F :'b -> 'c):
     indep d X Y => indep d X (F \o Y).
proof.
  rewrite !indep_eindep /eindep => Hi.
  apply (eq_trans _ (((d \o X) * (d \o Y)) \o (fun (p:'a * 'b) => (p.`1, F p.`2)))).
  + by rewrite -Hi dcomp_dmulc 1:smt dcomp_dcomp.
  by apply eq_distr_ext=> f;rewrite !(dprod_def, dcomp_def).
qed.

(* TODO *)
axiom dcomp_bij (d:'a distr) (f:'a -> 'a):
  bijective f => d \o f = d.

lemma indep_bij_comp (d:'m distr) (X:'m -> 'a) (Y: 'm -> 'b) (f: 'a -> 'b -> 'a) :
   (forall b, bijective (fun a => f a b)) =>
   indep d X Y => indep d (fun m => f (X m) (Y m)) Y.
proof.
  move=> Hf Hi;rewrite indep_eindep /eindep.
  cut H1 : d \o (fun m => (f (X m) (Y m), Y m)) = d \o (fun m => (X m, Y m)).
    apply (eq_trans _ ((d \o fun (m : 'm) => (X m, Y m)) \o 
               (fun (p:'a*'b) => (f p.`1 p.`2, p.`2)))).
    + by rewrite dcomp_dcomp //.
    apply dcomp_bij;cut {Hf} [g /= Hg]:= funchoice _ Hf. 
    exists (fun (p:'a*'b) => (g p.`2 p.`1, p.`2));split=> p;cut:= Hg p.`2;rewrite /cancel smt.
  cut -> : d \o (fun (m : 'm) => f (X m) (Y m)) = d \o X.
  + apply (eq_trans _ ((d \o (fun m => (f (X m) (Y m), Y m))) \o (fun (p:'a*'b) => p.`1))).
    + by rewrite dcomp_dcomp.
    by rewrite H1 // dcomp_dcomp.
  cut := Hi;rewrite indep_eindep /eindep => Hi'.
  by rewrite /fpair H1.
qed.

(* --------------------------------------------------------------------- *)

lemma foo (d:'m distr) (X:'m -> 'b) (Xs: ('m -> 'a) list):
  hindep d (I_ X :: map I_ Xs) =>
  hindep d [I_ X; I_ (fun m => map (fun Xi => Xi m) Xs) ]. 
proof.  
  move=> Hind;rewrite hindep_eindep /eindep.
  cut HXs := hindep_Icons _ _ _ Hind.
  case (DistrOp.weight d = 0%r). 
  + by move=> /w0_dzero ->; rewrite !dzero_dcomp dprod0l dmulc_dzero.
  move=> Hw.
  case 
  cut Hs : 0 < size Xs by smt.
  cut Hbd:= PR_bounded predT d.
  cut Hsi : 0 <= size Xs - 1 by smt.
  rewrite -(dmulc_eq_compat ((PR d predT)^(size Xs - 1))). smt.
  cut Hbd' := Rpow_bounded _ _ Hbd Hsi.
  rewrite dmulcA // Real.Comm.Comm -RpowS //.  
  cut -> : dproj d (fun (m : 'm) => (X m, map (fun (Xi : 'm -> 'a) => Xi m) Xs)) = 
           dproj (dproj d (fun m => map (fun Xi => Xi m) (X::Xs)))
            (fun (l:'a list) => (head witness l, drop 1 l)).
  + by rewrite dproj_dproj /(\o) map_cons drop_cons /= drop0.
  move:Hind;rewrite /muindep.
  rewrite (_:size Xs - 1 + 1 = size Xs) 1:smt.
  rewrite (_: size (X :: Xs) - 1 = size Xs) 1:smt => H.
  rewrite -dproj_dmulc // 1:smt H.
  cut -> : dproj (dlist (map (dproj d) (X :: Xs)))
             (fun (l : 'a list) => (head witness l, drop 1 l)) = 
           dproj d X * dlist (map (dproj d) Xs).
  + apply eq_distr_ext => f.
    by rewrite dproj_def dprod_def /dlist /= dcons_def /= drop0.
  by rewrite -HXS dmulc_dprod_r.
qed.











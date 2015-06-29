require import NewList.
require import StdBigop StdRing.
import Int Real Fun Option.
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

lemma valid2_nPr (Ps: ('a -> bool) list): valid2 [] Ps <=> Ps = [].
proof. by case Ps. qed.

lemma valid2_cPr (X:'a ppred) (Xs: 'a ppred list) (Ps: ('a -> bool) list):
   valid2 (X::Xs) Ps <=> exists P Ps', Ps = P :: Ps' /\ X P /\ valid2 Xs Ps'. 
proof. case Ps => //= P Ps'; smt. qed.

lemma valid2_catPr (Xs1 Xs2: 'a ppred list) (Ps: ('a -> bool) list):
   valid2 (Xs1 ++ Xs2) Ps <=> 
      exists Ps1 Ps2, Ps = Ps1 ++ Ps2 /\ valid2 Xs1 Ps1 /\ valid2 Xs2 Ps2.
proof.  
  elim Xs1 Ps => /=;1:smt.
  move=> X Xs1 Hrec [ | P Ps] /=;1:smt. 
  rewrite Hrec;split;1:smt.
  move=> [Ps1 Ps2 [Heq [/valid2_cPr [P' Ps' [->> [H1 H2]]] Hv]]];smt.
qed.

pred I_ (X:'m -> 'a) (P : 'm -> bool) =
  exists (P': 'a -> bool), P = P' \o X.

lemma valid2_Icons (X:'m -> 'a) (L: 'm ppred list) (Ps:('m -> bool) list):
  valid2 (I_ X :: L) Ps <=> exists (P:'a -> bool) Ps', Ps = (P \o X) :: Ps' /\ valid2 L Ps'.
proof. by rewrite valid2_cPr;smt. qed.

lemma valid2_Imap (Xs:('m -> 'a)list) (Ps:('m -> bool) list):
  valid2 (map I_ Xs) Ps <=> 
    exists (Ps':('a -> bool)list), 
    size Ps' = size Xs /\
    Ps = map (fun i => (nth predT Ps' i) \o (nth witness Xs i)) (range 0 (size Xs)).
proof.
  elim /last_ind Xs Ps => /=;1: smt.
  move=> Xs X Hrec Ps.
  rewrite -cats1 map_cat valid2_catPr Hrec size_cat /= =>{Hrec}.
  rewrite (range_cat (size Xs) 0 (size Xs + 1)) 1,2:smt.
  rewrite map_cat (range_ltn (size Xs) (size Xs + 1)) 1:smt (range_geq (size Xs + 1)) //=.
  rewrite !nth_cat /= valid2_cPr valid2_nPr /I_;progress.
  + exists (Ps' ++ [P']);rewrite size_cat !nth_cat H /=;congr.
    by apply eq_in_map=> /= x /mem_range [H0x ->].
  exists (map
           (fun (i : int) =>
              nth predT Ps' i \o
              if i < size Xs then nth witness Xs i
             else if i - size Xs = 0 then X else witness)
           (range 0 (size Xs))),
         ((nth predT Ps' (size Xs) \o X) :: []);progress.
  + exists (take (size Xs) Ps');split;1:smt.
    apply eq_in_map=> /= x /mem_range [H0x Hx];rewrite Hx /=;congr;smt.
  by exists (nth predT Ps' (size Xs) \o X), [] => /=;exists (nth predT Ps' (size Xs)).
qed.

lemma valid2_range (Xs: ('m -> 'a) list) Ps:
    valid2 (map I_  Xs) Ps <=>
    exists (Fs:int -> 'a -> bool), 
        Ps =
        map (fun i m => Fs i (nth witness Xs i m)) (range 0 (size Xs)).
proof.
  rewrite valid2_Imap;split.
  + move=> [Ps' [H1 ->>]]; exists (nth predT Ps')=> //.
  cut Hs : size (range 0 (size Xs)) = size Xs by rewrite size_range smt. 
  move => [Fs ->>];exists (map Fs (range 0 (size Xs)));rewrite size_map /= Hs /=.
  apply eq_in_map=> i /=;rewrite mem_range => Hi;apply fun_ext => /= m.
  rewrite /(\o) /= (nth_map witness) 1:Hs // nth_range //.
qed.

(* ------------------------------------------------------------------- *)
(* Generic definition of heterogeneous independence                    *)
(* ------------------------------------------------------------------- *)

op appf (a:'a) (f:'a -> 'b) = f a.

pred hindep (d:'m distr) (L: 'm ppred list) = 
  forall (Ps : ('m -> bool) list), 
    valid2 L Ps => 
    L = [] \/
    (DistrOp.weight d)^(size Ps - 1) * PR d (fun m => BBM.big predT (appf m) Ps) = 
    BRM.big predT (PR d) Ps.

(* ------------------------------------------------------------------- *)
(* Independence in term of equality of distribution                    *)
(* ------------------------------------------------------------------- *)

op fpair (X : 'm -> 'a) (Y : 'm -> 'b) (m:'m) = (X m, Y m).

op eindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
   dmulc (DistrOp.weight d) (d \o fpair X Y) = (d \o X) * (d \o Y).

pred eindeps (d:'m distr) (Xs : ('m -> 'a) list)  = 
  Xs = [] \/
  dmulc ((DistrOp.weight d)^(size Xs -1)) (d \o (fun m => map (appf m) Xs)) =
     dlist (map ((\o) d) Xs).

(* ------------------------------------------------------------------- *)
(* Independence in term of predicates                                  *)
(* ------------------------------------------------------------------- *)

pred indep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
  forall (P1:'a -> bool) (P2:'b -> bool), 
     (DistrOp.weight d) * PR d (fun m => P1 (X m) /\ P2 (Y m)) = PR d (P1 \o X) * PR d (P2 \o Y).

pred indeps (d:'m distr) (Xs:('m -> 'a) list)= 
   forall (Ps:int -> 'a -> bool),
      Xs = [] \/
      (DistrOp.weight d)^(size Xs - 1) * 
      PR d (fun m => BBM.bigi predT (fun i => Ps i (nth witness Xs i m)) 0 (size Xs)) = 
      BRM.bigi predT (fun i => PR d (fun m => Ps i (nth witness Xs i m))) 0 (size Xs).

(* ------------------------------------------------------------------- *)
(* Independence in term of points                                      *)
(* ------------------------------------------------------------------- *)

pred pwindep (d:'m distr) (X : 'm -> 'a) (Y : 'm -> 'b) =
  forall (a:'a) (b:'b), 
     (DistrOp.weight d) * PR d (fun m => a = X m /\ b = Y m) = 
                          PR d ((=) a \o X) * PR d ((=) b \o Y).

pred pwindeps (d:'m distr) (Xs:('m -> 'a)list) = 
   forall (Ps:int -> 'a),
      Xs = [] \/
      (DistrOp.weight d)^(size Xs - 1) * 
      PR d (fun m => BBM.bigi predT (fun i => Ps i = nth witness Xs i m) 0 (size Xs)) = 
      BRM.bigi predT (fun i => PR d (fun m => Ps i = nth witness Xs i m)) 0 (size Xs).

(* ------------------------------------------------------------------- *)
(* Equivalence of the different binary definitions                     *)
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

(* ------------------------------------------------------------------- *)
(* Equivalence of the different nary definitions                       *)
(* ------------------------------------------------------------------- *)

lemma hindeps_indeps (d:'m distr) (Xs: ('m -> 'a) list):
  hindep d (map I_ Xs) <=> indeps d Xs.
proof.
  rewrite /hindep /indeps.
  case (Xs = [])=> HXs /=;1:by rewrite HXs.
  cut -> /=: map I_ Xs <> [] by smt.
  cut Hr : size (range 0 (size Xs)) = size Xs by rewrite size_range smt.
  rewrite valid2_range;split => Hind Ps.
  + cut {Hind}:= Hind (map (fun i m => Ps i (nth witness Xs i m)) (range 0 (size Xs))) _.
    + by exists Ps.
    by rewrite size_map Hr BRM.big_mapT /BRM.bigi BBM.big_mapT => <-.
  move=> [Fs ->>].
  rewrite size_map Hr BBM.big_mapT BRM.big_mapT;apply Hind.
qed.

(* TODO: move this *)
lemma Rpow_bounded r n : 0%r <= r <= 1%r => 0 <= n => 0%r <= r ^ n <= 1%r.
proof. 
  move=> Hr. elim /Induction.induction n; smt. 
qed.

lemma Rpow_bounded_lt r n : 0%r < r <= 1%r => 0 <= n => 0%r < r ^ n <= 1%r.
proof. 
  move=> Hr. elim /Induction.induction n; smt. 
qed.

lemma Rpow_S (x:real) (n:int) : 0 <= n => x ^ (n+1) = x * x ^ n.
proof. smt. qed.

lemma BBM_big_Prop (P1 P2:'a -> bool) (s:'a list): 
   BBM.big P1 P2 s <=> forall a, mem s a => P1 a => P2 a.
proof.
  elim s => //= x s Hrec;rewrite BBM.big_cons;smt.
qed.

lemma BBM_bigi_Prop (P1 P2:int -> bool) k p: 
   BBM.bigi P1 P2 k p <=> forall i, k <= i < p => P1 i => P2 i.
proof. by rewrite /BBM.bigi BBM_big_Prop mem_range. qed.

lemma indeps_eindeps (d:'m distr) (Xs: ('m -> 'a)list):
  indeps d Xs <=> eindeps d Xs.
proof.
  rewrite /indeps /eindeps; case (Xs = []) => Hpk //=.
  cut Hc : d_compat (d \o fun (m : 'm) => map (appf m) Xs) ((DistrOp.weight d)^(size Xs - 1)).
  + apply d_compat_dcomp;smt. 
  split => Hind.
  + rewrite -pw_eq => l;rewrite /mu_x !muf_b2r dmulc_def //.
    rewrite dcomp_def /= /Fun.(\o) /=. 
    cut /= H:= Hind (fun i a => nth witness l i = a).
    case (size l = size Xs) => Hsize.
    + apply (eq_trans _ 
            ((DistrOp.weight d) ^ (size Xs - 1) *
            PR d
             (fun (m : 'm) =>
             BBM.bigi predT
                (fun (i : int) => nth witness l i = nth witness Xs i m) 
                0 (size Xs)))).
      + congr;rewrite /PR;apply muf_eq_compat=> m Hm /=. 
        congr; rewrite eq_iff;split.
        + by move=> ->; rewrite /BBM.bigi BBM.big1_seq // => i [_ ];rewrite mem_range /= => Hi;
          rewrite (nth_map witness). 
        move=> {H Hind Hm Hc Hpk} Hbigi.
        apply (eq_from_nth witness);1:by rewrite size_map.       
        move: Hbigi;rewrite BBM_bigi_Prop /predT Hsize //= => H i Hi.
        by rewrite (nth_map witness) // /appf;apply H. 
      rewrite H=> {Hind H Hc Hpk}.
      elim Xs l Hsize;1:smt.
      move=> X Xs Hrec [ | x l] /= Heq;1:smt.
      rewrite /dlist /= dcons_def /= b2r_and muf_mulc_l muf_mulc_r -Hrec 1:smt. 
      rewrite (addzC 1) BRM.big_nat_recl 1:smt /=;congr.
      rewrite /PR dcomp_def; apply muf_eq_compat=> m Hm /=;rewrite /(\o) /=. smt. 
      apply BRM.eq_big_seq => //= i /mem_range Hi. 
      rewrite /PR;apply muf_eq_compat => /= m Hm;smt.
    rewrite muf_0_f0 /=. 
    + move=> m Hm; case (l =  map (appf m) Xs) => // ->>;smt.
    move=> {Hind H Hc Hpk};elim Xs l Hsize; 1:smt.
    move => X Xs Hrec [ | x l] /= Hs;rewrite /dlist /= dcons_def /= b2r_false;
      1: by rewrite !muf_0. 
    rewrite b2r_and muf_mulc_l muf_mulc_r -Hrec /=;smt.
  move=> Ps;rewrite /PR -dmulc_def 1:smt.
  apply (eq_trans _
           ($[fun (x : 'a list) =>
              b2r
                (BBM.bigi predT (fun (i : int) => Ps i (nth witness x i)) 0 (size Xs)) 
             | (dmulc ((weight d)%DistrOp ^ (size Xs - 1)) d) \o (fun m => map (appf m) Xs)])).
  + rewrite dcomp_def;apply muf_eq_compat => m Hm;rewrite /(\o) /=;congr.
    by apply BBM.eq_big_nat => i Hi /=;rewrite (nth_map witness).
  rewrite dcomp_dmulc 1:smt Hind.
  move=> {Hpk Hc Hind};elim Xs Ps => /=;rewrite /dlist /=.
  + by move=> Ps;rewrite BRM.big_geq // dunit_def /= BBM.big_geq.
  move=> X Xs Hrec Ps;rewrite dcons_def.
  rewrite (addzC 1) BRM.big_nat_recl 1:smt BBM.big_nat_recl 1:smt /=.     
  rewrite b2r_and muf_mulc_l.
  apply (eq_trans _
           ($[fun (a : 'a) =>
              b2r (Ps 0 a) *
              $[fun (x : 'a list) =>
                 b2r (BBM.bigi predT
                   (fun (i : int) =>
                     Ps (i + 1) (nth witness x (i))) 0 (size Xs)) 
              | foldr dcons (dunit []) (map ((\o) d) Xs)] | d \o X])).
  + apply muf_eq_compat => a Ha /=;congr;apply muf_eq_compat => l Hl /=;congr.
    apply BBM.eq_big_nat => i Hi /=; smt.
  rewrite muf_mulc_r (Hrec (fun i => Ps (i+1)));congr. 
  + rewrite dcomp_def;apply muf_eq_compat;smt.
  apply BRM.eq_big_nat => i Hi /=;apply muf_eq_compat=> m Hm /=;smt. 
qed.

lemma pwindeps_eindeps (d:'m distr) (Xs: ('m -> 'a)list):
  pwindeps d Xs <=> eindeps d Xs.
proof.
  rewrite /pwindeps /eindeps; case (Xs = []) => Hpk //=.
  cut Hc : d_compat (d \o fun (m : 'm) => map (appf m) Xs) ((DistrOp.weight d)^(size Xs - 1)).
  + apply d_compat_dcomp;smt. 
  split => Hind.
  + rewrite -pw_eq => l;rewrite /mu_x !muf_b2r dmulc_def //.
    rewrite dcomp_def /= /Fun.(\o) /=. 
    cut /= H:= Hind (fun i => nth witness l i).
    case (size l = size Xs) => Hsize.
    + apply (eq_trans _ 
            ((DistrOp.weight d) ^ (size Xs - 1) *
            PR d
             (fun (m : 'm) =>
             BBM.bigi predT
                (fun (i : int) => nth witness l i = nth witness Xs i m) 
                0 (size Xs)))).
      + congr;rewrite /PR;apply muf_eq_compat=> m Hm /=. 
        congr; rewrite eq_iff;split.
        + by move=> ->; rewrite /BBM.bigi BBM.big1_seq // => i [_ ];rewrite mem_range /= => Hi;
          rewrite (nth_map witness). 
        move=> {H Hind Hm Hc Hpk} Hbigi.
        apply (eq_from_nth witness);1:by rewrite size_map.       
        move: Hbigi;rewrite BBM_bigi_Prop /predT Hsize //= => H i Hi.
        by rewrite (nth_map witness) // /appf;apply H. 
      rewrite H=> {Hind H Hc Hpk}.
      elim Xs l Hsize;1:smt.
      move=> X Xs Hrec [ | x l] /= Heq;1:smt.
      rewrite /dlist /= dcons_def /= b2r_and muf_mulc_l muf_mulc_r -Hrec 1:smt. 
      rewrite (addzC 1) BRM.big_nat_recl 1:smt /=;congr.
      rewrite /PR dcomp_def; apply muf_eq_compat=> m Hm /=;rewrite /(\o) /=. smt. 
      apply BRM.eq_big_seq => //= i /mem_range Hi. 
      rewrite /PR;apply muf_eq_compat => /= m Hm;smt.
    rewrite muf_0_f0 /=. 
    + move=> m Hm; case (l =  map (appf m) Xs) => // ->>;smt.
    move=> {Hind H Hc Hpk};elim Xs l Hsize; 1:smt.
    move => X Xs Hrec [ | x l] /= Hs;rewrite /dlist /= dcons_def /= b2r_false;
      1: by rewrite !muf_0. 
    rewrite b2r_and muf_mulc_l muf_mulc_r -Hrec /=;smt.
  move=> Ps;rewrite /PR -dmulc_def 1:smt.
  apply (eq_trans _
           ($[fun (x : 'a list) =>
              b2r
                (BBM.bigi predT (fun (i : int) => Ps i = (nth witness x i)) 0 (size Xs)) 
             | (dmulc ((weight d)%DistrOp ^ (size Xs - 1)) d) \o (fun m => map (appf m) Xs)])).
  + rewrite dcomp_def;apply muf_eq_compat => m Hm;rewrite /(\o) /=;congr.
    by apply BBM.eq_big_nat => i Hi /=;rewrite (nth_map witness).
  rewrite dcomp_dmulc 1:smt Hind.
  move=> {Hpk Hc Hind};elim Xs Ps => /=;rewrite /dlist /=.
  + by move=> Ps;rewrite BRM.big_geq // dunit_def /= BBM.big_geq.
  move=> X Xs Hrec Ps;rewrite dcons_def.
  rewrite (addzC 1) BRM.big_nat_recl 1:smt BBM.big_nat_recl 1:smt /=.     
  rewrite b2r_and muf_mulc_l.
  apply (eq_trans _
           ($[fun (a : 'a) =>
              b2r (Ps 0 = a) *
              $[fun (x : 'a list) =>
                 b2r (BBM.bigi predT
                   (fun (i : int) =>
                     Ps (i + 1) = (nth witness x (i))) 0 (size Xs)) 
              | foldr dcons (dunit []) (map ((\o) d) Xs)] | d \o X])).
  + apply muf_eq_compat => a Ha /=;congr;apply muf_eq_compat => l Hl /=;congr.
    apply BBM.eq_big_nat => i Hi /=; smt.
  rewrite muf_mulc_r (Hrec (fun i => Ps (i+1)));congr. 
  + rewrite dcomp_def;apply muf_eq_compat;smt.
  apply BRM.eq_big_nat => i Hi /=;apply muf_eq_compat=> m Hm /=;smt. 
qed.

lemma hindeps_eindeps (d:'m distr) (Xs:('m -> 'a)list):
  hindep d (map I_ Xs) <=> eindeps d Xs.
proof. by rewrite hindeps_indeps indeps_eindeps. qed.

lemma hindeps_pwindeps (d:'m distr) (Xs:('m -> 'a)list):  
  hindep d (map I_ Xs) <=> pwindeps d Xs.
proof. by rewrite hindeps_eindeps pwindeps_eindeps. qed.

lemma indeps_pwindeps (d:'m distr) (Xs:('m -> 'a)list):  
  indeps d Xs <=> pwindeps d Xs.
proof. by rewrite indeps_eindeps pwindeps_eindeps. qed.

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
  cut {Hv} /valid2_catPr [Ps_ Ps' [->> [Hv Hv']]] := Hv. 
  cut {Hv'} /valid2_catPr [Ps3 Ps'' [->> [Hv3 Hv']]] := Hv'.
  cut {Hv'} /valid2_cPr [P Ps4 [->> [HP Hv4]]] := Hv'.
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

lemma eindeps_eindep (d:'m distr) (X:'m -> 'a) (Xs: ('m -> 'a) list):
  eindeps d (X :: Xs) =>
  eindep d X (fun m => map (appf m) Xs).
proof. 
  move=> Hind;rewrite /eindep.
  case (Xs = []) => HeqXs.
  + rewrite HeqXs -distr_ext => f. 
    rewrite dprod_def /= dcomp_def dmulc_def /=;
      1: by apply d_compat_dcomp;apply d_compat_weight.
    by rewrite !dcomp_def /(\o) /fpair muf_c muf_mulc_r RField.mulrC.  
  case (DistrOp.weight d = 0%r). 
  + by rewrite w0_dzero => ->;rewrite !dzero_dcomp dprod0l dmulc_dzero. 
  move=> Hpr.
  cut /hindeps_indeps /indeps_eindeps HXS := hindep_Icons X d (map I_ Xs) _. 
  + by rewrite -map_cons hindeps_indeps indeps_eindeps. 
  cut Hs : 0 < size Xs by smt.
  cut Hbd:= weight_bounded d.
  cut Hsi : 0 <= size Xs - 1 by smt.
  rewrite -(dmulc_eq_compat1 ((DistrOp.weight d)^(size Xs - 1))).
  + apply Rpow_bounded_lt; smt. 
  cut Hbd' := Rpow_bounded _ _ Hbd Hsi.
  rewrite dmulcA. 
  + apply d_compat_dcomp;apply d_compat_weight.
  + apply d_compat_1. rewrite RField.mulrC -Rpow_S //; smt. 
  rewrite RField.mulrC -Rpow_S //.  
  cut -> : d \o (fun (m : 'm) => (X m, map (fun (Xi : 'm -> 'a) => Xi m) Xs)) = 
            (d \o (fun m => map (fun Xi => Xi m) (X::Xs))) \o
            (fun (l:'a list) => (head Option.witness l, drop 1 l)).
  + by rewrite dcomp_dcomp /(\o) map_cons drop_cons /= drop0.
  move:Hind;rewrite /eindeps. 
  rewrite (_:size Xs - 1 + 1 = size Xs) 1:smt.
  rewrite (_: size (X :: Xs) - 1 = size Xs) 1:smt => [ | H];1:smt.
  rewrite -dcomp_dmulc 1:smt H.
  cut -> : (dlist (map ((\o) d) (X :: Xs))) \o
             (fun (l : 'a list) => (head Option.witness l, drop 1 l)) = 
           (d \o X) * dlist (map ((\o) d) Xs).
  + apply eq_distr_ext => f.
    rewrite dcomp_def dprod_def /dlist /= dcons_def /= !dcomp_def. 
    by simplify Fun.(\o);rewrite drop0.
  rewrite dmulc_dprod_r;1:by apply d_compat_dcomp;smt. 
  by congr;move: HXS;rewrite /eindeps HeqXs /= => ->.
qed.


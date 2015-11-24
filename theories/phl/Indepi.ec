(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require export Indep.
require import IntDiv.
(*---*) import List Real Int StdBigop StdRing Bigreal.BRM.

pragma +withbd.

pred indepsi (d:'m distr) (Xi: int -> 'm -> 'a) (i j : int) = 
 forall (Ps : int -> 'a -> bool),
    j <= i \/
    $[fun m => 1%r | d] ^ (j-i-1) *
    $[fun (m : 'm) => b2r (BBM.bigi predT (fun k => Ps k (Xi k m)) i j) | d] =
     bigi predT (fun k => $[fun m => b2r (Ps k (Xi k m)) | d]) i j.

pred follows (d:'m distr) (X:'m -> 'a) (da:'a distr) = 
  forall (f:'a -> real), $[fun m => f (X m)| d] = $[f | da] * $[fun m => 1%r | d].

pred followsi (d:'m distr) (X:int -> 'm -> 'a) (da:'a distr) (i j : int) = 
  forall (k:int), i <= k < j => follows d (X k) da.

require import Option.

lemma indepsi_indeps (d:'m distr) (Xi:int -> 'm -> 'a) (i j:int):  
   indepsi d Xi i j <=> indeps d (map Xi (range i j)).
proof.
  rewrite /indepsi /indeps size_map size_range /DistrOp.weight /PR.
  case (j <= i) => Hij /=.   
  + by rewrite range_geq.
  cut -> : max 0 (j - i) = j - i by smt ml=0.
  split=> Hi Ps.
  + right;cut {Hi} /= Hi := Hi (fun k => Ps (k - i)).
    apply (eq_trans _ (bigi predT
              (fun (k : int) => $[fun (m : 'm) => b2r (Ps (k - i) (Xi k m)) | d]) i j)).
    + rewrite -Hi;congr;apply muf_eq_compat=> m Hm {Hi}/=;congr.
      rewrite {4}(_: i = 0 + i) 1:// BBM.big_addn; apply BBM.eq_big_int => /= i0 Hi0.
      rewrite (nth_map witness) 1:size_range 1:[smt ml=0] nth_range //; smt ml=0.
    rewrite {2}(_: i = 0 + i) // big_addn; apply eq_big_int => /= i0 Hi0.
    apply muf_eq_compat => m Hm.
    rewrite (nth_map witness) 1:size_range 1:[smt ml=0] nth_range //; smt ml=0.
  cut {Hi} /= [ | Hi] := Hi (fun k => Ps (k + i));1:smt.
  apply (eq_trans _ 
    (bigi predT
      (fun (i0 : int) =>
          $[fun (x : 'm) => b2r (Ps (i0 + i) (nth witness (map Xi (range i j)) i0 x)) | d])
              0 (j - i))).
  + rewrite -Hi;congr;apply muf_eq_compat=> m Hm {Hi}/=;congr.
      rewrite {1}(_: i = 0 + i) 1:// BBM.big_addn; apply BBM.eq_big_int => /= i0 Hi0.
      rewrite (nth_map witness) 1:size_range 1:[smt ml=0] nth_range //; smt ml=0.
    rewrite {4}(_: i = 0 + i)// big_addn; apply eq_big_int => /= i0 Hi0.
    apply muf_eq_compat => m Hm.
    rewrite (nth_map witness) 1:size_range 1:[smt ml=0] nth_range //; smt ml=0.  
qed.

lemma indepsi_sub (i j k l: int) (d:'m distr) (Xi: int -> 'm -> 'a):
   k <= i => j <= l => indepsi d Xi k l => indepsi d Xi i j.
proof.
  move=> Hi Hj;rewrite !indepsi_indeps.
  case (i <= j) => Hij.
  + rewrite (range_cat i k l) // 1:[smt ml=0] (range_cat j i l) // !map_cat.
    by rewrite -!hindep_indeps !map_cat=> /hindep_Icat_r /hindep_Icat_l.
  rewrite /indeps=> ? ?;left;smt.
qed.

abstract theory INDEPi.

  type from.
  type 'to map.

  op "_.[_]" : 'to map -> from -> 'to.
  op "_.[_<-_]" : 'to map -> from -> 'to -> 'to map.
 
  pred wf_from : ('to map , from).
  
  axiom get_set_eq m x (v:'to): wf_from m x => m.[x <- v].[x] = v.
  axiom get_set_neq m x y (v:'to): wf_from m x => wf_from m y => x <> y => m.[x <- v].[y] = m.[y].

  op fromint : 'to map -> int -> from.

  lemma indepsi_update (T:'m -> 'to map) (i:'m -> from) I (mu:'m distr) (d:'to distr):
    (forall m i j, 0 <= i <= I => 0 <= j <= I => fromint (T m) i = fromint (T m) j => i = j) =>
    $[fun m=> 1%r | d] = 1%r =>
    $@[fun m => i m = fromint (T m) I /\ 
                forall k, 0 <= k <= I => wf_from (T m) (fromint (T m) k) | mu] =>
    indepsi mu (fun k m => (T m).[fromint (T m) k]) 0 I =>
    forall (Ps : int -> 'to -> bool),
      I + 1 <= 0 \/
      $[fun m => 1%r | mu] ^ (I + 1 - 1) *
      $[fun m => $[fun v =>
         b2r (BBM.bigi predT (fun (k : int) => Ps k (T m).[i m <- v].[fromint (T m) k]) 0 (I + 1))
       | d] | mu] =
      bigi predT
       (fun (k : int) =>
          $[fun m => $[fun v => b2r (Ps k (T m).[i m<- v].[fromint (T m) k]) | d] | mu]) 0 (I + 1).
  proof.
    move=> Hinj Hd Hs Hind Ps.
    case (0 <= I) => Hi1;[right | by left;smt ml=0].
    rewrite BBM.big_int_recr // big_int_recr //=.
    cut ->:
      $[fun m =>  $[fun v =>
         b2r
          (BBM.bigi predT (fun (k : int) => Ps k (T m).[i m <- v].[fromint (T m) k]) 0 I /\
           Ps I (T m).[i m <- v].[fromint (T m) I]) | d] | mu] =
      $[fun m=> $[fun v=>b2r(BBM.bigi predT (fun k => Ps k (T m).[fromint (T m) k]) 0 I /\ Ps I v) 
                 | d ]| mu].
    + move:Hs;apply square_eq => /= m Hm;progress.
      apply muf_eq_compat => /= v Hv;congr;congr;2:by rewrite H get_set_eq //;apply H0.
      apply BBM.congr_big_int=> //= i0 [_ Hi0];cut := get_set_neq (T m);smt ml = 0.
    rewrite b2r_and muf_mulc_l muf_mulc_r.
    cut ->:
      bigi predT
        (fun k => $[fun m => $[fun v => b2r (Ps k (T m).[i m <- v].[fromint (T m) k]) | d] | mu]) 0 I =
      bigi predT
        (fun k => $[fun m => b2r (Ps k (T m).[fromint (T m) k]) | mu]) 0 I.
    + apply congr_big_int=> //= k [_ Hk].
      move:Hs;apply square_eq => m Hm {Hm};progress. 
      rewrite -(muf_c_ll (b2r (Ps k (T m).[fromint (T m) k])) d) //.
      apply muf_eq_compat => /= v Hv;cut:=get_set_neq (T m);smt ml=0.
    cut -> :
     $[fun (m : 'm) => $[fun v => b2r (Ps I (T m).[i m <- v].[fromint (T m) I]) | d] | mu] =
     $[fun v => b2r (Ps I v) | d] * $[fun (m : 'm) => 1%r| mu].
    + rewrite -muf_mulc_l;move:Hs;apply square_eq => m Hm {Hm};progress. 
      by apply muf_eq_compat => /= v Hv;rewrite H get_set_eq //;apply H0.
    cut := Hind Ps;rewrite -ora_or => {Hind} [] Hind.
    cut -> /= : I = 0 by smt ml=0.
    + by rewrite Power_0 -One /Int.one /= BBM.big_geq // 
      big_geq //= b2r_true RField.mulrC.
    cut -> : I - 0 - 1 = I - 1 by ringeq.
    cut -> : I + 1 - 1 = I - 1 + 1 by ringeq.
    move=> <-;rewrite Power_s 1:[smt ml=0];ringeq.
  qed.
 
  lemma followsi_update (T:'m -> 'to map) (i:'m -> from) I (mu:'m distr) (d:'to distr):
    (forall m i j, 0 <= i <= I => 0 <= j <= I => fromint (T m) i = fromint (T m) j => i = j) =>
    $[fun m=> 1%r | d] = 1%r =>
    $@[fun m => i m = fromint (T m) I /\ forall k, 0 <= k <= I => wf_from (T m) (fromint (T m) k) | mu] =>
    followsi mu (fun i m => (T m).[fromint (T m) i]) d 0 I =>
    forall (k : int),
      0 <= k < I + 1 =>
      forall (f : 'to -> real),
      $[fun m => $[fun v => f (T m).[i m <- v].[fromint (T m) k] | d] | mu] =
      $[f | d] * $[fun m => 1%r | mu].
  proof.
    move=> Hinj Hd Hs Hind k Hk f.
    case (k < I) => HkI.  
    + rewrite -(Hind k _ f);1:by move:Hk.
      move: Hs;apply square_eq => m Hm;progress. 
      rewrite -(muf_c_ll (f (T m).[fromint (T m) k]) d) 1:Hd //. 
      by apply muf_eq_compat => v Hv /=; smt.
    rewrite -muf_mulc_l -muf_mulc_r /=. 
    move:Hs; apply square_eq => m Hm;progress.
    apply muf_eq_compat => v Hv /=;smt.
  qed.

end INDEPi.

(* Instanciation with array *)
require import Array.

clone INDEPi as ArrIndep with
   type from <- int,
   type 'a map <- 'a array,
   op "_.[_]" <- Array."_.[_]" <:'to>,
   op "_.[_<-_]" <- Array."_.[_<-_]" <:'to>,
   pred wf_from <- fun (t:'a array) (i:int) => 0 <= i < Array.length t,
   op fromint <- fun (t:'a array) (i:int) => i
   proof * by smt.


(* Instanciation with Matrix *)
theory Matrix.

  type 'a matrix.

  op make : int -> int -> 'a -> 'a matrix.

  op size : 'a matrix -> int * int.

  op "_.[_]" : 'a matrix -> int*int -> 'a.
  op "_.[_<-_]" : 'a matrix -> int*int -> 'a -> 'a matrix.

  axiom size_make n m (v:'a) : 0 < n => 0 < m => size (make n m v) = (n,m).
  axiom size_pos (m:'a matrix) : 0 < (size m).`1 /\ 0 < (size m).`2.
  axiom size_upd (p:'a matrix) (ij:int*int) v : size p.[ij <- v] = size p.

  op wf_index (m:'a matrix) (ij:int*int) = 
    0 <= ij.`1 < (size m).`1 /\ 0 <= ij.`2 < (size m).`2.

  axiom get_seq_eq m x (v:'a): wf_index m x => m.[x <- v].[x] = v.
  axiom get_set_neq m x y (v:'a): wf_index m x => wf_index m y => x <> y => m.[x <- v].[y] = m.[y].

  op fromint (m:'a matrix) (k:int) = (k %/ (size m).`1, k %% (size m).`1).

  lemma fromint_inj (t:'a matrix) : Fun.injective (fromint t)
  by [].

  clone INDEPi as MatIndep with
   type from <- int*int,
   type 'a map <- 'a matrix,
   op "_.[_]" <- "_.[_]" <:'a>,
   op "_.[_<-_]" <- "_.[_<-_]" <:'a>,
   pred wf_from <- wf_index <:'a>,
   op fromint <- fromint <:'a> 
   proof * by smt.
 
end Matrix.


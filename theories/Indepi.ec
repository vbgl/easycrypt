require export Indep.
import Real Int StdBigop StdRing.

pred indepsi (d:'m distr) (Xi: int -> 'm -> 'a) (i j : int) = 
 forall (Ps : int -> 'a -> bool),
    j <= i \/
    $[fun m => 1%r | d] ^ (j-i-1) *
    $[fun (m : 'm) => b2r (BBM.bigi predT (fun k => Ps k (Xi k m)) i j) | d] =
     BRM.bigi predT (fun k => $[fun m => b2r (Ps k (Xi k m)) | d]) i j.

pred follows (d:'m distr) (X:'m -> 'a) (da:'a distr) = 
  forall (f:'a -> real), $[fun m => f (X m)| d] = $[f | da] * $[fun m => 1%r | d].

pred followsi (d:'m distr) (X:int -> 'm -> 'a) (da:'a distr) (i j : int) = 
  forall (k:int), i <= k < j => follows d (X k) da.

abstract theory INDEPi.

  type from.
  type 'to map.

  op "_.[_]" : 'to map -> from -> 'to.
  op "_.[_<-_]" : 'to map -> from -> 'to -> 'to map.
 
  pred wf_from : ('to map , from).
  
  axiom get_set_eq m x (v:'to): wf_from m x => m.[x <- v].[x] = v.
  axiom get_set_neq m x y (v:'to): wf_from m x => wf_from m y => x <> y => m.[x <- v].[y] = m.[y].

  op fromint : 'to map -> int -> from.
  axiom fromint_inj (t:'a map) : Fun.injective (fromint t). 

  lemma indepsi_update (T:'m -> 'to map) (i:'m -> from) I (mu:'m distr) (d:'to distr):
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
      BRM.bigi predT
       (fun (k : int) =>
          $[fun m => $[fun v => b2r (Ps k (T m).[i m<- v].[fromint (T m) k]) | d] | mu]) 0 (I + 1).
  proof.
    move=> Hd Hs Hind Ps.
    case (0 <= I) => Hi1;[right | by left;smt]. 
    rewrite BBM.big_nat_recr // BRM.big_nat_recr //=.
    cut ->:
      $[fun m =>  $[fun v =>
         b2r
          (BBM.bigi predT (fun (k : int) => Ps k (T m).[i m <- v].[fromint (T m) k]) 0 I /\
           Ps I (T m).[i m <- v].[fromint (T m) I]) | d] | mu] =
      $[fun m=> $[fun v=>b2r(BBM.bigi predT (fun k => Ps k (T m).[fromint (T m) k]) 0 I /\ Ps I v) 
                 | d ]| mu].
    + move:Hs;apply square_eq => /= m Hm;progress.
      apply muf_eq_compat => /= v Hv;congr;congr;2:smt.
      apply BBM.congr_big_nat=> //=; smt.
    rewrite b2r_and muf_mulc_l muf_mulc_r.
    cut ->:
      BRM.bigi predT
        (fun k => $[fun m => $[fun v => b2r (Ps k (T m).[i m <- v].[fromint (T m) k]) | d] | mu]) 0 I =
      BRM.bigi predT
        (fun k => $[fun m => b2r (Ps k (T m).[fromint (T m) k]) | mu]) 0 I.
    + apply BRM.congr_big_nat=> //= k [_ Hk].
      move:Hs;apply square_eq => m Hm {Hm};progress. 
      rewrite -(muf_c_ll (b2r (Ps k (T m).[fromint (T m) k])) d) //.
      apply muf_eq_compat => /= v Hv;smt.
    cut -> :
     $[fun (m : 'm) => $[fun v => b2r (Ps I (T m).[i m <- v].[fromint (T m) I]) | d] | mu] =
     $[fun v => b2r (Ps I v) | d] * $[fun (m : 'm) => 1%r| mu].
    + rewrite -muf_mulc_l;move:Hs;apply square_eq => m Hm {Hm};progress. 
      apply muf_eq_compat => /= v Hv;smt.
    cut := Hind Ps;rewrite -ora_or => {Hind} [] Hind.
    cut -> /= : I = 0 by smt.
    + by rewrite Power_0 -One /Int.one /= BBM.big_geq // 
      BRM.big_geq //= b2r_true RField.mulrC.
    cut -> : I - 0 - 1 = I - 1 by ringeq.
    cut -> : I + 1 - 1 = I - 1 + 1 by ringeq.
    move=> <-;rewrite Power_s 1:smt;ringeq.
  qed.
 
  lemma followsi_update (T:'m -> 'to map) (i:'m -> from) I (mu:'m distr) (d:'to distr):
    $[fun m=> 1%r | d] = 1%r =>
    $@[fun m => i m = fromint (T m) I /\ forall k, 0 <= k <= I => wf_from (T m) (fromint (T m) k) | mu] =>
    followsi mu (fun i m => (T m).[fromint (T m) i]) d 0 I =>
    forall (k : int),
      0 <= k < I + 1 =>
      forall (f : 'to -> real),
      $[fun m => $[fun v => f (T m).[i m <- v].[fromint (T m) k] | d] | mu] =
      $[f | d] * $[fun m => 1%r | mu].
  proof.
    move=> Hd Hs Hind k Hk f.
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

  op fromint (m:'a matrix) (k:int) = (k /% (size m).`1, k %% (size m).`1).

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


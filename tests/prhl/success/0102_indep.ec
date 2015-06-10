require import Distr.
require import Bool.
require import Real.

type t.
op sample : t distr.
axiom sample_ll : muf (fun (x:t)=> 1%r) sample = 1%r.

module M = {
  var x:t
  var y:t

  proc main() : unit = {
    x = $sample;
    y = $sample;
  }
}.

axiom muf_mulc_l' ['a]:
  forall (f : 'a -> real) (c : real) (d : 'a distr),
    muf (fun (x : 'a) => c * f x) d = c * muf f d.

lemma Mindep v w : muhoare[M.main : $[1%r]=1%r ==> $[b2r (M.x = v /\ M.y = w)] = $[b2r (M.x = v)] * $[b2r(M.y = w)] ].
proof.
  proc;auto=> mu Hll.
  do !(rewrite ?b2r_and muf_c (Hll, sample_ll)) => /=.
  rewrite -muf_mulc_r /=;apply muf_congr=> //= a.
  by cut /= -> := (muf_mulc_l (b2r (a = v)) (fun (y_ : t) => b2r (y_ = w)) sample).
qed.

lemma Mindep' : muhoare[M.main : $[1%r]=1%r ==> forall v w, $[b2r (M.x = v /\ M.y = w)] = $[b2r (M.x = v)] * $[b2r(M.y = w)] ].
proof.
  proc;auto=> mu Hll v w.
  do !(rewrite muf_c Hll) => /=.
  apply (eq_trans _ (muf (fun (x_ : t) =>  b2r (x_ = v) * muf (fun (y_ : t) => b2r (y_ = w)) sample) sample)).
  by apply muf_congr=> //= a; rewrite -muf_mulc_l;apply muf_congr=> //= a0;rewrite b2r_and.
  rewrite muf_c -Assoc.Assoc sample_ll /=.
  cut -> : 
    muf (fun (x_ : t) => muf (fun (y_ : t) => b2r (x_ = v)) sample) sample = 
    muf (fun (x_ : t) => b2r (x_ = v)) sample.
  + by apply muf_congr => //= a;rewrite muf_c sample_ll.
  by rewrite -muf_mulc_r.        
qed.

(*lemma Mindep' : muhoare[M.main : $[1%r]=1%r ==> fun mu => indep (fun m => M.x{m}) (fun m => M.y{m}) mu].
proof.
  proc;auto=> mu Hll v w.
  do !(rewrite muf_c Hll) => /=.
  apply (eq_trans _ (muf (fun (x_ : t) =>  b2r (x_ = v) * muf (fun (y_ : t) => b2r (y_ = w)) sample) sample)).
  by apply muf_congr=> //= a; rewrite -muf_mulc_l;apply muf_congr=> //= a0;rewrite b2r_and.
  rewrite muf_c -Assoc.Assoc sample_ll /=.
  cut -> : 
    muf (fun (x_ : t) => muf (fun (y_ : t) => b2r (x_ = v)) sample) sample = 
    muf (fun (x_ : t) => b2r (x_ = v)) sample.
  + by apply muf_congr => //= a;rewrite muf_c sample_ll.
  by rewrite -muf_mulc_r.        
qed. *)


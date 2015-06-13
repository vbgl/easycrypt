require import DistrF.
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

lemma Mindep v w : muhoare[M.main : $[1%r]=1%r ==> $[b2r (M.x = v /\ M.y = w)] = $[b2r (M.x = v)] * $[b2r(M.y = w)] ].
proof.
  proc;auto=> mu Hll.
  by rewrite b2r_and !(muf_mulc_l, muf_mulc_r) !(muf_c_ll _ _ Hll) 
             !(muf_c_ll _ _ sample_ll).
qed.

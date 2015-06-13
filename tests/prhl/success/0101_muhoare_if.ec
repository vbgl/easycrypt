require import DistrF.
require import Bool.
require import Real.
require import Int.

module M = { 
  var x:int


  proc main(z:int) : bool = {
    var b, w;
    b = ${0,1};
    if (b) {
      x = 3;
      w = x + z;
    } else {
      x = 4;
      w = z + x;
    }
    return (b /\ w = x + z);
  }
}.

lemma test1 : muhoare [M.main : 
     $[1%r] = 1%r ==> $[b2r (M.x = 3)] = 1%r/2%r /\ $[b2r (M.x = 4)] = 1%r/2%r /\ $[b2r res] = 1%r/2%r].
proof.
  proc.
  wp 1 => /=.
  wp.
  skip.
  move=> mu Hll.
  rewrite (addzC 4) /= -!b2r_and /= andK.
  cut -> : forall (b:bool), (!b /\ b) = false by smt.
  rewrite b2r_false /=.
  by rewrite !(muf_c_ll _ _ Hll) !muf_dbool /=.
qed.

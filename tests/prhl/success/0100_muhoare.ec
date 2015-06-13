require import DistrF.
require import Bool.
require import Real.

module M = { 
  var x:int


  proc main() : bool = {
    var b;
    b = ${0,1};
    x = 3;
    return b;
  }
}.

lemma test1 : muhoare [M.main : 
     $[1%r] = 1%r ==> $[b2r (M.x = 3)] = 1%r /\ $[b2r res] = 1%r/2%r].
proof.
  proc.
  wp 1 => /=.
  wp.
  skip.
  move=> mu Hll.
  by rewrite !(muf_c_ll _ _ Hll) (muf_c_ll _ _ dbool_ll) muf_dbool.
qed.


  
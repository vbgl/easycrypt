require import Distr.
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

axiom muf_bool (f:bool -> real) : muf f {0,1} = 
   1%r/2%r * f true + 1%r/2%r * f false.

axiom muf_congr (f1 f2:'a -> real) (d:'a distr) :
   (forall x, f1 x = f2 x) => muf f1 d = muf f2 d.

lemma test1 : muhoare [M.main : 
     $[1%r] = 1%r ==> $[b2r (M.x = 3)] = 1%r /\ $[b2r res] = 1%r/2%r].
proof.
  proc.
  wp 1 => /=.
  wp.
  skip.
  move=> mu Hll.
  by rewrite muf_c Hll muf_bool muf_c Hll muf_bool.
qed.


  
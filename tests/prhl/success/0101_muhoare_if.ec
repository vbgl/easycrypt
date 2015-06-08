require import Distr.
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

axiom muf_bool (f:bool -> real) : muf f {0,1} = 
   1%r/2%r * f true + 1%r/2%r * f false.

axiom muf_congr (f1 f2:'a -> real) (d:'a distr) :
   (forall x, f1 x = f2 x) => muf f1 d = muf f2 d.

lemma test1 : muhoare [M.main : 
     $[1%r] = 1%r ==> $[b2r (M.x = 3)] = 1%r/2%r /\ $[b2r (M.x = 4)] = 1%r/2%r /\ $[b2r res] = 1%r/2%r].
proof.
  proc.
  wp 1 => /=.
  wp.
  skip.
  move=> mu Hll.
  rewrite muf_c Hll muf_bool /=.
  rewrite muf_c Hll muf_bool /=.
  split=> //. split => //.
  apply (eq_trans _ (muf (fun hr =>
                      muf (fun (b_ : bool) => b2r b_ * b2r (b_) + b2r (! b_) * b2r (b_)) {0,1})
                     mu)).
  apply muf_congr => m /=; apply muf_congr => b /=; by rewrite addzC.
  by rewrite muf_c Hll muf_bool.
qed.

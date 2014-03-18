require import Distr.
require import Int.
require import Real.
require import FMap. import Core.
require import FSet.
require import CDH.
require (*--*) AWord.
require (*--*) RandOrcl.
require (*--*) PKE.

(** We extend the basic lazy random oracle with a generic argument
    replacing a single oracle call in the middle of an experiment
    with a random sampling. The probability of distinguishing the
    two is bounded by the probability that another query in the
    experiment collides with the one we singled out. Ideally, this
    should be pushed into either the ROM library, or into a
    ProveIt-specific context.                                       *)
theory ROM_Call.
  type from.
  type to.

  op dsample: to distr.
  axiom dsampleL: mu dsample cpTrue = 1%r.

  op qH:int.
  axiom qH_pos: 0 < qH.

  clone import RandOrcl as ROM with
    type from  <- from,
    type to    <- to,
    op dsample <- dsample.

  module type Dist(H:ARO) = {
    fun a1(): from
    fun a2(x:to): bool
  }.

  module ARO(O:ARO) = {
    var qs:from set

    fun o(x:from): to = {
      var r:to = default;

      if (card qs < qH) {
        r  = O.o(x);
        qs = add x qs;
      }
      return r;
    }
  }.

  module Bounder(D:Dist,O:ARO) = {
    module D' = D(ARO(O))

    fun a1(): from = { var x:from; x = D'.a1(); return x; }
    fun a2(y:to): bool = { var b:bool; b = D'.a2(y); return b; }
  }.

  module G0(D:Dist, H:Oracle) = {
    module D = Bounder(D,H)

    fun main(): bool = {
      var x:from;
      var y:to;
      var b:bool;

      H.init();
      ARO.qs = FSet.empty;
      x = D.a1();
      y = H.o(x);
      b = D.a2(y);
      return b;
    }
  }.

  module G1(D:Dist, H:Oracle) = {
    module D = Bounder(D,H)

    var x:from

    fun main(): bool = {
      var y:to;
      var b:bool;

      H.init();
      ARO.qs = FSet.empty;
      x = D.a1();
      y = $dsample;
      b = D.a2(y);
      return b;
    }
  }.

  module G2(D:Dist, H:Oracle) = {
    module D = Bounder(D,H)

    var x:from

    fun main(): bool = {
      var y:to;
      var b:bool;

      H.init();
      ARO.qs = FSet.empty;
      x = D.a1();
      y = $dsample;
      b = D.a2(y);
      return mem x ARO.qs;
    }
  }.

  lemma Abstract_Bad (D <: Dist {Bounder, ROM.RO, G1, G2}) &m:
    (forall (H <: ARO {D}), islossless H.o => islossless D(H).a1) =>
    (forall (H <: ARO {D}), islossless H.o => islossless D(H).a2) =>
    Pr[G0(D,ROM.RO).main() @ &m: res]
    <= Pr[G1(D,ROM.RO).main() @ &m: res]
     + Pr[G2(D,ROM.RO).main() @ &m: res].
  proof.
    intros=> Da1L Da2L.
    cut ->: Pr[G2(D,ROM.RO).main() @ &m: res] = Pr[G1(D,ROM.RO).main() @ &m: mem G1.x ARO.qs].
      equiv_deno (_: ={glob D} ==> res{1} = (mem G1.x ARO.qs){2})=> //.
      fun.
      call (_: ={glob D, glob ARO, glob ROM.RO}).
        call (_: ={glob ARO, glob ROM.RO});
          first by fun; sp; if=> //; inline ROM.RO.o;
                   wp; rnd; wp; skip; progress; smt.
        by skip; smt.
      rnd; call (_: ={glob D, glob ARO, glob ROM.RO}).
        call (_: ={glob ARO, glob ROM.RO});
          first by fun; sp; if=> //; inline ROM.RO.o;
                   wp; rnd; wp; skip; progress; smt.
        by skip; smt.
      by inline *; wp.
    cut: Pr[G0(D,ROM.RO).main() @ &m: res] <= Pr[G1(D,ROM.RO).main() @ &m: res \/ mem G1.x ARO.qs].
      equiv_deno (_: ={glob D} ==> !mem G1.x{2} ARO.qs{2} => ={res})=> //; last smt.
      fun; inline G0(D,ROM.RO).D.a2 G1(D,ROM.RO).D.a2.
      wp; call (_: mem G1.x ARO.qs,
                   ={ARO.qs} /\
                   ARO.qs{2} = dom ROM.RO.m{2} /\
                   eq_except ROM.RO.m{1} ROM.RO.m{2} G1.x{2})=> //.
        fun; sp; if=> //; inline ROM.RO.o; wp; rnd; wp; skip; progress; first 2 smt.
          rewrite eq_except_def=> x' neq.
          by cut:= H0; rewrite eq_except_def=> H0'; cut:= H0' x' _=> //; smt.
          smt.
          smt.
          case (x{2} = G1.x{2}); first smt.
          by intros=> neq; cut:= H0; rewrite eq_except_def; smt.
          smt.
          smt.
          case (x{2} = G1.x{2}); first smt.
          by intros=> neq; cut:= H0; rewrite eq_except_def; smt.
          smt.
          smt.
        by progress; fun; sp; if=> //; wp; call (ROM.lossless_o _); first smt.
        by progress; fun; sp; if=> //; wp; call (ROM.lossless_o _); [smt | skip; smt].
      inline ROM.RO.o; wp; rnd; wp.
      call (_: ={glob D, glob ARO, glob ROM.RO} /\ ARO.qs{2} = dom ROM.RO.m{2}).
        call (_: ={glob ARO, glob ROM.RO} /\ ARO.qs{2} = dom ROM.RO.m{2})=> //.
        by fun; sp; if=> //; inline ROM.RO.o; wp; rnd; wp; skip; progress; smt.
      by inline ROM.RO.init; wp; skip; progress; expect 7 smt.
    by rewrite Pr mu_or; smt.
  qed.
end ROM_Call.

(* The type of plaintexts: bitstrings of length k *)
type bits.
op k: int.
axiom k_pos: 0 < k.

op uniform: bits distr.
axiom uniformU: isuniform uniform.
axiom uniformX x: mu uniform ((=) x) = 1%r/(2^k)%r.
axiom uniformL: mu uniform cpTrue = 1%r.

op (^^): bits -> bits -> bits.

clone import AWord as Bitstring with
  type word <- bits,
  op length <- k,
  op (^) <- (^^),
  op Dword.dword <- uniform
proof
  Dword.*     by smt,
  leq0_length by smt.

(* Upper bound on the number of calls to H *)
op qH: int.
axiom qH_pos: 0 < qH.

(* Assumption *)
clone Set_CDH as SCDH with
  op n <- qH.

import Group.

type pkey       = group.
type skey       = int.
type plaintext  = bits.
type ciphertext = group * bits.

clone import PKE as PKE_ with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext. 

module type Hash = {
  fun init(): unit
  fun hash(x:group): bits
}.

module Hashed_ElGamal (H:Hash): Scheme = {
  fun kg(): pkey * skey = {
    var sk:skey;

    H.init();
    sk = $[0..q-1];
    return (g ^ sk, sk);   
  }

  fun enc(pk:pkey, m:plaintext): ciphertext = {
    var y:int;
    var h:bits;

    y = $[0..q-1];
    h = H.hash(pk ^ y);
    return (g ^ y, h ^^ m);
  }

  fun dec(sk:skey, c:ciphertext): plaintext option = {
    var gy:group;
    var h:bits;
    var hm:bits;

    (gy, hm) = c; 
    h = H.hash(gy ^ sk);
    return Option.Some (h ^^ hm); 
  }
}.

clone import ROM_Call as ROC with
  type from  <- group,
  type to    <- bits,
  op dsample <- uniform,
  op qH      <- qH
proof * by smt.

import ROM.

(* Adversary Definitions *)
module type Adversary (O:ARO) = {
  fun choose(pk:pkey)    : plaintext * plaintext
  fun guess(c:ciphertext): bool
}.

module Bounder'(A:Adversary,O:ARO) = {
  module A' = A(ARO(O))

  fun choose(pk:pkey): plaintext * plaintext = { var r:plaintext * plaintext; r = A'.choose(pk); return r; }
  fun guess(c:ciphertext): bool  = { var b:bool; b = A'.guess(c); return b; }
}.

(* Specializing and merging the hash function *)
module H:Hash = {
  fun init(): unit = { ROM.RO.init(); ARO.qs = FSet.empty; }
  fun hash(x:group): bits = { var y:bits; y = ROM.RO.o(x); return y; }
}.

(* The initial scheme *)
module S = Hashed_ElGamal(H).

(* Correctness result *)
lemma Correctness: hoare [Correctness(S).main: true ==> res].
proof.
  fun; inline *; do !(wp; rnd); wp; skip; progress.
    smt.
    cut ->: g ^ y4 ^ sk0 = g ^ sk0 ^ y4 by smt.
    smt.
    smt.
    smt.
qed.

(* The reduction *)
module SCDH_from_CPA(A:Adversary,O:ARO): SCDH.Adversary = {
  module BA = Bounder'(A,O)

  fun solve(gx:group, gy:group): group set = {
    var m0, m1:plaintext;
    var h:bits;
    var b':bool;

    H.init();
    (m0,m1)  = BA.choose(gx);
    h        = $uniform;
    b'       = BA.guess((gy, h));
    return ARO.qs;
  }
}.

(* We want to bound the probability of A winning CPA(Bounder(A,RO),S) in terms of
   the probability of B = CDH_from_CPA(SCDH_from_CPA(A,RO)) winning CDH(B) *)
section.
  declare module A: Adversary {ROM.RO, Bounder, ROC.G1, ROC.G2, SCDH.SCDH'}.

  axiom chooseL (O <: ARO {A}): islossless O.o => islossless A(O).choose.
  axiom guessL (O <: ARO {A}) : islossless O.o => islossless A(O).guess.

  local module BA = Bounder'(A,ROM.RO).

  local module G0 = {
    var gxy:group

    fun main(): bool = {
      var m0, m1:plaintext;
      var c:ciphertext;
      var b, b':bool;
      var x, y:int;
      var h:bits;
      var gx:group;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = H.hash(gxy);
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = BA.guess(c);
      return (b' = b);
    }
  }.

  local equiv RO_equiv: ROM.RO.o ~ ROM.RO.o:
    ={glob ROM.RO, x} ==> ={glob ROM.RO, res}.
  proof. by fun; wp; rnd; skip; progress; smt. qed.

  local equiv ARO_equiv: ARO(ROM.RO).o ~ ARO(ROM.RO).o:
    ={glob ROM.RO, glob ARO, x} ==>
    ={glob ROM.RO, glob ARO, res}.
  proof. by fun; sp; if=> //; wp; call RO_equiv. qed.

  local equiv ARO_equiv_full: ARO(ROM.RO).o ~ ARO(ROM.RO).o:
    ={glob ROM.RO, glob ARO, x} /\ dom ROM.RO.m{1} = ARO.qs{1} ==>
    ={glob ROM.RO, glob ARO, res} /\ dom ROM.RO.m{1} = ARO.qs{1}.
  proof.
    fun; sp; if=> //.
    inline ROM.RO.o.
    by wp; rnd; wp; skip; progress; smt.
  qed.

  local equiv CPA_G0: CPA(S,BA).main ~ G0.main: ={glob A} ==> ={res}.
  proof.
    fun.
    inline Hashed_ElGamal(H).kg Hashed_ElGamal(H).enc.
    swap{1} 8 -5.
    call (_: ={glob A, glob ROM.RO, glob ARO}).
      by call (_: ={glob ROM.RO, glob ARO})=> //; fun*; call ARO_equiv.
    wp; call (_: ={glob ROM.RO}); first by call RO_equiv.
    wp; rnd.
    call (_: ={glob A, glob ROM.RO, glob ARO}).
      by call (_: ={glob ROM.RO, glob ARO})=> //; fun*; call ARO_equiv.
    wp; do !rnd.
    by inline *; wp.
  qed.

  local lemma Pr_CPA_G0 &m:
    Pr[CPA(S,BA).main() @ &m: res] = Pr[G0.main() @ &m: res]
  by equiv_deno CPA_G0.

  local module G1 = { 
    fun main() : bool = {
      var m0, m1:plaintext;
      var c:ciphertext;
      var b, b':bool;
      var x, y:int;
      var h:bits;
      var gx, gxy:group;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = BA.guess(c);
      return (b' = b);
    }
  }.

  local module G2 = {
    var gxy : group

    fun main() : bool = {
      var m0, m1:plaintext;
      var c:ciphertext;
      var b, b':bool;
      var x, y:int;
      var h:bits;
      var gx:group;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h ^^ (b ? m1 : m0));
      b'      = BA.guess(c);
      return mem G2.gxy ARO.qs;
    }
  }.

  local module D(H:ARO): ROC.Dist(H) = {
    module A = A(H)

    var y:int
    var b:bool
    var m0, m1:plaintext

    fun a1(): group = {
      var x:int;
      var gx, gxy:group;

      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = A.choose(gx);
      b       = ${0,1};
      return gxy;
    }

    fun a2(x:bits): bool = {
      var c:ciphertext;
      var b':bool;

      c  = (g ^ y, x ^^ (b ? m1 : m0));
      b' = A.guess(c);
      return (b' = b);
    }
  }.

  local lemma G0_D &m: Pr[G0.main() @ &m: res] = Pr[ROC.G0(D,ROM.RO).main() @ &m: res].
  proof.
    equiv_deno (_: ={glob A} ==> ={res})=> //.
    fun.
    inline ROC.G0(D,ROM.RO).D.a1 ROC.G0(D,ROM.RO).D.a2
           Bounder(D,ROM.RO).D'.a1 Bounder(D,ROM.RO).D'.a2
           BA.choose BA.guess; wp.
    conseq* (_: _ ==> b0{1} = b'{2} /\ b{1} = D.b{2})=> //.
    inline H.hash H.init ROM.RO.init.
    call (_: ={glob ROM.RO, glob ARO}); first by fun*; call ARO_equiv.
    wp; call RO_equiv.
    wp; rnd.
    wp; call (_: ={glob ROM.RO, glob ARO}); first by fun*; call ARO_equiv.
    by wp; rnd; rnd; wp.
  qed.

  local lemma G1_D &m: Pr[G1.main() @ &m: res] = Pr[ROC.G1(D,ROM.RO).main() @ &m: res].
  proof.
    equiv_deno (_: ={glob A} ==> ={res})=> //.
    fun.
    inline ROC.G1(D,ROM.RO).D.a1 ROC.G1(D,ROM.RO).D.a2
           Bounder(D,ROM.RO).D'.a1 Bounder(D,ROM.RO).D'.a2
           BA.choose BA.guess; wp.
    conseq* (_: _ ==> b0{1} = b'{2} /\ b{1} = D.b{2})=> //.
    inline H.hash H.init ROM.RO.init.
    call (_: ={glob ROM.RO, glob ARO}); first by fun*; call ARO_equiv.
    wp; rnd.
    wp; rnd.
    wp; call (_: ={glob ROM.RO, glob ARO}); first by fun*; call ARO_equiv.
    by wp; rnd; rnd; wp.
  qed.

  local lemma G2_D &m: Pr[G2.main() @ &m: res] = Pr[ROC.G2(D,ROM.RO).main() @ &m: res].
  proof.
    equiv_deno (_: ={glob A} ==> ={res})=> //.
    fun.
    inline ROC.G2(D,ROM.RO).D.a1 ROC.G2(D,ROM.RO).D.a2
           Bounder(D,ROM.RO).D'.a1 Bounder(D,ROM.RO).D'.a2
           BA.choose BA.guess; wp.
    conseq* (_: _ ==> ={glob ARO} /\ b0{1} = b'{2} /\ b{1} = D.b{2} /\ G2.gxy{1} = ROC.G2.x{2})=> //.
    inline H.hash H.init ROM.RO.init.
    call (_: ={glob ROM.RO, glob ARO}); first by fun*; call ARO_equiv.
    wp; rnd.
    wp; rnd.
    wp; call (_: ={glob ROM.RO, glob ARO}); first by fun*; call ARO_equiv.
    by wp; rnd; rnd; wp.
  qed.

  local lemma G0_G1_G2 &m:
    Pr[G0.main() @ &m: res] <= Pr[G1.main() @ &m: res] + Pr[G2.main() @ &m: res].
  proof.
    rewrite (G0_D &m) (G1_D &m) (G2_D &m).
    apply (Abstract_Bad D &m).
      by progress; fun; rnd; call (chooseL H _)=> //; wp; rnd; rnd; skip; progress; smt.
      by progress; fun; call (guessL H _)=> //; wp.
  qed.

  local module G1' = {
    fun main() : bool = {
      var m0, m1:plaintext;
      var c:ciphertext;
      var b, b':bool;
      var x, y:int;
      var h:bits;
      var gx, gxy:group;

      H.init();
      x       = $[0..q-1];
      y       = $[0..q-1];
      gx      = g ^ x; 
      gxy     = gx ^ y;
      (m0,m1) = BA.choose(gx);
      b       = ${0,1};
      h       = $uniform;
      c       = (g ^ y, h);
      b'      = BA.guess(c);
      return (b' = b);
    }
  }.

  local lemma G1_G1' &m: Pr[G1.main() @ &m: res] = Pr[G1'.main() @ &m: res].
  proof.
    equiv_deno (_: ={glob A} ==> ={res})=> //.
    fun.
    call (_: ={glob A, glob ROM.RO, glob ARO}).
      call (_: ={glob ROM.RO, glob ARO})=> //; first by fun*; call ARO_equiv.
    wp; rnd (lambda h, h ^^ if b then m1 else m0){1}; rnd.
    call (_: ={glob A, glob ROM.RO, glob ARO}).
      call (_: ={glob ROM.RO, glob ARO})=> //; first by fun*; call ARO_equiv.
    by inline H.init ROM.RO.init; wp; rnd; rnd; wp; skip; progress; smt.
  qed.

  local lemma Pr_G1' &m: Pr[G1'.main() @ &m: res] = 1%r/2%r.
  proof.
    bdhoare_deno (_: true ==> res)=> //.
    fun.
    swap 7 3.
    rnd ((=) b').
    call (_: true).
      call (_: true)=> //;
        first by progress; apply (guessL O).
        by fun; sp; if=> //; wp; call (ROM.lossless_o _); first smt.
    wp; rnd.
    call (_: true).
      call (_: true)=> //;
        first by progress; apply (chooseL O).
        by fun; sp; if=> //; wp; call (ROM.lossless_o _); first smt.
    by inline H.init ROM.RO.init; wp; rnd; rnd; wp; skip; progress; expect 4 smt.
  qed.

  local module G2' = {
    var gxy : group
   
    fun main() : bool = {
      var m0, m1:plaintext;
      var c:ciphertext;
      var b, b':bool;
      var x, y:int;
      var h:bits;
      var gx:group;

      H.init();
      x        = $[0..q-1];
      y        = $[0..q-1];
      gx       = g ^ x; 
      gxy      = gx ^ y;
      (m0,m1)  = BA.choose(gx);
      b        = ${0,1};
      h        = $uniform;
      c        = (g ^ y, h);
      b'       = BA.guess(c);
      return mem gxy ARO.qs;
    }
  }.

  local lemma G2_G2' &m: Pr[G2.main() @ &m: res] = Pr[G2'.main() @ &m: res].
  proof.
    equiv_deno (_: ={glob A} ==> ={res})=> //.
    fun.
    call (_: ={glob A, glob ROM.RO, glob ARO}).
      call (_: ={glob ROM.RO, glob ARO})=> //; first by fun*; call ARO_equiv.
    wp; rnd (lambda h, h ^^ if b then m1 else m0){1}; rnd.
    call (_: ={glob A, glob ROM.RO, glob ARO}).
      call (_: ={glob ROM.RO, glob ARO})=> //; first by fun*; call ARO_equiv.
    by inline H.init ROM.RO.init; wp; rnd; rnd; wp; skip; progress; smt.
  qed.

  local equiv G2'_SCDH: G2'.main ~ SCDH.SCDH(SCDH_from_CPA(A,ROM.RO)).main:
    ={glob A} ==> res{1} = res{2} /\ card ARO.qs{1} <= qH.
  proof.
    fun.
    inline SCDH_from_CPA(A,ROM.RO).solve.
    swap{2} 5 -4; swap{1} 7 3.
    rnd{1}; wp.
    seq  8  7: (={glob BA} /\
                c{1} = (gy, h){2} /\
                G2'.gxy{1} = g ^ (x * y){2} /\
                card ARO.qs{1} <= qH).
      wp; rnd; call (_: ={glob A, glob H} /\ card ARO.qs{1} <= qH).
        call (_: ={glob H} /\ card ARO.qs{1} <= qH)=> //.
        by fun; sp; if=> //; wp; call RO_equiv; skip; smt.
      by inline H.init ROM.RO.init; wp; rnd; rnd; wp; skip; progress; smt.
    call (_: ={glob A, glob H} /\ card ARO.qs{1} <= qH).
      call (_: ={glob H} /\ card ARO.qs{1} <= qH)=> //.
      by fun; sp; if=> //; wp; call RO_equiv; skip; smt.
    by skip; smt.
  qed.
      
  local lemma Pr_G2'_SCDH &m : 
    Pr[G2'.main() @ &m: res]
    = Pr[SCDH.SCDH(SCDH_from_CPA(A,ROM.RO)).main() @ &m : res]
  by equiv_deno G2'_SCDH.
   
  local lemma Reduction &m :
    Pr[CPA(S,BA).main() @ &m : res] <=
    1%r / 2%r + Pr[SCDH.SCDH(SCDH_from_CPA(A,ROM.RO)).main() @ &m : res].
  proof. 
    rewrite (Pr_CPA_G0 &m).
    rewrite -(Pr_G1' &m) -(G1_G1' &m).
    rewrite -(Pr_G2'_SCDH &m) -(G2_G2' &m).
    by apply (G0_G1_G2 &m).
  qed.

  lemma mult_inv_le_r (x y z:real) : 
    0%r < x => (1%r / x) * y <= z => y <= x * z
  by [].

(*
  (* This is not working in master because the SDCH -> CDH reduction is expressed with an existential (boooh!) *)
  (** Composing reduction from CPA to SCDH with reduction from SCDH to CDH *)
  lemma Security &m :
      Pr[CPA(S,Bounder'(A,ROM.RO)).main() @ &m: res] - 1%r / 2%r <= 
      qH%r * Pr[CDH.CDH(SCDH.CDH_from_SCDH(SCDH_from_CPA(A,ROM.RO))).main() @ &m: res].
  proof.
    apply (Trans _ (Pr[SCDH.SCDH(SCDH_from_CPA(A,ROM.RO)).main() @ &m: res]));
      first smt.
    apply mult_inv_le_r; first smt.
    by apply (SCDH.Reduction (SCDH_from_CPA(A,ROM.RO)) &m); smt.
  qed.
*)
end section.

(*print axiom Security. *)

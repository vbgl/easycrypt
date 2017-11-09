(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore List.

(* -------------------------------------------------------------------- *)
pred enumerate ['a] (C : int -> 'a option) (E : 'a -> bool) =
     (forall i j x, C i = Some x => C j = Some x => i = j)
  /\ (forall x, E x => exists i, 0 <= i /\ C i = Some x).

(* -------------------------------------------------------------------- *)
lemma eq_enumerate ['a] E1 E2 (C : int -> 'a option) :
  (forall x, E1 x = E2 x) => enumerate C E1 => enumerate C E2.
proof. by move/fun_ext=> ->. qed.

(* -------------------------------------------------------------------- *)
pred countable ['a] (E : 'a -> bool) =
  exists (C : int -> 'a option),
    forall x, E x => exists i, C i = Some x.

(* -------------------------------------------------------------------- *)
lemma countableP ['a] (E : 'a -> bool):
  countable E <=> exists (C : int -> 'a option), enumerate C E.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
op cunion (C1 C2 : int -> 'a option) : (int -> 'a option).

(* -------------------------------------------------------------------- *)
axiom cunion_enum (C1 C2 : int -> 'a option) E1 E2 :
  enumerate C1 E1 => enumerate C2 E2 =>
    enumerate (cunion C1 C2) (predU E1 E2).

(* -------------------------------------------------------------------- *)
op cunions (Cs : (int -> 'a option) list) =
  foldr cunion (fun x => None) Cs.

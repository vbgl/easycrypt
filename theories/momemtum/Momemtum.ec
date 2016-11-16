(* -------------------------------------------------------------------- *)
require import Int IntExtra Real RealExtra List.

op path ['a] (e : 'a -> 'a -> bool) x p =
  with p = [] => true
  with p = y :: p' => e x y /\ path e y p'.

op pathn ['a] (e : 'a -> 'a -> bool) n x y =
  exists s, size s = n /\ path e x s /\ last x s = y.

op dclosure ['a] (e : 'a -> 'a -> bool) x y =
  exists n, pathn e n x y.

op dpath ['a] (e : 'a -> 'a -> bool) x y =
  choiceb (fun n =>
    pathn e n x y /\ forall k, k < n => !pathn e n x y)
    (-1).



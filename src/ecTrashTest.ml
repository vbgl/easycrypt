open EcCoreFol
open EcMatching

let test (_tc1 : EcCoreGoal.tcenv1) : EcCoreGoal.tcenv =
  let (name1 : EcSymbols.symbol) = "name1" in
  let name2 = "name2" in
  let name3 = "name3" in
  let name4 = "name4" in
  let add_name n p = Named (p, n) in

  let rec tuple_r f acc (i : int) =
    if i <= 0 then acc
    else tuple_r f (f :: acc) (i-1) in
  let tuple f n = f_tuple (tuple_r f [] n) in

  let size_tuple = 5 in

  let (f : form) = EcCoreFol.f_int EcBigInt.one in
  let _p = Base (BaseFPattern.Pint EcBigInt.one) in
  let p = Anything in

  let f = tuple f size_tuple in
  let f = tuple f size_tuple in

  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in

  let f = tuple f size_tuple in
  let f = tuple f size_tuple in

  let p2 = add_name name2 p in
  let p = Base (BaseFPattern.Ptuple [p;p2;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = add_name name3 p in

  let f = tuple f size_tuple in
  let f = tuple f size_tuple in

  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = add_name name4 p in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in

  let f = tuple f size_tuple in
  let f = tuple f size_tuple in

  let p = add_name name1 p in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in

  let f = tuple f size_tuple in
  let f = tuple f size_tuple in

  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in

  let f = tuple f size_tuple in
  let f = tuple f size_tuple in


  let f = tuple f size_tuple in
  let f = tuple f size_tuple in


  match FormPattern.search p f with
  | None -> raise NoMatches
  | Some map ->
     let err = [
         "there are ";
         string_of_int (EcMaps.Mstr.cardinal map);
         " names : ";
         String.concat " and " (List.map fst (EcMaps.Mstr.bindings map))
       ] in
     raise (Invalid_argument (String.concat "" err))

  (* EcCoreGoal.FApi.tcenv_of_tcenv1 tc1 *)

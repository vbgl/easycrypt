open EcCoreFol
open EcMatching

let test (_tc1 : EcCoreGoal.tcenv1) : EcCoreGoal.tcenv =
  let (name1 : EcSymbols.symbol) = "name1" in
  let name2 = "name2" in
  let name3 = "name3" in
  let add_name n p = Named (p, n) in
  let (f : form) = EcCoreFol.f_int EcBigInt.one in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in

  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in
  let f = f_tuple [f;f;f] in

  let p = Base (BaseFPattern.Pint EcBigInt.one) in
  let p2 = add_name name2 p in
  let p = add_name name1 p in
  let p = Base (BaseFPattern.Ptuple [p;p2;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = add_name name3 p in

  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in
  let p = Base (BaseFPattern.Ptuple [p;p;p]) in

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

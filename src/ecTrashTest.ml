open EcCoreFol
open EcMatching
open FPattern

let test (_tc1 : EcCoreGoal.tcenv1) : EcCoreGoal.tcenv =
  let add_name n p = Named (p, n) in
  let rec tuple_r f acc (i : int) =
    if i <= 0 then acc
    else tuple_r f (f :: acc) (i-1) in
  let tuple f n = f_tuple (tuple_r f [] n) in
  let ptuple p n = Ptuple (tuple_r p [] n) in

  let nb_tests = 4 in

  let get_test i f p =
    let err = match search f p with
      | None ->
         ["Test ";
          string_of_int i;
          " : failed. "]
      | Some map ->
         ["Test ";
          string_of_int i;
          " : there are ";
          string_of_int (M.cardinal map);
          " names : ";
          String.concat " and " (List.map fst (M.bindings map))
         ] in
    String.concat "" err in

  let size_tuple = 5 in
  let testall (i : int) =
      match i with
      | i when i < 0 -> ""
      | 0 ->
         let (f : form) = EcCoreFol.f_int EcBigInt.one in
         let p = Pint EcBigInt.one in
         get_test i f p

      | 1 ->
         let (name1 : EcSymbols.symbol) = "tuple1" in
         let name2 = "tuple2" in
         let name3 = "tuple3" in
         let name4 = "tuple4" in

         let (f : form) = EcCoreFol.f_int EcBigInt.one in
         let p = Pint EcBigInt.one in
         let p = add_name name1 p in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in
         let p = add_name name2 p in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in
         let p = add_name name3 p in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = add_name name4 p in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         let f = tuple f size_tuple in
         let p = ptuple p size_tuple in

         get_test i f p

      | 2 ->
         let cacahuete = EcIdent.create "cacahuete" in
         let pcond = Anything in
         let pthen = Plocal cacahuete in
         let pelse = Pproj (Anything,2) in
         let p = Pif (pcond,pthen,pelse) in

         let fcond = f_false in
         let fthen = f_local cacahuete EcTypes.tint in
         let felse = f_proj (tuple fthen 3) 2 EcTypes.tint in
         let f = f_if fcond fthen felse in
         get_test i f p

      | 3 ->
         let cacahuete = EcIdent.create "cacahuete" in
         let pcond = Anything in
         let pthen = Plocal cacahuete in
         let pelse = Sub (Pproj (Anything,2)) in
         let p = Pif (pcond,pthen,pelse) in

         let fcond = f_false in
         let fthen = f_local cacahuete EcTypes.tint in
         let felse = f_proj (tuple fthen 3) 2 EcTypes.tint in
         let felse = tuple felse size_tuple in
         let felse = tuple felse size_tuple in
         let felse = tuple felse size_tuple in
         let felse = tuple felse size_tuple in
         let felse = tuple felse size_tuple in
         let f = f_if fcond fthen felse in
         get_test i f p

      | _ -> ""
  in
  let x =
    let rec aux acc i =
      if i <= 0 then acc
      else let i = i - 1 in let acc = i::acc in
           aux acc i
    in
    String.concat "  --------------------------------------------------------  "
                  (List.map testall (aux [] nb_tests))
  in

  raise (Invalid_argument x)

  (* EcCoreGoal.FApi.tcenv_of_tcenv1 tc1 *)

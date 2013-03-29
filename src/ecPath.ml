(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols

(* -------------------------------------------------------------------- *)
type path = {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pident  of EcIdent.t
| Pqname  of path * symbol

type path_kind =
| PKmodule
| PKother

type mpath = {
  m_path : path;
  m_kind : path_kind list; 
  m_args : mpath list list;
  m_tag  : int;
}

type proot = [ `Symbol of symbol | `Ident of EcIdent.t ]

let name_path path = match path.p_node with 
  | Psymbol s -> s
  | Pident id -> EcIdent.name id
  | Pqname (_,s) -> s

let name_mpath mpath = name_path mpath.m_path

(* -------------------------------------------------------------------- *)
let p_equal   = ((==) : path -> path -> bool)
let p_hash    = fun p -> p.p_tag
let p_compare = fun p1 p2 -> p_hash p1 - p_hash p2

module Hspath = Why3.Hashcons.Make (struct 
  type t = path

  let equal_node p1 p2 = 
    match p1, p2 with
    | Psymbol id1, Psymbol id2 -> EcSymbols.equal id1 id2
    | Pident  id1, Pident  id2 -> EcIdent.id_equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) -> 
        EcSymbols.equal id1 id2 && p_equal p1 p2
    | _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p = 
    match p.p_node with
    | Psymbol id    -> Hashtbl.hash id
    | Pident  id    -> EcIdent.tag id
    | Pqname (p,id) -> Why3.Hashcons.combine p.p_tag (Hashtbl.hash id)
          
  let tag n p = { p with p_tag = n }
end)

module Path = MakeMSH (struct
  type t  = path
  let tag = p_hash
end)

module Sp = Path.S
module Mp = Path.M
module Hp = Path.H

(* -------------------------------------------------------------------- *)
let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let psymbol id   = mk_path (Psymbol id)
let pident  id   = mk_path (Pident id)
let pqname  p id = mk_path (Pqname(p,id))

(* -------------------------------------------------------------------- *)
let rec tostring p =
  match p.p_node with
  | Psymbol x    -> x
  | Pident x     -> EcIdent.name x
  | Pqname (p,x) -> Printf.sprintf "%s.%s" (tostring p) x

let tolist =
  let rec aux l p = 
    match p.p_node with 
    | Psymbol x     -> x :: l
    | Pident x      -> EcIdent.name x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

let toqsymbol (p : path) =
  match p.p_node with
  | Psymbol x     -> ([], x)
  | Pident x      -> ([], EcIdent.name x)
  | Pqname (p, x) -> (tolist p, x)

let basename p = 
  match p.p_node with 
  | Psymbol x     -> x
  | Pident  x     -> EcIdent.name x
  | Pqname (_, x) -> x

let prefix p = 
  match p.p_node with 
  | Psymbol _ | Pident _ -> None
  | Pqname (p, _) -> Some p

let rec rootname p = 
  match p.p_node with 
  | Psymbol x     -> x
  | Pident x      -> EcIdent.name x
  | Pqname (p, _) -> rootname p

let extend (p : path option) (x : symbol) =
  match p with
  | None   -> psymbol x
  | Some p -> pqname p x

let rec p_size p =
  match p.p_node with
  | Psymbol _     -> 1
  | Pident  _     -> 1
  | Pqname (p, _) -> 1 + (p_size p)

let rec p_fv fv p = 
  match p.p_node with
  | Psymbol _ -> fv 
  | Pident id -> EcIdent.fv_add id fv
  | Pqname(p,_) -> p_fv fv p

(* -------------------------------------------------------------------- *)
let m_equal   = ((==) : mpath -> mpath -> bool)
let m_hash    = fun p -> p.m_tag
let m_compare = fun p1 p2 -> m_hash p1 - m_hash p2

module Hsmpath = Why3.Hashcons.Make (struct 
  type t = mpath

  let equal m1 m2 = 
    p_equal m1.m_path m2.m_path &&
    m1.m_kind = m2.m_kind &&
    List.all2 (List.all2 m_equal) m1.m_args m2.m_args


  let hash m = 
    let p = m.m_path and args = m.m_args in 
      Why3.Hashcons.combine_list 
        (Why3.Hashcons.combine_list m_hash 0)
        p.p_tag args
          
  let tag n p = { p with m_tag = n }
end)

module MPath = MakeMSH (struct
  type t  = mpath
  let tag = m_hash
end)

module Sm = MPath.S
module Mm = MPath.M
module Hm = MPath.H

let rec m_fv fv mp = 
  List.fold_left (List.fold_left m_fv) (p_fv fv (mp.m_path)) mp.m_args 

(* -------------------------------------------------------------------- *)
let mk_mpath p k args =
  Hsmpath.hashcons { m_path = p; m_kind = k; m_args = args; m_tag = -1; }

let mpath = mk_mpath

let mident  id = mk_mpath (pident  id) [PKmodule] [[]]
let msymbol id = mk_mpath (psymbol id) [PKother]  [[]]

let mqname m k id a = 
  mk_mpath (pqname m.m_path id) (k::m.m_kind) (a::m.m_args)

let m_split m =
  match m.m_path.p_node, m.m_kind, m.m_args with
  | Pqname (prefix, x), k :: ks, a :: pfargs ->
      Some (mpath prefix ks pfargs, k, x, a)

  | _, _, _ -> None

let m_apply m newargs =
  match m.m_args with
  | [] -> assert false
  | a :: args -> mpath m.m_path m.m_kind ((a @ newargs) :: args)

let path_of_mpath  m = m.m_path 
let args_of_mpath  m = m.m_args
let kinds_of_mpath m = m.m_kind

let mpath_of_path p = 
  let rec args p = 
    match p.p_node with
    | Pident _      -> assert false 
    | Psymbol _     -> [PKother], [[]]
    | Pqname (p, _) -> 
        let k, args = args p in
        PKother::k,[]::args in
  let k, args = args p in
  mk_mpath p k args

(* -------------------------------------------------------------------- *)
let rec m_tostring(m : mpath) = 
  let p = m.m_path and args = m.m_args in

  let app_tostring id a =
    if   a = []
    then id 
    else
      let args = List.map m_tostring a in
        Printf.sprintf "%s(%s)" id (String.concat ", " args)
  in
  let rec aux p ks args = 
    match p.p_node, ks, args with
    | Psymbol id , [_], [a] -> app_tostring id a 
    | Pident   id, [_], [a] -> app_tostring (EcIdent.name id) a

    | Pqname(p, id), k::ks, a::args ->
        let s1 = aux p ks args in
        let s2 = app_tostring id a in
        let s =  if k = PKmodule then "@" else "." in
          Format.sprintf "%s%s%s" s1 s s2 

    | _, _, _ -> assert false
  in
    aux p m.m_kind args

(* -------------------------------------------------------------------- *)
type xpath = {
  xp_node : mpath * symbol;
  xp_tag  : int;
}

(* -------------------------------------------------------------------- *)
let x_equal   = ((==) : xpath -> xpath -> bool)
let x_hash    = fun p -> p.xp_tag
let x_compare = fun p1 p2 -> x_hash p1 - x_hash p2

module Hsxpath = Why3.Hashcons.Make (struct 
  type t = xpath

  let equal_node p1 p2 = 
    let (m1, id1) = p1 in
    let (m2, id2) = p2 in
      (id1 = id2) && (m_equal m1 m2)

  let equal p1 p2 = equal_node p1.xp_node p2.xp_node

  let hash p = 
    let (m, id) = p.xp_node in 
      Why3.Hashcons.combine (m_hash m) (Hashtbl.hash id)
          
  let tag n p = { p with xp_tag = n }
end)

module XPath = MakeMSH (struct
  type t  = xpath
  let tag = x_hash
end)

module Sx = XPath.S
module Mx = XPath.M
module Hx = XPath.H

(* -------------------------------------------------------------------- *)
let mk_xpath node =
  Hsxpath.hashcons { xp_node = node; xp_tag = -1; }

let xpath (m : mpath) (id : symbol) =
  mk_xpath (m, id)

let x_scope { xp_node = (m, _) } = m
let x_name  { xp_node = (_, x) } = x

let x_tostring { xp_node = (m, x) } =
  Printf.sprintf "%s.%s" (m_tostring m) x

(* -------------------------------------------------------------------- *)
module Msubp = struct
  type 'a t = ('a submaps) Msym.t

  and 'a submaps = {
    mp_value   : 'a option;
    mp_submaps : 'a t;
  }

  let empty : 'a t = Msym.empty

  let empty_sm : 'a submaps = {
    mp_value   = None;
    mp_submaps = empty;
  }

  let rec update up (path : path) (m : 'a t) =
    match path.p_node with
    | Pident  _ -> invalid_arg "path-with-ident"
    | Psymbol x -> up x m
    | Pqname (path, x) ->
        let up supx supm =
          let doupdate subxsm =
            let supxsm = odfl empty_sm subxsm in
              Some { supxsm with mp_submaps = up x supxsm.mp_submaps }
          in
            Msym.change doupdate supx supm
        in
          update up path m

  let add (path : path) (v : 'a) (m : 'a t) =
    let add1 (x : symbol) (v : 'a) (m : 'a t) =
      let doupdate sm =
        let sm = odfl empty_sm sm in
          Some { sm with mp_value = Some v }
      in
        Msym.change doupdate x m
    in
      update (add1^~ v) path m

  let find =
    let find1 (x : symbol) (sm : 'a submaps) =
      match Msym.find_opt x sm.mp_submaps with
      | None -> { mp_value   = sm.mp_value;
                  mp_submaps = empty; }

      | Some subsm -> begin
          match subsm.mp_value with
          | None   -> { subsm with mp_value = sm.mp_value }
          | Some _ -> subsm
        end
    in

    let rec find (path : path) (sm : 'a submaps) =
      match path.p_node with
      | Pident  _      -> invalid_arg "path-with-ident"
      | Psymbol x      -> find1 x sm
      | Pqname  (p, x) -> find1 x (find p sm)
    in

      fun (path : path) (m : 'a t) ->
        (find path { mp_value = None; mp_submaps = m }).mp_value
end

(* -------------------------------------------------------------------- *)

let p_subst (s : path Mp.t) =
  if Mp.is_empty s then identity
  else
    let p_subst aux p =
      try  Mp.find p s
      with Not_found ->
        match p.p_node with
        | Psymbol _
        | Pident  _ -> p
        | Pqname(p1, id) -> 
          let p1' = aux p1 in
          if p1 == p1' then p else pqname p1' id in
    Hp.memo_rec 107 p_subst

(* -------------------------------------------------------------------- *)

let rec m_subst (sp : path -> path) (sm : mpath EcIdent.Mid.t) m =
  let p    = m.m_path
  and ks   = m.m_kind 
  and args = m.m_args in
  let args = List.map (List.map (m_subst sp sm)) args in

  let rec aux p ks args =
    match p.p_node, ks, args with
    | Psymbol _, _, _ -> raise Not_found

    | Pident id, [_], [a] ->
        let mp = EcIdent.Mid.find id sm in
          m_apply mp a

    | Pqname(p,id), k::ks, a::args ->
        mqname (aux p ks args) k id a 

    | _, _, _ -> assert false
  in

  try  aux p ks args
  with Not_found -> mpath (sp p) ks args

let m_subst (sp : path -> path) (sm : mpath EcIdent.Mid.t) =
  if sp == identity && EcIdent.Mid.is_empty sm then identity
  else m_subst sp sm


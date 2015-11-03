(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)

let mt_fv = EcTypes.mt_fv

let lmt_equal = EcTypes.lmt_equal

let lmt_xpath mt = mt.mt_path
let lmt_bindings mt = mt.mt_vars

let mt_equal = EcTypes.mt_equal 

let mt_xpath = function
  | None -> assert false
  | Some mt -> lmt_xpath mt
 
let mt_bindings = function
  | None -> assert false
  | Some mt -> lmt_bindings mt

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype 

let me_equal (m1,mt1) (m2,mt2) = 
  mem_equal m1 m2 && mt_equal mt1 mt2 

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt
let xpath    (_,mt) = mt_xpath mt
let bindings (_,mt) = mt_bindings mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local (me : memory) mp =
  (me, Some {mt_path   = mp; mt_vars   = Msym.empty; } )

let abstract (me:memory) = (me,None)

(* -------------------------------------------------------------------- *)
let bindp (x : symbol) pr (ty : EcTypes.ty) ((m,mt) : memenv) =
  let mt = match mt with
    | None -> assert false
    | Some mt -> mt in
  let merger = function
    | Some _ -> raise (DuplicatedMemoryBinding x)
    | None   -> Some (pr,ty)
  in
    (m, Some { mt with mt_vars = Msym.change merger x mt.mt_vars })

let bind_proj i n x ty me = bindp x (Some (i,n)) ty me
let bind x ty me = bindp x None ty me

(* -------------------------------------------------------------------- *)
let lookup (x : symbol) ((_,mt) : memenv) =
  match mt with 
  | None -> None
  | Some mt ->  Msym.find_opt x (lmt_bindings mt)

let is_bound x me = lookup x me <> None
  
let is_bound_pv pv me = 
  is_loc pv && is_bound (EcPath.xbasename pv.pv_name) me
(* -------------------------------------------------------------------- *)

let mt_subst = EcTypes.mt_subst 

let mt_substm sp smp st o =
  mt_subst (EcPath.x_substm sp smp) st o

let me_subst sx st (m,mt as me) =
  let mt' = mt_subst sx st mt in
  if mt' == mt then me else 
    (m, mt')

let me_substm sp smp st me =
  me_subst (EcPath.x_substm sp smp) st me




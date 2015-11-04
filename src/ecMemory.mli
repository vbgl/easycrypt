(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcSymbols
open EcTypes
(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

val mem_equal : memory -> memory -> bool

(* -------------------------------------------------------------------- *)

val lmt_equal    : local_memtype -> local_memtype -> bool
val lmt_xpath    : local_memtype -> EcPath.xpath
val lmt_bindings : local_memtype -> ((int*int) option * ty) Msym.t
(* the "int option" indicate if the variable is defined as the projection of
   "arg" or as a variable *)                         

val mt_equal    : memtype -> memtype -> bool
val mt_xpath    : memtype -> EcPath.xpath
val mt_bindings : memtype -> ((int*int) option * ty) Msym.t
val mt_fv       : memtype -> int EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

val me_equal : memenv -> memenv -> bool

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

val memory   : memenv -> memory
val memtype  : memenv -> memtype 
val xpath    : memenv -> EcPath.xpath
val bindings : memenv -> ((int*int) option * ty) Msym.t

(* -------------------------------------------------------------------- *)
val empty_local : memory -> EcPath.xpath -> memenv
val abstract    : memory -> memenv

val bindp    : symbol -> (int*int) option -> ty -> memenv -> memenv
val bind     : symbol -> ty -> memenv -> memenv
val bind_proj: int -> int -> symbol -> ty -> memenv -> memenv
val lookup   : symbol -> memenv -> ((int*int) option * ty) option
val is_bound : symbol -> memenv -> bool
val is_bound_pv : prog_var -> memenv -> bool

(* -------------------------------------------------------------------- *)
val mt_subst :
     (EcPath.xpath -> EcPath.xpath)
  -> (ty -> ty)
  -> memtype -> memtype

val mt_substm :
     (EcPath.path -> EcPath.path)
  -> EcPath.mpath EcIdent.Mid.t
  -> (ty -> ty)
  -> memtype -> memtype

val me_subst :
     (EcPath.xpath -> EcPath.xpath)
  -> (ty -> ty)
  -> memenv -> memenv

val me_substm :
     (EcPath.path -> EcPath.path)
  -> EcPath.mpath EcIdent.Mid.t
  -> (ty -> ty)
  -> memenv -> memenv

(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcTypes
open EcEnv
open EcFol
open EcModules

(* -------------------------------------------------------------------- *)
val p_not        : env -> form -> form
val p_imp        : env -> form -> form -> form
val p_and        : env -> form -> form -> form
val p_forall_imp : env -> form -> form -> form


(* -------------------------------------------------------------------- *)
val oplus : ty -> ident -> ident -> ident -> form -> form
val curly : env -> expr -> form -> form -> form
val mu_restr : env -> bool -> expr -> form -> form
(* -------------------------------------------------------------------- *)
exception NoWpMuhoare

(* -------------------------------------------------------------------- *)
val wp_muhoare : env -> stmt -> form -> form

val wp_pre : env -> memtype -> xpath -> funsig -> form -> form
val wp_ret : env -> memtype -> prog_var -> expr -> form -> form

val max_wp : stmt -> int

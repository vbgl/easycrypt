(* -------------------------------------------------------------------- *)
open EcIdent
open EcPath
open EcTypes
open EcEnv
open EcFol
open EcModules
open EcMemory

(* -------------------------------------------------------------------- *)
val ldm_app : (EcIdent.t * memtype) -> lmd_form -> lmd_form
val ldm_forall_imp : lmd_form -> lmd_form -> form

(* -------------------------------------------------------------------- *)
val oplus : ident -> ident -> ident -> form -> form
val curly : expr -> lmd_form -> lmd_form -> lmd_form

(* -------------------------------------------------------------------- *)
exception NoWpMuhoare

(* -------------------------------------------------------------------- *)
val wp_muhoare : env -> stmt -> lmd_form -> lmd_form

val wp_pre : env -> memtype -> xpath -> funsig -> lmd_form -> lmd_form
val wp_ret : env -> memtype -> prog_var -> expr -> lmd_form -> lmd_form

val max_wp : stmt -> int

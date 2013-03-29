(* -------------------------------------------------------------------- *)
open EcDebug
open EcMaps
open EcIdent
open EcTypes
open EcModules
open EcMemory

(* -------------------------------------------------------------------- *)
val mhr    : memory
val mleft  : memory
val mright : memory

type gty =
  | GTty    of EcTypes.ty
  | GTmodty of module_type
  | GTmem

type quantif = 
  | Lforall
  | Lexists
  | Llambda

type binding =  (EcIdent.t * gty) list

type form = private { 
  f_node : f_node;
  f_ty   : ty; 
  f_fv   : int Mid.t;
  f_tag  : int;
}

and f_node = 
  | Fquant  of quantif * binding * form
  | Fif     of form * form * form
  | Flet    of lpattern * form * form
  | Fint    of int
  | Flocal  of EcIdent.t
  | Fpvar   of EcTypes.prog_var * memory
  | Fop     of EcPath.path * ty list
  | Fapp    of form * form list
  | Ftuple  of form list

  | FeqGlob of memory * memory * EcPath.mpath    (* FeqGlob(m1,m2,A) means 
                                                    equality of global variable of A *)
  | FhoareF of hoareF (* $hr / $hr *)
  | FhoareS of hoareS (* $hr  / $hr   *)

  | FequivF of equivF (* $left,$right / $left,$right *)
  | FequivS of equivS (* $left,$right / $left,$right *)

  | Fpr     of memory * EcPath.mpath * form list * form (* hr *)

and equivF = { 
  eqf_pre  : form;
  eqf_fl   : EcPath.mpath;
  eqf_fr   : EcPath.mpath;
  eqf_post : form;
}

and equivS = {
  eqs_mel  : EcMemory.memenv;
  eqs_mer  : EcMemory.memenv;
  eqs_pre  : form;
  eqs_sl   : stmt; (* In reverse order *)
  eqs_sr   : stmt; (* In reverse order *)
  eqs_post : form; }

and hoareF = { 
  hf_pre  : form;
  hf_f    : EcPath.mpath;
  hf_post : form;
}
and hoareS = {
  hs_me   : memenv;
  hs_pre  : form; 
  hs_s    : stmt; (* In reverse order *)
  hs_post : form; }

(* -------------------------------------------------------------------- *)
val f_equal   : form -> form -> bool
val f_compare : form -> form -> int
val f_hash    : form -> int 
val f_fv      : form -> int Mid.t 
val f_ty      : form -> EcTypes.ty

module Mf : Map.S with type key = form
module Sf : Mf.Set with type elt = form 
module Hf : EHashtbl.S with type key = form

(* -------------------------------------------------------------------- *)
val f_dump : form -> dnode

(* -------------------------------------------------------------------- *)
val mk_form : f_node -> EcTypes.ty -> form

val f_local : EcIdent.t -> EcTypes.ty -> form
val f_pvar : EcTypes.prog_var -> EcTypes.ty -> memory -> form

val f_true : form
val f_false : form
val f_bool : bool -> form

val f_int : int -> form

val f_op : EcPath.path -> EcTypes.ty list -> EcTypes.ty -> form
val f_app : form -> form list -> EcTypes.ty -> form

val f_tuple : form list -> form
val f_if : form -> form -> form -> form
val f_let : EcTypes.lpattern -> form -> form -> form
val f_quant : quantif -> binding -> form -> form
val f_exists : binding -> form -> form
val f_forall : binding -> form -> form
val f_lambda : binding -> form -> form

val f_hoareF  : form -> EcPath.mpath -> form -> form 
val f_hoareS  : memenv -> form -> EcModules.stmt -> form -> form 
val f_equivF  : form -> EcPath.mpath -> EcPath.mpath -> form -> form 
val f_equivS  : 
 memenv -> memenv -> form -> EcModules.stmt -> EcModules.stmt -> form -> form
val f_pr      : memory -> EcPath.mpath -> form list -> form -> form

val fop_not : form
val f_not : form -> form

val fop_and : form
val f_and : form -> form -> form

val fop_anda : form
val f_anda : form -> form -> form

val fop_or : form
val f_or : form -> form -> form

val fop_ora : form
val f_ora : form -> form -> form

val fop_imp : form
val f_imp : form -> form -> form

val fop_iff : form
val f_iff : form -> form -> form

val fop_eq : EcTypes.ty -> form
val f_eq : form -> form -> form

val f_int_le : form -> form -> form

val f_int_lt  : form -> form -> form

(* -------------------------------------------------------------------- *)
val f_if_simpl  : form -> form -> form -> form
val f_let_simpl : EcTypes.lpattern -> form -> form -> form
val f_lets_simpl : (EcTypes.lpattern * form) list -> form -> form

(*val f_quant_simpl : quantif -> binding -> form -> form
  val f_exists_simpl : binding -> form -> form *)
val f_forall_simpl  : binding -> form -> form

val f_not_simpl  : form -> form
val f_and_simpl  : form -> form -> form
val f_anda_simpl : form -> form -> form
val f_or_simpl   : form -> form -> form
val f_ora_simpl  : form -> form -> form
val f_imp_simpl  : form -> form -> form
val f_iff_simpl  : form -> form -> form

val f_eq_simpl     : form -> form -> form

(* -------------------------------------------------------------------- *)

exception DestrError of string

val destr_local   : form -> EcIdent.t 
val destr_and     : form -> form * form
val destr_or      : form -> form * form
val destr_imp     : form -> form * form
val destr_iff     : form -> form * form
val destr_eq      : form -> form * form
val destr_let1    : form -> EcIdent.t * ty * form * form
val destr_forall1 : form -> EcIdent.t * gty * form
val destr_exists1 : form -> EcIdent.t * gty * form
val destr_equivF  : form -> equivF
val destr_equivS  : form -> equivS
val destr_hoareF  : form -> hoareF
val destr_hoareS  : form -> hoareS


val is_and    : form -> bool
val is_or     : form -> bool
val is_imp    : form -> bool
val is_iff    : form -> bool
val is_forall : form -> bool
val is_exists : form -> bool
val is_let1   : form -> bool
val is_eq     : form -> bool
val is_local  : form -> bool 




val f_map : (EcTypes.ty -> EcTypes.ty) -> (form -> form) -> form -> form

(* -------------------------------------------------------------------- *)
type f_subst = { 
  fs_freshen : bool;
  fs_p       : EcPath.path -> EcPath.path;
  fs_ty      : ty -> ty;
  fs_mp      : EcPath.mpath Mid.t;
  fs_loc     : form Mid.t;
  fs_mem     : EcIdent.t Mid.t;
}

val f_subst_id : f_subst

val add_locals : f_subst -> (EcIdent.t * EcTypes.ty) list -> 
  f_subst * (EcIdent.t * EcTypes.ty) list

val bind_local : f_subst -> EcIdent.t -> form -> f_subst
val bind_mem   : f_subst -> EcIdent.t -> EcIdent.t -> f_subst
val bind_mod   : f_subst -> EcIdent.t -> EcPath.mpath -> f_subst
   
val f_subst : f_subst -> form -> form 

module Fsubst :
  sig
    val mapty : (EcTypes.ty -> EcTypes.ty) -> form -> form
    val uni : EcTypes.ty EcUidgen.Muid.t -> form -> form
    val init_subst_tvar : EcTypes.ty EcIdent.Mid.t -> f_subst
    val subst_tvar : EcTypes.ty EcIdent.Mid.t -> form -> form

(*    val subst_local : EcIdent.t -> form -> form -> form
    val subst_locals : form EcIdent.Mid.t -> form -> form *)

  end


val form_of_expr : EcMemory.memory -> EcTypes.expr -> form

type op_kind = 
  | OK_true
  | OK_false
  | OK_not
  | OK_and   of bool  (* true = asym *)
  | OK_or    of bool  (* true = asym *)
  | OK_imp
  | OK_iff
  | OK_eq
  | OK_other 

val op_kind       : EcPath.path -> op_kind
val is_logical_op : EcPath.path -> bool

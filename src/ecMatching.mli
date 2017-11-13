(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps
open EcUid
open EcParsetree
open EcIdent
open EcTypes
open EcModules
open EcFol
open EcUnify
open EcEnv
open EcGenRegexp
open EcPath

(* -------------------------------------------------------------------- *)
module Zipper : sig
  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath ;                    (* path (zipper) leading to me         *)
  }

  exception InvalidCPos

  (* [zipper] soft constructor *)
  val zipper : instr list -> instr list -> ipath -> zipper

  (* Return the zipper for the stmt [stmt] at code position [codepos].
   * Raise [InvalidCPos] if [codepos] is not valid for [stmt]. *)
  val zipper_of_cpos : codepos -> stmt -> zipper

  (* Zip the zipper, returning the corresponding statement *)
  val zip : zipper -> stmt

  (* [after ~strict zpr] returns all the statements that come after the
   * zipper cursor. They are returned as a list of statements, where the head
   * is the list of instructions coming directly after the cursor at the
   * same level, the next element is the ones coming after the cursor
   * parent block, and so forth. The cursor is included iff [strict] is [true].
   *)
  val after : strict:bool -> zipper -> instr list list

  type ('a, 'state) folder = 'a -> 'state -> instr -> 'state * instr list

  (* [fold cl cpos f state s] create the zipper for [s] at [cpos], and apply
   * [f] to it, along with [v] and the state [state]. [f] must return the
   * new [state] and a new [zipper]. These last are directly returned.
   *
   * Raise [InvalidCPos] if [cpos] is not valid for [s], or any exception
   * raised by [f].
   *)
  val fold : 'a -> codepos -> ('a, 'state) folder -> 'state -> stmt -> 'state * stmt
end

(* -------------------------------------------------------------------- *)
(* Formulas rigid unification                                           *)
(* -------------------------------------------------------------------- *)
type 'a evmap

module EV : sig
  val empty     : 'a evmap
  val of_idents : ident list -> 'a evmap

  val add    : ident -> 'a evmap -> 'a evmap
  val mem    : ident -> 'a evmap -> bool
  val isset  : ident -> 'a evmap -> bool
  val set    : ident -> 'a -> 'a evmap -> 'a evmap
  val get    : ident -> 'a evmap -> [`Unset | `Set of 'a] option
  val doget  : ident -> 'a evmap -> 'a
  val fold   : (ident -> 'a -> 'b -> 'b) -> 'a evmap -> 'b -> 'b
  val filled : 'a evmap -> bool
end

(* -------------------------------------------------------------------- *)
type mevmap = {
  evm_form : form            evmap;
  evm_mem  : EcMemory.memory evmap;
  evm_mod  : EcPath.mpath    evmap;
}

(* -------------------------------------------------------------------- *)
module MEV : sig
  type item = [
    | `Form of form
    | `Mem  of EcMemory.memory
    | `Mod  of EcPath.mpath
  ]

  type kind = [ `Form | `Mem | `Mod ]

  val empty     : mevmap
  val of_idents : ident list -> kind -> mevmap

  val add    : ident -> kind -> mevmap -> mevmap
  val mem    : ident -> kind -> mevmap -> bool
  val isset  : ident -> kind -> mevmap -> bool
  val set    : ident -> item -> mevmap -> mevmap
  val get    : ident -> kind -> mevmap -> [`Unset | `Set of item] option
  val filled : mevmap -> bool
  val fold   : (ident -> item -> 'a -> 'a) -> mevmap -> 'a -> 'a
  val assubst: EcUnify.unienv -> mevmap -> EcFol.f_subst
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta  : bool;
  fm_conv   : bool;
  fm_horder : bool;
}

val fmsearch   : fmoptions
val fmrigid    : fmoptions
val fmdelta    : fmoptions
val fmnotation : fmoptions

val f_match_core :
     fmoptions
  -> EcEnv.LDecl.hyps
  -> unienv * mevmap
  -> ptn:form
  -> form
  -> unienv * mevmap

val f_match :
     fmoptions
  -> EcEnv.LDecl.hyps
  -> unienv * mevmap
  -> ptn:form
  -> form
  -> unienv * (uid -> ty option) * mevmap

(* -------------------------------------------------------------------- *)
type ptnpos = private [`Select of int | `Sub of ptnpos] Mint.t
type occ    = [`Inclusive | `Exclusive] * Sint.t

exception InvalidPosition
exception InvalidOccurence

module FPosition : sig
  type select = [`Accept of int | `Continue]

  val empty : ptnpos

  val is_empty : ptnpos -> bool

  val tostring : ptnpos -> string

  val select : ?o:occ -> (Sid.t -> form -> select) -> form -> ptnpos

  val select_form : ?xconv:EcReduction.xconv ->
    LDecl.hyps -> occ option -> form -> form -> ptnpos

  val is_occurences_valid : Sint.t -> ptnpos -> bool

  val occurences : ptnpos -> int

  val filter : occ -> ptnpos -> ptnpos

  val map : ptnpos -> (form -> form) -> form -> form

  val topattern : ?x:EcIdent.t -> ptnpos -> form -> EcIdent.t * form
end

(* -------------------------------------------------------------------- *)
type cptenv = CPTEnv of f_subst

val can_concretize : mevmap -> EcUnify.unienv -> bool

(* -------------------------------------------------------------------------- *)
type regexp_instr = regexp1_instr gen_regexp

and regexp1_instr =
  | RAssign
  | RSample
  | RCall
  | RIf        of regexp_instr * regexp_instr
  | RWhile     of regexp_instr

module RegexpStmt : sig
  type regexp  = regexp_instr
  type subject = instr list
  type matches = subject Mstr.t

  val search : regexp -> subject -> matches option
end


(* ---------------------------------------------------------------------- *)

exception CannotUnify
exception NoNext
exception NoMatches


(* ---------------------------------------------------------------------- *)

module FPattern : sig

  type name = EcIdent.t

  type pattern =
    | Panything
    | Pnamed    of pattern * name
    | Psub      of pattern
    | Por       of pattern list

    | Pobject   of object_matches

    | Pif     of pattern * pattern * pattern
    | Papp    of pattern * pattern list
    | Ptuple  of pattern list
    | Pproj   of pattern * int
    | Pmatch  of pattern * pattern list
    | Pquant  of quantif * bindings * pattern
    (* | Plet    of lpattern * pattern * pattern *)
    | Ppvar   of pattern * pattern
    | Pglob   of pattern * pattern
    (* | FhoareF of hoareF (\* $hr / $hr *\) *)
    (* | FhoareS of hoareS *)
    (* | FbdHoareF of bdHoareF (\* $hr / $hr *\) *)
    (* | FbdHoareS of bdHoareS *)
    (* | FequivF of equivF (\* $left,$right / $left,$right *\) *)
    (* | FequivS of equivS *)
    (* | FeagerF of eagerF *)
    | Ppr             of pattern * pattern * pattern * pattern

    | Pprog_var       of prog_var

    | Pxpath          of xpath
    (* mpath patterns *)
    (*                   mpath_top, mpath  list *)
    | Pmpath          of pattern * pattern list


   and object_matches =
    | Oform      of form
    | Omem       of EcMemory.memory
    (* | Ompath     of mpath *)
    | Ompath_top of mpath_top

  type t_matches = object_matches * Sid.t

  type matches = t_matches Mid.t

  type to_match = t_matches * pattern

  type pat_continuation =
    | ZTop
    | Znamed     of t_matches * name * pat_continuation
    (* Zor (cont, e_list, ne) :
       - cont   : the continuation if the matching is correct
       - e_list : if not, the sorted list of next engines to try matching with
       - ne     : if no match at all, then take the nengine to go up
     *)
    | Zor        of pat_continuation * engine list * nengine
    (* Zand (before, after, cont) :
       - before : list of couples (form, pattern) that has already been checked
       - after  : list of couples (form, pattern) to check in the following
       - cont   : continuation if all the matches succeed
     *)
    | Zand       of to_match list * to_match list * pat_continuation

    | Zbinds     of pat_continuation * Sid.t

  and engine = {
      e_head         : t_matches;
      e_continuation : pat_continuation;
      e_pattern      : pattern;
      e_map          : matches;
    }

  and nengine = {
      ne_continuation : pat_continuation;
      ne_map          : matches;
      ne_binds        : Sid.t;
    }

  (* val get_matches   :  engine -> matches *)
  (* val get_n_matches : nengine -> matches *)
  val search          : form -> pattern -> matches option
  val pattern_of_form : bindings -> form -> pattern
end

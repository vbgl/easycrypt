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
type 'a gen_named =
  | Anything
  | Base     of 'a
  | Named    of 'a gen_named * EcSymbols.symbol
  (* | Subterm  of 'a gen_named *)

exception CannotUnify
exception NoNext
exception NoMatches

(* module type BaseNamed = sig *)

(*   type base *)
(*   type engine *)
(*   type named1 *)
(*   type pos *)

(*   type interval = *)
(*     | Son     of pos *)
(*     (\* | Between of pos * pos *\) *)

(*   type matches = base Mstr.t *)

(*   type named = named1 gen_named *)

(*   val mkengine    : base -> engine *)
(*   val eat_down    : engine -> engine *)
(*   val eat_next    : engine -> engine *)
(*   val eat_up      : engine -> engine *)
(*   val eat         : engine -> engine *)
(*   val eat_base    : engine -> named1 -> engine * (pos * named) list *)
(*   val position    : engine -> pos *)
(*   val goto        : engine -> pos -> engine *)
(*   (\* add_match can raise the exception : CannotUnify *\) *)
(*   val add_match   : engine -> interval -> EcSymbols.symbol -> matches -> engine *)
(*   val get_matches : engine -> matches *)
(* end *)


(* module Named(B : BaseNamed) : sig *)
(*   type named  = B.named *)
(*   type base = B.base *)
(*   type matches = base Mstr.t *)
(*   type interval = B.interval *)

(*   val search : named -> base -> matches option *)
(* end *)

module BaseFPattern : sig

  type pattern =
    | Anything
    | Named   of pattern * EcSymbols.symbol
    | Sub     of pattern
    | Pif     of pattern * pattern * pattern
    | Pint    of EcBigInt.zint
    | Plocal  of EcIdent.t
    | Pop     of EcPath.path * EcTypes.ty list
    | Papp    of pattern * pattern list
    | Ptuple  of pattern list
    | Pproj   of pattern * int
    | Pmatch  of pattern * pattern list
    (* | Pquant  of quantif * bindings * pattern *)
    (* | Plet    of lpattern * pattern * pattern *)
    (* | Ppvar   of EcTypes.prog_var * EcMemory.memory *)
    (* | Pglob   of EcPath.mpath * EcMemory.memory *)
    (* | FhoareF of hoareF (\* $hr / $hr *\) *)
    (* | FhoareS of hoareS *)
    (* | FbdHoareF of bdHoareF (\* $hr / $hr *\) *)
    (* | FbdHoareS of bdHoareS *)
    (* | FequivF of equivF (\* $left,$right / $left,$right *\) *)
    (* | FequivS of equivS *)
    (* | FeagerF of eagerF *)
    (* | Ppr of EcMemory.memory * EcPath.xpath * pattern * pattern *)

  type matches = form Mstr.t
  type pos = int list
  type to_match = form * pattern
  type pat_zipper =
    | ZTop
    | Znamed     of form * EcSymbols.symbol                  * pat_zipper
    | Zor        of pat_zipper * engine list                 * nengine
    | Zand       of to_match list * to_match list            * pat_zipper
    (* | Zproj      of                                            pat_zipper *)
    (* | PZquant    of form * quantif * bindings                * pat_zipper *)
    (* | PZmatch1   of form * form list * pattern list * ty       * pat_zipper *)
    (* | PZmatch2   of form * form * form list * form list * ty   * pat_zipper *)
    (* | PZlet1     of form * lpattern * form                   * pat_zipper *)
    (* | PZlet2     of form * lpattern * form                   * pat_zipper *)
    (* | PZprArgs   of form * EcMemory.memory * EcPath.xpath * form *)
    (*                                                   * pat_zipper *)
    (* | PZprEvent  of form * EcMemory.memory * EcPath.xpath * form *)
    (*                                                   * pat_zipper *)

  and engine = private {
      e_form     : form;
      e_zipper   : pat_zipper;
      e_pattern  : pattern;
      e_map      : matches;
    }

  and nengine = private {
      ne_zipper   : pat_zipper;
      ne_map      : matches;
    }
  (* ---------------------------------------------------------------------- *)

  val get_matches   :  engine -> matches
  val get_n_matches : nengine -> matches
  val search        : form -> pattern -> matches option
end

(* module FormPattern : sig *)
(*   type named = BaseFPattern.named *)
(*   type base = BaseFPattern.base *)
(*   type matches = base Mstr.t *)
(*   type interval = BaseFPattern.interval *)

(*   val search : named -> base -> matches option *)
(* end *)

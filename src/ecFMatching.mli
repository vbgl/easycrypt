open EcFol
open EcTypes
open EcIdent
open EcPath
open EcEnv

(* ---------------------------------------------------------------------- *)
exception NoMatches
exception CannotUnify
exception NoNext


(* -------------------------------------------------------------------------- *)

module FPattern : sig

  type name = ident

  (* invariant of pattern : if the form is not Pobject, then there is
     at least one of the first set of patterns *)
  type pattern =
    | Panything
    | Pnamed     of pattern * name
    | Psub       of pattern
    | Por        of pattern list

    | Ptype      of pattern * ty

    | Pobject    of tobject

    | Pif        of pattern * pattern * pattern
    | Papp       of pattern * pattern list
    | Ptuple     of pattern list
    | Pproj      of pattern * int
    | Pmatch     of pattern * pattern list
    | Pquant     of quantif * bindings * pattern
    (* | Plet    of lpattern * pattern * pattern *)
    | Ppvar      of pattern * pattern
    | Pglob      of pattern * pattern
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

   and tobject =
    | Oform      of form
    | Omem       of EcMemory.memory
    (* | Ompath     of mpath *)
    (* | Oxpath     of xpath *)
    | Ompath_top of mpath_top

  type tmatch = tobject * binding Mid.t

  type map = tmatch Mid.t

  type to_match = tmatch * pattern

  type pat_continuation =
    | ZTop
    | Znamed     of tmatch * name * pat_continuation
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

    | Zbinds     of pat_continuation * binding Mid.t

  and engine = {
      e_head         : tmatch;
      e_continuation : pat_continuation;
      e_pattern      : pattern;
      e_map          : map;
      e_hyps         : EcEnv.LDecl.hyps;
    }

  and nengine = {
      ne_continuation : pat_continuation;
      ne_map          : map;
      ne_binds        : binding Mid.t;
      ne_hyps         : EcEnv.LDecl.hyps;
    }

  val search          : form -> pattern -> LDecl.hyps -> map option

  val search_eng      : engine -> nengine option

  val mkengine        : form -> pattern -> LDecl.hyps -> engine

  val pattern_of_form : bindings -> form -> pattern

  val rewrite_term : map -> EcFol.form -> EcFol.form
end

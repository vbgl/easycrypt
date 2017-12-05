open EcIdent
open EcParsetree
open EcCoreGoal
(* open EcHiGoal *)
open EcEnv
open FApi
open EcLocation
open EcDecl
open EcFMatching
open EcCoreFol
open FPattern


let default_name = "object matched to rewrite"
let rewrite_name = "rewrited object"
let default_name = EcIdent.create default_name
let rewrite_name = EcIdent.create rewrite_name

let process_match (x : pqsymbol) (tc : tcenv1)  =
  let (env,hyps,_f) = tc1_eflat tc in
  let axiom = Ax.lookup (unloc x) env in

  let fmt    = Format.std_formatter in
  let ppe    = EcPrinting.PPEnv.ofenv env in

  (* let _ = Format.fprintf fmt "%a\n" (EcPrinting.pp_axiom ~long:true ppe) axiom in *)

  let f = (snd axiom).ax_spec in
  let binds,f' = match f.f_node with
    | Fquant (Lforall, binds, f1) -> binds, f1
    | _ -> [],f in

  let f1,f2 = match f'.f_node with
    | Fapp (op, [f1 ; f2]) when EcPath.p_equal EcCoreLib.CI_Bool.p_eq (fst (destr_op op)) -> f1,f2
    | _ -> f',f' in

  let p = pattern_of_form binds f1 in
  let p = Pnamed (p, default_name) in
  let p = Psub p in

  let f = tc1_goal tc in

  let print = function
    | (Omem m,_) ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_local ppe) m
    | Oform f,_ ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_form ppe) f
    | _,_ -> ()
  in

  let print_names n o =
       let _ = Format.fprintf fmt "with name \"%a\" :\n" (EcPrinting.pp_local ppe) n in
       print o
  in

  let _ = match FPattern.search f p hyps with
    | None ->
       Format.fprintf
         fmt "%a\n" (EcPrinting.pp_form ppe)
         (EcFol.f_local (EcIdent.create "there_is_no_map") EcTypes.tint)
    | Some map ->
       let map = Mid.add rewrite_name (Oform (rewrite_term map f2), Mid.empty) map in
       Mid.iter print_names map
  in

  tcenv_of_tcenv1 tc

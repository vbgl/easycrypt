open EcIdent
open EcParsetree
open EcCoreGoal
(* open EcHiGoal *)
open EcEnv
open FApi
open EcLocation
open EcDecl
open EcMatching
open EcCoreFol


let default_name = "object matched to rewrite"
let default_name = EcIdent.create default_name

let process_match (x : pqsymbol) (tc : tcenv1)  =
  let (env,_hyps,_f) = tc1_eflat tc in
  let axiom = Ax.lookup (unloc x) env in

  let fmt    = Format.std_formatter in
  let ppe    = EcPrinting.PPEnv.ofenv env in

  (* let _ = Format.fprintf fmt "%a\n" (EcPrinting.pp_axiom ~long:true ppe) axiom in *)

  let f = (snd axiom).ax_spec in
  let binds,f' = match f.f_node with
    | Fquant (Lforall, binds, f1) -> binds, f1
    | _ -> [],f in

  let f1 = match f'.f_node with
    | Fapp (op, [f1 ; _]) when EcPath.p_equal EcCoreLib.CI_Bool.p_eq (fst (destr_op op)) -> f1
    | _ -> f' in

  let p = FPattern.pattern_of_form binds f1 in
  let p = FPattern.Pnamed (p, default_name) in
  let p = FPattern.Psub p in

  let f = tc1_goal tc in

  let print = function
    | (FPattern.Omem m,_) ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_mem ppe) m
    | FPattern.Oform f,_ ->
       Format.fprintf fmt "%a\n" (EcPrinting.pp_form ppe) f
    | _,_ -> ()
  in

  let print_names n o =
       let _ = Format.fprintf fmt "with name \"%a\" :\n" (EcPrinting.pp_local ppe) n in
       print o
  in

  let _ = match FPattern.search f p with
    | None ->
       Format.fprintf
         fmt "%a\n" (EcPrinting.pp_form ppe)
         (EcFol.f_local (EcIdent.create "there_is_no_map") EcTypes.tint)
    | Some map ->
       Mid.iter print_names map
  in

  tcenv_of_tcenv1 tc

open EcUtils
open EcFol
open EcTypes
open EcPath
open EcIdent
open EcEnv
(* open EcGenRegexp *)
(* open EcMatching *)

(* ---------------------------------------------------------------------- *)
exception NoMatches
exception CannotUnify
exception NoNext


module Name = struct
  include EcIdent
  let compare = id_compare
end


(* -------------------------------------------------------------------------- *)

module FPattern = struct

  type name = Name.t

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

  (* val mkengine    : base -> engine *)
  let mkengine (f : form) (p : pattern) (h : LDecl.hyps) : engine = {
      e_head         = Oform f, Mid.empty ;
      e_continuation = ZTop ;
      e_map          = Mid.empty ;
      e_pattern      = p ;
      e_hyps         = h ;
    }

  type ismatch =
    | Match
    | NoMatch

  let object_equal (o1 : tobject) (o2 : tobject) (h : LDecl.hyps) : bool =
    match o1,o2 with
    | Oform f1, Oform f2 -> EcReduction.is_conv h f1 f2
    | Omem m1, Omem m2 -> EcMemory.mem_equal m1 m2
    | Ompath_top (`Local id1), Ompath_top (`Local id2) -> id_equal id1 id2
    | Ompath_top (`Concrete (p1,None)), Ompath_top (`Concrete (p2,None)) ->
       p_equal p1 p2
    | Ompath_top (`Concrete (p1,Some op1)), Ompath_top (`Concrete (p2,Some op2)) ->
       p_equal p1 p2 && p_equal op1 op2
    | ((Omem _|Ompath_top _|Oform _),
       (Omem _|Ompath_top _|Oform _))
      -> false

  let rec merge_binds bs1 bs2 map = match bs1,bs2 with
    | [], _ | _,[] -> Some (map,bs1,bs2)
    | (_,ty1)::_, (_,ty2)::_ when not(gty_equal ty1 ty2) -> None
    | (id1,_)::_, (_,_)::_ when Mid.mem id1 map -> None
    | (id1,_)::bs1, (id2,ty2)::bs2 ->
       merge_binds bs1 bs2 (Mid.add id1 (id2,ty2) map)

  (* add_match can raise the exception : CannotUnify *)
  (* val add_match : matches -> name -> t_matches -> matches *)
  let add_match (map : map) (name : name) (o : tmatch) h =
    if Mid.set_disjoint (snd o) map
    then
      let (o1,o2) = o in
      let o = o1,match o1 with
                 | Oform      f  -> Mid.set_inter o2 (f_fv f)
                 | Omem       m  -> Mid.set_inter o2 (Sid.singleton m)
                 | Ompath_top mp -> Mid.set_inter o2 (m_fv Mid.empty (mpath mp [])) in
      let map = match Mid.find_opt name map with
        | None   -> Mid.add name o map
        | Some x -> if object_equal (fst x) (fst o) h then map
                    else raise CannotUnify
      in map
    else raise CannotUnify

  let e_next (e : engine) : nengine =
    { ne_continuation = e.e_continuation;
      ne_map = e.e_map;
      ne_binds = snd e.e_head;
      ne_hyps = e.e_hyps;
    }

  let n_engine (tm : tmatch) (e_pattern : pattern) (n : nengine) =
    { e_head = (fst tm, n.ne_binds);
      e_pattern;
      e_continuation = n.ne_continuation;
      e_map = n.ne_map;
      e_hyps = n.ne_hyps;
    }

  let sub_engine e p f =
    { e with e_head = f; e_pattern = Psub p }


  let rec substitution n1 p1 p2 = match p2 with
    | Panything -> Panything
    | Pnamed (_,n2) when id_equal n1 n2 -> p1
    | Pnamed (p2,n2) -> Pnamed (substitution n1 p1 p2, n2)
    | Psub p -> Psub (substitution n1 p1 p)
    | Por pl -> Por (List.map (substitution n1 p1) pl)
    | Ptype (p,ty) -> Ptype (substitution n1 p1 p, ty)
    | Pif (p2,p3,p4) -> Pif (substitution n1 p1 p2,
                             substitution n1 p1 p3,
                             substitution n1 p1 p4)
    | Papp (p2,pl) -> Papp (substitution n1 p1 p2,
                            List.map (substitution n1 p1) pl)
    | Ptuple pl -> Ptuple (List.map (substitution n1 p1) pl)
    | Pproj (p2,i) -> Pproj (substitution n1 p1 p2,i)
    | Pmatch (p2,pl) -> Pmatch (substitution n1 p1 p2,
                                List.map (substitution n1 p1) pl)
    | Pquant (q,bs,p2) -> Pquant (q,bs,substitution n1 p1 p2)
    | Ppvar (p2,p3) -> Ppvar (substitution n1 p1 p2,substitution n1 p1 p3)
    | Pglob (p2,p3) -> Pglob (substitution n1 p1 p2,substitution n1 p1 p3)
    | Ppr (p2,p3,p4,p5) -> Ppr (substitution n1 p1 p2,
                                substitution n1 p1 p3,
                                substitution n1 p1 p4,
                                substitution n1 p1 p5)
    | Pprog_var pv ->
       let xp = pv.pv_name in
       let name = xp.x_sub in
       if (EcPath.tostring name) = (EcIdent.tostring n1) then p1 else p2
    | Pxpath xp ->
       let name = xp.x_sub in
       if (EcPath.tostring name) = (EcIdent.tostring n1) then p1 else p2
    | Pmpath (p2,pl) -> Pmpath (substitution n1 p1 p2,
                                List.map (substitution n1 p1) pl)
    | Pobject (Omem mem) ->
       if id_equal n1 mem then p1 else p2
    | Pobject (Ompath_top _) -> p2
    | Pobject (Oform f) ->
       if not(Mid.mem n1 f.f_fv) then p2
       else match f.f_node with
            |  Flocal id ->
                if id_equal id n1 then Ptype (p1,f.f_ty) else p2
            | Fquant (quant,bs,f') ->
               if Mid.mem n1 f'.f_fv then Pquant (quant,bs,substitution n1 p1 (Pobject (Oform f')))
               else p2
            | Fif (f1,f2,f3) ->
               Pif (substitution n1 p1 (Pobject (Oform f1)),
                    substitution n1 p1 (Pobject (Oform f2)),
                    substitution n1 p1 (Pobject (Oform f3)))
            | Fmatch _ | Flet _-> Pobject (Oform f) (* FIXME *)
            | Fint _ -> Pobject (Oform f)
            | Fpvar (pvar,mem) ->
               if id_equal mem n1 then Ppvar (Pprog_var pvar,p1)
               else p2
            | Fglob (mpath,mem) ->
               if id_equal mem n1 then Pglob (substitution_mpath n1 p1 mpath, p1)
               else p2
            | Fop _ -> Pobject (Oform f) (* FIXME *)
            | Fapp (f1,fargs) ->
               Papp (substitution n1 p1 (Pobject (Oform f1)),
                     List.map (fun f -> substitution n1 p1 (Pobject (Oform f))) fargs)
            | Ftuple t ->
               Ptuple (List.map (fun f -> substitution n1 p1 (Pobject (Oform f))) t)
            | Fproj (f1,i) -> Pproj (substitution n1 p1 (Pobject (Oform f1)),i)
            | _ -> (* FIXME *) p2

    and substitution_mpath n1 p1 mpath =
      Pmpath (Pobject (Ompath_top mpath.m_top),
              List.map (substitution_mpath n1 p1) mpath.m_args)

  (* ---------------------------------------------------------------------- *)
  let rec process (e : engine) : nengine =
    match e.e_pattern, e.e_head with
    | Panything, _ -> next Match e

    | Pnamed (p,name), _ ->
       process { e with
                 e_pattern = p;
                 e_continuation = Znamed(e.e_head,name,e.e_continuation);
               }

    | Psub p, _ ->
       let le = sub_engines e p in
       process { e with
                 e_pattern = p;
                 e_continuation = Zor (e.e_continuation,le,e_next e);
               }

    | Ptype (p,ty), (Oform f, _) ->
       if ty_equal ty f.f_ty then
         process { e with e_pattern = p }
       else next NoMatch e

    | Por [], _ -> next NoMatch e
    | Por (p::pl), _ ->
       let f p = { e with
                   e_pattern = p;
                 } in
       process { e with
                 e_pattern = p;
                 e_continuation = Zor (e.e_continuation,List.map f pl,e_next e);
               }

    | Pquant (q1,bs1,p), (Oform f,binds) ->
       begin match f.f_node with
       | Fquant (q2,bs2,f2) ->
          (* FIXME : lambda case to be considered in higher order *)
          if not(q1 = q2) then next NoMatch e
          else begin
              match merge_binds bs1 bs2 binds with
              | None -> next NoMatch e
              | Some (new_binds,[],args) ->
                 let p =
                   Mid.fold_left
                     (fun acc n1 (n2,ty) ->
                       match ty with
                       | GTty ty -> substitution n1 (Pobject (Oform (f_local n2 ty))) acc
                       | _ -> acc)
                     p new_binds in
                 process { e with
                           e_pattern = p;
                           e_head = (Oform (f_quant q2 args f2), new_binds);
                           e_continuation = Zbinds (e.e_continuation, binds);
                         }
              | Some (_new_binds,_args,[]) -> (* FIXME for higher order *)
              (*    let p = *)
              (*      Mid.fold_left *)
              (*        (fun acc n1 (n2,ty) -> *)
              (*          match ty with *)
              (*          | GTty ty -> substitution n1 (Pobject (Oform (f_local n2 ty))) acc *)
              (*          | _ -> acc) *)
              (*        p new_binds in *)
              (*    let p = Pquant (q1,args,p) in *)
              (*    process_higer_order { e with *)
              (*                          e_pattern = p; *)
              (*                          e_head = Oform f2, new_binds; *)
              (*                          e_continuation = Zbinds (e.e_continuation, binds); *)
              (*                        } *)
                 next NoMatch e
              | _ -> assert false
            end
       | _ -> next NoMatch e
       end

    | Pif (pcond,p1,p2), (Oform f,binds) ->
       begin match f_node f with
       | Fif (cond,b1,b2) ->
          let zand = [((Oform b1,binds),p1);((Oform b2,binds),p2)] in
          process { e with
                    e_head = Oform cond, binds;
                    e_pattern = pcond;
                    e_continuation = Zand ([],zand,e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Papp (pop,pargs), (Oform f, binds) ->
       (* FIXME : higher order *)
       begin match f_node f with
       | Fapp (fop,fargs) ->
          let pl,fl = List.length pargs, List.length fargs in
          if fl < pl
          then next NoMatch e (* process_higer_order e *)
          else
            let fargs1,fargs2 = List.split_at (fl - pl) fargs in
            let fop' = f_app fop fargs1 (EcTypes.toarrow (List.map f_ty fargs2) (f_ty fop)) in
            let to_match_args = List.combine (List.map (fun x -> Oform x, binds)fargs2) pargs in
            let l = ((Oform fop', binds), pop)::to_match_args in
            let p,h,l = match List.rev l with
              | [] -> assert false
              | (o,p)::l -> p,o,l in
            process { e with
                      e_pattern = p;
                      e_head = h;
                      e_continuation = Zand ([],l,e.e_continuation);
                    }
       | _ -> next NoMatch e (* process_higer_order e *)
       end

    | Ptuple [], (Oform f,_) ->
       begin match f_node f with
       | Ftuple [] -> next Match e
       | _ -> next NoMatch e
       end
    | Ptuple (p::ptuple), (Oform f, binds) ->
       begin match f_node f with
       | Ftuple [] -> next NoMatch e
       | Ftuple (f::ftuple) ->
          if (List.length ptuple = List.length ftuple)
          then
            let zand =
              List.combine (List.map (fun x -> Oform x, binds) ftuple) ptuple in
            let l = ((Oform f,binds),p)::zand in
            let pat,o,l = match List.rev l with
              | [] -> assert false
              | (o,p)::l -> p,o,l in
            process
              { e with
                e_pattern = p;
                e_head = Oform f, binds;
                e_continuation =
                  Zor (Zand ([],zand,e.e_continuation),
                       [{ e with
                          e_pattern = pat;
                          e_head = o;
                          e_continuation = Zand ([],l,e.e_continuation) }],
                       e_next e)
              }
          else next NoMatch e
       | _ -> next NoMatch e
       end

    | Pproj (e_pattern,i), (Oform f, binds) ->
       begin match f_node f with
       | Fproj (f,j) when i = j ->
          process { e with
                    e_pattern;
                    e_head = Oform f, binds;
                  }
       | _ -> next NoMatch e
       end

    | Pmatch (p,pl) , (Oform f,binds) ->
       begin match f_node f with
       | Fmatch (f,fl,_) when (List.length fl = List.length pl) ->
          let zand = List.combine (List.map (fun x -> Oform x, binds) fl) pl in
          process {
              e with
              e_pattern = p;
              e_head = Oform f, binds;
              e_continuation = Zand ([],zand,e.e_continuation);
            }
       | _ -> next NoMatch e
       end

    | Pobject o1, (o2,_) when object_equal o1 o2 e.e_hyps -> next Match e
    | Pobject (Oform f1), (Oform f2, _) -> begin
        match f1.f_node with
        | Flocal id1 -> begin
            match Mid.find_opt id1 e.e_map with
            | None -> next NoMatch e
            | Some (Oform f1, _) when EcReduction.is_conv e.e_hyps f1 f2 ->
               next Match e
            | _ -> next NoMatch e
          end
        | _ -> next NoMatch e
      end
    | Pobject _, _ -> next NoMatch e

    | Ppvar (p1,p2), (Oform f,binds) ->
       begin match f.f_node with
       | Fpvar (_,m) ->
          process { e with
                    e_pattern = p2;
                    e_head = Omem m, binds;
                    e_continuation = Zand ([],[(Oform f,binds),p1],e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Pprog_var x1, (Oform f,_) ->
       begin match f.f_node with
       | Fpvar (x2,_) when pv_equal x1 x2 -> next Match e
       | _ -> next NoMatch e
       end

    | Pglob (p1,p2), (Oform f,binds) ->
       begin match f.f_node with
       | Fglob (x,m) ->
          let zand = [(Ompath_top x.m_top,binds), p1] in
          process { e with
                    e_pattern = p2;
                    e_head = Omem m, binds;
                    e_continuation = Zand ([],zand,e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Pmpath (m,[]), (Ompath_top _,_ as omp) ->
       process { e with
                 e_pattern = m;
                 e_head = omp;
               }
    | Pmpath _,(Ompath_top _,_) -> next NoMatch e

    | Ppr (pmem,pfun,pargs,pevent), (Oform f, binds) ->
       begin match f.f_node with
       | Fpr pr ->
          let zand = [((Oform f, binds), pfun);
                      ((Oform pr.pr_args,binds), pargs);
                      ((Oform pr.pr_event, binds), pevent)] in
          process { e with
                    e_pattern = pmem;
                    e_head = Omem pr.pr_mem, binds;
                    e_continuation = Zand ([], zand, e.e_continuation);
                  }
       | _ -> next NoMatch e
       end

    | Pxpath pxp, (Oform f, _) ->
       begin match f.f_node with
       | Fpr pr when x_equal pr.pr_fun pxp -> next Match e
       | _ -> next NoMatch e
       end

    | ((Pmpath _|Pglob _|Pprog_var _|Ppvar _|Pquant _|Ppr _|Pxpath _),
       ((Oform _|Omem _|Ompath_top _),_))
      | (Pproj _|Ptuple _|Papp _|Pif _|Pmatch _|Ptype _),
        ((Omem _|Ompath_top _),_) ->
       next NoMatch e

  and next (m : ismatch) (e : engine) : nengine = next_n m (e_next e)

  and next_n (m : ismatch) (e : nengine) : nengine =
    match m,e.ne_continuation with
    | NoMatch, ZTop -> raise NoMatches

    | Match, ZTop   -> e

    | NoMatch, Znamed (_f, _name, ne_continuation) ->
       next_n NoMatch { e with ne_continuation }

    | Match, Znamed (f, name, ne_continuation) ->
       let m,e =
         try Match, { e with
                      ne_continuation;
                      ne_map = add_match e.ne_map name f e.ne_hyps;
                    }
         with
         | CannotUnify ->
            NoMatch, { e with
                       ne_continuation;
                     } in
       next_n m e

    | NoMatch, Zand (_,_,ne_continuation) ->
       next_n NoMatch { e with ne_continuation }

    | Match, Zand (_before,[],ne_continuation) -> next_n Match { e with ne_continuation }
    | Match, Zand (before,(f,p)::after,z) ->
       process (n_engine f p { e with ne_continuation = Zand ((f,p)::before,after,z)})

    | Match, Zor (ne_continuation, _, _) -> next_n Match { e with ne_continuation }

    | NoMatch, Zor (_, [], ne) ->
       next_n NoMatch ne

    | NoMatch, Zor (_, e'::engines, ne) ->
       process { e' with e_continuation = Zor (e'.e_continuation, engines, ne); }

    | Match, Zbinds (ne_continuation, ne_binds) ->
       next_n Match { e with ne_continuation; ne_binds }

    | NoMatch, Zbinds (ne_continuation, ne_binds) ->
       next_n NoMatch { e with ne_continuation; ne_binds }

  and sub_engines (e : engine) (p : pattern) : engine list =
    match e.e_head with
    | Omem _,_  -> []
    | Ompath_top _,_ -> []
    | Oform f, binds ->
       match f_node f with
       | Flet _
         | FhoareF _
         | FhoareS _
         | FbdHoareF _
         | FbdHoareS _
         | FequivF _
         | FequivS _
         | FeagerF _
         | Fint _
         | Flocal _
         | Fop _-> []
       | Fif (cond,f1,f2) ->
          List.map (sub_engine e p) [ Oform cond,binds ; Oform f1,binds ; Oform f2,binds ]
       | Fapp (f, args) ->
          List.map (sub_engine e p) ((Oform f,binds)::(List.map (fun x -> Oform x, binds) args))
       | Ftuple args ->
          List.map (sub_engine e p) (List.map (fun x -> Oform x, binds) args)
       | Fproj (f,_) -> [sub_engine e p (Oform f, binds)]
       | Fmatch (f,fl,_) ->
          List.map (sub_engine e p) ((Oform f, binds)::(List.map (fun x -> Oform x, binds) fl))
       | Fpr pr ->
          List.map (sub_engine e p) [ Omem pr.pr_mem   , binds ;
                                      Oform pr.pr_args , binds ;
                                      Oform pr.pr_event, binds ]
       | Fquant (_,bs,f1) ->
          [sub_engine e p (Oform f1, Mid.set_union binds (Mid.of_list (List.map (fun (x,y) -> (x,(x,y)))bs)))]
       | Fglob (mp,mem) ->
          List.map (sub_engine e p) [ Ompath_top mp.m_top,binds ;
                                      Omem mem, binds ]
       | Fpvar (_pv,mem) ->
          List.map (sub_engine e p) [ Omem mem, binds ]

  (* and process_higer_order (e : engine) = match e.e_head with *)
  (*   | Omem _,_ -> next NoMatch e (\* FIXME *\) *)
  (*   | Ompath_top _,_ -> next NoMatch e (\* FIXME *\) *)
  (*   | Oform f, _binds -> *)
  (*      match e.e_pattern,f.f_node with *)
  (*      | Pquant _,Fquant _ -> process e *)
  (*      | Pquant (_,[],p1), _ -> process { e with e_pattern = p1 } *)
  (*      | Pquant ((Lexists|Lforall),_,_),_ -> next NoMatch e *)
  (*      | Pquant (Llambda,(_x,_gty)::_args,_p1), _ -> *)
  (*         next NoMatch e *)

  (*      | Papp (pop, pargs), Fapp (fop,fargs) -> begin *)
  (*          let lp,lf = List.length pargs, List.length fargs in *)
  (*          let m x = min x 0 in *)
  (*          match List.split_at (m (lf-lp)) fargs, *)
  (*                List.split_at (m (lp-lf)) pargs with *)
  (*          | (_::_,_), (_::_,_) -> assert false *)
  (*          | ([],_), (_,_) -> process e *)
  (*          | (args,pargs), ([],fargs) -> *)

  (*          | _ -> next NoMatch e (\* FIXME *\) *)
  (*        end *)

  (*      | _,_ -> next NoMatch e (\* FIXME *\) *)



  let get_matches (e : engine) : map = e.e_map
  let get_n_matches (e : nengine) : map = e.ne_map

  let search_eng e =
    try Some (process e) with
    | NoMatches -> None

  let search (f : form) (p : pattern) (h : LDecl.hyps) =
    try Some (get_n_matches (process (mkengine f p h))) with
    | NoMatches -> None

  let pattern_of_form (bindings: bindings) (f : form) =
    let sbd = Sid.of_list (List.map fst bindings) in
    let rec aux f =
      if Mid.set_disjoint sbd f.f_fv then Pobject (Oform f)
      else
        match f.f_node with
        | Fif(f1,f2,f3)      -> Pif(aux f1, aux f2, aux f3)
        | Fapp(f,args)       -> Papp(aux f, List.map aux args)
        | Ftuple args        -> Ptuple(List.map aux args)
        | Fmatch(f,args,_ty) -> Pmatch(aux f, List.map aux args)
        | Fproj(f,i)         -> Pproj(aux f, i)
        | Flocal id          -> Pnamed (Ptype (Panything,f.f_ty), id)
        | Fpvar(x,m)         -> Ppvar(Pprog_var x, aux_mem m)
        | Fglob(mp, m)       -> Pglob(aux_mp mp, aux_mem m)
        | Fpr(pr)            -> Ppr (aux_mem pr.pr_mem,
                                     aux_xpath pr.pr_fun,
                                     aux pr.pr_args,
                                     aux_event pr.pr_event)
        | Fquant(quant,binds,f) -> Pquant (quant,binds,aux f)
        | _ -> raise (Invalid_argument "match case non-exhaustive in pattern_of_form")

    and aux_mem m =
      if Sid.mem m sbd then Pnamed (Panything, m)
      else Pobject(Omem m)

    and aux_mp mp =
      Pmpath (aux_mp_top mp.m_top, List.map aux_mp mp.m_args)

    and aux_mp_top mpt =
      match mpt with
      | `Local id when Sid.mem id sbd -> Pnamed (Panything, id)
      | _                             -> Pobject (Ompath_top mpt)

    and aux_xpath xpath = Pxpath xpath (* FIXME ?? *)

    and aux_event event = aux event
    in

    aux f




  let rec rewrite_term map f = match f.f_node with
    | Flocal id -> begin
        match Mid.find_opt id map with
        | None -> f
        | Some (Oform f', _) -> rewrite_term map f'
        | _ -> f
      end
    | Fquant (quant,bs,f') ->
       let f' = rewrite_term map f' in
       f_quant quant bs f'
    | Fif (f1,f2,f3) ->
       f_if (rewrite_term map f1) (rewrite_term map f2) (rewrite_term map f3)
    | Fmatch _ | Flet _-> f (* FIXME *)
    | Fint _ -> f
    | Fpvar (pvar,mem) ->
       begin match Mid.find_opt mem map with
       | None -> f
       | Some (Omem mem,_) -> f_pvar pvar f.f_ty mem
       | _ -> f
       end
    | Fglob (mpath,mem) ->
       begin match Mid.find_opt mem map with
       | None -> f
       | Some (Omem mem,_) -> f_glob mpath mem
       | _ -> f
       end
    | Fop _ -> f (* FIXME *)
    | Fapp (f1,fargs) ->
       f_app (rewrite_term map f1) (List.map (rewrite_term map) fargs) f.f_ty
    | Ftuple t -> f_tuple (List.map (rewrite_term map) t)
    | Fproj (f1,i) -> f_proj (rewrite_term map f1) i f.f_ty
    | _ -> (* FIXME *) f



end











(* (\* -------------------------------------------------------------------------- *\) *)

(* module IPattern = struct *)
(*   open FPattern *)
(*   open EcModules *)
(*   open Zipper *)

(*   exception AtEnd *)

(*   type anchor = Start | End *)

(*   type stmt_pattern = *)
(*     | Anchor of anchor *)
(*     | Any *)
(*     | Base   of instr_pattern *)
(*     | Choice of stmt_pattern list *)
(*     | Named  of stmt_pattern * EcIdent.t *)
(*     | Repeat of stmt_pattern * int option EcUtils.pair * *)
(*                   [ `Greedy | `Lazy ] *)
(*     | Seq    of stmt_pattern list *)

(*    and instr_pattern = *)
(*      | RAssign of pattern * pattern *)
(*      | RSample of pattern * pattern *)
(*      | RCall   of pattern * pattern * pattern *)
(*      | RIf     of pattern * stmt_pattern * stmt_pattern *)
(*      | RWhile  of pattern * stmt_pattern *)


(*   type stmt_engine = { *)
(*       se_head         : instr list; *)
(*       se_pattern      : stmt_pattern; *)
(*       se_zipper       : zipper; *)
(*       se_map          : instr list Mid.t; *)
(*       se_fmap         : tobject Mid.t; *)
(*       se_hyps         : LDecl.hyps; *)
(*       se_continuation : continuation; *)
(*     } *)

(*   and instr_engine = { *)
(*       ie_head         : instr; *)
(*       ie_pattern      : instr_pattern; *)
(*       ie_zipper       : zipper; *)
(*       ie_fmap         : tobject Mid.t; *)
(*       ie_hyps         : LDecl.hyps; *)
(*       ie_continuation : continuation; *)
(*     } *)

(*   and continuation = *)
(*     | Ctop *)
(*     | Cnamed of EcIdent.t * continuation *)
(*     | Cseq   of stmt_pattern list * continuation *)


(*   let mk_engine (stmt : stmt) (ps : stmt_pattern) (hyps : LDecl.hyps) = { *)
(*       se_head         = stmt.s_node; *)
(*       se_pattern      = ps; *)
(*       se_zipper       = zipper [] [] ZTop; *)
(*       se_map          = Mid.empty; *)
(*       se_fmap         = Mid.empty; *)
(*       se_hyps         = hyps; *)
(*       se_continuation = Ctop; *)
(*     } *)

(*   let process_stmt (se : stmt_engine) : instr_engine = *)
(*     match se.se_pattern with *)
(*     | Anchor Start when *)
(*            se.se_zipper.z_head = [] && se.se_zipper.z_path = ZTop -> *)
(*        next Match se *)
(*     | Anchor Start -> next NoMatch se *)

(*     | Anchor End when *)
(*            se.se_zipper.z_tail = [] && se.se_zipper.z_path = ZTop -> *)
(*        next Match se *)
(*     | Anchor End -> next NoMatch se *)
(*     | Seq [] -> next Match se *)
(*     | Seq (p::after) -> *)
(*        process_stmt { se with *)
(*                       se_pattern = p; *)
(*                       se_continuation = Cseq (after,se.se_continuation); *)
(*                     } *)

(*   and next m se = match se.se_continuation, m with *)
(*     | Ctop, Match -> Some se *)
(*     | Ctop, NoMatch -> None *)
(*     | Cnamed  *)


(*   and process_instr (ie : instr_engine) = *)

(* end *)

(* The main tactic is [run_solver] below *)
(*i camlp4deps: "grammar/grammar.cma" i*)
DECLARE PLUGIN "vpl_plugin"  

(*i*)
open Stdarg (* WARNING: necessary for "constr" campl4 notation ! *) 
open Ltac_plugin (* WARNING: necessary at the plugin load *)
open Vpl
(*i*)

module Rat = Scalar.Rat
module Vec = Vector.Rat.Positive
module Var = Var.Positive
module Cs = Cstr.Rat.Positive
module Cons = IneqSet.Cons

type compf = EConstr.constr -> EConstr.constr
  
module R = Reification
module M = R.Reduction

(***************)
(* reification *)
let check_may_cte (sigma: Evd.evar_map) (t: EConstr.constr): unit =
  match R.decomp_term sigma t with
  | Term.App(head, _) when
     (EConstr.eq_constr sigma head (Lazy.force R.Input.tag_cte) ||
        EConstr.eq_constr sigma head (Lazy.force R.Qc._Qcmake) ||
     EConstr.eq_constr sigma head (Lazy.force R.Input._Z2Qc) ) -> ()
  | Term.App(head, args) when EConstr.eq_constr sigma head (Lazy.force R.Qc._Q2Qc) -> (
     match R.decomp_term sigma args.(0) with
     |  Term.App(head, args) when EConstr.eq_constr sigma head (Lazy.force R.Qc._Qmake) -> ()
     | _ -> raise R.RatReifyError)  
  | _ -> raise R.RatReifyError

let addvar (m: R.Varmap.t) (t: EConstr.constr):  R.Input.term * R.AffTerm.t =
  let x = R.Varmap.add m t in (R.Input.var x, R.AffTerm.var x)
      
let rec reify_aff (sigma: Evd.evar_map) (comp:compf) (m: R.Varmap.t) (t: EConstr.constr): R.Input.term * R.AffTerm.t =
  (* R.print_debug t; *)
  match R.decomp_term sigma t with  
  | Term.App(head, args) when EConstr.eq_constr sigma head (Lazy.force R.Qc._Qcplus) -> (
     let (t1,a1) = reify_aff sigma comp m args.(0) in
     let (t2,a2) = reify_aff sigma comp m args.(1) in
     (R.Input.add t1 t2, R.AffTerm.add a1 a2))
  | Term.App(head, args) when EConstr.eq_constr sigma head (Lazy.force R.Qc._Qcopp) -> (
     let (t0,a0) = reify_aff sigma comp m args.(0) in
     (R.Input.opp t0, R.AffTerm.opp a0))
  | Term.App(head, args) when EConstr.eq_constr sigma head (Lazy.force R.Qc._Qcminus) -> (
     let (t1,a1) = reify_aff sigma comp m args.(0) in
     let (t2,a2) = reify_aff sigma comp m args.(1) in
     (R.Input.sub t1 t2, R.AffTerm.sub a1 a2))
  | Term.App(head, args) when EConstr.eq_constr sigma head (Lazy.force R.Qc._Qcmult) -> (
     let s = R.Varmap.get_state m in
     let (t1, a1) = reify_aff sigma comp m args.(0) in
     let (t2, a2) = reify_aff sigma comp m args.(1) in
     match R.AffTerm.is_cte a1 with
     | Some c1 ->
       (R.Input.mul t1 t2, R.AffTerm.mul c1 a2)
     | None -> (
        match R.AffTerm.is_cte a2 with
        | Some c2 ->
           (R.Input.mul t1 t2, R.AffTerm.mul c2 a1)
        | None -> (
          R.Varmap.restore m s;
          addvar m t)))
  | _ ->
     try
       check_may_cte sigma t;
       let c = R.Qc.reify_as_Rat sigma (comp t) in
       (R.Input.cte t, R.AffTerm.cte c)
     with
       R.RatReifyError -> addvar m t

(*************************)
(* debugging reification *)

let reify_term (sigma: Evd.evar_map) (comp:compf) (m: R.Varmap.t) (t: EConstr.constr): EConstr.constr =
  let (t, a) = reify_aff sigma comp m t in
  (* R.print_debug (R.Input.export t);
     R.AffTerm.print a; *)
  R.Input.export t

let invert_sem (lc:EConstr.constr) (g:EConstr.constr): unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let rcstr = Lazy.force R.Input._rcstr in
    let term = Lazy.force R.Input._term in
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl (*Proofview.Goal.sigma gl*) in
    let rcomp = Redexpr.cbv_vm env sigma in
    let mycomp t = (
      (* print_endline "starting vm_compute";
         R.print_debug t; *)
      let t' = rcomp t in
      (* print_endline "ending vm_compute";
         R.print_debug t'; *)
      t') in
    let m = R.Varmap.empty() in
    (* print_endline "\ntraverse list..."; *)
    let l = R.List.map sigma rcstr (R.Prod.set_fst sigma term (fun t _ -> reify_term sigma mycomp m t)) lc  in
    (* print_endline "to_varmap..."; *)
    let concl = R.Input.vplGoal l (R.Varmap.to_varmap m) g in
    (* 
       print_endline "change concl !";
       R.print_debug env sigma concl;
    *)
    Tacticals.New.tclTHENLIST
      [
        Tactics.change_concl concl
      ]
  )

(**********)
(* solver *)

      
(* hack from Guillaume Melquiond to solve universe constraints on the fresh universe of "vtype":
   we solve them on the typing of a small term with (hopefully) the same universe constraints !
*)

let dummy vtype =
  let h = M.mkv 1 in
  let v = M.mkv 2 in
  let dummy_1 = M.var v h in
  let dummy_2 = M.cons None dummy_1 (M.nil v) in
  let dummy_3 = M.return v dummy_2 in
  let dummy_4 = M.run v dummy_3 in
  M.export vtype (M.bindHyp h dummy_4)

let refreshed_sigma (env:Environ.env) (sigma: Evd.evar_map) (vtype: EConstr.types) =
  let l = R.List.of_list (Lazy.force R.Input._rcstr) [] in
  let p = M.reduceRun l (dummy vtype) in
  (* R.print_debug p; *)
  fst (Typing.type_of ~refresh:false env sigma p)

let reify_input (sigma: Evd.evar_map) (input: Cs.t list ref) (comp:compf) (m: R.Varmap.t) (t: EConstr.constr) (cmp: EConstr.constr): EConstr.constr =
  let (t, a) = reify_aff sigma comp m t in
  let cmp = R.Input.reify_as_cmpT sigma cmp in
  input := (Cs.mk2 cmp a.R.AffTerm.lin (Rat.neg a.R.AffTerm.cst)) :: (!input);
  R.Input.export t

let mkVar (level: int) (id: int): M.v =
  M.mkv (id-level)

let dcstr2var (level: int) (v: M.v) (c:ASTCert.dcstr): M.fexp =
  let id = ASTCert.get_id c in
  assert (id > 0);
  M.var v (mkVar level id)

let rec dcstr2fexp (level: int) (v: M.v) (c:ASTCert.dcstr): M.fexp =
  if ASTCert.get_id c > 0 then
    dcstr2var level v c
  else
    raw_fexp level v c 
and raw_fexp (level: int) (v: M.v)  (c:ASTCert.dcstr): M.fexp =
  match ASTCert.get_def c with
  | ASTCert.Hyp _ -> dcstr2var level v c
  | ASTCert.Top -> M.top v
  | ASTCert.Add(c1, c2) -> M.add v (dcstr2fexp level v c1) (dcstr2fexp level v c2)
  | ASTCert.Mul(n, c) -> M.mul v n (dcstr2fexp level v c)
  | ASTCert.Merge(c1, c2) -> M.merge v (dcstr2fexp level v c1) (dcstr2fexp level v c2)
  | _ -> assert false (* not yet implemented ! *)
(*
  | Triv (t, n) -> Printf.fprintf out "0 %s %s" (Cstr.cmpT_to_string t) (Rat.to_string n)
  | To_le c -> (
    Printf.fprintf out "! ";
    printc out c)
*)

let rec dcstrlist (v: M.v) (l:ASTCert.dcstr list) (acc: M.list_fexp): M.list_fexp =
  match l with
  | [] -> acc
  | c::l' -> dcstrlist v l' (M.cons (ASTCert.get_vardef c) (dcstr2fexp 0 v c) acc)

let return (vid: int) (l:ASTCert.dcstr list): M.pedra =
  let v = M.mkv vid in
  M.return v (dcstrlist v l (M.nil v))
     
let contrad (vid: int) (c:ASTCert.dcstr): M.pedra =
  let v = M.mkv vid in
  M.contrad v (dcstr2fexp 0 v c)

let rec insert_binds (level: int) (vid: int) (l:ASTCert.dcstr list) (p:M.pedra): M.pedra =
  match l with
  | [] -> p
  | c::l' ->
     let level = level+1 in
     let v = mkVar level vid in
     insert_binds level vid l' (M.bind v (raw_fexp level v c) p)

let rec insert_hyps_rec (level: int) (vid: int) (l:ASTCert.dcstr list) (p:M.script): M.script =
  match l with
  | [] -> p
  | c::l' -> (
    if ASTCert.get_id c > 0
    then
      let level = level+1 in
      insert_hyps_rec level vid l' (M.bindHyp (mkVar level vid) p)
    else
      insert_hyps_rec level vid l' (M.skipHyp (mkVar level vid) p)
  )

(* same code as insert_hyps above, except that we implicitly skip the deepest hyps that are unused *) 
let rec insert_skiphyps_rec (level: int) (vid: int) (l:ASTCert.dcstr list) (p:M.script): M.script =
  match l with
  | [] -> p
  | c::l' -> (
    if ASTCert.get_id c > 0
    then
      let level = level+1 in
      insert_hyps_rec level vid l' (M.bindHyp (mkVar level vid) p)
    else
      insert_skiphyps_rec level vid l' p
  )
 
let insert_hyps (level: int) (vid: int) (l:ASTCert.dcstr list) (p:M.pedra): M.script =
   insert_skiphyps_rec level vid l (M.run (mkVar level vid) p)
     
let solver (l: Cs.t list): M.script =
  (* print_endline "-- input:";
     List.iter (fun c -> Printf.printf "%s\n%!" (Cs.to_string Var.to_string c)) l;
  *)
  let i = ASTCert.make_smart () in
  let l = ASTCert.import i (fun c -> c) (fun c cert -> (c, cert)) l in
  let (out, ndefs, vid, res) = 
    match Pol.addM (ASTCert.factory i) Pol.top l with
    | Pol.Added pol -> (
      ASTCert.set_output_fp_map (fun c -> c) i pol;
      let out = ASTCert.export i in
      let ndefs = out.ASTCert.numdefs in
      let vid = ndefs + out.ASTCert.usedhyps + 1 in
      let res = return vid out.ASTCert.res in
      (out, ndefs, vid, res)
    )  
    | Pol.Contrad ce -> (
      ASTCert.set_output i [ASTCert.skip_mul ce];
      let out = ASTCert.export i in
      let ndefs = out.ASTCert.numdefs in
      let vid = ndefs + out.ASTCert.usedhyps + 1 in
      let res = contrad vid ce in
      (out, ndefs, vid, res)
    ) in
  (*  print_endline "-- output:";
      ASTCert.print_output stdout out;
  *)
  let defs = insert_binds 0 vid (List.rev_append out.ASTCert.defs []) res in
  insert_hyps ndefs vid out.ASTCert.hyps defs

(* A clause specifying that the [let] should not try to fold anything the goal
   matching the list of constructors (see [letin_tac] below). *)

let nowhere: Locus.clause = Locus.({ onhyps = Some []; concl_occs = NoOccurrences })

(* We expect here a goal of the form [VplGoal lc g] where [a] is a fresh name.
   This tactic first reifies [c] as [sem l m],
   Then it finds a "script" from the solver, 
   and acts like Ltac code: 
      change (VplGoal (sem l m) g); 
      pose (a:=(reduceRun l p))
*)  
let run_solver (lc:EConstr.constr) (g:EConstr.constr) (a:Names.Id.t) : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let rcstr = Lazy.force R.Input._rcstr in
    let term = Lazy.force R.Input._term in
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let rcomp = Redexpr.cbv_vm env sigma in
    let m = R.Varmap.empty() in
    let input = ref [] in
    let l = R.List.map sigma rcstr (R.Prod.set_fst sigma term (reify_input sigma input rcomp m)) lc in
    let m = R.Varmap.to_varmap m in
    let sigma, vtype = Evd.new_sort_variable Evd.univ_flexible_alg sigma in
    let vtype = EConstr.mkSort vtype in
    let p = M.reduceRun l (M.export vtype (solver !input)) in
    let concl = R.Input.vplGoal l m g in
    (* print_endline "change concl:"; 
       R.print_debug p; *)
    Tacticals.New.tclTHENLIST
      [
        Proofview.Unsafe.tclEVARS (refreshed_sigma env sigma vtype);
        Tactics.change_concl concl;
        Tactics.letin_tac None (Names.Name a) p None nowhere
      ]
  )

(***************)
(* coq tactics *)
 
TACTIC EXTEND vpl_run_solver
  | [ "run_solver" constr(lc) constr(g) ident(a) ] -> [ run_solver lc g a ]
END

TACTIC EXTEND vpl_invert_sem
  | [ "invert_sem" constr(lc) constr(g) ] -> [ invert_sem lc g ]
END


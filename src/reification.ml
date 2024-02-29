(* Simple Library for reification/generation of Coq ASTs.

   File initially inspired from 
     https://github.com/braibant/coq-tutorial-ml-tactics
   by thomas.braibant@gmail.com

*)

open Vpl

module Rat = Scalar.Rat
module Vec = Vector.Rat
exception RatReifyError

(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "Vpl"

exception DecompositionError of string

let raise_unknown_constructor s =
   raise (DecompositionError (Printf.sprintf "Unknown constructor in %s" s))

(** Getting constrs (primitive Coq terms) from existing Coq
   libraries. 
   
    - [find_reference] is located in {v interp/coqlib.ml v} and return a global reference to the name "dir.s" (it must be used lazily). 
    
    - [constr_of_global] is located in {v library/libnames.ml v} and turn a
    global reference into a constr.
*)
let find_constant contrib dir s =
  lazy (EConstr.of_constr (UnivGen.constr_of_global (Coqlib.find_reference contrib dir s)))

let init_constant dir s = find_constant contrib_name dir s

(** [decomp_term] returns a user view of a constr. 

This is inspired from plugins/quote/quote.ml
*)

let decomp_term (sigma:Evd.evar_map) (c : EConstr.constr)  = 
  EConstr.kind sigma (Termops.strip_outer_cast sigma c) 

let lapp c v  = EConstr.mkApp (Lazy.force c, v)

let mkLambda (t:EConstr.types) (b:EConstr.constr): EConstr.constr =
  EConstr.mkLambda (Names.Name.Anonymous, t, b)
  
let print_debug env sigma t =
  Printf.printf "--- BEGIN DEBUG TERM ---\n%s\n---------------\n%!" (Pp.string_of_ppcmds (Printer.pr_econstr_env env sigma t))

module Positive = struct
  let path = ["Coq" ; "Numbers"; "BinNums"]
  (* let typ = init_constant path "positive" *)
  let xH =  init_constant path "xH"
  let _xO =  init_constant path "xO"
  let _xI =  init_constant path "xI"
    
  let reify_as_RatZ sigma =
    let rec reify_with_shift (s:int) acc p =
      if EConstr.eq_constr sigma p (Lazy.force xH) then
        Z.logor acc (Z.shift_left Scalar.Int.u s)
      else 
        match decomp_term sigma p with
        | Constr.App(head, args) when EConstr.eq_constr sigma head (Lazy.force _xO) ->
           reify_with_shift (s+1) acc args.(0)
        | Constr.App(head, args) when EConstr.eq_constr sigma head (Lazy.force _xI) ->
           reify_with_shift (s+1) (Z.logor acc (Z.shift_left Scalar.Int.u s)) args.(0)
        | _ -> raise RatReifyError
    in fun p -> reify_with_shift 0 Scalar.Int.z p
         
  let xO p = lapp _xO [| p |]
  let xI p = lapp _xI [| p |]

  let from_RatZ =
    let rec from_RatZ p =
      if Scalar.Int.cmp p Scalar.Int.u <= 0 then
        Lazy.force xH
      else if Scalar.Int.cmp (Z.logand p Scalar.Int.u) Scalar.Int.u = 0 then
        xI (from_RatZ (Z.shift_right p 1))
      else
        xO (from_RatZ (Z.shift_right p 1))
    in fun p ->
      assert (Scalar.Int.cmp p Scalar.Int.u >= 0);
      (from_RatZ p)

  let rec from_Var p =
    match p with
    | Var.XH -> Lazy.force xH
    | Var.XI p -> xI (from_Var p)
    | Var.XO p -> xO (from_Var p)

end
  
module Z =
struct

  let path = ["Coq" ; "Numbers"; "BinNums"]
  let _Z0 =  init_constant path "Z0"
  let _Zpos =  init_constant path "Zpos"
  let _Zneg =  init_constant path "Zneg"
    
  let reify_as_RatZ sigma p =
    if EConstr.eq_constr sigma p (Lazy.force _Z0) then
      Scalar.Int.z
    else 
      match decomp_term sigma p with
      | Constr.App(head, args) when EConstr.eq_constr sigma head (Lazy.force _Zpos) ->
         Positive.reify_as_RatZ sigma args.(0)
      | Constr.App(head, args) when EConstr.eq_constr sigma head (Lazy.force _Zneg) ->
         Scalar.Int.neg (Positive.reify_as_RatZ sigma args.(0))
      | _ -> raise RatReifyError
    
  let from_RatZ x =
    let sign = Scalar.Int.cmp Scalar.Int.z x in
    if sign = 0 then
      Lazy.force _Z0
    else if sign < 0 then
      lapp _Zpos [| Positive.from_RatZ x |]
    else
      lapp _Zneg [| Positive.from_RatZ (Scalar.Int.neg x) |]
    
end 

module Qc = struct
  let path = [ "Coq" ; "QArith"; "Qcanon" ]
  let pathQ = [ "Coq" ; "QArith"; "QArith_base" ]
  let _Qcopp = init_constant path "Qcopp"
  let _Qcplus = init_constant path "Qcplus"
  let _Qcminus = init_constant path "Qcminus"
  let _Qcmult = init_constant path "Qcmult"
  let _Q2Qc = init_constant path "Q2Qc"
  let _Qcmake = init_constant path "Qcmake"
  let _Qmake = init_constant pathQ "Qmake" 

    
  let reify_as_Rat sigma p =
    match decomp_term sigma p with
    | Constr.App(head, args) when EConstr.eq_constr sigma head (Lazy.force _Qcmake) -> (
       match decomp_term sigma args.(0) with
       | Constr.App(head, args) when EConstr.eq_constr sigma head (Lazy.force _Qmake) ->
          let num = Z.reify_as_RatZ sigma args.(0) in
          let den = Positive.reify_as_RatZ sigma args.(1) in
          Rat.ofZ num den
       | _ -> raise RatReifyError)
    | _ -> raise RatReifyError

  let from_Rat q =
    let (num, den) = Rat.toZ q in
    let q = lapp _Qmake [| Z.from_RatZ num; Positive.from_RatZ den |] in
    lapp _Q2Qc [| q |]
    
end

module AffTerm =
struct
 
  type t = { lin: Vec.t; cst: Rat.t }
  type var = EConstr.constr *  t
  let cte x = { lin = Vec.nil; cst = x }
  let var x = snd x
  let add t1 t2 = { lin = Vec.add t1.lin t2.lin; cst = Rat.add t1.cst t2.cst }
  let sub t1 t2 = { lin = Vec.sub t1.lin t2.lin; cst = Rat.sub t1.cst t2.cst }
  let opp t = { lin = Vec.neg t.lin; cst = Rat.neg t.cst }
  let mul c t = { lin = Vec.mulc c t.lin; cst = Rat.mul c t.cst }
  let is_cte t =
    if Vec.equal t.lin Vec.nil then
      Some t.cst
    else
      None

  let print t =
    Printf.printf "AffTerm: %s + %s\n%!" (Vec.to_string Var.to_string t.lin) (Rat.to_string t.cst)

end

module Input = struct

  let path = [ "VplTactic" ; "Input" ]
  let pathN = [ "VplTactic" ; "Input"; "Notation" ]
  let pathNum = [ "Vpl" ; "NumC" ]
  (* let _pedraSem_correct = init_constant path "pedraSem_correct" *)
  let _Empty_vm = init_constant path "Empty_vm"
  let _Node_vm = init_constant path "Node_vm"
  let _Var = init_constant path "Var"
  let _Cte = init_constant path "Cte"
  let _Opp = init_constant path "Opp"
  let _Add = init_constant path "Add"
  let _Sub = init_constant path "Sub"
  let _Mul = init_constant path "Mul"
  let _rcstr = init_constant path "rcstr"
  let _term = init_constant path "term"
  let tag_cte =  init_constant pathN "cte"
  let _Z2Qc =  init_constant pathN "Z2Qc"
  let _LeT = init_constant pathNum "LeT"
  let _EqT = init_constant pathNum "EqT"
  let _LtT = init_constant pathNum "LtT"
  let _vplGoal = init_constant path "vplGoal"
  let _sem = init_constant path "sem"
  let _varmap_find = init_constant path "varmap_find"
    
    
  type varmap = EConstr.constr
  type term = EConstr.constr

  let vplGoal l m g = lapp _vplGoal [| lapp _sem [| l; lapp _varmap_find [| m |] |]; g |]
  (* let pedraSem_correct l m g = lapp _pedraSem_correct [| l; m; g |] *)
    
  let cte x = lapp _Cte [| x |]
  let var x = fst x
  let add t1 t2 = lapp _Add [| t1; t2 |]
  let sub t1 t2 = lapp _Sub [| t1; t2 |]
  let opp t = lapp _Opp [| t |]
  let mul t1 t2 = lapp _Mul [| t1; t2 |]
  let export t = t
    
  let reify_as_cmpT sigma t = 
    if EConstr.eq_constr sigma t (Lazy.force _LeT) then
      Cstr_type.Le
    else if EConstr.eq_constr sigma t (Lazy.force _EqT) then
      Cstr_type.Eq
    else if EConstr.eq_constr sigma t (Lazy.force _LtT) then
      Cstr_type.Lt
    else
      assert false

end

(* inspired from the module of the same name in plugins/quote/quote.ml *)
module ConstrHashed = struct
  type t = Constr.t
  let equal = Constr.equal
  let hash = Constr.hash
end
module ConstrHashtbl = Hashtbl.Make (ConstrHashed)

module Varmap = struct

  type key = { vid: int;
               vaff: AffTerm.var;
               mutable value: EConstr.constr }

  type state = key list
    
  type t = { map: key ConstrHashtbl.t;
             mutable undo_stack: state;
             mutable nxt: key }

  let to_path: int -> AffTerm.var =
    let rec to_path p acc =
      if p=1 then
        acc
      else
        let x, rx = acc in
        if p land 1 = 1 then (
        to_path (p lsr 1) (Positive.xI x, Var.XI rx)
      ) else (
        to_path (p lsr 1) (Positive.xO x, Var.XO rx)
      ) in
    fun p ->
      let x, rx = to_path p (Lazy.force Positive.xH, Var.XH)
      in (lapp Input._Var [| x |], { AffTerm.lin = Vec.mk [(Rat.u, rx)];  AffTerm.cst = Rat.z })

    
  let add (env : t) (t : EConstr.constr) =
    let raw_t = (EConstr.Unsafe.to_constr t) in
    try (ConstrHashtbl.find env.map raw_t).vaff 
    with
    | Not_found -> (
      let n = env.nxt in
       n.value <- t;
       ConstrHashtbl.add env.map raw_t n;
       env.undo_stack <- env.nxt::env.undo_stack;
       let p = n.vid+1 in
       env.nxt <- { vid = p; vaff = to_path (p+1); value = t };
       n.vaff)

  let get_state env =
    (* Printf.printf "save: %d\n" (fst env.nxt); *)
    env.undo_stack;;

  let rec restore env l =
    (* Printf.printf "restore: %d\n" (fst env.nxt); *)
    if env.undo_stack != l then
      match env.undo_stack with
      | nxt::stack -> (
        ConstrHashtbl.remove env.map (EConstr.Unsafe.to_constr nxt.value);
        env.undo_stack <- stack;
        env.nxt <- nxt;
        restore env l)
      | _ -> assert false

  let empty () =
    let xH = Lazy.force Positive.xH in
    { map = ConstrHashtbl.create 17;
      undo_stack = [];
      nxt = { vid = 0; vaff = (lapp Input._Var [|xH|], { AffTerm.lin = Vec.mk [(Rat.u,Var.XH)]; AffTerm.cst = Rat.z }); value = xH }
    }

  let to_varmap env =
    let n = env.nxt.vid in
    let a = Array.make n (Lazy.force Positive.xH) in
    let empty_vm = Lazy.force Input._Empty_vm in
    let node_vm = Lazy.force Input._Node_vm in
    let rec build p =
      if p > n then
        empty_vm
      else (
        let p0 = p lsl 1 in
        EConstr.mkApp (node_vm, [| a.(p-1); build p0; build (p0 lor 1) |])
      )
    in
      ConstrHashtbl.iter (fun _ k -> a.(k.vid) <- k.value) env.map;
      build 1
    
        
end 

(** Lists from the standard library *)
module List = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let _nil = init_constant path "nil"
  let _cons = init_constant path "cons"

  let cons ty h t =
    lapp _cons [|  ty; h ; t |]

  let nil ty =
    lapp _nil [|  ty |]

  let map sigma ty f l =
    let cons = Lazy.force _cons in
    let rec map_acc l acc =
      match decomp_term sigma l with
      | Constr.App(head, args) when EConstr.eq_constr sigma head cons ->
         map_acc args.(2) (EConstr.mkApp (cons, [| ty; f args.(1); acc|]))
      | _ ->
         acc
    in map_acc l (nil ty)

  let rec of_list ty = function
    | [] -> nil ty
    | t::q -> cons ty t (of_list ty q)

end
  
(** Prod from the standard library *)
module Prod = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let _pair = init_constant path "pair"
  let typ = init_constant path "prod"
    
  let set_fst sigma ty f p =
    let pair = Lazy.force _pair in
    match decomp_term sigma p with
    | Constr.App(head, args) when EConstr.eq_constr sigma head pair ->
      EConstr.mkApp (pair, [| ty; args.(1); (f args.(2) args.(3)); args.(3) |])
    | _ -> raise_unknown_constructor "Prod"
end

module Option =
struct
  let path = [ "Coq" ; "Init"; "Datatypes" ]
  let _None = init_constant path "None"
  let _Some = init_constant path "Some"
  let typ = init_constant path "option"
  
end 
  
module Reduction =
struct

  let path = [ "VplTactic" ; "Reduction" ]
  let _pvart = init_constant ["Vpl";"ProgVar";"PVar"] "t"
  let _fexp = init_constant path "fexp"
  let _Top = init_constant path "Top"
  let _Var = init_constant path "Var"
  let _Add = init_constant path "Add"
  let _Mul = init_constant path "Mul"
  let _Merge = init_constant path "Merge"
  let _Return = init_constant path "Return"
  let _Contrad = init_constant path "Contrad"
  let _Bind = init_constant path "Bind"
  let _BindHyp = init_constant path "BindHyp"
  let _SkipHyp = init_constant path "SkipHyp"
  let _Run = init_constant path "Run"
  let _reduceRun = init_constant path "reduceRun"

  let from_Var_option x =
    match x with
    | None -> lapp Option._None [| Lazy.force _pvart |]
    | Some p -> lapp Option._Some [| Lazy.force _pvart; Positive.from_Var p |]
    
  type fexp = EConstr.constr
  type v = EConstr.constr
  type list_fexp =EConstr.constr * EConstr.constr * EConstr.constr * EConstr.constr
  type pedra = EConstr.constr
  type script = EConstr.constr
  type proof = EConstr.constr
  let mkv x = EConstr.mkRel x
  let top v = lapp _Top [| v |]
  let var v x = lapp _Var [| v; x|]
  let add v x y = lapp _Add [| v; x; y|]
  let mul v n c = lapp _Mul [| v; Qc.from_Rat n; c|]
  let merge v x y = lapp _Merge [| v; x; y|]
  let nil ty =
    let ty1 = lapp Option.typ [| Lazy.force _pvart |] in
    let ty2 = lapp _fexp [| ty |] in
    let ty = lapp Prod.typ [| ty1; ty2 |] in
    (ty, ty1, ty2, List.nil ty)
  let cons o x (ty, ty1, ty2, l) = (ty, ty1, ty2, List.cons ty (lapp Prod._pair [|ty1; ty2; from_Var_option o; x|]) l)
  let return v (_,_,_, l) = lapp _Return [| v; l |]
  let contrad v x = lapp _Contrad [| v; x |]
  let run v p = lapp _Run [| v; p |] 
  let bind v c p = lapp _Bind [| v; c; mkLambda v p |]
  let bindHyp v s = lapp _BindHyp [| v; mkLambda v s |]
  let skipHyp v s = lapp _SkipHyp [| v; s |]
  let export vtype s = mkLambda vtype s
  let reduceRun l p = lapp _reduceRun [| l; p |]

end

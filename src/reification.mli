(* Simple Library for reification/generation of Coq ASTs.

   File initially inspired from 
     https://github.com/braibant/coq-tutorial-ml-tactics
   by thomas.braibant@gmail.com

*)
open Vpl
module Rat = Scalar.Rat
module Vec = Vector.Rat.Positive
module Var = Var.Positive
exception RatReifyError
  
exception DecompositionError of string
(** Getting Coq terms from the environment  *)

(** [init_constant path cst] returns the constr corresponding to
    [path.cst]. *)
val init_constant : string list -> string -> Term.constr Lazy.t

(** General purpose functions *)

(** [decomp_term c] returns a user-view of a term (as defined in the
    module kernel/term.mli). *)
val decomp_term : Term.constr -> (Term.constr , Term.types) Term.kind_of_term

(** [lapp c args] build the application of the lazy constr [c] to the
    array of arguments [args]. This is a handy shortcut. *)
val lapp : Term.constr lazy_t -> Term.constr array -> Term.constr

val print_debug: Term.constr -> unit

val mkLambda: Term.types -> Term.constr -> Term.constr

(** Reified affine term 
This has almost nothing todo with Coq AST, 
except for the type "var", itself related to varmap below !
*)  
module AffTerm:
sig

  type t = { lin: Vec.t; cst: Rat.t }
  type var
    
  val cte: Rat.t -> t
  val var: var -> t
  val add: t -> t -> t
  val sub: t -> t -> t
  val opp: t -> t
  val mul: Rat.t -> t -> t
  val is_cte: t -> Rat.t option

  val print: t -> unit  
end

(** Input of Vpl Library *)
module Input:
sig
  val _rcstr: Term.constr lazy_t
  val _term: Term.constr lazy_t
  val tag_cte: Term.constr lazy_t
  val _Z2Qc: Term.constr lazy_t
    
  type varmap
  type term

  val cte: Term.constr -> term
  val var: AffTerm.var -> term
  val add: term -> term -> term
  val sub: term -> term -> term
  val opp: term -> term
  val mul: term -> term -> term
  val export: term -> Term.constr

  (* [vplGoal l m g] is a short cut for Coq [vplGoal (sem l m) g] *) 
  val vplGoal: Term.constr -> varmap -> Term.constr -> Term.constr
  val reify_as_cmpT: Term.constr -> Cstr.cmpT
end
  
(** Reduction of Vpl Library *)
module Reduction:
sig
  type fexp
  type v
  type list_fexp
  type pedra
  type script
  type proof
  val mkv: int -> v
  val var: v -> v -> fexp
  val top: v -> fexp
  val add: v -> fexp -> fexp -> fexp
  val mul: v -> Rat.t -> fexp -> fexp
  val merge: v -> fexp -> fexp -> fexp
  val nil: v -> list_fexp
  val cons: Var.t option -> fexp -> list_fexp -> list_fexp
  val return: v -> list_fexp -> pedra
  val contrad: v -> fexp -> pedra
  val bind: v -> fexp -> pedra -> pedra
  val bindHyp: v -> script -> script
  val skipHyp: v -> script -> script
  val run: v -> pedra -> script
  val export: Term.types -> script -> proof
  val reduceRun: Term.constr -> proof -> Term.constr
end


(** Getting Coq terms from the environment  *)
module Varmap:
sig
  (** This module defines a very simple environment for Coq terms. It
      associate an index (as a Coq positive) to terms. If a term is added twice,
      then the same index is returned. *)
  
  
  type t (** abstract type of the environment  *)

    
  (** [add env c] add a new term to the environment. 

      - If the term [c] is not bound in [env] then we associate a fresh
      index to it (for varmap below), and this pair to [env].

      - If the term [c] is already present in [env], we return its
      index.  
  *)
  val add : t -> Term.constr -> AffTerm.var
    
  (** [empty ()] return an empty environment *)
  val empty : unit -> t

  (** [to_varmap env] builds a varmap of terms that were stored in
      the environment. This allows to access them by their position in
      the varmap. *)
  val to_varmap : t -> Input.varmap

  (** useful to backtrack *)
  type state
    
  val get_state: t -> state  

  val restore: t -> state -> unit  
end
 
 
(** Bindings with Coq' Standard Library  *)
 
(** Coq lists *)
module List:
sig
  (** [of_list ty l]  *)
  val of_list:Term.constr -> Term.constr list -> Term.constr

  (* [map ty f l]: but reverse of the order !*)
  val map: Term.constr -> (Term.constr -> Term.constr) -> Term.constr -> Term.constr
end

(** Coq pairs *)
module Prod:
sig
  (* [set_fst ty f l]: change fst component of the pair *)
  val set_fst: Term.constr -> (Term.constr -> Term.constr -> Term.constr) -> Term.constr -> Term.constr
end

(** Coq Positive *)
module Positive:
sig
  (* raise [RatReifyError] in case of non-closed term *)
  val reify_as_RatZ: Term.constr -> Rat.Z.t
  val from_RatZ: Rat.Z.t -> Term.constr
end

(* Coq Z *) 
module Z:
sig
  (* raise [RatReifyError] in case of non-closed term *)
  val reify_as_RatZ: Term.constr -> Rat.Z.t
  val from_RatZ: Rat.Z.t -> Term.constr
end 
  
(* Coq Qc *) 
module Qc:
sig  
  val _Qcopp: Term.constr lazy_t
  val _Qcplus: Term.constr lazy_t
  val _Qcminus: Term.constr lazy_t
  val _Qcmult: Term.constr lazy_t
  val _Q2Qc: Term.constr lazy_t
  val _Qcmake: Term.constr lazy_t
  val _Qmake: Term.constr lazy_t


  (* raise [RatReifyError] in case of non-closed term *)
  val reify_as_Rat: Term.constr -> Rat.t
  val from_Rat: Rat.t -> Term.constr
end

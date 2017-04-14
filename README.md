# VplTactic (A Coq Tactic from Verified Polyhedra Library)

Current version: 0.2

## Introduction

The [VPL](https://github.com/VERIMAG-Polyhedra/VPL) is an Ocaml
library allowing to compute with convex polyhedra.  It provides
standard operators -- certified in Coq -- to use this library as an
abstract domain of polyhedra.

The VplTactic is a tactic to solve arithmetic goals in Coq.  It is
implemented through a Coq plugin that invokes the guard operator of
the VPL.  The main feature of our tactic with respect to similar
tactics (`lra`, `fourier`, `omega`, `lia`) is that our tactic never
fails. Indeed, when it can not prove the goal, it tries to simplify
the goal and in particular to replace inequalities by equalities. See
examples below. Currently, this tactic is highly experimental and it only works on
[`Qc`](https://coq.inria.fr/library/Coq.QArith.Qcanon.html)
which is a canonical type of rationals.

If you find a bug or have any comment, please
[contact us](mailto:verimag-polyhedra-developers@univ-grenoble-alpes.fr)

Main Contributors: Alexandre Maréchal and Sylvain Boulmé.
Developed at [Verimag](http://www-verimag.imag.fr/)
and supported by [ANR Verasco](http://verasco.imag.fr/)
and [ERC Stator](http://stator.imag.fr/).

## Using VplTactic

First, add the two following lines at the head of your Coq files:

    Require Import VplTactic.Tactic.
    Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Module `VplTactic.Tactic` actually provides several variants of our tactic.
The most complex is `vpl_auto`.

    Lemma ex_intro (x: Qc) (f: Qc -> Qc):
      x <= 1
      -> (f x) < (f 1)
      -> x < 1.
    Proof.
      vpl_auto.
    Qed.

Actually, `vpl_auto` is a macro for `vpl_reduce; vpl_post` where `vpl_reduce`
is the main call to the VPL oracle. It try to find a polyhedron in
your goal and then, it simplifies this polyhedron.

For example, consider the following goal:

    Goal forall (v1 v2 v3: Qc) (f: Qc -> Qc),
       f ((v2 - 1)*v3) <> f ((2#3) * v1 * v2)
       -> v1+3 <= (v2 + v3)
       -> v1 <= 3*(v3-v2-1)
       -> 2*v1 < 3*(v3-2).

The `vpl_reduce` tactic simplifies this goal into

    H : f ((v2 - (1 # 1)) * v3) = f ((2 # 3) * v1 * v2) -> False
    ============================
    v1 = (-3 # 1) + (3 # 2) * v3
    -> v2 = (1 # 2) * v3
    -> False

Hence, the linear inequalities of the initial goal have been replaced
by linear equalities.  Then, `vpl_post` proves the remaining goal by
combininig `auto` and `field` tactics.

The `vpl` tactic is a slight variant of `vpl_reduce` which rewrites
the discovered equalities in the remaining goal: it is a macro for
`vpl_reduce; vpl_rewrite`.

If needed, you may also directly invoke some subcomponent of
`vpl_reduce`, see file `theories/Tactic.v`.  You may also find
examples in file `test-suite/*.v`.

A [HAL preprint](https://hal.archives-ouvertes.fr/hal-01505598) presents this tactic in details.


## Installation through [opam](https://opam.ocaml.org/)

1. Dependencies

   * See [External Dependencies](https://github.com/VERIMAG-Polyhedra/VPL/blob/master/README.md#installation)
   of [VPL](https://github.com/VERIMAG-Polyhedra/VPL)

   * [coq](https://coq.inria.fr/)
        __required version 8.6__
       (available in OPAM)

2. Installation

   First, add the following repository in your opam system:

          opam repo add vpl http://www-verimag.imag.fr/~boulme/opam-vpl

   Then, install the following package:

          opam install coq-vpltactic

  This will also install other `opam-vpl` packages.

In case of trouble with this `opam` install, you should read
[this](https://github.com/VERIMAG-Polyhedra/opam-vpl/blob/master/README.md#using-the-vpl-on-a-vagrantvirtualbox-virtual-machine).

## Browsing the sources

Following usual conventions in Coq projects, directories are organized as follows:

* `src/` contains `ocaml` code for the plugin (reification + oracle wrapper).

* `theories/` contains the `coq` code of `VplTactic`

   - `Input.v` finds a polyhedron from the goal

   - `Output.v` exports back the reduced polyhedron into the goal

   - `Reduction.v` transforms the input goal into the output goal (thanks to a "script" provided by the VPL oracle)

   - `Tactic.v` is the main file

* `test-suite/` contains examples.

Currently, the code is not really documented (sorry!). It only includes a few comments inside.


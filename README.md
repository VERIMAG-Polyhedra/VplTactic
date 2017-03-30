# VplTactic (A Coq Tactic from Verified Polyhedra Library)

Current version: 0.2

## Introduction

The [VPL](https://github.com/VERIMAG-Polyhedra) is an Ocaml library allowing to compute with convex polyhedra. 
It provides standard operators -- certified in Coq -- to use this library as an abstract domain of polyhedra.

The VplTactic is a tactic to solve arithmetic goals in Coq.
It provides a Coq plugin that invokes some VPL operator.

If you find a bug or have any comment, feel free to contact us at verimag-polyhedra-developers@univ-grenoble-alpes.fr

Main Contributors: Alexandre Maréchal and Sylvain Boulmé.
Developed at Verimag and supported by ANR Verasco and ERC Stator.


## Installation through [opam](https://opam.ocaml.org/) 

1. External Dependencies for [VPL](https://github.com/VERIMAG-Polyhedra)
	
   * [glpk](https://www.gnu.org/software/glpk/)
	  __required version >= 4.61__
		
   * [eigen](http://eigen.tuxfamily.org/)
         (automatically installed by depexts on debian or ubuntu)
	  _debian package libeigen3-dev_
	  __tested with version 3.3.3__
		
2. Installation
	
   First, add the following repository in your opam system:

          opam repo add vpl http://www-verimag.imag.fr/~boulme/opam-vpl

   Then, install the following package:
        
          opam install coq-vpltactic

  This will also install other `opam-vpl` packages.

## Using VplTactic.

TODO

## Browsing the sources.

TODO

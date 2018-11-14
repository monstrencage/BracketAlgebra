# BracketAlgebra #

*Nominal sets, automata and bracket algebra*

This repository contains :chicken:[Coq](https://coq.inria.fr):chicken: libraries dealing with nominal sets and regular expressions. It is focused towards **Bracket Algebra**, a style of nominal Kleene algebra well suited for modelling imperative programs.

## Download ##

To obtain this library, simply run the command:
``` shell
	git clone  --recurse-submodules git@github.com:monstrencage/BracketAlgebra.git
```
Notice the `--recurse-submodules`, which is necessary to get the submodule [`relation-algebra`](https://github.com/damien-pous/relation-algebra), due to Damien Pous.

## Compiling ##

This library was compiled using:

  * [Coq](https://coq.inria.fr) version 8.8
  * [OCaml](http://ocaml.org/) version 4.05.0
  
To compile it, one needs to first compile `relation-algebra`, then the main library. To compile everything and produce the html documentation, run the following command from the main folder:

``` shell
	cd relation-algebra && make && cd .. && make gallinahtml
```


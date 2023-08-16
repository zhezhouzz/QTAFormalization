# Proof Readme: QTAFormalization #

## Proof File Structures

The files are structured as follows:
+ Definitions and proofs of our core language **λ<sup>E</sup>**.
  - `Atom.v`: Definitions and notations of atoms (variables) in **λ<sup>E</sup>**.
  - `Tactics.v`: Some auxiliary tactics.
  - `CoreLang.v`: Definitions and notations of terms in **λ<sup>E</sup>**.
  - `NamelessTactics.v`: Auxiliary tactics for the locally nameless representation.
  - `CoreLangProp.v`: Lemmas for our core language **λ<sup>E</sup>**.
  - `OperationalSemantics.v`: Definitions and notations of the small-step operational semantics of **λ<sup>E</sup>**.
  - `BasicTyping.v`: Definitions and notations for the basic typing.
  - `BasicTypingProp.v`: Lemmas for the basic typing rules.
  - `Qualifier.v`: Definitions and notations for qualifiers.
  - `ListCtx.v`: Definitions and notations for reasoning about type context.
  - `RefinementType.v`: Definitions and notations of Hoare Automata Types.
  - `Denotation.v`: Definitions and notations of the automaton and type denotation.
  - `Instantiation.v`: Lemmas for the substitution under type context.
  - `Typing.v`: Definitions and notations used in the typing rules; as well as statement and proof of the fundamental and soundness theorem.

## Compilation and Dependencies

Our formalization is tested against `Coq 8.16.1`, and requires the libraries
`coq-stdpp 1.8.0` and `coq-hammer-tactics 1.3.2+8.16`. The easiest way to install the
dependencies is via [OPAM](https://opam.ocaml.org/doc/Install.html). For
example:

```sh
# If you have not already used opam
opam init
opam update
# Create a new opam environment for testing this project
opam switch create HAT --package=ocaml-variants.4.14.1+options,ocaml-option-flambda
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam pin coq 8.16.1
opam pin coq-stdpp 1.8.0
opam pin coq-hammer-tactics 1.3.2+8.16
```

To build and check the Coq formalization, simply run `make` in the
`formalization` directory. The command `Print Assumptions soundness` at the end
of file `Typing.v` should print out `Axioms: builtin_typing_relation : ...`. It
means our proofs do not rely on any axioms except for the definition
`builtin_typing_relation` (i.e. `Δ` in the paper), which we deliberately leave
undefined, as the type system is parameterized over this relation.

Our formalization takes inspiration and ideas from the following work, though does not directly depend on them:
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/): a lot of our formalization is inspired by the style used in Software Foundations.
- [The Locally Nameless Representation](https://chargueraud.org/research/2009/ln/main.pdf): we use the locally nameless representation for variable bindings.

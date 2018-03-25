# Specifying the unboxability check on mutually recursive datatypes in OCaml

Simon Colin  
Research project (M1, 3ECTS) supervised by [Gabriel Scherer](http://gasche.info/) (Parsifal, INRIA Saclay)  
November 2017 to March 2018

## Problem

OCaml recently the ability to "unbox" single-construct datatypes and single-field records

```ocaml
type name = Name of string [@@unboxed]
type 'a cont = { run : 'b. ('a -> 'b) -> 'b } [@@unboxed]
```

However, due to the runtime optimization of float arrays, it would be
unsound to introduced in OCaml an (unboxed) datatype with both float
values and non-float values as elements. This restricts the way some
GADTs can be unboxed:

```ocaml
type any_cont = K : 'a cont -> any_cont [@@unboxed];; (* correct *)

type any = Any : 'a -> any [@@unboxed];; (* incorrect *)
Error: This type cannot be unboxed because
       it might contain both float and non-float values.
       You should annotate it with [@@ocaml.boxed].
```

The implementation of this soundness check in the compiler is
currently fairly incomplete, it handles recursive types in an
unsatisfying way and in particular restricts mutually-recursive
declarations more than necessary. See
[MPR#7364](https://caml.inria.fr/mantis/view.php?id=7364),
"Inflexibility of unboxed types in recursive declarations".



## This project

This project developed:

- a system of inference rules to express/specify the correctness of
  a set of (possibly mutually-recursive) type declarations

- a fixpoint procedure on these rules to check actual declarations

- an OCaml prototype of the rules and the fixpoint algorithm (but no
  patch to the compiler yet)

See [the report](tex/report.pdf) and [the
presentation](tex/presentation.pdf) that describe the work, and the
current prototype code in [check.ml](./check.ml).

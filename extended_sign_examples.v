
From pv Require Import library.

From pv Require Import abstract_interpreter.
Require Import String ZArith List.
Open Scope Z_scope.

Module B := AbstractInterpreter ExtendedSign.
Import ExtendedSign.
Import B.
Definition example3_expr :=
    while_do (bop ne (var "x") (const 0)) (assign "x" (aop add (var "x") (const 1))).

Definition example3_state := [("x", lt0)].

Definition example4_state := [("x", eq0)].

Definition example5_state := [("x", gt0)].

Compute (AI example3_expr example3_state).

Compute (AI example3_expr example4_state).

Compute (AI example3_expr example5_state).
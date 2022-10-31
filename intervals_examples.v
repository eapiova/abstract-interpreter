From pv Require Import library.

From pv Require Import abstract_interpreter.
Require Import String ZArith List.
Open Scope Z_scope.

Module C := AbstractInterpreter Intervals.

Import Intervals.
Import C.

Definition example6_expr :=
    while_do (bop ge (var "x") (const 0)) (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1)))).

Definition example6_state := [("x", between 10 10); ("y", between 0 0)].

Compute (AI example6_expr example6_state).

Compute let b := (bop ge (var "x") (const 0)) in let S := (AI (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1))))) in let s' := (step2 S b example6_state example6_state 20) in widening S b s' s' 20.

Compute let b := (bop ge (var "x") (const 0)) in let S := (AI (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1))))) in let s' := (step2 S b example6_state example6_state 20) in find_inv S b example6_state 20 20.

Compute let b := (bop ge (var "x") (const 0)) in let S := (AI (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1))))) in let s' := (step2 S b example6_state example6_state 20) in is_inv S example6_state s' b.


Compute (B_sharp (bop lt (var "x") (const 0)) [("y", right_of 0); ("x", between (-1) 10)]).



Definition example7_expr :=
    while_do (bop lt (var "x") (const 10)) (assign "x" (aop add (var "x") (const 1))).

Definition example7_state := [("x", between 0 0)].

Compute (AI example7_expr example7_state).


Definition example8_expr :=
    while_do (bop le (var "x") (const 100)) (assign "x" (aop add (var "x") (const 1))).

Definition example8_state := [("x", between 1 1)].

Compute (AI example8_expr example8_state).

Compute (is_inv (AI (assign "x" (aop add (var "x") (const 1)))) example8_state [("x", between 1 101)] (bop le (var "x") (const 100))).

Compute step1 (AI (assign "x" (aop add (var "x") (const 1)))) (bop le (var "x") (const 100)) example8_state [("x", between 1 101)].

Compute s_stable [("x", between 1 101)] [("x", between 1 101)].


Definition example9_expr :=
    sequence (assign "x" (const 0)) (while_do (bop lt (var "x") (const 40)) (assign "x" (aop add (var "x") (const 1)))).

Compute (AI example9_expr nil).

Compute (is_inv (AI (assign "x" (aop add (var "x") (const 1)))) example8_state [("x", between 1 101)] (bop le (var "x") (const 100))).

Compute step1 (AI (assign "x" (aop add (var "x") (const 1)))) (bop le (var "x") (const 100)) example8_state [("x", between 1 101)].

Compute s_stable [("x", between 1 101)] [("x", between 1 101)].
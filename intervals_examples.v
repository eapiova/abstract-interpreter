From pv Require Import library.

Require Import String ZArith List.
Open Scope Z_scope.

From pv Require Import abstract_interpreter.


(**

Compute let b := (bop ge (var "x") (const 0)) in let S := (AI (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1))))) in let s' := (step2 S b example6_state example6_state 20) in widening S b s' s' 20.

Compute let b := (bop ge (var "x") (const 0)) in let S := (AI (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1))))) in let s' := (step2 S b example6_state example6_state 20) in find_inv S b example6_state 20 20.

Compute let b := (bop ge (var "x") (const 0)) in let S := (AI (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1))))) in let s' := (step2 S b example6_state example6_state 20) in is_inv S example6_state s' b.


Compute (B_sharp (bop lt (var "x") (const 0)) [("y", right_of 0); ("x", between (-1) 10)]).

*)



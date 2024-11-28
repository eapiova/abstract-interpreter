From pv Require Import library.
Require Import String ZArith List Unicode.Utf8.
Open Scope Z_scope.

From ReductionEffect Require Import PrintingEffect.

Require Coq.extraction.Extraction.
Extraction Language OCaml.


Fixpoint string_list_update {A} l x (a : A) :=
    match l with 
    | nil => (x, a) :: nil
    | (y, a') :: tl => if string_dec x y then (y, a) :: tl else (y, a') :: string_list_update tl x a
    end.



(* Language *)

Inductive ABinOp :=
    | add
    | sub
    | mul
    | div.

Inductive Aexp : Type :=
    | var : string -> Aexp
    | const : Z -> Aexp
    | opp : Aexp -> Aexp
    | aop : ABinOp -> Aexp -> Aexp -> Aexp.

Inductive BBinOp :=
    | eq
    | lt
    | gt
    | le
    | ge
    | ne.

Inductive Bexp : Type :=
    | tt : Bexp
    | ff : Bexp
    | bop : BBinOp -> Aexp -> Aexp -> Bexp
    | and : Bexp -> Bexp -> Bexp
    | or : Bexp -> Bexp -> Bexp.

Inductive While : Type :=
    | assign : string -> Aexp -> While
    | skip : While
    | sequence : While -> While -> While
    | if_then_else : Bexp -> While -> While -> While
    | while_do : Bexp -> While -> While.

Notation "a1 + a2" := (aop add a1 a2).
Notation "a1 ≠ a2" := (bop ne a1 a2).





(* Abstract Domain structure *)

Module Type AbstractDomain.

Parameter AbD : Type.
Parameter AbS : Type.
Parameter top_AbS : AbS.
Parameter bot_AbS : AbS.

Parameter ab_update : AbS -> string -> AbD -> AbS.
Parameter ab_lookup : AbS -> string -> AbD.
Parameter alpha_singleton : Z -> AbD.
Parameter ab_opp : AbD -> AbD.
Parameter ab_op : ABinOp -> AbD -> AbD -> AbD.
Parameter A_sharp : Aexp -> AbS -> AbD.

Parameter eq_sem : Aexp -> Aexp -> AbS -> AbS.
Parameter ne_sem : Aexp -> Aexp -> AbS -> AbS.
Parameter lt_sem : Aexp -> Aexp -> AbS -> AbS.
Parameter gt_sem : Aexp -> Aexp -> AbS -> AbS.
Parameter le_sem : Aexp -> Aexp -> AbS -> AbS.
Parameter ge_sem : Aexp -> Aexp -> AbS -> AbS.

Parameter join : AbD -> AbD -> AbD.
Parameter join_state : AbS -> AbS -> AbS.
Parameter ab_le : AbD -> AbD -> bool.
Parameter ab_le_state : AbS -> AbS -> bool.
Parameter widen : AbD -> AbD -> AbD.
Parameter widen_state : AbS -> AbS -> AbS.
Parameter narrow : AbD -> AbD -> AbD.
Parameter narrow_state : AbS -> AbS -> AbS.

End AbstractDomain.





(* Abstract Interpreter function *)

Module AbstractInterpreter (AbDom : AbstractDomain).
Import AbDom.

Fixpoint B_sharp b s_sharp :=
    match b with
    | tt => s_sharp
    | ff => bot_AbS
    | bop op e1 e2 => match op with 
                        | eq => eq_sem e1 e2 s_sharp
                        | lt => lt_sem e1 e2 s_sharp
                        | gt => gt_sem e1 e2 s_sharp
                        | le => le_sem e1 e2 s_sharp
                        | ge => ge_sem e1 e2 s_sharp
                        | ne => ne_sem e1 e2 s_sharp
                        end
    | and b1 b2 => B_sharp b2 (B_sharp b1 s_sharp)
    | or b1 b2 => join_state (B_sharp b1 s_sharp) (B_sharp b2 s_sharp)
    end. 

Fixpoint neg_sem b :=
    match b with
    | tt => ff
    | ff => tt
    | bop eq e1 e2 => bop ne e1 e2
    | bop lt e1 e2 => bop ge e1 e2
    | bop gt e1 e2 => bop le e1 e2
    | bop le e1 e2 => bop gt e1 e2
    | bop ge e1 e2 => bop lt e1 e2
    | bop ne e1 e2 => bop eq e1 e2
    | and b1 b2 => or (neg_sem b1) (neg_sem b2)
    | or b1 b2 => and (neg_sem b1) (neg_sem b2)
    end.

Definition step (AI_state : AbS -> AbS * list AbS) b s_sharp t_sharp :=
    let (v_sharp, invs) := (AI_state (B_sharp b t_sharp)) in (join_state s_sharp v_sharp, invs).

Definition is_inv AI_state s_sharp t_sharp b := let (u_sharp, _) := step AI_state b s_sharp t_sharp in ab_le_state t_sharp u_sharp.

Unset Guard Checking.

Fixpoint steps AI_state (b : Bexp) s_sharp t_sharp {struct b} :=
    if is_inv AI_state s_sharp t_sharp b
        then (t_sharp, [t_sharp])
    else 
        let (u_sharp, invs1) := print_id (step AI_state b s_sharp t_sharp) in let (v_sharp, invs2) := steps AI_state b s_sharp u_sharp in (v_sharp, invs1 ++ invs2).   
    

Fixpoint widening AI_state b s_sharp t_sharp {struct b} :=
    if is_inv AI_state s_sharp t_sharp b
        then t_sharp
    else 
        let (u_sharp, _) := print_id (step AI_state b s_sharp t_sharp) in widening AI_state b s_sharp (widen_state t_sharp u_sharp).

Fixpoint narrowing AI_state b s_sharp t_sharp {struct b} :=
    let (u_sharp, _) := print_id (step AI_state b s_sharp t_sharp) in let v_sharp := narrow_state t_sharp u_sharp in
    if is_inv AI_state s_sharp v_sharp b
        then (v_sharp, [v_sharp])
    else 
        let (w_sharp, invs1) := print_id (step AI_state b s_sharp v_sharp) in let (z_sharp, invs2) := narrowing AI_state b s_sharp (narrow_state v_sharp w_sharp) in (z_sharp, invs1 ++ invs2).

Set Guard Checking.

Definition ab_lfp AI_state b s_sharp (widen_toggle : bool) :=
    if widen_toggle then let t_sharp := widening AI_state b s_sharp s_sharp in narrowing AI_state b s_sharp t_sharp
    else steps AI_state b s_sharp s_sharp.

Fixpoint AI (P : While) widen_toggle s_sharp :=
    match P with
    | assign x e => ((ab_update s_sharp x (A_sharp e s_sharp)), nil)
    | skip => (s_sharp, nil)
    | sequence S1 S2 => let (t_sharp, invs1) := AI S1 widen_toggle s_sharp in let (u_sharp, invs2) := AI S2 widen_toggle t_sharp in (u_sharp, invs1 ++ invs2)
    | if_then_else b S1 S2 => let (t_sharp, invs1) := AI S1 widen_toggle (B_sharp b s_sharp) in let (u_sharp, invs2) := AI S2 widen_toggle (B_sharp (neg_sem b) s_sharp) in (join_state t_sharp u_sharp, invs1 ++ invs2)
    | while_do b S' => let (t_sharp, invs) := (ab_lfp (AI S' widen_toggle) b s_sharp widen_toggle) in (B_sharp (neg_sem b) t_sharp, invs)
    end.

End AbstractInterpreter.



(* Extended Sign domain *)

Module ExtendedSign <: AbstractDomain.

Inductive extended_sign :=
    | top
    | le0
    | ne0
    | ge0
    | lt0
    | eq0
    | gt0
    | bot.

Notation "⊤" := top.
Notation "≤0" := le0.
Notation "≠0" := ne0.
Notation "≥0" := ge0.
Notation "<0" := lt0.
Notation "=0" := eq0.
Notation ">0" := gt0.
Notation "⊥" := bot.




Definition AbD := extended_sign.

Check AbD.

Definition AbS := option (list (string * AbD)).

Check AbS.

Definition top_AbS : AbS := Some nil.

Check top_AbS.

Definition bot_AbS : AbS := None.

Definition alpha_singleton z :=
    if z =? 0 then =0
    else if z <? 0 then <0
    else >0.

Definition ab_opp v :=
    match v with
    | <0 => >0
    | >0 => <0
    | ≤0 => ≥0
    | ≥0 => ≤0
    | v' => v'
    end.

Notation "- z" := (ab_opp z).

Definition sign_eq_dec : forall (x y : AbD), { x = y } + { x <> y }.
Proof.
    decide equality.
Defined.

Infix "=?" := sign_eq_dec.

Definition add_op v1 v2 :=
    match v1, v2 with
    | ⊥, _ | _, ⊥ => ⊥
    | =0, a3 | a3, =0 => a3
    | <0, ≤0 | ≤0, <0 => <0
    | >0, ≥0 | ≥0, >0 => >0
    | ≠0, ≠0 => ⊤
    | v3, v4 => if v3 =? v4 then v3 else ⊤
    end.

Definition sub_op v1 v2 :=
    match v1, v2 with
    | ⊥, _ => ⊥
    | _, ⊥ => ⊥
    | =0, v3 => -v3
    | v3, =0 => v3
    | <0, >0 | <0, ≥0 | ≤0, >0 => <0
    | >0, <0 | >0, ≤0 | ≥0, <0 => >0
    | ≤0, ≥0 => ≤0
    | ≥0, ≤0 => ≥0
    | _, _ => ⊤
    end.

Definition mul_op v1 v2 :=
    match v1, v2 with
    | ⊥, _ | _, ⊥ => ⊥
    | =0, _ | _, =0 => =0
    | <0, v3 | v3, <0 => -v3
    | >0, v3 | v3, >0 => v3
    | ≤0, ≤0 | ≥0, ≥0 => ≥0
    | ≤0, ≥0 | ≥0, ≤0 => ≤0
    | ≠0, ≠0 => ≠0
    | _, _ => ⊤
    end.

Definition div_op v1 v2 :=
    match v1, v2 with
    | ⊥, _ | _, ⊥ | _, =0 => ⊥
    | =0, _ => =0
    | ≠0, _ | <0, ≠0 | <0, ⊤ | >0, ≠0 | >0, ⊤ => ≠0
    | <0, <0 | <0, ≤0 | >0, >0 | >0, ≥0 => >0
    | <0, >0 | <0, ≥0 | >0, <0 | >0, ≤0 => <0
    | ≤0, <0 | ≤0, ≤0 | ≥0, >0 | ≥0, ≥0 => ≥0
    | ≤0, >0 | ≤0, ≥0 | ≥0, <0 | ≥0, ≤0 => ≤0
    | _, _ => ⊤
    end.

Notation "v1 + v2" := (add_op v1 v2).
Notation "v1 - v2" := (sub_op v1 v2).
Notation "v1 * v2" := (mul_op v1 v2).
Notation "v1 / v2" := (div_op v1 v2).



Definition ab_update m x v : AbS :=
    match m with
    | Some l => Some (string_list_update l x v)
    | None => Some ((x, v) :: nil)
    end.


Fixpoint string_list_lookup l x :=
    match l with
    | nil => ⊤
    | (y, a) :: tl => if string_dec x y then a else string_list_lookup tl x
    end.

Definition ab_lookup s_sharp x :=
    match s_sharp with
    | Some l => string_list_lookup l x
    | None => ⊥
    end.







Definition ab_op op a1 a2 :=
    match op with
    | add => add_op a1 a2
    | sub => sub_op a1 a2
    | mul => mul_op a1 a2
    | div => div_op a1 a2
    end.

Fixpoint A_sharp e s_sharp :=
    match e with
    | var x => ab_lookup s_sharp x
    | const n => alpha_singleton n
    | aop op e1 e2 => ab_op op (A_sharp e1 s_sharp) (A_sharp e2 s_sharp)
    | opp e' => ab_opp (A_sharp e' s_sharp)
    end.

Definition eq_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ 
                | =0, <0 | =0, >0 | <0, =0 | >0, =0 | <0, >0 | >0, <0 
                | <0, ≥0 | ≥0, <0 | =0, ≠0 | ≠0, =0 | >0, ≤0 | ≤0, >0 => bot_AbS
                | ≤0, <0 | ≠0, <0 | ≠0, ≤0 | ≤0, ≠0 => ab_update s_sharp x <0
                | ≤0, =0 | ≥0, =0 | ≥0, ≤0 | ≤0, ≥0 => ab_update s_sharp x =0
                | ≠0, >0 | ≥0, >0 | ≥0, ≠0 | ≠0, ≥0 => ab_update s_sharp x >0
                | ⊤, a => ab_update s_sharp x a
                | _, _ => s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ 
            | =0, <0 | =0, >0 | <0, =0 | >0, =0 | <0, >0 | >0, <0 
            | <0, ≥0 | ≥0, <0 | =0, ≠0 | ≠0, =0 | >0, ≤0 | ≤0, >0 => bot_AbS
            | _, _ => s_sharp
            end
    end.
        
Definition ne_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ | =0, =0 => bot_AbS
                | ≤0, =0 =>  (ab_update s_sharp x <0)
                | ≥0, =0 =>  (ab_update s_sharp x >0)
                | ⊤, =0 =>  (ab_update s_sharp x ≠0)
                | _, _ =>  s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ | =0, =0 => bot_AbS
            | _, _ =>  s_sharp
            end
    end.

Definition lt_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ 
                | =0, <0 | =0, =0 | =0, ≤0
                | >0, <0 | >0, =0 | >0, ≤0
                | ≥0, <0 | ≥0, =0 | ≥0, ≤0 => bot_AbS
                | ≤0, <0 | ≤0, =0 | ≤0, ≤0
                | ≠0, <0 | ≠0, =0 | ≠0, ≤0
                | ⊤, <0 | ⊤, =0 | ⊤, ≤0 =>  (ab_update s_sharp x <0)
                | _, _ =>  s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ 
            | =0, <0 | =0, =0 | =0, ≤0
            | >0, <0 | >0, =0 | >0, ≤0
            | ≥0, <0 | ≥0, =0 | ≥0, ≤0 => bot_AbS
            | _, _ =>  s_sharp
            end
    end.

Definition gt_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ 
                | =0, >0 | =0, =0 | =0, ≥0
                | <0, >0 | <0, =0 | <0, ≥0
                | ≤0, >0 | ≤0, =0 | ≤0, ≥0 => bot_AbS
                | ≥0, >0 | ≥0, =0 | ≥0, ≥0
                | ≠0, >0 | ≠0, =0 | ≠0, ≥0
                | ⊤, >0 | ⊤, =0 | ⊤, ≥0 =>  (ab_update s_sharp x >0)
                | _, _ =>  s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ 
            | =0, >0 | =0, =0 | =0, ≥0
            | <0, >0 | <0, =0 | <0, ≥0
            | ≤0, >0 | ≤0, =0 | ≤0, ≥0 => bot_AbS
            | _, _ =>  s_sharp
            end
    end.

Definition le_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ 
                | =0, <0 
                | >0, <0 | >0, =0 | >0, ≤0
                | ≥0, <0 => bot_AbS
                | ≤0, <0 
                | ≠0, <0 | ≠0, =0 | ≠0, ≤0
                | ⊤, <0 =>  (ab_update s_sharp x <0)
                | ≥0, =0 | ≥0, ≤0 =>  (ab_update s_sharp x =0)
                | ⊤, =0 | ⊤, ≤0 =>  (ab_update s_sharp x ≥0)
                | _, _ =>  s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ 
            | =0, <0
            | >0, <0 | >0, =0 | >0, ≤0
            | ≥0, <0 => bot_AbS
            | _, _ =>  s_sharp
            end
    end.

Definition ge_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ 
                | =0, >0 
                | <0, >0 | <0, =0 | <0, ≥0
                | ≤0, >0 => bot_AbS
                | ≥0, >0 
                | ≠0, >0 | ≠0, =0 | ≠0, ≥0
                | ⊤, >0 =>  (ab_update s_sharp x >0)
                | ≤0, =0 | ≤0, ≥0 =>  (ab_update s_sharp x =0)
                | ⊤, =0 | ⊤, ≥0 =>  (ab_update s_sharp x ≤0)
                | _, _ =>  s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ 
            | =0, >0
            | <0, >0 | <0, =0 | <0, ≥0
            | ≤0, >0 => bot_AbS
            | _, _ =>  s_sharp
            end
    end.

Definition join a1 a2 :=
    match a1, a2 with
    | ⊥,  a3 |  a3,  ⊥ =>  a3
    | =0,  <0 |  <0,  =0 
    | =0,  ≤0 |  ≤0,  =0
    | <0,  ≤0 |  ≤0,  <0 =>  ≤0
    | =0,  >0 |  >0,  =0 
    | =0,  ≥0 |  ≥0,  =0
    | >0,  ≥0 |  ≥0,  >0 =>  ≥0
    | <0,  >0 |  >0,  <0
    | <0,  ≠0 |  ≠0,  <0
    | >0,  ≠0 |  ≠0,  >0 =>  ≠0
    | a3, a4 => if sign_eq_dec a3 a4 then a3 else ⊤
    end.

Fixpoint join_state_helper l t_sharp :=
    match l with 
    | nil => top_AbS 
    | (x, a) :: tl => ab_update (join_state_helper tl t_sharp) x (join a (ab_lookup t_sharp x)) 
    end.

Definition join_state s_sharp t_sharp :=
    match s_sharp with
    | None => t_sharp
    | Some l => join_state_helper l t_sharp
    end.



Definition ab_le a1 a2 := if sign_eq_dec (join a1 a2) a2 then true else false.

Fixpoint ab_le_state_helper l t_sharp :=
    match l with
    | nil => true
    | (x, a) :: tl => ab_le (ab_lookup t_sharp x) a && ab_le_state_helper tl t_sharp
    end.

Definition ab_le_state s_sharp t_sharp :=
    match s_sharp with
    | None => true
    | Some l => ab_le_state_helper l t_sharp
    end.

Definition widen a1 a2 := join a1 a2.

Definition widen_state s_sharp t_sharp :=
    match s_sharp with
    | None => t_sharp
    | Some l => Some (map (fun c : string * AbD => let (x, a) := c in (x, widen a (ab_lookup t_sharp x))) l)
    end.

Definition narrow (a1 a2 : AbD) := 
    match a1, a2 with
    | ⊤,  a3 |  a3,  ⊤ => a3
    | ≠0,  <0 |  <0,  ≠0 
    | ≠0,  ≤0 |  ≤0,  ≠0
    | <0,  ≤0 |  ≤0,  <0 =>  <0
    | ≠0,  >0 |  >0,  ≠0 
    | ≠0,  ≥0 |  ≥0,  ≠0
    | >0,  ≥0 |  ≥0,  >0 =>  >0
    | ≤0,  ≥0 |  ≥0,  ≤0
    | ≤0,  =0 |  =0,  ≤0
    | ≥0,  =0 |  =0,  ≥0 =>  =0
    | a3, a4 => if sign_eq_dec a3 a4 then a3 else ⊥
    end.

Definition narrow_state s_sharp t_sharp :=
    match s_sharp with
    | None => bot_AbS
    | Some l => Some (map (fun c : string * AbD => let (x, a) := c in (x, narrow a (ab_lookup t_sharp x))) l)
    end.

End ExtendedSign.



(* Intervals domain *)

Module Intervals <: AbstractDomain.

Inductive Interval : Type :=
| top : Interval
| left_of : Z -> Interval
| between : Z -> Z -> Interval
| right_of : Z -> Interval
| bot : Interval.

Notation "⊤" := top.
Notation "⊥" := bot.
Notation "[ a , b ]" := (between a b) (at level 1).
Notation "(-∞, a ]" := (left_of a).

Definition AbD := Interval.

Definition AbS := option (list (string * AbD)). 

Definition top_AbS : AbS := Some nil.

Definition bot_AbS : AbS := None.

Fixpoint string_list_update {A} l x (a : A) :=
    match l with 
    | nil => (x, a) :: nil
    | (y, a') :: tl => if string_dec x y then (y, a) :: tl else (y, a') :: string_list_update tl x a
    end.

Definition ab_update s_sharp x a : AbS :=
    match s_sharp with
    | Some l => Some (string_list_update l x a)
    | None => Some ((x, a) :: nil)
    end.

Fixpoint string_list_lookup l x :=
    match l with
    | nil => ⊤
    | (y, a) :: tl => if string_dec x y then a else string_list_lookup tl x
    end.

Definition ab_lookup s_sharp x :=
    match s_sharp with
    | Some l => string_list_lookup l x
    | None => ⊥
    end.

Definition alpha_singleton n := [ n , n ].

Definition ab_opp a :=
    match a with
    | right_of n => left_of (-n)
    | (-∞, n] => right_of (-n)
    | between m n => between (-n) (-m)
    | ⊤ => ⊤
    | ⊥ => ⊥
    end.

Definition add_op a1 a2 :=
    match a1, a2 with
    | ⊥, _ | _, ⊥ => ⊥
    | left_of b, left_of d | left_of b, between _ d | between _ b, left_of d => left_of (b + d)
    | between a b, between c d => between (a + c) (b + d)
    | between a _, right_of c | right_of a, right_of c | right_of a, between c _ => right_of (a + c)
    | _, _ => ⊤
    end.
    
Definition sub_op a1 a2 :=
    match a1, a2 with
    | ⊥, _ | _, ⊥ => ⊥
    | left_of b, between c _ | left_of b, right_of c | between _ b, right_of c => left_of (b - c)
    | between a b, between c d => between (a - d) (b - c)
    | between a _, left_of d | right_of a, left_of d | right_of a, between _ d => right_of (a - d)
    | _, _ => ⊤
    end.

Definition mul_op a1 a2 :=
    match a1, a2 with
    | left_of b, left_of d => if (b >? 0) && (d >? 0) then ⊤ else right_of (b * d)
    | left_of b, between c d => if ((c <? 0) && (d >? 0)) || ((c >? 0) && (d <? 0)) then ⊤
                                else if (c =? 0) && (d =? 0) then between 0 0
                                else if (c <=? 0) && (d <=? 0) then right_of (Z.min (b * c) (b * d))
                                else left_of (Z.max (b * c) (b * d))
    | left_of b, right_of c => if (b >? 0) && (c <? 0) then ⊤ else left_of (b * c)
    | between a b, left_of d => if ((a <? 0) && (b >? 0)) || ((a >? 0) && (b <? 0)) then ⊤
                                else if (a =? 0) && (b =? 0) then between 0 0
                                else if (a <=? 0) && (b <=? 0) then right_of (Z.min (a * d) (b * d))
                                else left_of (Z.max (a * d) (b * d))
    | between a b, between c d => between (Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d))) (Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d)))
    | between a b, right_of c => if ((a <? 0) && (b >? 0)) || ((a >? 0) && (b <? 0)) then ⊤
                                 else if (a =? 0) && (b =? 0) then between 0 0
                                 else if (a <=? 0) && (b <=? 0) then right_of (Z.min (a * c) (b * c))
                                 else left_of (Z.max (a * c) (b * c))
    | right_of a, left_of d => if (d >? 0) && (a <? 0) then ⊤ else left_of (a * d)
    | right_of a, between c d => if ((c <? 0) && (d >? 0)) || ((c >? 0) && (d <? 0)) then ⊤
                                else if (c =? 0) && (d =? 0) then between 0 0
                                else if (c <=? 0) && (d <=? 0) then left_of (Z.max (a * c) (a * d))
                                else right_of (Z.min (a * c) (a * d))
    | right_of a, right_of c => if (a <? 0) && (c <? 0) then ⊤ else left_of (a * c)
    | between a b, ⊤ => if (a =? 0) && (b =? 0) then between 0 0 else ⊤
    | ⊤, between c d => if (c =? 0) && (d =? 0) then between 0 0 else ⊤
    | _, _ => ⊤
    end.

Definition join a1 a2 :=
    match a1, a2 with
    | ⊥, a3 | a3, ⊥ => a3
    | left_of b, left_of d | left_of b, between _ d | between _ b, left_of d => left_of (Z.max b d)
    | right_of a, right_of c | right_of a, between c _ | between a _, right_of c => right_of (Z.min a c)
    | between a b, between c d => between (Z.min a c) (Z.max b d)
    | _, _ => ⊤
    end.

    Unset Guard Checking.

    Fixpoint div_op a1 a2 {struct a1} :=
        match a1, a2 with
        | left_of b, left_of d => if d <? 0 then right_of (Z.min 0 (b / d)) 
                                  else if d =? 0 then div_op (left_of b) (left_of (-1))
                                  else ⊤
        | left_of b, between c d => if (c =? 0) && (d =? 0) then ⊥
                                    else if (c >? 0) && (d >=? c) then left_of (Z.max (b / c) (b / d))
                                    else if (c =? 0) && (d >? c) then div_op (left_of b) (between 1 d)
                                    else if (c <=? d) && (d <? 0) then right_of (Z.min (b / c) (b / d))
                                    else if (c <? d) && (d =? 0) then div_op (left_of b) (between c (-1))
                                    else ⊤
        | left_of b, right_of c => if c >? 0 then left_of (Z.max (b / c) 0) 
                                    else if c =? 0 then div_op (left_of b) (right_of 1)
                                    else ⊤
        | between a b, left_of d => if d <? 0 then between (Z.min (b / d) 0) (Z.max (a / d) 0)
                                     else if d =? 0 then div_op (between a b) (left_of (-1))
                                     else join (div_op (between a b) (left_of (-1))) (div_op (between a b) (between 1 d))
        | between a b, between c d => if (c =? 0) && (d =? 0) then ⊥
                                        else if (c =? 0) && (d >? c) then div_op (between a b) (between 1 d)
                                        else if (c <? 0) && (d =? 0) then div_op (between a b) (between c (-1))
                                        else if (c <? 0) && (d >? 0) then join (div_op (between a b) (between c (-1))) (div_op (between a b) (between 1 d))
                                        else between (Z.min (Z.min (a / c) (a / d)) (Z.min (b / c) (b / d))) (Z.max (Z.max (a / c) (a / d)) (Z.max (b / c) (b / d)))
        | between a b, right_of c => if c >? 0 then between (Z.min (a / c) 0) (Z.max (b / c) 0)
                                        else if c =? 0 then div_op (between a b) (right_of 1)
                                        else join (div_op (between a b) (between c (-1))) (div_op (between a b) (right_of 1))
        | between a b, ⊤ => join (div_op (between a b) (left_of (-1))) (div_op (between a b) (right_of 1))
        | right_of a, left_of d => if d <? 0 then left_of (Z.max 0 (a / d)) 
                                   else if d =? 0 then div_op (right_of a) (left_of (-1))
                                   else ⊤
        | right_of a, between c d => if (c =? 0) && (d =? 0) then ⊥
                                        else if (c >? 0) && (d >=? c) then right_of (Z.min (a / c) (a / d))
                                        else if (c =? 0) && (d >? c) then div_op (right_of a) (between 1 d)
                                        else if (c <=? d) && (d <? 0) then left_of (Z.max (a / c) (a / d))
                                        else if (c <? d) && (d =? 0) then div_op (right_of a) (between c (-1))
                                        else ⊤
        | right_of a, right_of c => if c >? 0 then right_of (Z.min (a / c) 0) 
                                    else if c =? 0 then div_op (right_of a) (right_of 1)
                                    else ⊤
        | ⊤, between c d => if (c =? 0) && (d =? 0) then ⊥ else ⊤
        | _, _ => ⊤
        end.

Set Guard Checking.

Definition ab_op op a1 a2 :=
    match op with
    | add => add_op a1 a2
    | sub => sub_op a1 a2
    | mul => mul_op a1 a2
    | div => div_op a1 a2 
    end.

    Fixpoint A_sharp e s_sharp :=
        match e with
        | var x => ab_lookup s_sharp x
        | const n => alpha_singleton n
        | aop op e1 e2 => ab_op op (A_sharp e1 s_sharp) (A_sharp e2 s_sharp)
        | opp e' => ab_opp (A_sharp e' s_sharp)
        end.

Definition eq_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ => bot_AbS
                | left_of b, left_of d => if b <=? d then  s_sharp 
                                          else  (ab_update s_sharp x (left_of d))
                | left_of b, between c d => if b <? c then bot_AbS
                                            else if (c <=? b) && (b <=? d) then  (ab_update s_sharp x (between c b))
                                            else  (ab_update s_sharp x (between c d))
                | left_of b, right_of c => if b <? c then bot_AbS 
                                           else  (ab_update s_sharp x (between c b))
                | between a b, left_of d => if a >? d then bot_AbS 
                                            else if (a <=? d) && (b >? d) then  (ab_update s_sharp x (between a d))
                                            else  s_sharp
                | between a b, between c d => if (b <? c) || (a >? d) then bot_AbS 
                                              else if (b >? d) && (a <? c) then  (ab_update s_sharp x (between c d))
                                              else if (b >? d) && (a >=? c) then  (ab_update s_sharp x (between a d))
                                              else if (c <=? b) && (b <=? d) && (a <? c) then  (ab_update s_sharp x (between c b))
                                              else  s_sharp
                | between a b, right_of c => if b <? c then bot_AbS 
                                             else if (b >=? c) && (a <? c) then  (ab_update s_sharp x (between c b))
                                             else  s_sharp
                | right_of a, left_of d => if a >? d then bot_AbS else  (ab_update s_sharp x (between a d))
                | right_of a, between c d => if a >? d then bot_AbS 
                                             else if a <? c then  (ab_update s_sharp x (between c d))
                                             else  (ab_update s_sharp x (between a d))
                | right_of a, right_of c => if a <? c then  (ab_update s_sharp x (right_of c)) else  s_sharp
                | ⊤, left_of d =>  (ab_update s_sharp x (left_of d))
                | ⊤, between c d =>  (ab_update s_sharp x (between c d))
                | ⊤, right_of c =>  (ab_update s_sharp x (right_of c))
                | _, _ =>  s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ => bot_AbS
            | left_of b, between c _ | left_of b, right_of c | between _ b, right_of c => if b <? c then bot_AbS else  s_sharp
            | right_of a, between _ d | right_of a, left_of d | between a _, left_of d => if a >? d then bot_AbS else  s_sharp
            | between a b, between c d => if (b <? c) || (a >? d) then bot_AbS else  s_sharp
            | _, _ =>  s_sharp
            end
    end.
        
Definition ne_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ => bot_AbS
                | left_of b, between c d => if (b =? c) && (c =? d) then  (ab_update s_sharp x (left_of (b - 1)))
                                            else  s_sharp
                | between a b, between c d => if (a =? b) && (b =? c) && (c =? d) then bot_AbS
                                              else if (negb (a =? b)) && (a =? c) && (c =? d) then  (ab_update s_sharp x (between (a + 1) b))
                                              else if (negb (a =? b)) && (b =? c) && (c =? d) then  (ab_update s_sharp x (between a (b - 1)))
                                              else  s_sharp
                | right_of a, between c d => if (a =? c) && (c =? d) then  (ab_update s_sharp x (right_of (a + 1)))
                                             else  s_sharp
                | _, _ =>  s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ => bot_AbS
            | between a b, between c d => if (a =? b) && (b =? c) && (c =? d) then bot_AbS
                                            else  s_sharp
            | _, _ =>  s_sharp
            end
    end.
    
Definition lt_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ => bot_AbS
                | left_of b, left_of d | left_of b, between _ d => if b >=? d then  (ab_update s_sharp x (left_of (d - 1))) 
                                                                   else  s_sharp
                | between a b, between _ d | between a b, left_of d => if a >=? d then bot_AbS 
                                                                       else if b >=? d then  (ab_update s_sharp x (between a (d - 1)))
                                                                       else  s_sharp
                | right_of a, between _ d | right_of a, left_of d => if a >=? d then bot_AbS else  (ab_update s_sharp x (between a (d - 1)))
                | ⊤, left_of d | ⊤, between _ d =>  (ab_update s_sharp x (left_of (d - 1)))
                | _, _ =>  s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ => bot_AbS
            | between a _, between _ d | between a _, left_of d 
            | right_of a, between _ d | right_of a, left_of d => if a >=? d then bot_AbS else  s_sharp
            | _, _ =>  s_sharp
            end
    end.

Definition gt_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ => bot_AbS
                | between a b, between c _ | between a b, right_of c => if b <=? c then bot_AbS else 
                                                                         if a <=? c then  (ab_update s_sharp x (between (c + 1) b))
                                                                         else  s_sharp
                | left_of b, between c _ | left_of b, right_of c => if b <=? c then bot_AbS else  (ab_update s_sharp x (between (c + 1) b))
                | right_of a, between c _ | right_of a, right_of c => if a <=? c then  (ab_update s_sharp x (right_of (c + 1))) else  s_sharp
                | ⊤, between c _ | ⊤, right_of c =>  (ab_update s_sharp x (right_of (c + 1)))
                | _, _ =>  s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ => bot_AbS
            | between _ b, between c _ | between _ b, right_of c
            | left_of b, between c _ | left_of b, right_of c  => if b <=? c then bot_AbS else  s_sharp
            | _, _ =>  s_sharp
            end
    end.

Definition le_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ => bot_AbS
                | left_of b, left_of d | left_of b, between _ d => if b >? d then  (ab_update s_sharp x (left_of d)) 
                                                                   else  s_sharp
                | between a b, between _ d | between a b, left_of d => if a >? d then bot_AbS 
                                                                       else if b >? d then  (ab_update s_sharp x (between a d))
                                                                       else  s_sharp
                | right_of a, between _ d | right_of a, left_of d => if a >? d then bot_AbS else  (ab_update s_sharp x (between a d))
                | ⊤, left_of d | ⊤, between _ d =>  (ab_update s_sharp x (left_of d))
                | _, _ =>  s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ => bot_AbS
            | between a _, between _ d | between a _, left_of d 
            | right_of a, between _ d | right_of a, left_of d => if a >? d then bot_AbS else  s_sharp
            | _, _ =>  s_sharp
            end
    end.

Definition ge_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | ⊥, _ | _, ⊥ => bot_AbS
                | between a b, between c _ | between a b, right_of c => if b <? c then bot_AbS else 
                                                                         if a <? c then  (ab_update s_sharp x (between c b))
                                                                         else  s_sharp
                | left_of b, between c _ | left_of b, right_of c => if b <? c then bot_AbS else  (ab_update s_sharp x (between c b))
                | right_of a, between c _ | right_of a, right_of c => if a <? c then  (ab_update s_sharp x (right_of c)) else  s_sharp
                | ⊤, between c _ | ⊤, right_of c =>  (ab_update s_sharp x (right_of c))
                | _, _ =>  s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | ⊥, _ | _, ⊥ => bot_AbS
            | between _ b, between c _ | between _ b, right_of c
            | left_of b, between c _ | left_of b, right_of c  => if b <? c then bot_AbS else  s_sharp
            | _, _ =>  s_sharp
            end
    end.

    Fixpoint join_state_helper l t_sharp :=
        match l with 
        | nil => top_AbS 
        | (x, a) :: tl => ab_update (join_state_helper tl t_sharp) x (join a (ab_lookup t_sharp x)) 
        end.
    
    Definition join_state s1_sharp s2_sharp :=
        match s1_sharp with
        | None => s2_sharp
        | Some l => join_state_helper l s2_sharp
        end.

Definition ab_le a1 a2 :=
    match a1, a2 with 
    | ⊥, _ | _, ⊤ => true
    | between a b, between c d => (c <=? a) && (b <=? d)
    | between a _, right_of c => c <=? a
    | between _ a, left_of c => a <=? c
    | right_of a, right_of c => c <=? a
    | left_of a, left_of c => a <=? c
    | _, _ => false
    end.

    Fixpoint ab_le_state_helper l t_sharp :=
        match l with
        | nil => true
        | (x, a) :: tl => ab_le (ab_lookup t_sharp x) a && ab_le_state_helper tl t_sharp
        end.
    
    Definition ab_le_state s_sharp t_sharp :=
        match s_sharp with
        | None => true
        | Some l => ab_le_state_helper l t_sharp
        end.


Definition widen a1 a2 :=
    match a1, a2 with
    | ⊥, a3 | a3, ⊥ => a3
    | right_of a, right_of c | right_of a, between c _ | between a _, right_of c => if a <=? c then right_of a else ⊤
    | between a b, between c d => if a <=? c then
                                    if d <=? b then
                                        between a b
                                    else 
                                        right_of a
                                  else 
                                    if d <=? b then
                                        left_of b
                                    else
                                        ⊤
    | between _ b, left_of d | left_of b, between _ d | left_of b, left_of d => if d <=? b then left_of b else ⊤
    | _, _ => ⊤
    end.

    Definition widen_state s_sharp t_sharp :=
        match s_sharp with
        | None => t_sharp
        | Some l => Some (map (fun c : string * AbD => let (x, a) := c in (x, widen a (ab_lookup t_sharp x))) l)
        end.

Definition narrow a1 a2 :=
    match a1, a2 with
    | ⊥, _ | _, ⊥ => ⊥
    | ⊤, a3 | a3, ⊤ => a3
    | right_of a, right_of _ => right_of a
    | right_of a, between _ d | right_of a, left_of d => between a d
    | between a b, _ => between a b
    | left_of b, right_of c | left_of b, between c _ => between c b
    | left_of b, left_of _ => left_of b
    end.

    Definition narrow_state s_sharp t_sharp :=
        match s_sharp with
        | None => bot_AbS
        | Some l => Some (map (fun c : string * AbD => let (x, a) := c in (x, narrow a (ab_lookup t_sharp x))) l)
        end.




End Intervals.



(* Extended Sign examples *)

Module B := AbstractInterpreter ExtendedSign.
Import ExtendedSign.
Import B.


(** 
    Example 1

    while x != 0 do
        x := x + 1
*)

Definition example1_expr :=
    while_do ((var "x") ≠ (const 0)) (assign "x" ((var "x") + (const 1))).

Definition example1_1_state := Some [("x", <0)].

Definition example1_2_state := Some [("x", =0)].

Definition example1_3_state := Some [("x", >0)].

Eval compute in (AI example1_expr false example1_1_state).

Eval compute in (AI example1_expr false example1_2_state).

Eval compute in (AI example1_expr false example1_3_state).


(** 
    Example 2

    x := x + y
    y := y + 1
*)

Definition example2_expr :=
    (sequence (assign "x" ((var "x") + (var "y"))) (assign "y" ((var "y") + (const 1)))).

Definition example2_state := Some [("x", ≤0); ("y", <0)].

Eval compute in (AI example2_expr false example2_state).


(** 
    Example 3

    x := 40
    while x != 0 do
        x := x - 1
*)

Definition example3_expr :=
    sequence (assign "x" (const 40)) (while_do (bop ne (var "x") (const 0)) (assign "x" (aop sub (var "x") (const 1)))).

Eval compute in (AI example3_expr false top_AbS).



(* Intervals examples *)

Module C := AbstractInterpreter Intervals.
Import Intervals.
Import C.

(** 
    Example 3

    x := 40
    while x != 0 do
        x := x - 1
*)

Eval compute in (AI example3_expr false top_AbS).
Eval compute in (AI example3_expr true top_AbS).


(** 
    Example 4

    while x >= 0 do
        x := x - 1
        y := y + 1
*)

Definition example4_expr :=
    while_do (bop ge (var "x") (const 0)) (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1)))).

Definition example4_state := Some [("x", [10,10]); ("y", [0,0])].


(* Eval compute in (AI example4_expr false example4_state). *)
Eval compute in (AI example4_expr true example4_state).



(** 
    Example 5

    while x < 10 do
        x := x + 1
*)

Definition example5_expr :=
    while_do (bop lt (var "x") (const 10)) (assign "x" (aop add (var "x") (const 1))).

Definition example5_state := Some [("x", between 0 0)].

Eval compute in (AI example5_expr false example5_state).
Eval compute in (AI example5_expr true example5_state).



(** 
    Example 6

    while x <= 100 do
        x := x + 1
*)

Definition example6_expr :=
    while_do (bop le (var "x") (const 100)) (assign "x" (aop add (var "x") (const 1))).

Definition example6_state := Some [("x", between 1 1)].

Eval compute in (AI example6_expr false example6_state).
Eval compute in (AI example6_expr true example6_state).

(** 
    Example 7

    x := 0
    while x < 40 do
        x := x + 1
*)

Definition example7_expr :=
    sequence (assign "x" (const 0)) (while_do (bop lt (var "x") (const 40)) (assign "x" (aop add (var "x") (const 1)))).

Eval compute in (AI example7_expr false top_AbS).
Eval compute in (AI example7_expr true top_AbS).




(** 
    Example 8

    x := 0
    while 1 = 1 do
        if y = 0 then
            x := x + 1
            if x < 40 then
                x := 0
*)

Definition example8_expr :=
    sequence (assign "x" (const 0)) 
             (while_do (bop eq (const 1) (const 1)) 
                (if_then_else (bop eq (var "y") (const 0))
                    (sequence (assign "x" (aop add (var "x") (const 1)))
                              (if_then_else (bop gt (var "x") (const 40)) 
                                    (assign "x" (const 0)) 
                                    skip))
                    skip)).

Definition example8_state := Some [("y", between 0 1)].

Eval compute in (AI example8_expr false top_AbS).
Eval compute in (AI example8_expr true top_AbS).



(** 
    Example 9

    j := 1
    i := 1
    while i <= 3 do
        j := 1
        while j <= i do
            j := j + 1
        i := i + 1
*)

Definition example9_expr :=
    sequence (assign "j" (const 1))
    (sequence (assign "i" (const 1)) 
             (while_do (bop le (var "i") (const 3)) 
                (sequence (sequence (assign "j" (const 1)) 
                                    (while_do (bop le (var "j") (var "i")) 
                                        (assign "j" (aop add (var "j") (const 1))))) 
                          (assign "i" (aop add (var "i") (const 1)))))).

Eval compute in (AI example9_expr true top_AbS).
Eval compute in (AI example9_expr false top_AbS).


(** 
    Example 10

    i := 1
    while i <= 4 do
        j := 0
        while j <= 3 do
            k := 0
            while k <= 5 do
                z := i * j * k
                k := k + 1
            j := j + 1
        i := i + 1
*)

Definition example10_expr :=
    sequence (assign "i" (const 1)) 
             (while_do (bop le (var "i") (const 4)) 
                (sequence (sequence (assign "j" (const 0)) 
                                    (while_do (bop le (var "j") (const 3)) 
                                        (sequence (sequence (assign "k" (const 0)) 
                                                            (while_do (bop le (var "k") (const 5)) 
                                                                (sequence (assign "z" (aop mul (aop mul (var "i") (var "j")) (var "k"))) 
                                                                            (assign "k" (aop add (var "k") (const 1))))))
                                                  (assign "j" (aop add (var "j") (const 1))))))
                          (assign "i" (aop add (var "i") (const 1))))).

Eval compute in (AI example10_expr false top_AbS).
Eval compute in (AI example10_expr true top_AbS).


(** 
    Example 11

    x := 1 / 0;
    while x <= 5 do
*)

Definition example11_expr :=
    sequence (assign "x" (aop div (const 1) (const 0))) (while_do (bop le (var "x") (const 5)) skip).
    
Eval compute in (AI example11_expr false top_AbS).


(** 
    Example 12

    while (1 / 0) < 1 do
*)

Definition example12_expr :=
    (while_do (bop lt (aop div (const 1) (const 0)) (const 1)) skip).
    
Eval compute in (AI example12_expr false top_AbS).





    
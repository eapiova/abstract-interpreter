From pv Require Import library.
Require Import String ZArith List.
Open Scope Z_scope.

From ReductionEffect Require Import PrintingEffect.

Require Coq.extraction.Extraction.
Extraction Language OCaml.



(* Language *)

Inductive ABinOp :=
    | add
    | sub
    | mul
    (**| div *).

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



(* Abstract Domain structure *)

Module Type AbstractDomain.

Parameter AbD : Type.
Parameter AbS : Type.
Parameter top_AbS : AbS.

Parameter ab_update : AbS -> string -> AbD -> AbS.
Parameter lookup : AbS -> string -> AbD.
Parameter alpha_singleton : Z -> AbD.
Parameter ab_opp : AbD -> AbD.
Parameter ab_op : ABinOp -> AbD -> AbD -> AbD.
Parameter A_sharp : Aexp -> AbS -> AbD.

Parameter eq_sem : Aexp -> Aexp -> AbS -> option AbS.
Parameter ne_sem : Aexp -> Aexp -> AbS -> option AbS.
Parameter lt_sem : Aexp -> Aexp -> AbS -> option AbS.
Parameter gt_sem : Aexp -> Aexp -> AbS -> option AbS.
Parameter le_sem : Aexp -> Aexp -> AbS -> option AbS.
Parameter ge_sem : Aexp -> Aexp -> AbS -> option AbS.

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
    
Definition join_state' s_sharp opt_t_sharp :=
    match opt_t_sharp with
    | Some t_sharp => join_state s_sharp t_sharp
    | None => s_sharp
    end.
    
Fixpoint B_sharp b s_sharp :=
    match b with
    | tt => Some s_sharp
    | ff => None
    | bop op e1 e2 => match op with 
                        | eq => eq_sem e1 e2 s_sharp
                        | lt => lt_sem e1 e2 s_sharp
                        | gt => gt_sem e1 e2 s_sharp
                        | le => le_sem e1 e2 s_sharp
                        | ge => ge_sem e1 e2 s_sharp
                        | ne => ne_sem e1 e2 s_sharp
                        end
    | and b1 b2 => match B_sharp b1 s_sharp with
                    | Some t_sharp => B_sharp b2 t_sharp
                    | None => None
                    end
    | or b1 b2 => match B_sharp b1 s_sharp with 
                    | Some t_sharp => Some (join_state' t_sharp (B_sharp b2 s_sharp))
                    | None => B_sharp b2 s_sharp
                    end
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

Definition step (AI_state : AbS -> option AbS * list AbS) b s_sharp t_sharp :=
    match B_sharp b t_sharp with
    | Some u_sharp => let (opt_v_sharp, invs) := (AI_state u_sharp) in (join_state' s_sharp opt_v_sharp, invs)
    | None => (s_sharp, nil)
    end.

Definition is_inv AI_state s_sharp t_sharp b := let (u_sharp, _) := step AI_state b s_sharp t_sharp in ab_le_state t_sharp u_sharp.

Unset Guard Checking.

Fixpoint steps AI_state (b : Bexp) s_sharp t_sharp {struct b} :=
    if is_inv AI_state s_sharp t_sharp b
        then (t_sharp, [t_sharp])
    else 
        let (u_sharp, invs1) := print_id (step AI_state b s_sharp t_sharp) in let (v_sharp, invs2) := steps AI_state b s_sharp u_sharp in (v_sharp, invs1 ++ invs2).        

Fixpoint widening AI_state b s_sharp t_sharp {struct b} :=
    if is_inv AI_state s_sharp t_sharp b
        then (t_sharp, [t_sharp])
    else 
        let (u_sharp, invs1) := print_id (step AI_state b s_sharp t_sharp) in let (v_sharp, invs2) := widening AI_state b s_sharp (widen_state t_sharp u_sharp) in (v_sharp, invs1 ++ invs2).

Fixpoint narrowing AI_state b s_sharp t_sharp {struct b} :=
    if is_inv AI_state s_sharp t_sharp b
        then (t_sharp, [t_sharp])
    else 
        let (u_sharp, invs1) := print_id (step AI_state b s_sharp t_sharp) in let (v_sharp, invs2) := narrowing AI_state b s_sharp (narrow_state t_sharp u_sharp) in (v_sharp, invs1 ++ invs2).

Definition ab_lfp AI_state b s_sharp (widen_toggle : bool) :=
    if widen_toggle then let (t_sharp, invs1) := widening AI_state b s_sharp s_sharp in let (v_sharp, invs2) := narrowing AI_state b s_sharp t_sharp in (v_sharp, invs1 ++ invs2)
    else steps AI_state b s_sharp s_sharp.

Fixpoint AI (P : While) widen_toggle s_sharp :=
    match P with
    | assign x e => (Some (ab_update s_sharp x (A_sharp e s_sharp)), nil)
    | skip => (Some s_sharp, nil)
    | sequence S1 S2 => match AI S1 widen_toggle s_sharp with
                        | (Some t_sharp, invs1) => let (opt_u_sharp, invs2) := AI S2 widen_toggle t_sharp in (opt_u_sharp, invs1 ++ invs2)
                        | (None, invs1) => (None, invs1)
                        end
    | if_then_else b S1 S2 => match B_sharp b s_sharp, B_sharp (neg_sem b) s_sharp with
                            | Some t_sharp, Some u_sharp => match AI S1 widen_toggle t_sharp with
                                                            | (Some v_sharp, invs1) => let (opt_w_sharp, invs2) := AI S2 widen_toggle u_sharp in (Some (join_state' v_sharp opt_w_sharp), invs1 ++ invs2)
                                                            | (None, invs1) => AI S2 widen_toggle u_sharp 
                                                            end
                            | Some t_sharp, None => AI S1 widen_toggle t_sharp 
                            | None, Some u_sharp => AI S2 widen_toggle u_sharp 
                            | None, None => (None, nil) 
                            end
    | while_do b S' => let (inv, invs) := (ab_lfp (AI S' widen_toggle) b s_sharp widen_toggle) in (B_sharp (neg_sem b) inv, invs)
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

Definition AbD := extended_sign.

Definition AbS := list (string * AbD).

Definition top_AbS : AbS := nil.

Fixpoint ab_update s_sharp x a : AbS :=
    match s_sharp with 
    | nil => (x, a) :: nil
    | (y, a') :: sl => if string_dec x y then (y, a) :: sl else (y, a') :: ab_update sl x a
    end.

Fixpoint lookup s_sharp x :=
    match s_sharp with
    | nil => top
    | (y, a) :: sl => if string_dec x y then a else lookup sl x
    end.

Definition alpha_singleton n :=
    if n =? 0 then eq0
    else if n <? 0 then lt0
    else gt0.

Definition sign_eq_dec : forall (x y : AbD), { x = y } + { x <> y }.
Proof.
    decide equality.
Defined.

Definition ab_opp a :=
    match a with
    | lt0 => gt0
    | gt0 => lt0
    | le0 => ge0
    | ge0 => le0
    | a' => a'
    end.

Definition add_op a1 a2 :=
    match a1, a2 with
    | bot, _ | _, bot => bot
    | eq0, a3 | a3, eq0 => a3
    | lt0, le0 | le0, lt0 => lt0
    | gt0, ge0 | ge0, gt0 => gt0
    | ne0, ne0 => top
    | a3, a4 => if sign_eq_dec a3 a4 then a3 else top
    end.

Definition sub_op a1 a2 :=
    match a1, a2 with
    | bot, _ => bot
    | _, bot => bot
    | eq0, a3 => ab_opp a3
    | a3, eq0 => a3
    | lt0, gt0 | lt0, ge0 | le0, gt0 => lt0
    | gt0, lt0 | gt0, le0 | ge0, lt0 => gt0
    | le0, ge0 => le0
    | ge0, le0 => ge0
    | _, _ => top
    end.

Definition mul_op a1 a2 :=
    match a1, a2 with
    | bot, _ | _, bot => bot
    | eq0, _ | _, eq0 => eq0
    | lt0, a3 | a3, lt0 => ab_opp a3
    | gt0, a3 | a3, gt0 => a3
    | le0, le0 | ge0, ge0 => ge0
    | le0, ge0 | ge0, le0 => le0
    | ne0, ne0 => ne0
    | _, _ => top
    end.

(**
Definition div_op a1 a2 :=
    match a1, a2 with
    | bot, _ | _, bot | _, eq0 => bot
    | eq0, _ => eq0
    | ne0, _ | lt0, ne0 | lt0, top | gt0, ne0 | gt0, top => ne0
    | lt0, lt0 | lt0, le0 | gt0, gt0 | gt0, ge0 => gt0
    | lt0, gt0 | lt0, ge0 | gt0, lt0 | gt0, le0 => lt0
    | le0, lt0 | le0, le0 | ge0, gt0 | ge0, ge0 => ge0
    | le0, gt0 | le0, ge0 | ge0, lt0 | ge0, le0 => le0
    | _, _ => top
    end.
*)

Definition ab_op op a1 a2 :=
    match op with
    | add => add_op a1 a2
    | sub => sub_op a1 a2
    | mul => mul_op a1 a2
    (* | div => div_op a1 a2 *)
    end.

Fixpoint A_sharp e s_sharp :=
    match e with
    | var x => lookup s_sharp x
    | const n => alpha_singleton n
    | aop op e1 e2 => ab_op op (A_sharp e1 s_sharp) (A_sharp e2 s_sharp)
    | opp e' => ab_opp (A_sharp e' s_sharp)
    end.

Definition eq_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot 
                | eq0, lt0 | eq0, gt0 | lt0, eq0 | gt0, eq0 | lt0, gt0 | gt0, lt0 
                | lt0, ge0 | ge0, lt0 | eq0, ne0 | ne0, eq0 | gt0, le0 | le0, gt0 => None
                | le0, lt0 | ne0, lt0 | ne0, le0 | le0, ne0 => Some (ab_update s_sharp x lt0)
                | le0, eq0 | ge0, eq0 | ge0, le0 | le0, ge0 => Some (ab_update s_sharp x eq0)
                | ne0, gt0 | ge0, gt0 | ge0, ne0 | ne0, ge0 => Some (ab_update s_sharp x gt0)
                | top, a => Some (ab_update s_sharp x a)
                | _, _ => Some s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot 
            | eq0, lt0 | eq0, gt0 | lt0, eq0 | gt0, eq0 | lt0, gt0 | gt0, lt0 
            | lt0, ge0 | ge0, lt0 | eq0, ne0 | ne0, eq0 | gt0, le0 | le0, gt0 => None
            | _, _ => Some s_sharp
            end
    end.
        
Definition ne_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot | eq0, eq0 => None
                | le0, eq0 => Some (ab_update s_sharp x lt0)
                | ge0, eq0 => Some (ab_update s_sharp x gt0)
                | top, eq0 => Some (ab_update s_sharp x ne0)
                | _, _ => Some s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot | eq0, eq0 => None
            | _, _ => Some s_sharp
            end
    end.

Definition lt_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot 
                | eq0, lt0 | eq0, eq0 | eq0, le0
                | gt0, lt0 | gt0, eq0 | gt0, le0
                | ge0, lt0 | ge0, eq0 | ge0, le0 => None
                | le0, lt0 | le0, eq0 | le0, le0
                | ne0, lt0 | ne0, eq0 | ne0, le0
                | top, lt0 | top, eq0 | top, le0 => Some (ab_update s_sharp x lt0)
                | _, _ => Some s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot 
            | eq0, lt0 | eq0, eq0 | eq0, le0
            | gt0, lt0 | gt0, eq0 | gt0, le0
            | ge0, lt0 | ge0, eq0 | ge0, le0 => None
            | _, _ => Some s_sharp
            end
    end.

Definition gt_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot 
                | eq0, gt0 | eq0, eq0 | eq0, ge0
                | lt0, gt0 | lt0, eq0 | lt0, ge0
                | le0, gt0 | le0, eq0 | le0, ge0 => None
                | ge0, gt0 | ge0, eq0 | ge0, ge0
                | ne0, gt0 | ne0, eq0 | ne0, ge0
                | top, gt0 | top, eq0 | top, ge0 => Some (ab_update s_sharp x gt0)
                | _, _ => Some s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot 
            | eq0, gt0 | eq0, eq0 | eq0, ge0
            | lt0, gt0 | lt0, eq0 | lt0, ge0
            | le0, gt0 | le0, eq0 | le0, ge0 => None
            | _, _ => Some s_sharp
            end
    end.

Definition le_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot 
                | eq0, lt0 
                | gt0, lt0 | gt0, eq0 | gt0, le0
                | ge0, lt0 => None
                | le0, lt0 
                | ne0, lt0 | ne0, eq0 | ne0, le0
                | top, lt0 => Some (ab_update s_sharp x lt0)
                | ge0, eq0 | ge0, le0 => Some (ab_update s_sharp x eq0)
                | top, eq0 | top, le0 => Some (ab_update s_sharp x ge0)
                | _, _ => Some s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot 
            | eq0, lt0
            | gt0, lt0 | gt0, eq0 | gt0, le0
            | ge0, lt0 => None
            | _, _ => Some s_sharp
            end
    end.

Definition ge_sem e1 e2 s_sharp :=
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot 
                | eq0, gt0 
                | lt0, gt0 | lt0, eq0 | lt0, ge0
                | le0, gt0 => None
                | ge0, gt0 
                | ne0, gt0 | ne0, eq0 | ne0, ge0
                | top, gt0 => Some (ab_update s_sharp x gt0)
                | le0, eq0 | le0, ge0 => Some (ab_update s_sharp x eq0)
                | top, eq0 | top, ge0 => Some (ab_update s_sharp x le0)
                | _, _ => Some s_sharp
                end
    | _ => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot 
            | eq0, gt0
            | lt0, gt0 | lt0, eq0 | lt0, ge0
            | le0, gt0 => None
            | _, _ => Some s_sharp
            end
    end.

Definition join a1 a2 :=
    match a1, a2 with
    | bot,  a3 |  a3,  bot =>  a3
    | eq0,  lt0 |  lt0,  eq0 
    | eq0,  le0 |  le0,  eq0
    | lt0,  le0 |  le0,  lt0 =>  le0
    | eq0,  gt0 |  gt0,  eq0 
    | eq0,  ge0 |  ge0,  eq0
    | gt0,  ge0 |  ge0,  gt0 =>  ge0
    | lt0,  gt0 |  gt0,  lt0
    | lt0,  ne0 |  ne0,  lt0
    | gt0,  ne0 |  ne0,  gt0 =>  ne0
    | a3, a4 => if sign_eq_dec a3 a4 then a3 else top
    end.

Fixpoint join_state s1_sharp s2_sharp :=
    match s1_sharp with 
    | nil => nil 
    | (x, a) :: sl => ab_update (join_state sl s2_sharp) x (join a (lookup s2_sharp x)) 
    end.

Definition ab_le a1 a2 := if sign_eq_dec (join a1 a2) a2 then true else false.

Fixpoint ab_le_state s_sharp t_sharp :=
    match s_sharp with
    | nil => true
    | (x, a) :: sl => ab_le (lookup t_sharp x) a && ab_le_state sl t_sharp
    end.

Definition widen a1 a2 := join a1 a2.

Definition widen_state s_sharp t_sharp :=
    map (fun c : string * AbD => let (x, a) := c in (x, widen a (lookup t_sharp x))) s_sharp.

Definition narrow (a1 a2 : AbD) := a1.

Definition narrow_state s_sharp t_sharp :=
    map (fun c : string * AbD => let (x, a) := c in (x, narrow a (lookup t_sharp x))) s_sharp.

End ExtendedSign.



(* Intervals domain *)

Module Intervals <: AbstractDomain.

Inductive Interval : Type :=
| top : Interval
| left_of : Z -> Interval
| between : Z -> Z -> Interval
| right_of : Z -> Interval
| bot : Interval.

Definition AbD := Interval.

Definition AbS := list (string * AbD). 

Definition top_AbS : AbS := nil.

Fixpoint ab_update s_sharp x a : AbS :=
    match s_sharp with 
    | nil => (x, a) :: nil
    | (y, a') :: sl => if string_dec x y then (y, a) :: sl else (y, a') :: ab_update sl x a
    end.

Fixpoint lookup s_sharp x :=
    match s_sharp with
    | nil => top
    | (y, a) :: sl => if string_dec x y then a else lookup sl x
    end.

Definition alpha_singleton n := between n n.

Definition ab_opp a :=
    match a with
    | right_of n => left_of (-n)
    | left_of n => right_of (-n)
    | between m n => between (-n) (-m)
    | top => top
    | bot => bot
    end.

Definition add_op a1 a2 :=
    match a1, a2 with
    | bot, _ | _, bot => bot
    | left_of b, left_of d | left_of b, between _ d | between _ b, left_of d => left_of (b + d)
    | between a b, between c d => between (a + c) (b + d)
    | between a _, right_of c | right_of a, right_of c | right_of a, between c _ => right_of (a + c)
    | _, _ => top
    end.
    
Definition sub_op a1 a2 :=
    match a1, a2 with
    | bot, _ | _, bot => bot
    | left_of b, between c _ | left_of b, right_of c | between _ b, right_of c => left_of (b - c)
    | between a b, between c d => between (a - d) (b - c)
    | between a _, left_of d | right_of a, left_of d | right_of a, between _ d => right_of (a - d)
    | _, _ => top
    end.

Definition mul_op a1 a2 :=
    match a1, a2 with
    | left_of b, left_of d => if (b >? 0) && (d >? 0) then top else right_of (b * d)
    | left_of b, between c d => if ((c <? 0) && (d >? 0)) || ((c >? 0) && (d <? 0)) then top
                                else if (c =? 0) && (d =? 0) then between 0 0
                                else if (c <=? 0) && (d <=? 0) then right_of (Z.min (b * c) (b * d))
                                else left_of (Z.max (b * c) (b * d))
    | left_of b, right_of c => if (b >? 0) && (c <? 0) then top else left_of (b * c)
    | between a b, left_of d => if ((a <? 0) && (b >? 0)) || ((a >? 0) && (b <? 0)) then top
                                else if (a =? 0) && (b =? 0) then between 0 0
                                else if (a <=? 0) && (b <=? 0) then right_of (Z.min (a * d) (b * d))
                                else left_of (Z.max (a * d) (b * d))
    | between a b, between c d => between (Z.min (Z.min (a * c) (a * d)) (Z.min (b * c) (b * d))) (Z.max (Z.max (a * c) (a * d)) (Z.max (b * c) (b * d)))
    | between a b, right_of c => if ((a <? 0) && (b >? 0)) || ((a >? 0) && (b <? 0)) then top
                                 else if (a =? 0) && (b =? 0) then between 0 0
                                 else if (a <=? 0) && (b <=? 0) then right_of (Z.min (a * c) (b * c))
                                 else left_of (Z.max (a * c) (b * c))
    | right_of a, left_of d => if (d >? 0) && (a <? 0) then top else left_of (a * d)
    | right_of a, between c d => if ((c <? 0) && (d >? 0)) || ((c >? 0) && (d <? 0)) then top
                                else if (c =? 0) && (d =? 0) then between 0 0
                                else if (c <=? 0) && (d <=? 0) then left_of (Z.max (a * c) (a * d))
                                else right_of (Z.min (a * c) (a * d))
    | right_of a, right_of c => if (a <? 0) && (c <? 0) then top else left_of (a * c)
    | between a b, top => if (a =? 0) && (b =? 0) then between 0 0 else top
    | top, between c d => if (c =? 0) && (d =? 0) then between 0 0 else top
    | _, _ => top
    end.

Definition join a1 a2 :=
    match a1, a2 with
    | bot, a3 | a3, bot => a3
    | left_of b, left_of d | left_of b, between _ d | between _ b, left_of d => left_of (Z.max b d)
    | right_of a, right_of c | right_of a, between c _ | between a _, right_of c => right_of (Z.min a c)
    | between a b, between c d => between (Z.min a c) (Z.max b d)
    | _, _ => top
    end.

(**
Definition div_op a1 a2 :=
    match a1, a2 with
    | left_of b, left_of d => if d <=? 0 then right_of (Z.min 0 (b / d)) else top
    | left_of b, between c d => if (c =? 0) && (d =? 0) then bot
                                else if (c >? 0) && (d >=? c) then left_of (Z.max (b / c) (b / d))
                                else if (c =? 0) && (d >? c) && (b <=? 0) then left_of (b / d)
                                else if (c <=? d) && (d <? 0) then right_of (Z.min (b / c) (b / d))
                                else top
    | left_of b, right_of c => if c >=? 0 then left_of (Z.max (b / c) 0) else top
    | between a b, left_of d => if d <=? 0 then between (Z.min (Z.min (a / d) (b / d)) 0) (Z.max (Z.max (a / d) (b / d)) 0)
                                 else if (a =? 0) && (b =? 0) then between 0 0
                                 else if (a >=? 0) && (b >? 0) then left_of (Z.max (a / d) (b / d))
                                 else if (a <? 0) && (b <=? 0) then right_of (Z.min (a / d) (b / d))
                                 else top
    | between a b, between c d => if (c =? 0) && (d =? 0) then bot
                                    else if (c <? 0) && (d >? 0) then join (between (Z.min (Z.min (a / c) (b / c)) 0) (Z.max (Z.max (a / c) (b / c)) 0)) (between (Z.min (Z.min (a / d) (b / d)) 0) (Z.max (Z.max (a / d) (b / d)) 0))
                                    else between (Z.min (Z.min (a / c) (a / d)) (Z.min (b / c) (b / d))) (Z.max (Z.max (a / c) (a / d)) (Z.max (b / c) (b / d)))
    
    
    
    | between a b, right_of c => if c >=? 0 then between (Z.min (Z.min (a / c) (b / c)) 0) (Z.max (Z.max (a / c) (b / c)) 0)
                                    else if (a =? 0) && (b =? 0) then between 0 0
                                    else if (a >=? 0) && (b >? 0) then left_of (Z.max (a / c) (b / c))
                                    else if (a <? 0) && (b <=? 0) then right_of (Z.min (a / c) (b / c))
                                    else top
    | between a b, top => if (a =? 0) && (b =? 0) then between 0 0 else top
    | right_of a, left_of d => if d <=? 0 then left_of (Z.max 0 (a / d)) else top
    | right_of a, between c d => if (c =? 0) && (d =? 0) then bot
                                    else if (c >? 0) && (d >=? c) then right_of (Z.min (a / c) (a / d))
                                    else if (c =? 0) && (d >? c) && (a >=? 0) then right_of (a / d)
                                    else if (c <=? d) && (d <? 0) then left_of (Z.max (a / c) (a / d))
                                    else top
    | right_of a, right_of c => if c >=? 0 then right_of (Z.min (a / c) 0) else top
    | top, between c d => if (c =? 0) && (d =? 0) then bot else top
    | _, _ => top
    end.
*)

Definition ab_op op a1 a2 :=
    match op with
    | add => add_op a1 a2
    | sub => sub_op a1 a2
    | mul => mul_op a1 a2
    (* | div => div_op a1 a2 *)
    end.

Fixpoint A_sharp e s_sharp :=
    match e with
    | var x => lookup s_sharp x
    | const n => alpha_singleton n
    | aop op e1 e2 => ab_op op (A_sharp e1 s_sharp) (A_sharp e2 s_sharp)
    | opp e' => ab_opp (A_sharp e' s_sharp)
    end.

Definition eq_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot => None
                | left_of b, left_of d => if b <=? d then Some s_sharp 
                                          else Some (ab_update s_sharp x (left_of d))
                | left_of b, between c d => if b <? c then None
                                            else if (c <=? b) && (b <=? d) then Some (ab_update s_sharp x (between c b))
                                            else Some (ab_update s_sharp x (between c d))
                | left_of b, right_of c => if b <? c then None 
                                           else Some (ab_update s_sharp x (between c b))
                | between a b, left_of d => if a >? d then None 
                                            else if (a <=? d) && (b >? d) then Some (ab_update s_sharp x (between a d))
                                            else Some s_sharp
                | between a b, between c d => if (b <? c) || (a >? d) then None 
                                              else if (b >? d) && (a <? c) then Some (ab_update s_sharp x (between c d))
                                              else if (b >? d) && (a >=? c) then Some (ab_update s_sharp x (between a d))
                                              else if (c <=? b) && (b <=? d) && (a <? c) then Some (ab_update s_sharp x (between c b))
                                              else Some s_sharp
                | between a b, right_of c => if b <? c then None 
                                             else if (b >=? c) && (a <? c) then Some (ab_update s_sharp x (between c b))
                                             else Some s_sharp
                | right_of a, left_of d => if a >? d then None else Some (ab_update s_sharp x (between a d))
                | right_of a, between c d => if a >? d then None 
                                             else if a <? c then Some (ab_update s_sharp x (between c d))
                                             else Some (ab_update s_sharp x (between a d))
                | right_of a, right_of c => if a <? c then Some (ab_update s_sharp x (right_of c)) else Some s_sharp
                | top, left_of d => Some (ab_update s_sharp x (left_of d))
                | top, between c d => Some (ab_update s_sharp x (between c d))
                | top, right_of c => Some (ab_update s_sharp x (right_of c))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot => None
            | left_of b, between c _ | left_of b, right_of c | between _ b, right_of c => if b <? c then None else Some s_sharp
            | right_of a, between _ d | right_of a, left_of d | between a _, left_of d => if a >? d then None else Some s_sharp
            | between a b, between c d => if (b <? c) || (a >? d) then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.
        
Definition ne_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot => None
                | left_of b, between c d => if (b =? c) && (c =? d) then Some (ab_update s_sharp x (left_of (b - 1)))
                                            else Some s_sharp
                | between a b, between c d => if (a =? b) && (b =? c) && (c =? d) then None
                                              else if (negb (a =? b)) && (a =? c) && (c =? d) then Some (ab_update s_sharp x (between (a + 1) b))
                                              else if (negb (a =? b)) && (b =? c) && (c =? d) then Some (ab_update s_sharp x (between a (b - 1)))
                                              else Some s_sharp
                | right_of a, between c d => if (a =? c) && (c =? d) then Some (ab_update s_sharp x (right_of (a + 1)))
                                             else Some s_sharp
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot => None
            | between a b, between c d => if (a =? b) && (b =? c) && (c =? d) then None
                                            else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.
    
Definition lt_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot => None
                | left_of b, left_of d | left_of b, between _ d => if b >=? d then Some (ab_update s_sharp x (left_of (d - 1))) 
                                                                   else Some s_sharp
                | between a b, between _ d | between a b, left_of d => if a >=? d then None 
                                                                       else if b >=? d then Some (ab_update s_sharp x (between a (d - 1)))
                                                                       else Some s_sharp
                | right_of a, between _ d | right_of a, left_of d => if a >=? d then None else Some (ab_update s_sharp x (between a (d - 1)))
                | top, left_of d | top, between _ d => Some (ab_update s_sharp x (left_of (d - 1)))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot => None
            | between a _, between _ d | between a _, left_of d 
            | right_of a, between _ d | right_of a, left_of d => if a >=? d then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Definition gt_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot => None
                | between a b, between c _ | between a b, right_of c => if b <=? c then None else 
                                                                         if a <=? c then Some (ab_update s_sharp x (between (c + 1) b))
                                                                         else Some s_sharp
                | left_of b, between c _ | left_of b, right_of c => if b <=? c then None else Some (ab_update s_sharp x (between (c + 1) b))
                | right_of a, between c _ | right_of a, right_of c => if a <=? c then Some (ab_update s_sharp x (right_of (c + 1))) else Some s_sharp
                | top, between c _ | top, right_of c => Some (ab_update s_sharp x (right_of (c + 1)))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot => None
            | between _ b, between c _ | between _ b, right_of c
            | left_of b, between c _ | left_of b, right_of c  => if b <=? c then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Definition le_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | bot, _ | _, bot => None
                | left_of b, left_of d | left_of b, between _ d => if b >? d then Some (ab_update s_sharp x (left_of d)) 
                                                                   else Some s_sharp
                | between a b, between _ d | between a b, left_of d => if a >? d then None 
                                                                       else if b >? d then Some (ab_update s_sharp x (between a d))
                                                                       else Some s_sharp
                | right_of a, between _ d | right_of a, left_of d => if a >? d then None else Some (ab_update s_sharp x (between a d))
                | top, left_of d | top, between _ d => Some (ab_update s_sharp x (left_of d))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot => None
            | between a _, between _ d | between a _, left_of d 
            | right_of a, between _ d | right_of a, left_of d => if a >? d then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Definition ge_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match lookup s_sharp x, A_sharp e2 s_sharp with
                | bot, _ | _, bot => None
                | between a b, between c _ | between a b, right_of c => if b <? c then None else 
                                                                         if a <? c then Some (ab_update s_sharp x (between c b))
                                                                         else Some s_sharp
                | left_of b, between c _ | left_of b, right_of c => if b <? c then None else Some (ab_update s_sharp x (between c b))
                | right_of a, between c _ | right_of a, right_of c => if a <? c then Some (ab_update s_sharp x (right_of c)) else Some s_sharp
                | top, between c _ | top, right_of c => Some (ab_update s_sharp x (right_of c))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | bot, _ | _, bot => None
            | between _ b, between c _ | between _ b, right_of c
            | left_of b, between c _ | left_of b, right_of c  => if b <? c then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Fixpoint join_state s1_sharp s2_sharp :=
    match s1_sharp with 
    | nil => nil 
    | (x, a) :: sl => ab_update (join_state sl s2_sharp) x (join a (lookup s2_sharp x)) 
    end.

Definition ab_le a1 a2 :=
    match a1, a2 with 
    | bot, _ | _, top => true
    | between a b, between c d => (c <=? a) && (b <=? d)
    | between a _, right_of c => c <=? a
    | between _ a, left_of c => a <=? c
    | right_of a, right_of c => c <=? a
    | left_of a, left_of c => a <=? c
    | _, _ => false
    end.

Fixpoint ab_le_state s_sharp t_sharp :=
    match s_sharp with
    | nil => true
    | (x, a) :: sl => ab_le (lookup t_sharp x) a && ab_le_state sl t_sharp
    end.


Definition widen a1 a2 :=
    match a1, a2 with
    | bot, a3 | a3, bot => a3
    | right_of a, right_of c | right_of a, between c _ | between a _, right_of c => if a <=? c then right_of a else top
    | between a b, between c d => if a <=? c then
                                    if d <=? b then
                                        between a b
                                    else 
                                        right_of a
                                  else 
                                    if d <=? b then
                                        left_of b
                                    else
                                        top
    | between _ b, left_of d | left_of b, between _ d | left_of b, left_of d => if d <=? b then left_of b else top
    | _, _ => top
    end.

Definition widen_state s_sharp t_sharp :=
    map (fun c : string * AbD => let (x, a) := c in (x, widen a (lookup t_sharp x))) s_sharp.

Definition narrow a1 a2 :=
    match a1, a2 with
    | bot, _ | _, bot => bot
    | top, a3 | a3, top => a3
    | right_of a, right_of _ => right_of a
    | right_of a, between _ d | right_of a, left_of d => between a d
    | between a b, _ => between a b
    | left_of b, right_of c | left_of b, between c _ => between c b
    | left_of b, left_of _ => left_of b
    end.

Definition narrow_state s_sharp t_sharp :=
    map (fun c : string * AbD => let (x, a) := c in (x, narrow a (lookup t_sharp x))) s_sharp.

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
    while_do (bop ne (var "x") (const 0)) (assign "x" (aop add (var "x") (const 1))).

Definition example1_1_state := [("x", lt0)].

Definition example1_2_state := [("x", eq0)].

Definition example1_3_state := [("x", gt0)].



Eval compute in (AI example1_expr false example1_1_state).

Eval compute in (AI example1_expr false example1_2_state).

Eval compute in (AI example1_expr false example1_3_state).


(** 
    Example 2

    x := x + y
    y := y + 1
*)

Definition example2_expr :=
    (sequence (assign "x" (aop add (var "x") (var "y"))) (assign "y" (aop add (var "y") (const 1)))).

Definition example2_state := [("x", le0); ("y", lt0)].

Eval compute in (AI example1_expr false example2_state).



(* Intervals examples *)

Module C := AbstractInterpreter Intervals.
Import Intervals.
Import C.


(** 
    Example 3

    while x >= 0 do
        x := x - 1
        y := y + 1
*)

Definition example3_expr :=
    while_do (bop ge (var "x") (const 0)) (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1)))).

Definition example3_state := [("x", between 10 10); ("y", between 0 0)].


(* Eval compute in (AI example3_expr false example3_state). *)
Eval compute in (AI example3_expr true example3_state).



(** 
    Example 4

    while x < 10 do
        x := x + 1
*)

Definition example4_expr :=
    while_do (bop lt (var "x") (const 10)) (assign "x" (aop add (var "x") (const 1))).

Definition example4_state := [("x", between 0 0)].

Eval compute in (AI example4_expr true example4_state).



(** 
    Example 5

    while x <= 100 do
        x := x + 1
*)

Definition example5_expr :=
    while_do (bop le (var "x") (const 100)) (assign "x" (aop add (var "x") (const 1))).

Definition example5_state := [("x", between 1 1)].

Eval compute in (AI example5_expr false example5_state).
Eval compute in (AI example5_expr true example5_state).

(** 
    Example 6

    x := 0
    while x < 40 do
        x := x + 1
*)

Definition example6_expr :=
    sequence (assign "x" (const 0)) (while_do (bop lt (var "x") (const 40)) (assign "x" (aop add (var "x") (const 1)))).

Eval compute in (AI example6_expr true nil).
Eval compute in (AI example6_expr false nil).


(** 
    Example 7

    i := 1
    while i <= 3 do
        j := 1
        while j <= i do
            j := j + 1
        i := i + 1
*)

Definition nested_while_1_expr :=
    sequence (assign "i" (const 1)) 
             (while_do (bop le (var "i") (const 3)) 
                (sequence (sequence (assign "j" (const 1)) 
                                    (while_do (bop le (var "j") (var "i")) 
                                        (assign "j" (aop add (var "j") (const 1))))) 
                          (assign "i" (aop add (var "i") (const 1))))).

Eval compute in (AI nested_while_1_expr false nil).
Eval compute in (AI nested_while_1_expr true nil).


(** 
    Example 8

    i := 1
    while i <= 4 do
        j := 0
        while j <= 3 do
            k := 0
            while k <= 5 do
                z := i * j * k
                x := x + 1
            j := j + 1
        i := i + 1
*)

Definition nested_while_2_expr :=
    sequence (assign "i" (const 1)) 
             (while_do (bop le (var "i") (const 4)) 
                (sequence (sequence (assign "j" (const 0)) 
                                    (while_do (bop le (var "j") (var "3")) 
                                        (sequence (sequence (assign "k" (const 0)) 
                                                            (while_do (bop le (var "k") (var "5")) 
                                                                (sequence (assign "z" (aop mul (aop mul (var "i") (var "j")) (var "k"))) 
                                                                            (assign "x" (aop add (var "x") (const 1))))))
                                                  (assign "j" (aop add (var "j") (const 1))))))
                          (assign "i" (aop add (var "i") (const 1))))).

(* Eval compute in (AI nested_while_2_expr false nil). *)
Eval compute in (AI nested_while_2_expr true nil).


    
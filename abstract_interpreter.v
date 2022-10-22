From pv Require Export library.
Require Import String ZArith List.
Open Scope Z_scope.
    


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



Module Type AbstractDomain.

Parameter A : Type.
Definition AbState := list (string * A).
Parameter ab_op : ABinOp -> A -> A -> A.
Parameter alpha_singleton : Z -> A.
Parameter ab_opp : A -> A.
Parameter ab_update : AbState -> string -> A -> AbState.
Parameter lookup : AbState -> string -> A.
Parameter eq_sem : Aexp -> Aexp -> AbState -> option AbState.
Parameter lt_sem : Aexp -> Aexp -> AbState -> option AbState.
Parameter gt_sem : Aexp -> Aexp -> AbState -> option AbState.
Parameter le_sem : Aexp -> Aexp -> AbState -> option AbState.
Parameter ge_sem : Aexp -> Aexp -> AbState -> option AbState.
Parameter ne_sem : Aexp -> Aexp -> AbState -> option AbState.
Parameter join : A -> A -> A.
Parameter A_sharp : Aexp -> AbState -> A.
Parameter thinner : A -> A -> bool.
Parameter widen : A -> A -> A.

End AbstractDomain.


Module AbstractInterpreter (AbDom : AbstractDomain).
Import AbDom.



Fixpoint join_state s1_sharp s2_sharp :=
    match s1_sharp with 
    | nil => nil 
    | (x, a) :: sl => ab_update (join_state sl s2_sharp) x (join a (lookup s2_sharp x)) 
    end.
    
Definition join_state' s s' :=
    match s' with
    | Some s' => join_state s s'
    | None => s
    end.

Definition widen_state s s' :=
    map (fun p : string * A => let (x, v) := p in (x, widen v (lookup s' x))) s.
    
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

Definition step1 AI_state b s_sharp t_sharp :=
    match B_sharp b t_sharp with
    | Some u_sharp => join_state' s_sharp (AI_state u_sharp)
    | None => s_sharp
    end.

Fixpoint s_stable s_sharp t_sharp :=
    match s_sharp with
    | nil => true
    | (x, a) :: sl => thinner (lookup t_sharp x) a && s_stable sl t_sharp
    end.

Definition is_inv AI_state s_sharp t_sharp b := s_stable t_sharp (step1 AI_state b s_sharp t_sharp).

Fixpoint step2 AI_state (b : Bexp) s_sharp t_sharp (n : nat) :=
    match n with 
    | 0%nat => t_sharp
    | S m => if is_inv AI_state s_sharp t_sharp b
                then t_sharp
             else 
                step2 AI_state b s_sharp (step1 AI_state b s_sharp t_sharp) m
    end.

Fixpoint widening AI_state b s_sharp t_sharp n :=
    match n with 
    | 0%nat => t_sharp
    | S m => if is_inv AI_state s_sharp t_sharp b
                then t_sharp
            else 
                widening AI_state b s_sharp (widen_state t_sharp (step1 AI_state b s_sharp t_sharp)) m
    end.

Definition find_inv AI_state b s_sharp n_iter n_widen :=
    let s' := step2 AI_state b s_sharp s_sharp n_iter in
    if is_inv AI_state s_sharp s' b then 
        s' 
    else
        widening AI_state b s_sharp s_sharp n_widen.

Fixpoint AI (P : While) s_sharp :=
    match P with
    | assign x e => Some (ab_update s_sharp x (A_sharp e s_sharp))
    | skip => Some s_sharp
    | sequence S1 S2 => match AI S1 s_sharp with
                    | Some t_sharp => AI S2 t_sharp
                    | None => None
                    end
    | if_then_else b S1 S2 => match B_sharp b s_sharp, B_sharp (neg_sem b) s_sharp with
                            | Some t_sharp, Some u_sharp => match AI S1 t_sharp with
                                                            | Some v_sharp => Some (join_state' v_sharp (AI S2 u_sharp))
                                                            | None => AI S2 u_sharp
                                                            end
                            | Some t_sharp, None => AI S1 t_sharp
                            | None, Some u_sharp => AI S2 u_sharp
                            | None, None => None 
                            end
    | while_do b S' => let inv := (find_inv (AI S') b s_sharp 3 3) in B_sharp (neg_sem b) inv
    end.

End AbstractInterpreter.



Module ExtendedSign <: AbstractDomain.

Inductive extended_sign :=
    | Top
    | LeZero
    | NeZero
    | GeZero
    | LtZero
    | EqZero
    | GtZero
    | Bot.

Definition A := extended_sign.

Definition AbState := list (string * A).

Fixpoint ab_update s_sharp x a : AbState :=
    match s_sharp with 
    | nil => (x, a) :: nil
    | (y, a') :: sl => if string_dec x y then (y, a) :: sl else (y, a') :: ab_update sl x a
    end.

Fixpoint lookup s_sharp x :=
    match s_sharp with
    | nil => Top
    | (y, a) :: sl => if string_dec x y then a else lookup sl x
    end.

Definition alpha_singleton n :=
    if n =? 0 then EqZero
    else if n <? 0 then LtZero
        else GtZero.


Definition opp_sem a :=
    match a with
    | LtZero => GtZero
    | GtZero => LtZero
    | LeZero => GeZero
    | GeZero => LeZero
    | a' => a'
    end.

Definition add_op a1 a2 :=
    match a1, a2 with
    | Bot, _ => Bot
    | _, Bot => Bot
    | EqZero, a3 => a3
    | a3, EqZero => a3
    | LtZero, LtZero => LtZero
    | LtZero, LeZero => LtZero
    | GtZero, GtZero => GtZero
    | GtZero, GeZero => GtZero
    | LeZero, LeZero => LeZero
    | GeZero, GeZero => GeZero
    | _, _ => Top
    end.

Definition sub_op a1 a2 :=
    match a1, a2 with
    | Bot, _ => Bot
    | _, Bot => Bot
    | EqZero, a3 => opp_sem a3
    | a3, EqZero => a3
    | LtZero, GtZero => LtZero
    | LtZero, GeZero => LtZero
    | GtZero, LtZero => GtZero
    | GtZero, LeZero => GtZero
    | LeZero, GtZero => LtZero
    | LeZero, GeZero => LeZero
    | GeZero, LtZero => GtZero
    | GeZero, LeZero => GeZero
    | _, _ => Top
    end.

Definition mul_op a1 a2 :=
    match a1, a2 with
    | Bot, _ => Bot
    | _, Bot => Bot
    | EqZero, _ => EqZero
    | _, EqZero => EqZero
    | LtZero, LtZero => GtZero
    | LtZero, GtZero => LtZero
    | LtZero, LeZero => GeZero
    | LtZero, GeZero => LeZero
    | LtZero, NeZero => NeZero
    | GtZero, LtZero => LtZero
    | LeZero, LtZero => GeZero
    | GeZero, LtZero => LeZero
    | NeZero, LtZero => NeZero
    | GtZero, GtZero => GtZero
    | GtZero, LeZero => LeZero
    | GtZero, GeZero => GeZero
    | GtZero, NeZero => NeZero
    | LeZero, GtZero => LeZero
    | GeZero, GtZero => GeZero
    | NeZero, GtZero => NeZero
    | LeZero, LeZero => GeZero
    | LeZero, GeZero => LeZero
    | GeZero, GeZero => GeZero
    | NeZero, NeZero => NeZero
    | _, _ => Top
    end.

Definition div_op a1 a2 :=
    match a1, a2 with
    | Bot, _ => Bot
    | _, Bot => Bot
    | EqZero, _ => EqZero
    | _, EqZero => EqZero
    | LtZero, LtZero => GtZero
    | LtZero, GtZero => LtZero
    | LtZero, LeZero => GeZero
    | LtZero, GeZero => LeZero
    | LtZero, NeZero => NeZero
    | GtZero, LtZero => LtZero
    | LeZero, LtZero => GeZero
    | GeZero, LtZero => LeZero
    | NeZero, LtZero => NeZero
    | GtZero, GtZero => GtZero
    | GtZero, LeZero => LeZero
    | GtZero, GeZero => GeZero
    | GtZero, NeZero => NeZero
    | LeZero, GtZero => LeZero
    | GeZero, GtZero => GeZero
    | NeZero, GtZero => NeZero
    | LeZero, LeZero => GeZero
    | LeZero, GeZero => LeZero
    | GeZero, GeZero => GeZero
    | NeZero, NeZero => NeZero
    | _, _ => Top
    end.

(* FINIRE E SISTEMARE SOTTRAZIONE

Definition by_sign a1 a2 :=
    match a1, a2 with
    | Bot, _ => Bot
    | _, Bot => Bot
    | _, EqZero => Bot
    | EqZero, _ => EqZero
    | a3, GtZero => a3
    | a3, GeZero => a3
    | LtZero

    | LtZero, LtZero => GtZero
    | LtZero, GtZero => LtZero
    | LtZero, LeZero => GeZero
    | LtZero, GeZero => LeZero
    | LtZero, NeZero => NeZero
    | GtZero, LtZero => LtZero
    | LeZero, LtZero => GeZero
    | GeZero, LtZero => LeZero
    | NeZero, LtZero => NeZero
    | GtZero, GtZero => GtZero
    | GtZero, LeZero => LeZero
    | GtZero, GeZero => GeZero
    | GtZero, NeZero => NeZero
    | LeZero, GtZero => LeZero
    | GeZero, GtZero => GeZero
    | NeZero, GtZero => NeZero
    | LeZero, LeZero => GeZero
    | LeZero, GeZero => LeZero
    | GeZero, GeZero => GeZero
    | NeZero, NeZero => NeZero
    | _, _ => Top
    end.
*)

Definition op_sem op a1 a2 :=
    match op with
    | add => add_op a1 a2
    | sub => sub_op a1 a2
    | mul => mul_op a1 a2
    | div => div_op a1 a2
    end.

Fixpoint A_sharp e s_sharp :=
match e with
| var x => lookup s_sharp x
| const n => alpha_singleton n
| aop op e1 e2 => op_sem op (A_sharp e1 s_sharp) (A_sharp e2 s_sharp)
| opp e' => opp_sem (A_sharp e' s_sharp)
end.

(**

        *)

Definition eq_sem e1 e2 s_sharp :=
    match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
    | Bot, _ | _, Bot | EqZero, LtZero | EqZero, GtZero | LtZero, EqZero | GtZero, EqZero => None
    | _, _ => Some s_sharp
    end.
        
        Definition ne_sem e1 e2 s_sharp :=
            match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | Bot, _ | _, Bot | EqZero, EqZero => None
            | _, _ => Some s_sharp
            end.
        
            Definition lt_sem e1 e2 s_sharp :=
                match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                | Bot, _ | _, Bot | EqZero, EqZero => None
                | _, _ => Some s_sharp
                end.
        
                Definition gt_sem e1 e2 s_sharp :=
                    match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                    | Bot, _ | _, Bot | EqZero, EqZero => None
                    | _, _ => Some s_sharp
                    end.
        
                    Definition le_sem e1 e2 s_sharp :=
                        match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                        | Bot, _ | _, Bot | EqZero, EqZero => None
                        | _, _ => Some s_sharp
                        end.
        
                        Definition ge_sem e1 e2 s_sharp :=
                            match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
                            | Bot, _ | _, Bot | EqZero, EqZero => None
                            | _, _ => Some s_sharp
                            end.

                            Definition sign_eq_dec : forall (x y : A), { x = y } + { x <> y }.
                            Proof.
                            decide equality.
                            Defined.


                            Definition join a1 a2 :=
                                match a1, a2 with
                                | Bot,  a3 |  a3,  Bot =>  a3
                                | EqZero,  LtZero |  LtZero,  EqZero 
                                | EqZero,  LeZero |  LeZero,  EqZero
                                | LtZero,  LeZero |  LeZero,  LtZero =>  LeZero
                                | EqZero,  GtZero |  GtZero,  EqZero 
                                | EqZero,  GeZero |  GeZero,  EqZero
                                | GtZero,  GeZero |  GeZero,  GtZero =>  GeZero
                                | LtZero,  GtZero |  GtZero,  LtZero
                                | LtZero,  NeZero |  NeZero,  LtZero
                                | GtZero,  NeZero |  NeZero,  GtZero =>  NeZero
                                | a3, a4 => if sign_eq_dec a3 a4 then  a3 else Top
                                end.

Definition thinner a1 a2 :=
    match a1, a2 with 
    | Bot, _ | _, Top
    | EqZero, GeZero | EqZero, LeZero
    | LtZero, LeZero | LtZero, NeZero
    | GtZero, GeZero | GtZero, NeZero => true 
    | a3, a4 => if sign_eq_dec a3 a4 then true else false
    end.

Definition widen a1 a2 := join a1 a2.


End ExtendedSign.



Module Intervals <: AbstractDomain.

Inductive Interval : Type :=
| LeftBound : Z -> Interval
| RightBound : Z -> Interval
| Bounded : Z -> Z -> Interval
| IntTop : Interval
| IntBot : Interval.

Definition A := Interval.

Definition AbState := list (string * A). 

Fixpoint ab_update s_sharp x a : AbState :=
    match s_sharp with 
    | nil => (x, a) :: nil
    | (y, a') :: sl => if string_dec x y then (y, a) :: sl else (y, a') :: ab_update sl x a
    end.

Fixpoint lookup s_sharp x :=
    match s_sharp with
    | nil => IntTop
    | (y, a) :: sl => if string_dec x y then a else lookup sl x
    end.

Definition alpha_singleton n := Bounded n n.


Definition add_op a1 a2 :=
    match a1, a2 with
    | LeftBound m, LeftBound n => LeftBound (m + n) 
    | LeftBound m, Bounded n p => LeftBound (m + n)
    | RightBound m, RightBound n => RightBound (m + n)
    | Bounded a b, Bounded c d => Bounded (a + c) (b + d)
    | _, _ => IntTop
    end.
    
Definition sub_op a1 a2 :=
    match a1, a2 with
    | LeftBound m, LeftBound n => LeftBound (m + n) 
    | LeftBound m, Bounded n p => LeftBound (m + n)
    | RightBound m, RightBound n => RightBound (m + n)
    | Bounded a b, Bounded c d => Bounded (a - d) (b - c)
    | _, _ => IntTop
    end.

Definition mul_op a1 a2 :=
    match a1, a2 with
    | LeftBound m, LeftBound n => LeftBound (m + n) 
    | LeftBound m, Bounded n p => LeftBound (m + n)
    | RightBound m, RightBound n => RightBound (m + n)
    | _, _ => IntTop
    end.

Definition div_op a1 a2 :=
    match a1, a2 with
    | LeftBound m, LeftBound n => LeftBound (m + n) 
    | LeftBound m, Bounded n p => LeftBound (m + n)
    | RightBound m, RightBound n => RightBound (m + n)
    | _, _ => IntTop
    end.

Definition operation op a1 a2 :=
    match op with
    | add => add_op a1 a2
    | sub => sub_op a1 a2
    | mul => mul_op a1 a2
    | div => div_op a1 a2
    end.

Definition opposite a :=
    match a with
    | LeftBound n => RightBound (-n)
    | RightBound n => LeftBound (-n)
    | Bounded m n => Bounded (-n) (-m)
    | IntTop => IntTop
    | IntBot => IntBot
    end.

Fixpoint A_sharp e s_sharp :=
    match e with
    | var x => lookup s_sharp x
    | const n => alpha_singleton n
    | aop op e1 e2 => operation op (A_sharp e1 s_sharp) (A_sharp e2 s_sharp)
    | opp e' => opposite (A_sharp e' s_sharp)
    end.

Definition eq_sem e1 e2 s_sharp := 
    match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
    | IntBot, IntTop => None
    | _, _ => Some s_sharp
    end.
        
Definition ne_sem e1 e2 s_sharp := 
    match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
    | IntBot, IntTop => None
    | _, _ => Some s_sharp
    end.
    
Definition lt_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match lookup s_sharp x, A_sharp e2 s_sharp with
                | IntBot, _ | _, IntBot => None
                | Bounded a b, Bounded _ d | Bounded a b, RightBound d => if a >=? d then None else 
                                                                         if b >=? d then Some (ab_update s_sharp x (Bounded a (d - 1)))
                                                                         else Some s_sharp
                | LeftBound a, Bounded _ d | LeftBound a, RightBound d => if a >=? d then None else Some (ab_update s_sharp x (Bounded a (d - 1)))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | IntBot, _ | _, IntBot => None
            | Bounded a _, Bounded _ d | Bounded a _, RightBound d
            | LeftBound a, Bounded _ d | LeftBound a, RightBound d  => if a <? d then Some s_sharp else None
            | _, _ => Some s_sharp
            end
    end.


Definition gt_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match lookup s_sharp x, A_sharp e2 s_sharp with
                | IntBot, _ | _, IntBot => None
                | Bounded a b, Bounded c _ | Bounded a b, LeftBound c => if b <=? c then None else 
                                                                         if a <=? c then Some (ab_update s_sharp x (Bounded (c + 1) b))
                                                                         else Some s_sharp
                | RightBound b, Bounded c _ | RightBound b, LeftBound c => if b <=? c then None else Some (ab_update s_sharp x (Bounded (c + 1) b))
                | LeftBound a, Bounded c _ | LeftBound a, LeftBound c => if a <=? c then Some (ab_update s_sharp x (LeftBound (c + 1))) else Some s_sharp
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | IntBot, _ | _, IntBot => None
            | Bounded _ b, Bounded c _ | Bounded _ b, LeftBound c
            | RightBound b, Bounded c _ | RightBound b, LeftBound c  => if b <=? c then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Definition le_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match lookup s_sharp x, A_sharp e2 s_sharp with
                | IntBot, _ | _, IntBot => None
                | Bounded a b, Bounded _ d | Bounded a b, RightBound d => if d <? a then None else 
                                                                         if d <? b then Some (ab_update s_sharp x (Bounded a d))
                                                                         else Some s_sharp
                | LeftBound a, Bounded _ d | LeftBound a, RightBound d => if d <? a then None else Some (ab_update s_sharp x (Bounded a d))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | IntBot, _ | _, IntBot => None
            | Bounded a _, Bounded _ d | Bounded a _, RightBound d
            | LeftBound a, Bounded _ d | LeftBound a, RightBound d  => if d <? a then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Definition ge_sem e1 e2 s_sharp := 
    match e1 with
    | var x => match lookup s_sharp x, A_sharp e2 s_sharp with
                | IntBot, _ | _, IntBot => None
                | Bounded a b, Bounded c _ | Bounded a b, LeftBound c => if b <? c then None else 
                                                                         if a <? c then Some (ab_update s_sharp x (Bounded c b))
                                                                         else Some s_sharp
                | RightBound b, Bounded c _ | RightBound b, LeftBound c => if b <? c then None else Some (ab_update s_sharp x (Bounded c b))
                | _, _ => Some s_sharp
                end
    | _ =>  match A_sharp e1 s_sharp, A_sharp e2 s_sharp with
            | IntBot, _ | _, IntBot => None
            | Bounded _ b, Bounded c _ | Bounded _ b, LeftBound c
            | RightBound b, Bounded c _ | RightBound b, LeftBound c  => if b <? c then None else Some s_sharp
            | _, _ => Some s_sharp
            end
    end.

Definition join a1 a2 :=
    match a1, a2 with
    | Bounded a b, Bounded c d => Bounded (Z.min a c) (Z.max b d)
    | _, _ => IntBot
    end.

Definition thinner a1 a2 :=
    match a1, a2 with 
    | IntBot, _ | _, IntTop => true
    | Bounded a b, Bounded c d => (c <=? a) && (b <=? d)
    | Bounded a _, LeftBound c => c <=? a
    | Bounded _ a, RightBound c => a <=? c
    | LeftBound a, LeftBound c => c <=? a
    | RightBound a, RightBound c => a <=? c
    | _, _ => false
    end.

Definition widen a1 a2 :=
    match a1, a2 with
    | Bounded a b, Bounded c d => if a <=? c then
                                    if d <=? b then
                                        Bounded a b
                                    else 
                                        LeftBound a
                                  else 
                                    if d <=? b then
                                        RightBound b
                                    else
                                        IntTop
    | _, _ => IntTop
    end.

End Intervals.



Module B := AbstractInterpreter ExtendedSign.
Import ExtendedSign.
Import B.
Definition example3_expr :=
    while_do (bop ne (var "x") (const 0)) (assign "x" (aop add (var "x") (const 1))).

Definition example3_state := [("x", LtZero)].

Definition example4_state := [("x", EqZero)].

Definition example5_state := [("x", GtZero)].

Compute 3+1.

Compute (AI example3_expr example3_state).

Compute (AI example3_expr example4_state).

Compute (AI example3_expr example5_state).



Module C := AbstractInterpreter Intervals.

Import Intervals.
Import C.

Definition example6_expr :=
    while_do (bop ge (var "x") (const 0)) (sequence (assign "x" (aop sub (var "x") (const 1))) (assign "y" (aop add (var "y") (const 1)))).

Definition example6_state := [("x", Bounded 10 10); ("y", Bounded 0 0)].

Compute 3+1.

Compute (AI example6_expr example6_state).


Definition example7_expr :=
    while_do (bop lt (var "x") (const 10)) (assign "x" (aop add (var "x") (const 1))).

Definition example7_state := [("x", Bounded 0 0)].

Compute (AI example7_expr example7_state).


Definition example8_expr :=
    while_do (bop le (var "x") (const 100)) (assign "x" (aop add (var "x") (const 1))).

Definition example8_state := [("x", Bounded 1 1)].

Compute (AI example8_expr example8_state).

Compute (is_inv (AI (assign "x" (aop add (var "x") (const 1)))) example8_state [("x", Bounded 1 101)] (bop le (var "x") (const 100))).

Compute step1 (AI (assign "x" (aop add (var "x") (const 1)))) (bop le (var "x") (const 100)) example8_state [("x", Bounded 1 101)].

Compute s_stable [("x", Bounded 1 101)] [("x", Bounded 1 101)].


Definition example9_expr :=
    sequence (assign "x" (const 0)) (while_do (bop lt (var "x") (const 40)) (assign "x" (aop add (var "x") (const 1)))).

Compute (AI example9_expr nil).

Compute (is_inv (AI (assign "x" (aop add (var "x") (const 1)))) example8_state [("x", Bounded 1 101)] (bop le (var "x") (const 100))).

Compute step1 (AI (assign "x" (aop add (var "x") (const 1)))) (bop le (var "x") (const 100)) example8_state [("x", Bounded 1 101)].

Compute s_stable [("x", Bounded 1 101)] [("x", Bounded 1 101)].








(**


    
    
Definition example1_expr :=
    AOp Plus (AOp Times (Const 2) (Var "y")) (AOp Times (Const 3) (Var "x")).

Definition example1_state := [("x", LtZero); ("y", LtZero)].

Compute abstract_semantics_A example1_expr example1_state.


Definition example2_expr :=
    AOp Minus (AOp Times (Var "x") (Var "y")) (AOp Times (Const 2) (Var "z")).

Definition example2_state := [("x", LtZero); ("y", LtZero); ("z", GtZero)].
        
Compute abstract_semantics_A example2_expr example2_state.




    




(* FINIRE CASI *)










    



Fixpoint neg_sem b :=
    match b with
    | TT => FF
    | FF => TT
    | BOp Eq e1 e2 => BOp Neq e1 e2
    | BOp Lt e1 e2 => BOp Ge e1 e2
    | BOp Gt e1 e2 => BOp Le e1 e2
    | BOp Le e1 e2 => BOp Gt e1 e2
    | BOp Ge e1 e2 => BOp Lt e1 e2
    | BOp Neq e1 e2 => BOp Eq e1 e2
    | And b1 b2 => Or (neg_sem b1) (neg_sem b2)
    | Or b1 b2 => And (neg_sem b1) (neg_sem b2)
    end.

Fixpoint abstract_semantics_B (b : Bexp) (s_sharp : AbstractState) : option AbstractState :=
    match b with
    | TT => Some s_sharp
    | FF => None
    | BOp op e1 e2 => match op with 
                        | Eq => eq_sem e1 e2 s_sharp
                        | Lt => lt_sem e1 e2 s_sharp
                        | Gt => gt_sem e1 e2 s_sharp
                        | Le => le_sem e1 e2 s_sharp
                        | Ge => ge_sem e1 e2 s_sharp
                        | Neq => neq_sem e1 e2 s_sharp
                        end
    | And b1 b2 => match abstract_semantics_B b1 s_sharp with
                    | Some t_sharp => abstract_semantics_B b2 t_sharp
                    | None => None
                    end
    | Or b1 b2 => match abstract_semantics_B b1 s_sharp with 
                    | Some t_sharp => Some (join_state' t_sharp (abstract_semantics_B b2 s_sharp))
                    | None => abstract_semantics_B b2 s_sharp
                    end
    end. 

Definition n_iter_Kleene_chain := 3.




End Sign.
    




Definition example3_expr :=
    WhileDo (BOp Neq (Var "x") (Const 0)) (Assign "x" (AOp Plus (Var "x") (Const 1))).

Definition example3_state := [("x", LtZero)].

Definition example4_state := [("x", EqZero)].

Definition example5_state := [("x", GtZero)].

Compute 3+1.

Compute (AI example3_expr example3_state).

Compute (AI example3_expr example4_state).

Compute (AI example3_expr example5_state).


     *)       









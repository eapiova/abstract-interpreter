From pv Require Import library.
Require Import String ZArith List Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

From ReductionEffect Require Import PrintingEffect.

Require Coq.extraction.Extraction.
Extraction Language OCaml.





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

Notation "v1 + v2" := (aop add v1 v2).
Notation "v1 ≠ v2" := (bop ne v1 v2).





(* Abstract Domain structure *)

Module Type AbstractDomain.

Parameter AbD : Type.
Definition AbM := string -> AbD.
Parameter top_AbM : AbM.
Parameter bot_AbM : AbM.

Parameter ab_update : AbM -> string -> AbD -> AbM.
Parameter alpha_singleton : Z -> AbD.
Parameter ab_opp : AbD -> AbD.
Parameter ab_op : ABinOp -> AbD -> AbD -> AbD.
Parameter AbsEval : Aexp -> AbM -> AbD.

Parameter eq_sem : Aexp -> Aexp -> AbM -> AbM.
Parameter ne_sem : Aexp -> Aexp -> AbM -> AbM.
Parameter lt_sem : Aexp -> Aexp -> AbM -> AbM.
Parameter gt_sem : Aexp -> Aexp -> AbM -> AbM.
Parameter le_sem : Aexp -> Aexp -> AbM -> AbM.
Parameter ge_sem : Aexp -> Aexp -> AbM -> AbM.

Parameter join : AbD -> AbD -> AbD.
Parameter join_mem : AbM -> AbM -> AbM.
Parameter ab_po : AbD -> AbD -> bool.
Parameter ab_po_mem : list string -> AbM -> AbM -> bool.
Parameter widen : AbD -> AbD -> AbD.
Parameter widen_mem : AbM -> AbM -> AbM.
Parameter narrow : AbD -> AbD -> AbD.
Parameter narrow_mem : AbM -> AbM -> AbM.

End AbstractDomain.





(* Abstract Interpreter function *)

Module AbstractInterpreter (AbDom : AbstractDomain).
Import AbDom.

Definition vars := ["x";"y";"i";"j";"k"].

Fixpoint B_sharp b m :=
    match b with
    | tt => m
    | ff => bot_AbM
    | bop op e1 e2 => match op with 
                        | eq => eq_sem e1 e2 m
                        | lt => lt_sem e1 e2 m
                        | gt => gt_sem e1 e2 m
                        | le => le_sem e1 e2 m
                        | ge => ge_sem e1 e2 m
                        | ne => ne_sem e1 e2 m
                        end
    | and b1 b2 => B_sharp b2 (B_sharp b1 m)
    | or b1 b2 => join_mem (B_sharp b1 m) (B_sharp b2 m)
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

Definition step (AI_state : AbM -> AbM * list AbM) b m1 t_sharp :=
    let (v_sharp, invs) := (AI_state (B_sharp b t_sharp)) in (join_mem m1 v_sharp, invs).

Definition is_inv AI_state m1 m2 b := let (m3, _) := step AI_state b m1 m2 in ab_po_mem vars m2 m3.

Unset Guard Checking.

Fixpoint steps AI_state (b : Bexp) m t_sharp {struct b} :=
    if is_inv AI_state m t_sharp b
        then (t_sharp, [t_sharp])
    else 
        let (u_sharp, invs1) := print_id (step AI_state b m t_sharp) in let (v_sharp, invs2) := steps AI_state b m u_sharp in (v_sharp, invs1 ++ invs2).   
    

Fixpoint widening AI_state b m t_sharp {struct b} :=
    if is_inv AI_state m t_sharp b
        then t_sharp
    else 
        let (u_sharp, _) := print_id (step AI_state b m t_sharp) in widening AI_state b m (widen_mem t_sharp u_sharp).

Fixpoint narrowing AI_state b m t_sharp {struct b} :=
    let (u_sharp, _) := print_id (step AI_state b m t_sharp) in let v_sharp := narrow_mem t_sharp u_sharp in
    if is_inv AI_state m v_sharp b
        then (v_sharp, [v_sharp])
    else 
        let (w_sharp, invs1) := print_id (step AI_state b m v_sharp) in let (z_sharp, invs2) := narrowing AI_state b m (narrow_mem v_sharp w_sharp) in (z_sharp, invs1 ++ invs2).

Set Guard Checking.

Definition ab_lfp AI_state b m (widen_toggle : bool) :=
    if widen_toggle then let t_sharp := widening AI_state b m m in narrowing AI_state b m t_sharp
    else steps AI_state b m m.

Fixpoint AI (P : While) widen_toggle m :=
    match P with
    | assign x e => ((ab_update m x (AbsEval e m)), nil)
    | skip => (m, nil)
    | sequence S1 S2 => let (t_sharp, invs1) := AI S1 widen_toggle m in let (u_sharp, invs2) := AI S2 widen_toggle t_sharp in (u_sharp, invs1 ++ invs2)
    | if_then_else b S1 S2 => let (t_sharp, invs1) := AI S1 widen_toggle (B_sharp b m) in let (u_sharp, invs2) := AI S2 widen_toggle (B_sharp (neg_sem b) m) in (join_mem t_sharp u_sharp, invs1 ++ invs2)
    | while_do b S' => let (t_sharp, invs) := (ab_lfp (AI S' widen_toggle) b m widen_toggle) in (B_sharp (neg_sem b) t_sharp, invs)
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
Definition AbM := string -> extended_sign.


Definition top_AbM : AbM := fun x => ⊤.
Definition bot_AbM : AbM := fun x => ⊥.

Definition alpha_singleton z :=
    if z =? 0 then =0
    else if z <? 0 then <0
    else >0.

Notation "z ♯" := (alpha_singleton z).

Definition ab_opp v :=
    match v with
    | <0 => >0
    | >0 => <0
    | ≤0 => ≥0
    | ≥0 => ≤0
    | v' => v'
    end.

Notation "- ♯ v" := (ab_opp v).

Definition sign_eq_dec : forall (x y : AbD), { x = y } + { x <> y }.
Proof.
    decide equality.
Defined.

Infix "=?" := sign_eq_dec.

Definition eqb_extended_sign (v1 v2 : extended_sign) : bool :=
  match v1 =? v2 with
  | left _  => true
  | right _ => false
  end.


Definition add_op v1 v2 :=
    match v1, v2 with
    | ⊥, _ | _, ⊥ => ⊥
    | =0, v3 | v3, =0 => v3
    | <0, ≤0 | ≤0, <0 => <0
    | >0, ≥0 | ≥0, >0 => >0
    | ≠0, ≠0 => ⊤
    | v3, v4 => if v3 =? v4 then v3 else ⊤
    end.

Definition sub_op v1 v2 :=
    match v1, v2 with
    | ⊥, _ => ⊥
    | _, ⊥ => ⊥
    | =0, v3 => -♯v3
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
    | <0, v3 | v3, <0 => -♯v3
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

Infix "+♯" := add_op (at level 40).
Infix "-♯" := sub_op (at level 40).
Infix "*♯" := mul_op (at level 40).
Infix "/♯" := div_op (at level 40).


Definition ab_update
           m 
           (x : string)
           (v : extended_sign)
  :=
  fun y =>
    if string_dec x y then v else m y.

Notation "m { x ↤ v }" := (ab_update m x v).

Definition ab_op op v1 v2 :=
    match op with
    | add => add_op v1 v2
    | sub => sub_op v1 v2
    | mul => mul_op v1 v2
    | div => div_op v1 v2
    end.

Fixpoint AbsEval e m :=
    match e with
    | var x => m x
    | const n => n♯
    | aop op e1 e2 => ab_op op (AbsEval e1 m) (AbsEval e2 m)
    | opp e' => ab_opp (AbsEval e' m)
    end.

Definition eq_sem e1 e2 m :=
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ 
                | =0, <0 | =0, >0 | <0, =0 | >0, =0 | <0, >0 | >0, <0 
                | <0, ≥0 | ≥0, <0 | =0, ≠0 | ≠0, =0 | >0, ≤0 | ≤0, >0 => bot_AbM
                | ≤0, <0 | ≠0, <0 | ≠0, ≤0 | ≤0, ≠0 => m{x↤<0}
                | ≤0, =0 | ≥0, =0 | ≥0, ≤0 | ≤0, ≥0 => m{x↤=0}
                | ≠0, >0 | ≥0, >0 | ≥0, ≠0 | ≠0, ≥0 => m{x↤>0}
                | ⊤, v => m{x↤v}
                | _, _ => m
                end
    | _ => match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ 
            | =0, <0 | =0, >0 | <0, =0 | >0, =0 | <0, >0 | >0, <0 
            | <0, ≥0 | ≥0, <0 | =0, ≠0 | ≠0, =0 | >0, ≤0 | ≤0, >0 => bot_AbM
            | _, _ => m
            end
    end.
        
Definition ne_sem e1 e2 m :=
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ | =0, =0 => bot_AbM
                | ≤0, =0 =>  (ab_update m x <0)
                | ≥0, =0 =>  (ab_update m x >0)
                | ⊤, =0 =>  (ab_update m x ≠0)
                | _, _ =>  m
                end
    | _ => match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ | =0, =0 => bot_AbM
            | _, _ =>  m
            end
    end.

Definition lt_sem e1 e2 m :=
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ 
                | =0, <0 | =0, =0 | =0, ≤0
                | >0, <0 | >0, =0 | >0, ≤0
                | ≥0, <0 | ≥0, =0 | ≥0, ≤0 => bot_AbM
                | ≤0, <0 | ≤0, =0 | ≤0, ≤0
                | ≠0, <0 | ≠0, =0 | ≠0, ≤0
                | ⊤, <0 | ⊤, =0 | ⊤, ≤0 => (ab_update m x <0)
                | _, _ =>  m
                end
    | _ => match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ 
            | =0, <0 | =0, =0 | =0, ≤0
            | >0, <0 | >0, =0 | >0, ≤0
            | ≥0, <0 | ≥0, =0 | ≥0, ≤0 => bot_AbM
            | _, _ =>  m
            end
    end.

Definition gt_sem e1 e2 m :=
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ 
                | =0, >0 | =0, =0 | =0, ≥0
                | <0, >0 | <0, =0 | <0, ≥0
                | ≤0, >0 | ≤0, =0 | ≤0, ≥0 => bot_AbM
                | ≥0, >0 | ≥0, =0 | ≥0, ≥0
                | ≠0, >0 | ≠0, =0 | ≠0, ≥0
                | ⊤, >0 | ⊤, =0 | ⊤, ≥0 =>  (ab_update m x >0)
                | _, _ =>  m
                end
    | _ => match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ 
            | =0, >0 | =0, =0 | =0, ≥0
            | <0, >0 | <0, =0 | <0, ≥0
            | ≤0, >0 | ≤0, =0 | ≤0, ≥0 => bot_AbM
            | _, _ =>  m
            end
    end.

Definition le_sem e1 e2 m :=
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ 
                | =0, <0 
                | >0, <0 | >0, =0 | >0, ≤0
                | ≥0, <0 => bot_AbM
                | ≤0, <0 
                | ≠0, <0 | ≠0, =0 | ≠0, ≤0
                | ⊤, <0 =>  (ab_update m x <0)
                | ≥0, =0 | ≥0, ≤0 =>  (ab_update m x =0)
                | ⊤, =0 | ⊤, ≤0 =>  (ab_update m x ≤0)
                | _, _ =>  m
                end
    | _ => match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ 
            | =0, <0
            | >0, <0 | >0, =0 | >0, ≤0
            | ≥0, <0 => bot_AbM
            | _, _ =>  m
            end
    end.

Definition ge_sem e1 e2 m :=
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ 
                | =0, >0 
                | <0, >0 | <0, =0 | <0, ≥0
                | ≤0, >0 => bot_AbM
                | ≥0, >0 
                | ≠0, >0 | ≠0, =0 | ≠0, ≥0
                | ⊤, >0 =>  (ab_update m x >0)
                | ≤0, =0 | ≤0, ≥0 =>  (ab_update m x =0)
                | ⊤, =0 | ⊤, ≥0 =>  (ab_update m x ≥0)
                | _, _ =>  m
                end
    | _ => match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ 
            | =0, >0
            | <0, >0 | <0, =0 | <0, ≥0
            | ≤0, >0 => bot_AbM
            | _, _ =>  m
            end
    end.

Definition join v1 v2 :=
    match v1, v2 with
    | ⊥,  v3 |  v3,  ⊥ =>  v3
    | =0,  <0 |  <0,  =0 
    | =0,  ≤0 |  ≤0,  =0
    | <0,  ≤0 |  ≤0,  <0 =>  ≤0
    | =0,  >0 |  >0,  =0 
    | =0,  ≥0 |  ≥0,  =0
    | >0,  ≥0 |  ≥0,  >0 =>  ≥0
    | <0,  >0 |  >0,  <0
    | <0,  ≠0 |  ≠0,  <0
    | >0,  ≠0 |  ≠0,  >0 =>  ≠0
    | v3, v4 => if sign_eq_dec v3 v4 then v3 else ⊤
    end.

Infix "∪" := join (at level 40).

Definition join_mem m1 m2 : AbM := fun x => (m1 x) ∪ (m2 x).
Infix "∪♯" := join_mem (at level 40).

Definition ab_po (v1 v2 : extended_sign) : bool :=
  eqb_extended_sign (join v1 v2) v2.

Infix "⊆" := ab_po (at level 40).

Definition ab_po_mem (vars : list string) (m1 m2 : AbM) : bool :=
  forallb (fun x => ab_po (m1 x) (m2 x)) vars.

Definition widen v1 v2 := join v1 v2.
Infix "∇" := widen (at level 40).

Definition widen_mem m1 m2 : AbM := fun x => (m1 x) ∇ (m2 x).
Infix "∇♯" := widen_mem (at level 40).

Definition narrow (v1 v2 : AbD) := 
    match v1, v2 with
    | ⊤,  v3 |  v3,  ⊤ => v3
    | ≠0,  <0 |  <0,  ≠0 
    | ≠0,  ≤0 |  ≤0,  ≠0
    | <0,  ≤0 |  ≤0,  <0 =>  <0
    | ≠0,  >0 |  >0,  ≠0 
    | ≠0,  ≥0 |  ≥0,  ≠0
    | >0,  ≥0 |  ≥0,  >0 =>  >0
    | ≤0,  ≥0 |  ≥0,  ≤0
    | ≤0,  =0 |  =0,  ≤0
    | ≥0,  =0 |  =0,  ≥0 =>  =0
    | v3, v4 => if sign_eq_dec v3 v4 then v3 else ⊥
    end.

Definition narrow_mem m1 m2 := fun x : string => narrow (m1 x) (m2 x).
(**
    match m with
    | None => bot_AbM
    | Some l => Some (map (fun c : string * AbD => let (x, a) := c in (x, narrow a (ab_lookup t_sharp x))) l)
    end.
*)

End ExtendedSign.



(* Intervals domain *)

Module Intervals <: AbstractDomain.

(** Extended integers: -∞, finite z, +∞. *)
Inductive eZ : Type :=
  | NegInf
  | Fin (z : Z)
  | PosInf.

Definition buildFin z := Fin z.
Coercion buildFin : Z >-> eZ.

(** Minimum of two extended integers. *)
Definition eZ_min (x y : eZ) : eZ :=
  match x, y with
  | NegInf, _ => NegInf                    (* -∞ is always the smallest *)
  | _, NegInf => NegInf
  | PosInf, v => v                         (* +∞ is bigger than anything *)
  | v, PosInf => v
  | Fin a, Fin b => Fin (Z.min a b)        (* ordinary min for finite integers *)
  end.

(** Maximum of two extended integers. *)
Definition eZ_max (x y : eZ) : eZ :=
  match x, y with
  | PosInf, _ => PosInf                    (* +∞ is always the largest *)
  | _, PosInf => PosInf
  | NegInf, v => v                         (* -∞ is smaller than anything *)
  | v, NegInf => v
  | Fin a, Fin b => Fin (Z.max a b)        (* ordinary max for finite integers *)
  end.


Definition eZ_opp (x : eZ) : eZ :=
  match x with
  | NegInf   => PosInf
  | PosInf   => NegInf
  | Fin z    => Fin (-z)
  end.

Notation "- v" := (eZ_opp v).

Definition eZ_add (x y : eZ) : eZ :=
  match x, y with
  | NegInf, PosInf
  | PosInf, NegInf => (* can define it as top or leave it as a special case *) PosInf
  | NegInf, _      => NegInf
  | _, NegInf      => NegInf
  | PosInf, _      => PosInf
  | _, PosInf      => PosInf
  | Fin a, Fin b   => Fin (a + b)
  end.

Infix "+" := eZ_add.

Definition eZ_sub (x y : eZ) : eZ :=
  eZ_add x (eZ_opp y).

Infix "-" := eZ_sub.

Definition eZ_mul (x y : eZ) : eZ :=
  match x, y with
  | Fin a, Fin b =>
      Fin (a * b)

  (* 0 annihilates everything (except possibly ±∞?), but here we unify ±∞ * 0 = 0.  *)
  | Fin 0, _ => Fin 0
  | _, Fin 0 => Fin 0

  (* -∞ * -∞ = +∞ *)
  | NegInf, NegInf => PosInf

  (* +∞ * +∞ = +∞ *)
  | PosInf, PosInf => PosInf

  (* -∞ * +∞ or +∞ * -∞ = -∞ in this naive approach *)
  (* Some designs treat these as 'indeterminate => top'. 
     We'll just pick -∞ here for demonstration. *)
  | NegInf, PosInf => NegInf
  | PosInf, NegInf => NegInf

  (* -∞ * finite, sign depends on the sign of the finite integer. *)
  | NegInf, Fin n =>
      if Z.eqb n 0
      then Fin 0
      else if Z.ltb n 0
           then PosInf
           else NegInf
  | Fin n, NegInf =>
      if Z.eqb n 0
      then Fin 0
      else if Z.ltb n 0
           then PosInf
           else NegInf

  (* +∞ * finite, sign depends on the sign of the finite integer. *)
  | PosInf, Fin n =>
      if Z.eqb n 0
      then Fin 0
      else if Z.ltb n 0
           then NegInf
           else PosInf
  | Fin n, PosInf =>
      if Z.eqb n 0
      then Fin 0
      else if Z.ltb n 0
           then NegInf
           else PosInf
  end.

Infix "*" := eZ_mul.

Definition eZ_div (x y : eZ) : eZ :=
  match x, y with
  (* Div by zero.  Could also be top or an error; we'll pick +∞ here. *)
  | _, Fin 0 => PosInf

  (* Finite ÷ Finite => normal integer division. 
     (Z.div is truncated toward zero in Coq’s standard library.) *)
  | Fin a, Fin b =>
      Fin (Z.div a b)

  (* -∞ ÷ ±∞, +∞ ÷ ±∞, etc. 
     We'll do a handful of guessy definitions:
     -∞ ÷ -∞ => +∞ 
     -∞ ÷ +∞ => -∞ ÷ +∞ => etc. 
     Some domain designs say "top."  Here is a toy pattern:
  *)
  | NegInf, NegInf => Fin 1   (* or PosInf, or top, or ??? *)
  | NegInf, PosInf => Fin 0   (* "like -∞ / +∞ = ~ -0, but we do 0" *)
  | PosInf, PosInf => Fin 1   (* "∞ / ∞ = 1"?  Very ad-hoc. *)
  | PosInf, NegInf => Fin 0

  (* -∞ ÷ Fin n => sign depends on n's sign, ignoring zero. *)
  | NegInf, Fin n =>
      if Z.eqb n 0
      then PosInf (* or top? "∞ ÷ 0" is definitely suspect. *)
      else if Z.ltb n 0
           then PosInf    (* -∞ ÷ negative => +∞ *)
           else NegInf    (* -∞ ÷ positive => -∞ *)

  (* +∞ ÷ Fin n => sign depends on n's sign. *)
  | PosInf, Fin n =>
      if Z.eqb n 0
      then PosInf  (* or top?  +∞ / 0??? *)
      else if Z.ltb n 0
           then NegInf
           else PosInf
  | Fin _, NegInf => Fin 0
  | Fin _, PosInf => Fin 0
  end.
Infix "/" := eZ_mul.

(** Comparison of extended integers. *)
Definition eZ_le (x y : eZ) : Prop :=
  match x, y with
  | NegInf, _        => True                    (* -∞ ≤ anything *)
  | _, PosInf        => True                    (* anything ≤ +∞ *)
  | Fin a, Fin b     => a <= b
  | PosInf, NegInf   => False
  | Fin _, NegInf    => False
  | PosInf, Fin _    => False
  end.



(** Notation for convenience. *)
Infix "≤ₑ" := eZ_le (at level 70).


Definition eZ_le_dec (x y : eZ) : { x ≤ₑ y } + { ~ x ≤ₑ y }.
Proof.
  destruct x, y.
  - (* x=NegInf, y=NegInf *)
    (* eZ_le NegInf NegInf => True *)
    left. simpl. exact I.
  - (* x=NegInf, y=Fin b *)
    (* -∞ ≤ b is True *)
    left. simpl. exact I.
  - (* x=NegInf, y=PosInf *)
    (* -∞ ≤ +∞ is True *)
    left. simpl. exact I.

  - (* x=Fin a, y=NegInf *)
    (* Fin a ≤ -∞ => False *)
    right. simpl. intros C. exact C.
  - (* x=Fin a, y=Fin b *)
    (* a <= b ?  We use Z.le_dec. *)
    simpl. destruct (Z_le_dec z z0).
    + left. assumption.
    + right. intro CONTRA. apply n. assumption.

  - (* x=Fin a, y=PosInf *)
    (* Fin a ≤ +∞ => True *)
    left. simpl. exact I.

  - (* x=PosInf, y=NegInf *)
    (* +∞ ≤ -∞ => False *)
    right. simpl. intros C. exact C.
  - (* x=PosInf, y=Fin b *)
    (* +∞ ≤ b => False *)
    right. simpl. intros C. exact C.
  - (* x=PosInf, y=PosInf *)
    (* +∞ ≤ +∞ => True *)
    left. simpl. exact I.
Defined.

Notation "-∞" := NegInf.
Notation "+∞" := PosInf.

Record interval : Type := Interval {
  lower : eZ;
  upper : eZ
}.

Notation "[ a , b ]" := (Interval a b) (at level 1).
Definition well_formed (I : interval) : Prop :=
  (lower I) ≤ₑ (upper I).

Definition interval_le (I1 I2 : interval) : Prop :=
  (lower I2) ≤ₑ (lower I1)  (*  a' ≤ a  *)
  /\ (upper I1) ≤ₑ (upper I2). (* b ≤ b' *)

Infix "⊑" := interval_le (at level 70).



Notation "⊤" := (Interval NegInf PosInf).
Notation "⊥" := (Interval PosInf NegInf).
Definition normalize (I : interval) : interval :=
  match I.(lower), I.(upper) with
  | PosInf, PosInf
  | NegInf, NegInf =>
      ⊥                             (* map these degenerate cases to bot *)
  | l, u =>
      (* Also check the usual condition l ≤ u, else bot *)
      if eZ_le_dec l u then [l,u] else ⊥
  end.

Definition AbD := interval.
Definition AbM := string -> interval. 

Definition top_AbM : AbM := fun x => ⊤.
Definition bot_AbM : AbM := fun x => ⊥.


Definition ab_update
           m 
           (x : string)
           (v : interval)
  :=
  fun y =>
    if string_dec x y then v else m y.

Notation "m { x ↤ v }" := (ab_update m x v).

Definition alpha_singleton z := [ z , z ].
Notation "z ♯" := (alpha_singleton z).

Definition ab_opp v :=
    match v with
    | [a, b] => normalize [-b, -a]
    end.

Definition add_op v1 v2 :=
    match v1, v2 with
    | [a,b], [c,d] => normalize [a + c, b + d]
    end.
    
Definition sub_op (I1 I2 : interval) : interval :=
  add_op I1 (ab_opp I2).

Infix "+♯" := add_op (at level 40).
Infix "-♯" := sub_op (at level 40).





Definition mul_op (I1 I2 : interval) : interval :=
  match I1, I2 with
  | [a,b], [c,d] =>
      let ac := a * c in
      let ad := a * d in
      let bc := b * c in
      let bd := b * d in
      let mn := eZ_min ac (eZ_min ad (eZ_min bc bd)) in
      let mx := eZ_max ac (eZ_max ad (eZ_max bc bd)) in
      normalize [mn, mx]
  end.

Definition div_op (I1 I2 : interval) : interval :=
  match I1, I2 with
  | [a,b], [c,d] =>
      let ac := a / c in
      let ad := a / d in
      let bc := b / c in
      let bd := b / d in
      let mn := eZ_min ac (eZ_min ad (eZ_min bc bd)) in
      let mx := eZ_max ac (eZ_max ad (eZ_max bc bd)) in
      normalize [mn, mx]
  end.

Infix "*♯" := mul_op (at level 40).
Infix "/♯" := div_op (at level 40).

Compute (⊥ *♯ ⊥).
Compute (⊥ *♯ [-∞, 4]).
Compute (⊥ *♯ [-∞, 4]).



Definition join v1 v2 :=
    match v1, v2 with
    | ⊥, v3 | v3, ⊥ => v3
    | left_of b, left_of d | left_of b, between _ d | between _ b, left_of d => left_of (Z.max b d)
    | right_of a, right_of c | right_of a, [c,_] | [a,_], right_of c => right_of (Z.min a c)
    | [a,b], [c,d] => between (Z.min a c) (Z.max b d)
    | _, _ => ⊤
    end.

    Unset Guard Checking.

    Fixpoint div_op v1 v2 {struct v1} :=
        match v1, v2 with
        | left_of b, left_of d => if d <? 0 then right_of (Z.min 0 (b / d)) 
                                  else if d =? 0 then div_op (left_of b) (left_of (-1))
                                  else ⊤
        | left_of b, [c,d] => if (c =? 0) && (d =? 0) then ⊥
                                    else if (c >? 0) && (d >=? c) then left_of (Z.max (b / c) (b / d))
                                    else if (c =? 0) && (d >? c) then div_op (left_of b) (between 1 d)
                                    else if (c <=? d) && (d <? 0) then right_of (Z.min (b / c) (b / d))
                                    else if (c <? d) && (d =? 0) then div_op (left_of b) (between c (-1))
                                    else ⊤
        | left_of b, right_of c => if c >? 0 then left_of (Z.max (b / c) 0) 
                                    else if c =? 0 then div_op (left_of b) (right_of 1)
                                    else ⊤
        | [a,b], left_of d => if d <? 0 then between (Z.min (b / d) 0) (Z.max (a / d) 0)
                                     else if d =? 0 then div_op ([a,b]) (left_of (-1))
                                     else join (div_op ([a,b]) (left_of (-1))) (div_op ([a,b]) (between 1 d))
        | [a,b], [c,d] => if (c =? 0) && (d =? 0) then ⊥
                                        else if (c =? 0) && (d >? c) then div_op ([a,b]) (between 1 d)
                                        else if (c <? 0) && (d =? 0) then div_op ([a,b]) (between c (-1))
                                        else if (c <? 0) && (d >? 0) then join (div_op ([a,b]) (between c (-1))) (div_op ([a,b]) (between 1 d))
                                        else between (Z.min (Z.min (a / c) (a / d)) (Z.min (b / c) (b / d))) (Z.max (Z.max (a / c) (a / d)) (Z.max (b / c) (b / d)))
        | [a,b], right_of c => if c >? 0 then between (Z.min (a / c) 0) (Z.max (b / c) 0)
                                        else if c =? 0 then div_op ([a,b]) (right_of 1)
                                        else join (div_op ([a,b]) (between c (-1))) (div_op ([a,b]) (right_of 1))
        | [a,b], ⊤ => join (div_op ([a,b]) (left_of (-1))) (div_op ([a,b]) (right_of 1))
        | right_of a, left_of d => if d <? 0 then left_of (Z.max 0 (a / d)) 
                                   else if d =? 0 then div_op (right_of a) (left_of (-1))
                                   else ⊤
        | right_of a, [c,d] => if (c =? 0) && (d =? 0) then ⊥
                                        else if (c >? 0) && (d >=? c) then right_of (Z.min (a / c) (a / d))
                                        else if (c =? 0) && (d >? c) then div_op (right_of a) (between 1 d)
                                        else if (c <=? d) && (d <? 0) then left_of (Z.max (a / c) (a / d))
                                        else if (c <? d) && (d =? 0) then div_op (right_of a) (between c (-1))
                                        else ⊤
        | right_of a, right_of c => if c >? 0 then right_of (Z.min (a / c) 0) 
                                    else if c =? 0 then div_op (right_of a) (right_of 1)
                                    else ⊤
        | ⊤, [c,d] => if (c =? 0) && (d =? 0) then ⊥ else ⊤
        | _, _ => ⊤
        end.

Set Guard Checking.

Definition ab_op op v1 v2 :=
    match op with
    | add => add_op v1 v2
    | sub => sub_op v1 v2
    | mul => mul_op v1 v2
    | div => div_op v1 v2 
    end.

Fixpoint AbsEval e m :=
    match e with
    | var x => m x
    | const n => alpha_singleton n
    | aop op e1 e2 => ab_op op (AbsEval e1 m) (AbsEval e2 m)
    | opp e' => ab_opp (AbsEval e' m)
    end.

Definition eq_sem e1 e2 m := 
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ => bot_AbM
                | left_of b, left_of d => if b <=? d then  m 
                                          else  (ab_update m x (left_of d))
                | left_of b, [c,d] => if b <? c then bot_AbM
                                            else if (c <=? b) && (b <=? d) then  (ab_update m x (between c b))
                                            else  (ab_update m x ([c,d]))
                | left_of b, right_of c => if b <? c then bot_AbM 
                                           else  (ab_update m x (between c b))
                | [a,b], left_of d => if a >? d then bot_AbM 
                                            else if (a <=? d) && (b >? d) then  (ab_update m x ([a,d]))
                                            else  m
                | [a,b], [c,d] => if (b <? c) || (a >? d) then bot_AbM 
                                              else if (b >? d) && (a <? c) then  (ab_update m x ([c,d]))
                                              else if (b >? d) && (a >=? c) then  (ab_update m x ([a,d]))
                                              else if (c <=? b) && (b <=? d) && (a <? c) then  (ab_update m x (between c b))
                                              else  m
                | [a,b], right_of c => if b <? c then bot_AbM 
                                             else if (b >=? c) && (a <? c) then  (ab_update m x (between c b))
                                             else  m
                | right_of a, left_of d => if a >? d then bot_AbM else  (ab_update m x ([a,d]))
                | right_of a, [c,d] => if a >? d then bot_AbM 
                                             else if a <? c then  (ab_update m x ([c,d]))
                                             else  (ab_update m x ([a,d]))
                | right_of a, right_of c => if a <? c then  (ab_update m x (right_of c)) else  m
                | ⊤, left_of d =>  (ab_update m x (left_of d))
                | ⊤, [c,d] =>  (ab_update m x ([c,d]))
                | ⊤, right_of c =>  (ab_update m x (right_of c))
                | _, _ =>  m
                end
    | _ =>  match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ => bot_AbM
            | left_of b, [c,_] | left_of b, right_of c | between _ b, right_of c => if b <? c then bot_AbM else  m
            | right_of a, between _ d | right_of a, left_of d | [a,_], left_of d => if a >? d then bot_AbM else  m
            | [a,b], [c,d] => if (b <? c) || (a >? d) then bot_AbM else  m
            | _, _ =>  m
            end
    end.
        
Definition ne_sem e1 e2 m := 
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ => bot_AbM
                | left_of b, [c,d] => if (b =? c) && (c =? d) then  (ab_update m x (left_of (b - 1)))
                                            else  m
                | [a,b], [c,d] => if (a =? b) && (b =? c) && (c =? d) then bot_AbM
                                              else if (negb (a =? b)) && (a =? c) && (c =? d) then  (ab_update m x (between (a + 1) b))
                                              else if (negb (a =? b)) && (b =? c) && (c =? d) then  (ab_update m x (between a (b - 1)))
                                              else  m
                | right_of a, [c,d] => if (a =? c) && (c =? d) then  (ab_update m x (right_of (a + 1)))
                                             else  m
                | _, _ =>  m
                end
    | _ =>  match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ => bot_AbM
            | [a,b], [c,d] => if (a =? b) && (b =? c) && (c =? d) then bot_AbM
                                            else  m
            | _, _ =>  m
            end
    end.
    
Definition lt_sem e1 e2 m := 
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ => bot_AbM
                | left_of b, left_of d | left_of b, between _ d => if b >=? d then  (ab_update m x (left_of (d - 1))) 
                                                                   else  m
                | [a,b], between _ d | [a,b], left_of d => if a >=? d then bot_AbM 
                                                                       else if b >=? d then  (ab_update m x (between a (d - 1)))
                                                                       else  m
                | right_of a, between _ d | right_of a, left_of d => if a >=? d then bot_AbM else  (ab_update m x (between a (d - 1)))
                | ⊤, left_of d | ⊤, between _ d =>  (ab_update m x (left_of (d - 1)))
                | _, _ =>  m
                end
    | _ =>  match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ => bot_AbM
            | [a,_], between _ d | [a,_], left_of d 
            | right_of a, between _ d | right_of a, left_of d => if a >=? d then bot_AbM else  m
            | _, _ =>  m
            end
    end.

Definition gt_sem e1 e2 m := 
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ => bot_AbM
                | [a,b], [c,_] | [a,b], right_of c => if b <=? c then bot_AbM else 
                                                                         if a <=? c then  (ab_update m x (between (c + 1) b))
                                                                         else  m
                | left_of b, [c,_] | left_of b, right_of c => if b <=? c then bot_AbM else  (ab_update m x (between (c + 1) b))
                | right_of a, [c,_] | right_of a, right_of c => if a <=? c then  (ab_update m x (right_of (c + 1))) else  m
                | ⊤, [c,_] | ⊤, right_of c =>  (ab_update m x (right_of (c + 1)))
                | _, _ =>  m
                end
    | _ =>  match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ => bot_AbM
            | between _ b, [c,_] | between _ b, right_of c
            | left_of b, [c,_] | left_of b, right_of c  => if b <=? c then bot_AbM else  m
            | _, _ =>  m
            end
    end.

Definition le_sem e1 e2 m := 
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ => bot_AbM
                | left_of b, left_of d | left_of b, between _ d => if b >? d then  (ab_update m x (left_of d)) 
                                                                   else  m
                | [a,b], between _ d | [a,b], left_of d => if a >? d then bot_AbM 
                                                                       else if b >? d then  (ab_update m x ([a,d]))
                                                                       else  m
                | right_of a, between _ d | right_of a, left_of d => if a >? d then bot_AbM else  (ab_update m x ([a,d]))
                | ⊤, left_of d | ⊤, between _ d =>  (ab_update m x (left_of d))
                | _, _ =>  m
                end
    | _ =>  match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ => bot_AbM
            | [a,_], between _ d | [a,_], left_of d 
            | right_of a, between _ d | right_of a, left_of d => if a >? d then bot_AbM else  m
            | _, _ =>  m
            end
    end.

Definition ge_sem e1 e2 m := 
    match e1 with
    | var x => match AbsEval e1 m, AbsEval e2 m with
                | ⊥, _ | _, ⊥ => bot_AbM
                | [a,b], [c,_] | [a,b], right_of c => if b <? c then bot_AbM else 
                                                                         if a <? c then  (ab_update m x (between c b))
                                                                         else  m
                | left_of b, [c,_] | left_of b, right_of c => if b <? c then bot_AbM else  (ab_update m x (between c b))
                | right_of a, [c,_] | right_of a, right_of c => if a <? c then  (ab_update m x (right_of c)) else  m
                | ⊤, [c,_] | ⊤, right_of c =>  (ab_update m x (right_of c))
                | _, _ =>  m
                end
    | _ =>  match AbsEval e1 m, AbsEval e2 m with
            | ⊥, _ | _, ⊥ => bot_AbM
            | between _ b, [c,_] | between _ b, right_of c
            | left_of b, [c,_] | left_of b, right_of c  => if b <? c then bot_AbM else  m
            | _, _ =>  m
            end
    end.


Definition join_mem s1_sharp s2_sharp :=
    match s1_sharp with
    | None => s2_sharp
    | Some l => join_state_helper l s2_sharp
    end.

Definition ab_po v1 v2 :=
    match v1, v2 with 
    | ⊥, _ | _, ⊤ => true
    | [a,b], [c,d] => (c <=? a) && (b <=? d)
    | [a,_], right_of c => c <=? a
    | between _ a, left_of c => a <=? c
    | right_of a, right_of c => c <=? a
    | left_of a, left_of c => a <=? c
    | _, _ => false
    end.

    Fixpoint ab_le_state_helper l t_sharp :=
        match l with
        | nil => true
        | (x, a) :: tl => ab_po (ab_lookup t_sharp x) a && ab_le_state_helper tl t_sharp
        end.
    
    Definition ab_po_mem m t_sharp :=
        match m with
        | None => true
        | Some l => ab_le_state_helper l t_sharp
        end.


Definition widen v1 v2 :=
    match v1, v2 with
    | ⊥, v3 | v3, ⊥ => v3
    | right_of a, right_of c | right_of a, [c,_] | [a,_], right_of c => if a <=? c then right_of a else ⊤
    | [a,b], [c,d] => if a <=? c then
                                    if d <=? b then
                                        [a,b]
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

    Definition widen_mem m t_sharp :=
        match m with
        | None => t_sharp
        | Some l => Some (map (fun c : string * AbD => let (x, a) := c in (x, widen a (ab_lookup t_sharp x))) l)
        end.

Definition narrow v1 v2 :=
    match v1, v2 with
    | ⊥, _ | _, ⊥ => ⊥
    | ⊤, v3 | v3, ⊤ => v3
    | right_of a, right_of _ => right_of a
    | right_of a, between _ d | right_of a, left_of d => [a,d]
    | [a,b], _ => [a,b]
    | left_of b, right_of c | left_of b, [c,_] => between c b
    | left_of b, left_of _ => left_of b
    end.

    Definition narrow_mem m t_sharp :=
        match m with
        | None => bot_AbM
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





    
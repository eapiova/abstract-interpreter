(** Import a number of standard data types and results about these *)
From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Import ZifyBool.
From Coq Require Export Strings.String.
From Coq Require Strings.BinaryString.
From Coq Require Export Lists.List.
From Coq Require Export Program.Basics.
From Coq Require Import NArith.

(** ######################################################################### *)
(** * Common utilities *)
(** ######################################################################### *)

(** Enforce the use of bullets *)
Export Set Default Goal Selector "!".

(** Enable list and string notations *)
Open Scope string_scope.
Open Scope nat_scope.
Open Scope list_scope.
Export ListNotations.

(** Coq's standard library does not use maximally implicit arguments for the
various list functions. Override that. *)
Global Arguments List.nil {_}.
Global Arguments List.cons {_}.
Global Arguments List.app {_} _ _.
Global Arguments List.length {_}.

(** A hack to make sure we get the right length, and not the one on strings. *)
Notation length := List.length.

(** Make sure that [xorb] only simplifies if both arguments are constructors. *)
Global Arguments xorb : simpl nomatch.

(** Make sure that [compose] simplifies if it is fully applied. *)
Global Arguments compose {_ _ _} _ _ _ /.

Global Arguments min : simpl nomatch.
Global Arguments max : simpl nomatch.
Global Arguments N.add : simpl nomatch.
Global Arguments N.mul : simpl never.
Global Arguments N.sub : simpl never.

(** Avoid eager unfolding *)
Strategy 100 [Acc_intro_generator].

(** ######################################################################### *)
(** * Options *)
(** ######################################################################### *)

Definition option_union {A} (mx my : option A) : option A :=
  match mx with Some a => mx | None => my end.
Definition option_difference {A} (mx my : option A) : option A :=
  match my with Some _ => None | None => mx end.

Definition option_bind {A B} (f : A -> option B) (mx : option A) : option B :=
  match mx with
  | Some x => f x
  | None => None
  end.

(** ######################################################################### *)
(** * Strings *)
(** ######################################################################### *)

(** To compare strings, we define the function [eqb_string], which internally
uses the function [string_dec] from Coq's string library. *)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Lemma eqb_string_eq x y :
  eqb_string x y = true <-> x = y.
Proof. unfold eqb_string. destruct (string_dec x y); intuition congruence. Qed.

Lemma eqb_string_refl x : eqb_string x x = true.
Proof. unfold eqb_string. destruct (string_dec x x); intuition congruence. Qed.

Lemma eqb_string_neq x y :
  eqb_string x y = false <-> x <> y.
Proof. unfold eqb_string. destruct (string_dec x y); intuition congruence. Qed.

(** ######################################################################### *)
(** * Tactics *)
(** ######################################################################### *)

(** Simplifies equations by doing substitution and injection. *)
(** Our [simplify_eq] tactic is a simplified version of the [simplify_eq/=]
tactic from std++. *)

Tactic Notation "simplify_eq" := repeat
  match goal with
  | _ => progress (simpl in * || subst || discriminate)
  | H : ?f _ = ?f _ |- _ => progress injection H as H
  | H : ?f _ _ = ?f _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ = ?f _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => progress injection H as H
  | H : ?f _ _ _ _ _ _ = ?f _ _ _ _ _ _ |- _ => progress injection H as H
  | H : ?x = ?x |- _ => clear H
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
     assert (y = x) by congruence; clear H2
  | H1 : ?o = Some ?x, H2 : ?o = None |- _ => congruence
  end.

(** Our [done] tactic is a simplified version of the [done] tactic from std++. *)

Local Ltac fast_done :=
  solve
    [ eassumption
    | symmetry; eassumption
    | reflexivity ].

Ltac done :=
  solve
  [ repeat first
    [ fast_done
    | solve [trivial]
    (* All the tactics below will introduce hypothesis themselves, or make no
    sense for implications/foralls. So this is a good place for us to do it. *)
    | progress intros
    | solve [symmetry; trivial]
    | discriminate
    | contradiction
    | split
    | match goal with H : ~_ |- _ => case H; clear H; fast_done end ]
  ].
Tactic Notation "by" tactic(tac) :=
  tac; done.

(** The [inv] tactic is inspired by its version in CompCert. Compared to Coq's
standard [inversion] tactic, it cleans up the original hypothesis and
substitutes generated equalities. Compared to CompCert's original version, we
use the more powerful [simplify_eq] instead of a mere [subst]. *)

Tactic Notation "inv" ident(H) "as" simple_intropattern(ipat) :=
  inversion H as ipat; clear H; simplify_eq.

Tactic Notation "inv" ident(H) :=
  inversion H; clear H; simplify_eq.

(** ######################################################################### *)
(** * Maps *)
(** ######################################################################### *)

Module Type Inf.
  Parameter t : Type.
  Parameter eq_dec : forall x1 x2 : t, { x1 = x2 } + { x1 <> x2 }.
  Parameter fresh : list t -> t.
  Axiom not_in_fresh : forall xs, ~In (fresh xs) xs.
End Inf.

Module Type InfDerived (Import K : Inf).
  Lemma eq_dec_eq {B} (y1 y2 : B) x :
    (if eq_dec x x then y1 else y2) = y1.
  Proof. by destruct (eq_dec _ _). Qed.

  Lemma eq_dec_neq {B} (y1 y2 : B) x1 x2 :
    x1 <> x2 ->
    (if eq_dec x1 x2 then y1 else y2) = y2.
  Proof. by destruct (eq_dec _ _). Qed.
End InfDerived.

Module Type MapAxioms (K : Inf).
  Parameter map : Type -> Type.

  Parameter lookup : forall {A}, map A -> K.t -> option A.
  Parameter empty : forall {A}, map A.
  Parameter update : forall {A}, K.t -> option A -> map A -> map A.
  Parameter merge : forall {A B C},
    (option A -> option B -> option C) -> map A -> map B -> map C.
  Parameter dom : forall {A}, map A -> list K.t.

  Axiom map_eq : forall {A} (m1 m2 : map A),
    m1 = m2 <-> forall k, lookup m1 k = lookup m2 k.
  Axiom lookup_empty : forall {A} k, lookup (@empty A) k = None.
  Axiom lookup_update : forall {A} (m : map A) k k' mx,
    lookup (update k mx m) k' = if K.eq_dec k' k then mx else lookup m k'.
  Axiom lookup_merge : forall {A B C}
      (f : option A -> option B -> option C) (m1 : map A) (m2 : map B) k,
    f None None = None ->
    lookup (merge f m1 m2) k = f (lookup m1 k) (lookup m2 k).
  Axiom dom_lookup : forall {A} (m : map A) k,
    In k (dom m) <-> exists x, lookup m k = Some x.
End MapAxioms.

Module Type MapDerived (K : Inf) (Import Map : MapAxioms K).
  Implicit Types k : K.t.

  (** Derived operations *)
  Definition insert {A} (k : K.t) (x : A) (m : map A) : map A :=
    update k (Some x) m.

  Definition delete {A} (k : K.t) (m : map A) : map A :=
    update k None m.

  Definition singleton {A} (k : K.t) (x : A) : map A :=
    insert k x empty.

  Definition union {A} (m1 m2 : map A) : map A :=
    merge option_union m1 m2.
  Definition difference {A} (m1 m2 : map A) : map A :=
    merge option_difference m1 m2.

  Definition incl {A} (m1 m2 : map A) : Prop :=
    forall k x, lookup m1 k = Some x -> lookup m2 k = Some x.
  Definition disjoint {A} (m1 m2 : map A) : Prop :=
    forall k, lookup m1 k = None \/ lookup m2 k = None.

  Definition fresh {A} (m : map A) : K.t :=
    K.fresh (dom m).

  (** Derived lookup laws *)
  Lemma lookup_insert {A} (m : map A) k k' y :
    lookup (insert k y m) k' = if K.eq_dec k' k then Some y else lookup m k'.
  Proof. unfold insert. by rewrite lookup_update. Qed.

  Lemma lookup_delete {A} (m : map A) k k' :
    lookup (delete k m) k' = if K.eq_dec k' k then None else lookup m k'.
  Proof. unfold delete. by rewrite lookup_update. Qed.

  Lemma lookup_singleton {A} k k' (x : A) :
    lookup (singleton k x) k' = if K.eq_dec k' k then Some x else None.
  Proof. unfold singleton. by rewrite lookup_insert, lookup_empty. Qed.

  Lemma lookup_union {A} (m1 m2 : map A) k :
    lookup (union m1 m2) k = option_union (lookup m1 k) (lookup m2 k).
  Proof. unfold union. by rewrite lookup_merge. Qed.

  Lemma lookup_difference {A} (m1 m2 : map A) k :
    lookup (difference m1 m2) k = option_difference (lookup m1 k) (lookup m2 k).
  Proof. unfold difference. by rewrite lookup_merge. Qed.

  Lemma lookup_fresh {A} (m : map A) : lookup m (fresh m) = None.
  Proof.
    destruct (lookup m _) as [x|] eqn:Hx; [|done].
    exfalso. apply (K.not_in_fresh (dom m)), dom_lookup. by exists x.
  Qed.

  (** An automated tactic for equalities *)
  Ltac map_solver :=
    try (apply map_eq; intros ?);
    by repeat first
      [done|progress simplify_eq
      |rewrite lookup_empty|rewrite lookup_update|rewrite lookup_merge by done
      |rewrite lookup_insert|rewrite lookup_delete|rewrite lookup_singleton
      |rewrite lookup_union|rewrite lookup_difference|rewrite lookup_fresh
      |destruct (K.eq_dec _ _)
      |match goal with
       | |- context [ lookup ?m ?k ] => is_var m; destruct (lookup m k) eqn:?
       end].

  (** Properties about dom *)
  Lemma dom_empty {A} : dom (@empty A) = [].
  Proof.
    destruct (dom empty) as [|k ks] eqn:Hdom; [done|].
    assert (In k (dom (@empty A))) as [x Hk]%dom_lookup.
    { rewrite Hdom. by left. }
    by rewrite lookup_empty in Hk.
  Qed.

  Lemma dom_nil {A} (m : map A) : dom m = [] <-> m = empty.
  Proof.
    split; [|intros ->; apply dom_empty].
    intros Hdom. apply map_eq; intros k.
    destruct (lookup m k) as [x|] eqn:?; [|map_solver].
    assert (In k []) as []. rewrite <-Hdom. apply dom_lookup. by exists x.
  Qed.

  (** Map induction *)
  Lemma map_dom_ind {A} (P : map A -> Prop) :
    P empty ->
    (forall k x m, lookup m k = None -> P m -> P (insert k x m)) ->
    forall m, P m.
  Proof.
    intros Hempty Hinsert.
    cut (forall ks m, List.incl (dom m) ks -> P m).
    { intros help m. apply (help (dom m)), incl_refl. }
    intros ks. induction ks as [|k ks IH]; intros m Hdom; simpl in *.
    { by apply incl_l_nil in Hdom as ->%dom_nil. }
    destruct (lookup m k) as [x|] eqn:Hk.
    - replace m with (insert k x (delete k m)) by map_solver.
      apply Hinsert; [map_solver|]. apply IH; intros k' [x' Hk']%dom_lookup.
      rewrite lookup_delete in Hk'. destruct (K.eq_dec _ _); [done|].
      destruct (Hdom k'); [apply dom_lookup|..]; by eauto.
    - apply IH. intros k' [x' Hk']%dom_lookup.
      destruct (Hdom k'); [apply dom_lookup|..]; simplify_eq; eauto.
  Qed.

  Lemma map_ind {A} (P : map A -> Prop) :
    P empty ->
    (forall k x m, lookup m k = None -> P m -> P (insert k x m)) ->
    forall m, P m.
  Proof.
    intros Hempty Hinsert.
    cut (forall ks m, List.incl (dom m) ks -> P m).
    { intros help m. apply (help (dom m)), incl_refl. }
    intros ks. induction ks as [|k ks IH]; intros m Hdom; simpl in *.
    { by apply incl_l_nil in Hdom as ->%dom_nil. }
    destruct (lookup m k) as [x|] eqn:Hk.
    - replace m with (insert k x (delete k m)) by map_solver.
      apply Hinsert; [map_solver|]. apply IH; intros k' [x' Hk']%dom_lookup.
      rewrite lookup_delete in Hk'. destruct (K.eq_dec _ _); [done|].
      destruct (Hdom k'); [apply dom_lookup|..]; by eauto.
    - apply IH. intros k' [x' Hk']%dom_lookup.
      destruct (Hdom k'); [apply dom_lookup|..]; simplify_eq; eauto.
  Qed.

  (** Derived equality laws *)
  Lemma update_update {A} (m : map A) k1 k2 mx1 mx2 :
    update k2 mx2 (update k1 mx1 m) =
      if K.eq_dec k1 k2 then update k2 mx2 m
      else update k1 mx1 (update k2 mx2 m).
  Proof. map_solver. Qed.

  Lemma insert_insert {A} (m : map A) k1 k2 y1 y2 :
    insert k2 y2 (insert k1 y1 m) =
      if K.eq_dec k1 k2 then insert k2 y2 m else insert k1 y1 (insert k2 y2 m).
  Proof. map_solver. Qed.

  Lemma insert_delete {A} (m : map A) k1 k2 y2 :
    insert k2 y2 (delete k1 m) =
      if K.eq_dec k1 k2 then insert k2 y2 m else delete k1 (insert k2 y2 m).
  Proof. map_solver. Qed.

  Lemma delete_insert {A} (m : map A) k1 k2 y1 :
    delete k2 (insert k1 y1 m) =
      if K.eq_dec k1 k2 then delete k2 m else insert k1 y1 (delete k2 m).
  Proof. map_solver. Qed.

  Lemma delete_delete {A} (m : map A) k1 k2 :
    delete k2 (delete k1 m) =
      if K.eq_dec k1 k2 then delete k2 m
      else delete k1 (delete k2 m).
  Proof. map_solver. Qed.

  Lemma insert_empty {A} k (x : A) :
    insert k x empty = singleton k x.
  Proof. map_solver. Qed.

  Lemma delete_empty {A} k :
    delete k (@empty A) = empty.
  Proof. map_solver. Qed.

  Lemma delete_singleton {A} k1 k2 (y1 : A) :
    delete k2 (singleton k1 y1) =
      if K.eq_dec k1 k2 then empty else singleton k1 y1.
  Proof. map_solver. Qed.

  Lemma insert_singleton {A} k (y1 y2 : A) :
    insert k y2 (singleton k y1) = singleton k y2.
  Proof. map_solver. Qed.

  Lemma union_assoc {A} (m1 m2 m3 : map A) :
    union m1 (union m2 m3) = union (union m1 m2) m3.
  Proof. map_solver. Qed.

  Lemma union_empty_l {A} (m : map A) :
    union empty m = m.
  Proof. map_solver. Qed.

  Lemma union_empty_r {A} (m : map A) :
    union m empty = m.
  Proof. map_solver. Qed.

  Lemma update_union {A} (m1 m2 : map A) k mx :
    update k mx (union m1 m2) = union (update k mx m1) (update k mx m2).
  Proof. destruct mx; map_solver. Qed.

  Lemma insert_union {A} (m1 m2 : map A) k x :
    insert k x (union m1 m2) = union (insert k x m1) (insert k x m2).
  Proof. map_solver. Qed.

  Lemma delete_union {A} (m1 m2 : map A) k :
    delete k (union m1 m2) = union (delete k m1) (delete k m2).
  Proof. map_solver. Qed.

  Lemma insert_union_l {A} (m1 m2 : map A) k x :
    insert k x (union m1 m2) = union (insert k x m1) m2.
  Proof. map_solver. Qed.

  Lemma union_singleton_l {A} (m : map A) k x :
    union (singleton k x) m = insert k x m.
  Proof. map_solver. Qed.

  Lemma union_singleton_r {A} (m : map A) k x :
    union m (singleton k x) = if lookup m k then m else insert k x m.
  Proof. map_solver. Qed.

  Lemma difference_empty_l {A} (m : map A) :
    difference empty m = empty.
  Proof. map_solver. Qed.

  Lemma difference_empty_r {A} (m : map A) :
    difference m empty = m.
  Proof. map_solver. Qed.

  Lemma difference_diag {A} (m : map A) :
    difference m m = empty.
  Proof. map_solver. Qed.

  Lemma difference_singleton_r {A} (m : map A) k x :
    difference m (singleton k x) = delete k m.
  Proof. map_solver. Qed.

  Lemma difference_singleton_l {A} (m : map A) k x :
    difference (singleton k x) m = if lookup m k then empty else singleton k x.
  Proof. map_solver. Qed.

  Lemma difference_union_l {A} (m1 m2 m3 : map A) :
    difference (union m1 m2) m3 = union (difference m1 m3) (difference m2 m3).
  Proof. map_solver. Qed.

  Lemma difference_union_r {A} (m1 m2 m3 : map A) :
    difference m1 (union m2 m3) = difference (difference m1 m2) m3.
  Proof. map_solver. Qed.

  Lemma difference_union_r' {A} (m1 m2 m3 : map A) :
    difference m1 (union m2 m3) = difference (difference m1 m3) m2.
  Proof. map_solver. Qed.

  Lemma difference_delete_l {A} (m1 m2 : map A) k :
    difference (delete k m1) m2 = delete k (difference m1 m2).
  Proof. map_solver. Qed.

  Lemma difference_delete_r {A} (m1 m2 : map A) k :
    difference m1 (delete k m2) = update k (lookup m1 k) (difference m1 m2).
  Proof. map_solver. Qed.

  Lemma difference_insert_l {A} (m1 m2 : map A) k x :
    difference (insert k x m1) m2 =
      if lookup m2 k then difference m1 m2
      else insert k x (difference m1 m2).
  Proof. map_solver. Qed.

  Lemma difference_insert_r {A} (m1 m2 : map A) k x :
    difference m1 (insert k x m2) = delete k (difference m1 m2).
  Proof. map_solver. Qed.

  Lemma delete_difference {A} (m1 m2 : map A) k :
    delete k (difference m1 m2) = difference (delete k m1) (delete k m2).
  Proof. map_solver. Qed.

  Lemma insert_difference {A} (m1 m2 : map A) k x :
    insert k x (difference m1 m2) = difference (insert k x m1) (delete k m2).
  Proof. map_solver. Qed.

  Lemma union_difference_r {A} (m1 m2 m3 : map A) :
    union m1 (difference m2 m3) = difference (union m1 m2) (difference m3 m1).
  Proof. map_solver. Qed.

  Lemma union_difference_irrel {A} (m1 m2 : map A) :
    union m1 (difference m2 m1) = union m1 m2.
  Proof. map_solver. Qed.

  (** Laws about map inclusion *)
  Lemma incl_refl {A} (m : map A) :
    incl m m.
  Proof. by intros ??. Qed.

  Lemma incl_trans {A} (m1 m2 m3 : map A) :
    incl m1 m2 -> incl m2 m3 -> incl m1 m3.
  Proof. intros Hm12 Hm23 k y; auto. Qed.

  Lemma incl_antisymm {A} (m1 m2 : map A) :
    incl m1 m2 -> incl m2 m1 -> m1 = m2.
  Proof.
    intros Hm12 Hm21. apply map_eq; intros k.
    specialize (Hm12 k); specialize (Hm21 k).
    repeat destruct (lookup _ k); (symmetry + idtac); by eauto.
  Qed.

  Lemma incl_lookup_None {A} (m1 m2 : map A) k :
    lookup m2 k = None -> incl m1 m2 -> lookup m1 k = None.
  Proof.
    intros Hk2 Hincl. destruct (lookup m1 k) as [x|] eqn:Hk1; [|done].
    apply Hincl in Hk1. congruence.
  Qed.

  Lemma incl_empty_l {A} (m : map A) :
    incl empty m.
  Proof. intros k y. by rewrite lookup_empty. Qed.
  Lemma incl_empty_r {A} (m : map A) :
    incl m empty <-> m = empty.
  Proof.
    split; [|intros ->; apply incl_empty_l].
    intros Hsub. apply map_eq; intros k. specialize (Hsub k).
    destruct (lookup m k); [|map_solver]. symmetry; by eauto.
  Qed.

  Lemma incl_singleton_l {A} (m : map A) k y :
    incl (singleton k y) m <-> lookup m k = Some y.
  Proof.
    split.
    - intros Hsub. apply Hsub. map_solver.
    - intros Hk k' x. map_solver.
  Qed.
  Lemma incl_singleton_r {A} (m : map A) k y :
    incl m (singleton k y) <-> m = empty \/ m = singleton k y.
  Proof.
    split; [|intros [->| ->]; [apply incl_empty_l|apply incl_refl]].
    intros Hsub. assert (forall k', k' <> k -> lookup m k' = None).
    { intros k' ?. destruct (lookup m k') as [x'|] eqn:Hk'; [|done].
      specialize (Hsub _ _ Hk'). rewrite lookup_singleton in Hsub.
      by destruct (K.eq_dec _ _). }
    destruct (lookup m k) as [x|] eqn:Hk.
    - right. apply map_eq; intros k'. rewrite lookup_singleton.
      destruct (K.eq_dec _ _) as [->|]; [|by eauto].
      specialize (Hsub _ _ Hk). rewrite lookup_singleton in Hsub.
      destruct (K.eq_dec _ _); by simplify_eq.
    - left. apply map_eq; intros k'. rewrite lookup_empty.
      destruct (K.eq_dec k k'); simplify_eq; eauto.
  Qed.

  Lemma incl_insert_r {A} (m : map A) k x :
    lookup m k = None ->
    incl m (insert k x m).
  Proof. intros Hk k' x' Hk'. map_solver. Qed.
  Lemma insert_mono {A} (m1 m2 : map A) k x :
    incl m1 m2 ->
    incl (insert k x m1) (insert k x m2).
  Proof.
    intros Hincl k' x'. rewrite !lookup_insert. destruct (K.eq_dec _ _); eauto.
  Qed.

  Lemma incl_union_l {A} (m1 m2 : map A) :
    incl m1 (union m1 m2).
  Proof. intros k x. rewrite lookup_union. by intros ->. Qed.

  Lemma lookup_fresh_incl {A} (m1 m2 : map A) :
    incl m1 m2 ->
    lookup m1 (fresh m2) = None.
  Proof. apply incl_lookup_None, lookup_fresh. Qed.

  Lemma disjoint_alt {A} (m1 m2 : map A) :
    disjoint m1 m2 <->
      forall k x1 x2,
        lookup m1 k = Some x1 -> lookup m2 k = Some x2 -> False.
  Proof.
    split; intros Hdisj k; specialize (Hdisj k).
    - by destruct Hdisj as [-> | ->].
    - repeat destruct (lookup _ k); (exfalso + idtac); by eauto.
  Qed.

  Lemma disjoint_comm {A} (m1 m2 : map A) :
    disjoint m1 m2 <-> disjoint m2 m1.
  Proof. split; intros Hdisj k; destruct (Hdisj k); tauto. Qed.

  Lemma disjoint_empty {A} (m : map A) :
    disjoint empty m.
  Proof. intros k. left. by rewrite lookup_empty. Qed.

  Lemma disjoint_singleton {A} (m : map A) k y :
    disjoint (singleton k y) m <-> lookup m k = None.
  Proof.
    split.
    - intros Hdisj. specialize (Hdisj k) as [Hdisj|]; [|done].
      rewrite lookup_singleton in Hdisj. by (destruct (K.eq_dec _ _)).
    - intros Hk k'. rewrite lookup_singleton.
      destruct (K.eq_dec _ _) as [->|]; auto.
  Qed.

  Lemma disjoint_union {A} (m1 m2 m : map A) :
    disjoint (union m1 m2) m <-> disjoint m1 m /\ disjoint m2 m.
  Proof.
    split.
    - intros Hdisj; split; intros k; (destruct (Hdisj k) as [Hk|?]; [|by right]);
        rewrite lookup_union in Hk; destruct (lookup m1 _); by auto.
    - intros [Hdisj1 Hdisj2] k. rewrite lookup_union.
      destruct (Hdisj1 k) as [->| ->], (Hdisj2 k); auto.
  Qed.

  Lemma disjoint_union_comm {A} (m1 m2 : map A) :
    disjoint m1 m2 -> union m1 m2 = union m2 m1.
  Proof.
    intros Hdisj. apply map_eq; intros k. rewrite !lookup_union.
    destruct (Hdisj k) as [-> | ->]; map_solver.
  Qed.

  Lemma disjoint_difference_id {A} (m1 m2 : map A) :
    disjoint m1 m2 -> difference m1 m2 = m1.
  Proof.
    intros Hdisj. apply map_eq; intros k. rewrite lookup_difference.
    destruct (Hdisj k) as [-> | ->]; map_solver.
  Qed.
End MapDerived.

Module Nat <: Inf.
  Definition t := nat.
  Definition eq_dec := Nat.eq_dec.
  Fixpoint fresh (ns : list nat) : nat :=
    match ns with
    | [] => 0
    | n :: ns => max (S n) (fresh ns)
    end.
  Lemma not_in_fresh ns : ~In (fresh ns) ns.
  Proof.
    assert (forall n, In n ns -> n < fresh ns) as help.
    { induction ns as [|n' ns IH]; intros n Hin; simpl in *; [done|].
      destruct Hin as [?|?%IH]; lia. }
    intros ?%help; lia.
  Qed.

  Include InfDerived.
End Nat.

Module N <: Inf.
  Definition t := N.
  Definition eq_dec := N.eq_dec.
  Local Open Scope N_scope.

  Definition lt_dec (n m : N) : { n < m } + { ~n < m }.
  Proof.
    destruct (N.ltb n m) eqn:?; [left|right]; rewrite <-N.ltb_lt; congruence.
  Defined.

  Fixpoint fresh (ns : list N) : N :=
    match ns with
    | [] => 0
    | n :: ns => N.max (1 + n) (fresh ns)
    end.
  Lemma not_in_fresh ns : ~In (fresh ns) ns.
  Proof.
    assert (forall n, In n ns -> n < fresh ns) as help.
    { induction ns as [|n' ns IH]; intros n Hin; simpl in *; [done|].
      destruct Hin as [?|?%IH]; lia. }
    intros ?%help; lia.
  Qed.

  Include InfDerived.
End N.

Module String <: Inf.
  Definition t := string.
  Definition eq_dec := string_dec.
  Local Open Scope N_scope.

  (** We prove that strings are isomorphic to natural numbers [N] so that we can
  lift maps [NMap] on [N] to strings.
  The isomorphism is based on https://en.wikipedia.org/wiki/Bijective_numeration *)
  Definition ascii_to_N (a : Ascii.ascii) : N :=
    match a with
    | Ascii.Ascii β1 β2 β3 β4 β5 β6 β7 β8 =>
       1 + N.b2n β1 + 2 * N.b2n β2 + 4 * N.b2n β3 + 8 * N.b2n β4 +
       16 * N.b2n β5 + 32 * N.b2n β6 + 64 * N.b2n β7 + 128 * N.b2n β8
    end.
  Definition ascii_of_N (n : N) : Ascii.ascii :=
    let n := n - 1 in
    Ascii.Ascii (N.odd n) (N.odd (n / 2)) (N.odd (n / 4)) (N.odd (n / 8))
      (N.odd (n / 16)) (N.odd (n / 32)) (N.odd (n / 64)) (N.odd (n / 128)).

  Lemma ascii_of_to_N a : ascii_of_N (ascii_to_N a) = a.
  Proof. by destruct a as [[][][][][][][][]]. Qed.
  Lemma ascii_to_N_bound a : 0 < ascii_to_N a <= 256.
  Proof. by destruct a as [[][][][][][][][]]. Qed.
  Lemma ascii_to_of_N n : 0 < n <= 256 -> ascii_to_N (ascii_of_N n) = n.
  Proof.
    assert (forall n' : nat,
      0 < n' <= 256 ->
      ascii_to_N (ascii_of_N (N.of_nat n')) = N.of_nat n')%nat as help.
    { intros n' ?. do 257 (destruct n' as [|n']; [done || lia|]); lia. }
    intros ?. rewrite <-(N2Nat.id n). apply help. lia.
  Qed.

  Arguments ascii_to_N : simpl never.
  Arguments ascii_of_N : simpl never.

  Fixpoint to_N (s : string) : N :=
    match s with
    | EmptyString => 0
    | String a s => ascii_to_N a + 256 * to_N s
    end.

  Lemma of_N_aux_decr n :
    n <> 0 ->
    (n - 1) / 256 < n.
  Proof. intros. apply N.div_lt_upper_bound; lia. Qed.
  Definition of_N_aux (n : N) (rec : forall n', n' < n -> string) : string :=
    match N.eq_dec n 0 with
    | left _ => ""
    | right Hn =>
      let q := (n - 1) / 256 in
      String (ascii_of_N (n - q * 256)) (rec q (of_N_aux_decr _ Hn))
    end.
  Definition of_N (n : N) : string :=
    Fix (Acc_intro_generator 32 N.lt_wf_0) _ of_N_aux n.
  Lemma of_N_unfold n :
    of_N n =
      if N.eq_dec n 0 then "" else
      let q := (n - 1) / 256 in
      String (ascii_of_N (n - q * 256)) (of_N q).
  Proof.
    apply (Fix_eq _ _ of_N_aux). intros n' rec1 rec2 Hrec. unfold of_N_aux.
    destruct (N.eq_dec n' 0); by repeat f_equal.
  Qed.

  Lemma of_to_N s : of_N (to_N s) = s.
  Proof.
    induction s as [|a s IH]; simpl; [done|].
    assert (0 < ascii_to_N a <= 256) by apply ascii_to_N_bound.
    pose proof (N.mod_bound_pos (ascii_to_N a + 256 * to_N s - 1) 256
      ltac:(lia) ltac:(lia)).
    pose proof (N.div_mod (ascii_to_N a + 256 * to_N s - 1) 256 ltac:(lia)).
    rewrite of_N_unfold. destruct (N.eq_dec _ _) as [|_]; [lia|]. simpl; f_equal.
    - etransitivity; [|apply ascii_of_to_N]. f_equal. lia.
    - etransitivity; [|apply IH]. f_equal. lia.
  Qed.
  Lemma to_of_N n : to_N (of_N n) = n.
  Proof.
    induction (N.lt_wf_0 n) as [n _ IH].
    rewrite of_N_unfold. destruct (N.eq_dec _ _); simpl; [done|].
    pose proof (N.mod_bound_pos (n - 1) 256 ltac:(lia) ltac:(lia)).
    pose proof (N.div_mod (n - 1) 256 ltac:(lia)).
    rewrite IH, ascii_to_of_N; lia.
  Qed.

  Definition fresh (ns : list string) : string :=
    of_N (N.fresh (List.map to_N ns)).
  Lemma not_in_fresh ns : ~In (fresh ns) ns.
  Proof.
    intros Hin. apply (N.not_in_fresh (List.map to_N ns)).
    apply in_map_iff. exists (fresh ns). split; [|done]. apply to_of_N.
  Qed.

  Include InfDerived.
End String.

Module NMap <: MapAxioms N.
  Definition map A := list (N * A).
  Local Open Scope N_scope.

  Fixpoint lookup {A} (m : map A) (k : N) : option A :=
    match m with
    | [] => None
    | (k',y) :: m =>
       if N.lt_dec k k' then None
       else if N.eq_dec k k' then Some y
       else lookup m (k - N.succ k')
    end.

  Definition empty {A} : map A := [].

  Local Definition key0 {A} (m : map A) : N :=
    match m with [] => 0 | (k,_) :: _ => k end.
  Local Definition set_key0 {A} (m : map A) (k : N) : map A :=
    match m with [] => [] | (_,x) :: m => (k,x) :: m end.

  Fixpoint update {A} (k : N) (mx : option A) (m : map A) : map A :=
    match m with
    | [] => match mx with Some x => [(k,x)] | None => [] end
    | (k',y) :: m =>
       if N.lt_dec k k' then
         match mx with
         | Some x => (k,x) :: (k' - N.succ k,y) :: m | None => (k',y) :: m
         end
       else if N.eq_dec k k' then
         match mx with
         | Some x => (k,x) :: m | None => set_key0 m (N.succ (k' + key0 m))
         end
       else (k',y) :: update (k - N.succ k') mx m
    end.

  (** We thread through the first keys to make this definition structurally
  recursive. *)
  Local Fixpoint merge_help {A B C} (f : option A -> option B -> option C)
      (m1 : map A) : N -> map B -> N -> map C :=
    fix go k1 m2 k2 :=
    match m1, m2 with
    | [], [] => []
    | [], (_,x2) :: m2 =>
       match f None (Some x2) with
       | Some y => (k2,y) :: go 0 m2 (key0 m2)
       | None => go 0 m2 (N.succ (k2 + key0 m2))
       end
    | (_,x1) :: m1, [] =>
       match f (Some x1) None with
       | Some x => (k1,x) :: merge_help f m1 (key0 m1) [] 0
       | None => merge_help f m1 (N.succ (k1 + key0 m1)) [] 0
       end
    | (_,x1) :: m1, (_,x2) :: m2 =>
       if N.lt_dec k1 k2 then
         match f (Some x1) None with
         | Some x => (k1,x) :: merge_help f m1 (key0 m1) ((0,x2) :: m2) (k2 - N.succ k1)
         | None => merge_help f m1 (N.succ (k1 + key0 m1)) ((0,x2) :: m2) k2
         end
       else if N.eq_dec k1 k2 then
         match f (Some x1) (Some x2) with
         | Some x => (k1,x) :: merge_help f m1 (key0 m1) m2 (key0 m2)
         | None => merge_help f m1 (N.succ (k1 + key0 m1)) m2 (N.succ (k2 + key0 m2))
         end
       else
         match f None (Some x2) with
         | Some x => (k2,x) :: go (k1 - N.succ k2) m2 (key0 m2)
         | None => go k1 m2 (N.succ (k2 + key0 m2))
         end
    end.
  Definition merge {A B C} (f : option A -> option B -> option C)
      (m1 : map A) (m2 : map B) : map C :=
    merge_help f m1 (key0 m1) m2 (key0 m2).

  Local Fixpoint dom_help {A} (k : N) (m : map A) : list N :=
    match m with
    | [] => []
    | (k',_) :: m => k' + k :: dom_help (N.succ (k' + k)) m
    end.
  Definition dom {A} (m : map A) : list N := dom_help 0 m.

  Local Lemma set_get_key0 {A} (m : map A) : set_key0 m (key0 m) = m.
  Proof. by destruct m as [|[]]. Qed.

  Local Ltac simplify := repeat first
     [done
     |destruct (N.eq_dec _ _); try (exfalso; lia)
     |destruct (N.lt_dec _ _); try (exfalso; lia)
     |progress simplify_eq|f_equal; by repeat (lia||f_equal)
     |rewrite set_get_key0
     |match goal with
      | H : context [lookup _ _ = _] |- _ => rewrite H
      | |- context [match ?ox with _ => _ end] => destruct ox eqn:?; simpl
      | |- context [set_key0 ?m _] => destruct m as [|[]] eqn:?; simpl
      end].

  Lemma map_eq {A} (m1 m2 : map A) :
    m1 = m2 <-> forall k, lookup m1 k = lookup m2 k.
  Proof.
    split; [by intros ->|].
    revert m2; induction m1 as [|[k1 y1] m1 IH]; intros [|[k2 y2] m2] Hlookup.
    - done.
    - specialize (Hlookup k2); simplify.
    - specialize (Hlookup k1); simplify.
    - pose proof (Hlookup k1); pose proof (Hlookup k2); simplify.
      f_equal. apply IH. intros k. specialize (Hlookup (k + N.succ k2)). simplify.
      by replace (k + N.succ k2 - N.succ k2) with k in Hlookup by lia.
  Qed.

  Lemma lookup_empty {A} k : lookup (@empty A) k = None.
  Proof. done. Qed.
  Lemma lookup_update {A} (m : map A) k k' mx :
    lookup (update k mx m) k' = if N.eq_dec k' k then mx else lookup m k'.
  Proof.
    revert k k'. induction m as [|[k'' x] m IH]; intros; destruct mx; simplify.
  Qed.

  Lemma lookup_merge {A B C} (f : option A -> option B -> option C)
      (m1 : map A) (m2 : map B) k :
    f None None = None ->
    lookup (merge f m1 m2) k = f (lookup m1 k) (lookup m2 k).
  Proof.
    intros. assert (forall k1 k2,
      lookup (merge_help f m1 k1 m2 k2) k
      = f (lookup (set_key0 m1 k1) k) (lookup (set_key0 m2 k2) k)) as help.
    { revert m2 k. (* many cases *)
      induction m1 as [|[k1' x1] m1 IH]; intros m2;
        induction m2 as [|[k2' x2] m2 IH2]; intros; simplify. }
    unfold merge. by rewrite help, !set_get_key0 by done.
  Qed.

  Lemma dom_lookup {A} (m : map A) k :
    In k (dom m) <-> exists x, lookup m k = Some x.
  Proof.
    assert (forall k',
      In k (dom_help k' m) <->
      exists x, k' <= k /\ lookup m (k - k') = Some x) as help.
    { revert k. induction m as [|[k'' x] m IH]; intros k k'; simpl.
      { split; [done|]. intros [x [_ [=]]]. }
      rewrite IH. split.
      - intros [<-|(x'&?&Hx')].
        + exists x. split; simplify.
        + exists x'. rewrite <-Hx'. split; simplify.
      - intros (x'&?&Hx'). destruct (N.eq_dec k (k'' + k')); [by left|right].
        exists x'. rewrite <-Hx'. split; simplify. }
    unfold dom. rewrite help, N.sub_0_r.
    split; [intros (x'&?&?); by exists x'|].
    intros [x' ?]; exists x'; split; [lia|done].
  Qed.

  #[global] Arguments lookup : simpl never.
  #[global] Arguments update : simpl never.

  Include MapDerived N.
End NMap.

Module NatMap <: MapAxioms Nat.
  Definition map := NMap.map.

  Definition lookup {A} (m : map A) (k : nat) : option A :=
    NMap.lookup m (N.of_nat k).
  Definition empty {A} : map A := NMap.empty.
  Definition update {A} (k : nat) (mx : option A) : map A -> map A :=
    NMap.update (N.of_nat k) mx.
  Definition merge {A B C} :
    (option A -> option B -> option C) ->
    map A -> map B -> map C := NMap.merge.
  Definition dom {A} (m : map A) : list nat := List.map N.to_nat (NMap.dom m).

  Lemma map_eq {A} (m1 m2 : map A) :
    m1 = m2 <-> forall k, lookup m1 k = lookup m2 k.
  Proof.
    split; [by intros ->|]. intros Hm. apply NMap.map_eq; intros k.
    rewrite <-(N2Nat.id k). apply Hm.
  Qed.
  Lemma lookup_empty {A} k : lookup (@empty A) k = None.
  Proof. apply NMap.lookup_empty. Qed.
  Lemma lookup_update {A} (m : map A) k k' mx :
    lookup (update k mx m) k' = if Nat.eq_dec k' k then mx else lookup m k'.
  Proof.
    unfold lookup, update. rewrite NMap.lookup_update.
    destruct (N.eq_dec _ _), (Nat.eq_dec _ _); done || lia.
  Qed.
  Lemma lookup_merge {A B C}
      (f : option A -> option B -> option C) (m1 : map A) (m2 : map B) k :
    f None None = None ->
    lookup (merge f m1 m2) k = f (lookup m1 k) (lookup m2 k).
  Proof. apply NMap.lookup_merge. Qed.
  Lemma dom_lookup {A} (m : map A) k :
    In k (dom m) <-> exists x, lookup m k = Some x.
  Proof.
    unfold lookup, dom. rewrite <-NMap.dom_lookup.
    rewrite in_map_iff. split; [intros (k'&<-&?); by rewrite N2Nat.id|].
    intros. exists (N.of_nat k). by rewrite Nat2N.id.
  Qed.

  Include MapDerived Nat.
End NatMap.

Notation natmap := NatMap.map.

Module StringMap <: MapAxioms String.
  Record map' A := StringMap { map_car : NMap.map A }.
  Local Coercion map_car : map' >-> NMap.map.
  Arguments StringMap {_}.
  Definition map := map'.

  Definition lookup {A} (m : map A) (k : string) : option A :=
    NMap.lookup m (String.to_N k).
  Definition empty {A} : map A := StringMap NMap.empty.
  Definition update {A} (k : string) (mx : option A) (m : map A) : map A :=
    StringMap (NMap.update (String.to_N k) mx m).
  Definition merge {A B C} (f : option A -> option B -> option C)
      (m1 : map A) (m2 : map B) : map C :=
    StringMap (NMap.merge f m1 m2).
  Definition dom {A} (m : map A) : list string :=
    List.map String.of_N (NMap.dom m).

  Lemma map_eq {A} (m1 m2 : map A) :
    m1 = m2 <-> forall k, lookup m1 k = lookup m2 k.
  Proof.
    split; [by intros ->|]. intros Hm. destruct m1 as [m1], m2 as [m2].
    f_equal. apply NMap.map_eq; intros k. rewrite <-(String.to_of_N k). apply Hm.
  Qed.
  Lemma lookup_empty {A} k : lookup (@empty A) k = None.
  Proof. apply NMap.lookup_empty. Qed.
  Lemma lookup_update {A} (m : map A) k k' mx :
    lookup (update k mx m) k' = if String.eq_dec k' k then mx else lookup m k'.
  Proof.
    unfold lookup, update. destruct m as [m]; simpl. rewrite NMap.lookup_update.
    destruct (N.eq_dec _ _), (String.eq_dec _ _) as [->|Hneq]; try done.
    destruct Hneq. rewrite <-(String.of_to_N k'), <-(String.of_to_N k).
    congruence.
  Qed.
  Lemma lookup_merge {A B C}
      (f : option A -> option B -> option C) (m1 : map A) (m2 : map B) k :
    f None None = None ->
    lookup (merge f m1 m2) k = f (lookup m1 k) (lookup m2 k).
  Proof. apply NMap.lookup_merge. Qed.
  Lemma dom_lookup {A} (m : map A) k :
    In k (dom m) <-> exists x, lookup m k = Some x.
  Proof.
    unfold lookup, dom. rewrite <-NMap.dom_lookup.
    rewrite in_map_iff. split; [intros (k'&<-&?); by rewrite String.to_of_N|].
    intros. exists (String.to_N k). by rewrite String.of_to_N.
  Qed.

  Include MapDerived String.
End StringMap.

Notation stringmap := StringMap.map.

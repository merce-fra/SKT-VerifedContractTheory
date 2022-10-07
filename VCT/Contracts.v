Require Import Sets.
Require Import FunctionalExtensionality.
(* Require Import ProofIrrelevance. *)
Include CoqSet.

Definition set := @τ.

Class Base_Types := {
  value : Type ;
  ident : Type
}.

Class Theory (bt : Base_Types) := {
  any_value : value ;
  eq_dec_ident : forall x y : ident, {x = y} + {x <> y} ;
  in_dec_ident : forall (v : ident) (d : set ident), {v ∈ d} + {v ∉ d}
}.

Section theory_defined.

Context {bt : Base_Types}.
Context {theo : Theory bt}.

Instance discr_ident : Discr ident := {eq_dec := eq_dec_ident}.

Definition alphabet : Type := set ident.

Section one_alphabet.

Variable d : alphabet.
Definition var := { v : ident | v ∈ d }.
Definition behavior : Type :=  {v : ident | v ∈ d} ->  value.
Definition assertion : Type := set behavior.
Definition component := assertion.
Definition environment := component.
Record contract : Type := mkContract {A : assertion ; G : assertion}.

Definition behavior_equiv (s1 : behavior) (s2 : behavior) : Prop :=
  forall x : {v : ident | v ∈ d}, s1 x = s2 x.

Theorem behavior_extensionality : forall (s1 s2 : behavior),
  behavior_equiv s1 s2 -> s1 = s2.
Proof.
  unfold behavior_equiv, behavior, alphabet.
  intros.
  extensionality x.
  apply H.
Qed.

Definition component_refines (σ1 σ2 : component) : Prop :=
  σ1 ⊆ σ2.

Definition satisfies (s : behavior) (c : contract) : Prop :=
  s ∈ ¬ c.(A) ∪ c.(G).

Definition implements (σ : component) (c : contract) :  Prop :=
  forall s, s  ∈ σ -> satisfies s c.

Notation "σ ⊢ c" := (implements σ c) (at level 70, no associativity).

Definition provides (e : environment) (c : contract) : Prop :=
  e ⊆ c.(A).

Definition saturate (c : contract) : contract :=
  mkContract (c.(A)) (¬ c.(A) ∪ c.(G)).

Notation "# c" := (saturate c) (at level 80, no associativity).

Definition is_saturated (c : contract) : Prop := SubsetEq (¬ c.(A)) (c.(G)).

Definition refines (c1 : contract) (c2 : contract) : Prop :=
  let c1' := saturate c1 in let c2' := saturate c2 in
  (c2'.(A)) ⊆ (c1'.(A)) /\ (c1'.(G)) ⊆ (c2'.(G)).

Notation "c1 ≼ c2" := (refines c1 c2) (at level 70, no associativity).

Definition equiv (c1 : contract) (c2 : contract) : Prop := refines c1 c2 /\ refines c2 c1.

Notation "c1 ≍ c2" := (equiv c1 c2) (at level 70 , no associativity).

Theorem contract_extensionality : forall (c1 c2 : contract), c1 ≍ c2 -> saturate c1 = saturate c2.
Proof.
  intros [a1 g1] [a2 g2].
  unfold equiv, refines, saturate.
  simpl.
  intros.
  f_equal ; apply Eq_extensionality ; apply SubsetEq_Asym ; tauto.
Qed.

Definition compose (c1 c2 : contract) : contract :=
  let c1' := saturate c1 in let c2' := saturate c2 in
  let g := c1'.(G) ∩ c2'.(G) in let a := (c1'.(A) ∩ c2'.(A)) ∪ ¬ g in
  mkContract a g.

Notation "c1 ⊗ c2" := (compose c1 c2) (at level 61, left associativity).

Definition glb (c1 : contract) (c2 : contract) : contract :=
  let c1' := saturate c1 in let c2' := saturate c2 in
  mkContract (c1'.(A) ∪ c2'.(A)) (c1'.(G) ∩ c2'.(G)).

Notation "c1 ⊓ c2" := (glb c1 c2) (at level 61, left associativity).

Definition lub (c1 c2 : contract) : contract :=
  let c1' := saturate c1 in let c2' := saturate c2 in
  mkContract (c1'.(A) ∩ c2'.(A)) (c1'.(G) ∪ c2'.(G)).

Notation "c1 ⊔ c2" := (lub c1 c2) (at level 61, left associativity).

Definition conforms (c : contract) (e : assertion) : Prop :=
  (c.(A) ∩ c.(G)) ⊆ e.

Definition is_consistent (c : contract) : Prop := exists s : behavior, satisfies s c.

Definition is_compatible (c : contract) : Prop := exists s : behavior, s ∈ (c.(A)).

Lemma is_satured_sature : forall c : contract, is_saturated (saturate c).
Proof.
  firstorder.
Qed.

Lemma implements_saturate_implements : forall (σ : component) (c : contract),
  σ ⊢ (saturate c) -> σ ⊢ c.
Proof.
  firstorder.
Qed.

Theorem saturate_sound : forall (s : behavior) (c : contract),
  satisfies s c <-> satisfies s (saturate c).
Proof.
  firstorder.
Qed.

Lemma implements_implements_saturate : forall (σ : component) (c : contract),
  σ ⊢ c -> σ ⊢ (saturate c).
Proof.
  firstorder.
Qed.

Theorem implements_refines_implements : forall (σ : component) (c1 c2 : contract),
  σ ⊢ c1 -> c1 ≼ c2 -> σ ⊢ c2.
Proof.
  firstorder.
Qed.

Theorem provides_refines_provides : forall (e : environment) (c1 c2 : contract),
  provides e c2 -> c1 ≼ c2 -> provides e c1.
Proof.
  firstorder.
Qed.

Theorem implements_refines : forall (c1 c2 : contract),
  (forall σ : component, σ ⊢ c1 -> σ ⊢ c2) ->
  (forall e : environment, provides e c2 -> provides e c1) ->
  c1 ≼ c2.
Proof.
  intros [a1 g1] [a2 g2] H1 H2.
  unfold refines.
  simpl.
  split.
  - clear H1.
    unfold SubsetEq.
    intros s Hs.
    generalize (H2 {s}).
    unfold provides.
    simpl.
    unfold singleton, add, SubsetEq, In.
    intro Hx.
    apply Hx.
    + intros x [xs_eq | x_in_empty].
      * subst ; assumption.
      * exfalso ; tauto.
    + left ; reflexivity.
  - clear H2.
    unfold SubsetEq.
    intros s Hs.
    generalize (H1 {s}).
    unfold implements.
    simpl.
    unfold singleton, add, SubsetEq, In.
    intro Hx.
    apply Hx.
    + intros x [Hxs | Hnul].
      * subst.
        exact Hs.
      * exfalso.
        exact Hnul.
    + left ; reflexivity.
Qed.

Theorem refines_implements : forall (c1 c2 : contract), c1 ≼ c2 ->
  (forall σ : component, σ ⊢ c1 -> σ ⊢ c2) /\
  (forall e : environment, provides e c2 -> provides e c1).
Proof.
  intros c1 c2 Href.
  split.
  intros σ Hσ.
  apply (implements_refines_implements σ c1 c2) ; assumption.
  intros e He.
  apply (provides_refines_provides e c1 c2) ; assumption.
Qed.

Theorem refines_correct : forall (c1 c2 : contract), c1 ≼ c2 <->
  (forall σ : component, σ ⊢ c1 -> σ ⊢ c2) /\
  (forall e : environment, provides e c2 -> provides e c1).
Proof.
  split.
  apply refines_implements.
  intro H; apply implements_refines ; tauto.
Qed.

Theorem refines_refl : forall c1 : contract, c1 ≼ c1.
Proof.
  firstorder.
Qed.

Theorem refines_trans : forall c1 c2 c3 : contract, c1 ≼ c2 -> c2 ≼ c3 -> c1 ≼ c3.
Proof.
  unfold refines.
  intros c1 c2 c3 [A21 G12] [A32 G23].
  split.
  apply (SubsetEq_Trans _ _ _  A32) ; assumption.
  apply (SubsetEq_Trans _ _ _  G12) ; assumption.
Qed.

Theorem refines_antisym : forall c1 c2 : contract, c1 ≼ c2 -> c2 ≼ c1 -> c1 ≍ c2.
Proof.
  unfold equiv ; auto.
Qed.

Theorem equiv_refl : forall c : contract, c ≍ c.
Proof.
  unfold equiv ; split ; apply refines_refl.
Qed.

Theorem equiv_sym : forall c1 c2 : contract, c1 ≍ c2 -> c2 ≍ c1.
Proof.
  unfold equiv ; tauto.
Qed.

Theorem equiv_trans : forall c1 c2 c3 : contract, c1 ≍ c2 -> c2 ≍ c3 -> c1 ≍ c3.
Proof.
  unfold equiv ; split ; apply refines_trans with (c2 := c2) ; tauto.
Qed.

Theorem saturate_idempotent : forall c : contract, saturate (saturate c) ≍ saturate c.
Proof.
  firstorder.
Qed.

Theorem saturate_satisfies : forall (s : behavior) (c : contract),
  satisfies s c <-> satisfies s (saturate c).
Proof.
  firstorder.
Qed.

Theorem glb_refines_l : forall c1 c2 : contract, (c1 ⊓ c2) ≼ c2.
Proof.
  unfold glb, refines .
  simpl.
  firstorder.
Qed.

Theorem glb_refines_r : forall c1 c2 : contract, (c1 ⊓ c2) ≼ c1.
Proof.
  firstorder.
Qed.

Theorem glb_greatest : forall c c1 c2 : contract, c ≼ c1 -> c ≼ c2 -> c ≼ (c1 ⊓ c2).
Proof.
  intros [a g] [a1 g1] [a2 g2].
  unfold refines ; simpl.
  intros [A1 G1] [A2 G2].
  split.
  firstorder.
  unfold SubsetEq, inter, union, compl, In in *.
  intros x H.
  right.
  split.
  apply G1 ; assumption.
  apply G2 ; assumption.
Qed.

Theorem glb_correct : forall c1 c2 : contract, (c1 ⊓ c2) ≼ c1 /\ (c1 ⊓ c2) ≼ c2 /\
  (forall c, c ≼ c1 -> c ≼ c2 -> c ≼ (c1 ⊓ c2)).
Proof.
  split.
  apply glb_refines_r.
  split.
  apply glb_refines_l.
  intro c.
  apply (glb_greatest c c1 c2).
Qed.

Theorem glb_sym : forall c1 c2 : contract, (c1 ⊓ c2) ≍ (c2 ⊓ c1).
Proof.
  unfold equiv.
  firstorder.
Qed.

Theorem lub_refines_l : forall c1 c2 : contract, c1 ≼ (c1 ⊔ c2).
Proof.
  firstorder.
Qed.

Theorem lub_refines_r : forall c1 c2 : contract, c2 ≼ (c1 ⊔ c2) .
Proof.
  firstorder.
Qed.

Theorem lub_lowest : forall c c1 c2 : contract, c1 ≼ c -> c2 ≼ c -> (c1 ⊔ c2) ≼ c.
Proof.
  intros [a g] [a1 g1] [a2 g2].
  unfold refines ; simpl.
  intros [A1 G1] [A2 G2].
  split.
  firstorder.
  unfold SubsetEq, inter, union, compl, In in *.
  intros x [H | [H | H] ].
  firstorder.
  apply (G1 x) ; assumption.
  apply (G2 x) ; assumption.
Qed.

Theorem lub_sym : forall c1 c2 : contract, (c1 ⊔ c2) ≍ (c2 ⊔ c1).
Proof.
  firstorder.
Qed.

Theorem compose_correct_implements : forall (σ1 σ2 : component) (c1 c2 : contract),
  σ1 ⊢ c1 -> σ2 ⊢ c2 -> σ1 ∩ σ2 ⊢ c1 ⊗ c2.
Proof.
  firstorder.
Qed.

Theorem compose_correct_provides : forall (e1 e2 : environment) (c1 c2 : contract),
  provides e1 c1 -> provides e2 c2 -> provides (e1 ∩ e2) (c1 ⊗ c2).
Proof.
  firstorder.
Qed.

Theorem compose_assumption : forall c1 c2 : contract,
  A (c1 ⊗ c2) ⊆ (c1).(A) ∪ ¬ (c2).(G).
Proof.
  intros [A1 G1] [A2 G2].
  simpl.
  rewrite morgan2.
  rewrite <- morgan.
  rewrite comp_comp.
  rewrite <- morgan.
  rewrite comp_comp.
  unfold inter, union, compl, SubsetEq, In.
  intro s.
  firstorder.
Qed.

Theorem compose_correct : forall (c1 c2 : contract) (σ1 σ2 : component) (e : environment),
  σ1 ⊢ c1 -> σ2 ⊢ c2 -> provides e (c1 ⊗ c2) ->
  (σ1 ∩ σ2 ⊢ c1 ⊗ c2 /\ provides (e ∩ σ2) c1 /\ provides (e ∩ σ1) c2).
Proof.
  intros [A1 G1] [A2 G2].
  unfold compose, implements, provides, satisfies.
  simpl.
  intros.
  split.
  - firstorder.
  - split.
    + apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ σ2).
      { firstorder. }
      apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ (¬ A2 ∪ G2)).
      {  firstorder. }
      rewrite inter_commut_eq.
      rewrite inter_distrib.
      rewrite morgan2.
      rewrite inter_distrib.
      rewrite inter_anoa.
      rewrite <- morgan.
      rewrite comp_comp.
      firstorder.
    + apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ σ1).
      { firstorder. }
      apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ (¬ A1 ∪ G1)).
      * unfold inter, union, compl, SubsetEq, In in *.
        intros x [HG1 HS1].
        split ; try assumption.
        apply (H x) ; assumption.
      * rewrite inter_commut_eq.
        rewrite inter_distrib.
        rewrite morgan2.
        rewrite inter_distrib.
        rewrite inter_anoa.
        rewrite <- morgan.
        rewrite comp_comp.
        firstorder.
Qed.


Lemma inter_idem_eq : forall (a : assertion), a ∩ a = a.
Proof.
  intros.
  apply Eq_extensionality.
  apply inter_idem.
Qed.

Lemma inter_add : forall (s e : behavior), e  ∈ inter {s} {s} -> e = s.
Proof.
  intros.
  rewrite inter_idem_eq in H.
  generalize H.
  unfold  singleton, add, In, emptyset.
  tauto.
Qed.

Theorem compose_set : forall (c1 c2 c : contract),
  (forall (σ1 σ2 : component) (e : environment), σ1 ⊢ c1 -> σ2 ⊢ c2 -> provides e c ->
  (σ1 ∩ σ2 ⊢ c /\ provides (e ∩ σ2) c1 /\ provides (e ∩ σ1) c2)) ->
  (# c1).(G) ∩ (# c2).(G) ⊆ (# c).(G) /\
  (# c).(A) ∩ (# c2).(G) ⊆ (# c1).(A) /\ (# c).(A) ∩ (# c1).(G) ⊆ (# c2).(A).
Proof.
  intros.
  unfold saturate.
  simpl.
  apply H ; try firstorder.
Qed.

Theorem compose_lowest : forall (c1 c2 c : contract),
  (forall (σ1 σ2 : component) (e : environment), σ1 ⊢ c1 -> σ2 ⊢ c2 -> provides e c ->
  (σ1 ∩ σ2 ⊢ c /\ provides (e ∩ σ2) c1 /\ provides (e ∩ σ1) c2)) -> c1 ⊗ c2 ≼ c.
Proof.
  intros c1 c2 c H0.
  apply compose_set in H0.
  unfold saturate in H0.
  revert H0.
  simpl.
  intros [H1 [H2 H3]].
  unfold refines, compose.
  simpl.
  assert (A c ∩ (¬ A c2 ∪ G c2) ∩ A c ∩ (¬ A c1 ∪ G c1) = A c ∩ ((¬ A c1 ∪ G c1) ∩ (¬ A c2 ∪ G c2))).
  {
    rewrite inter_abac.
    rewrite inter_inter_commut.
    reflexivity.
  }
  split.
  - apply SubsetEq_Trans with
    ((A c ∩ (¬ A c2 ∪ G c2) ∩ A c ∩ (¬ A c1 ∪ G c1)) ∪ ¬ ((¬ A c1 ∪ G c1) ∩ (¬ A c2 ∪ G c2))).
    {
      rewrite H.
      rewrite union_distrib.
      rewrite union_anoa.
      rewrite inter_univ.
      apply union_monotonic_l.
    }
    apply union_monotonic_lr.
    rewrite inter_assoc_eq.
    apply inter_monotonic_lr ; assumption.
    apply SubsetEq_Refl.
  - rewrite <- morgan.
    rewrite comp_comp.
    rewrite inter_union_abb.
    firstorder.
Qed.

Theorem consistent_correct : forall c : contract,
  is_consistent c <-> exists σ, is_not_empty σ /\ implements σ c.
Proof.
  intros.
  split.
  - unfold is_consistent.
    intros [s Hsat].
    exists {s}.
    unfold implements.
    split.
    + exists s.
      unfold In, singleton, add.
      tauto.
    + intros x.
      unfold singleton, add, In.
      intros [xs_eq | x_in_empty].
      * subst ; assumption.
      * exfalso ; assumption.
  - unfold implements.
    intros [σ [σ_non_empty Hsat]].
    unfold is_consistent.
    destruct σ_non_empty as [s s_in_σ].
    exists s.
    apply Hsat.
    assumption.
Qed.

Theorem compatible_correct : forall c : contract,
  is_compatible c <-> exists e, is_not_empty e /\ provides e c.
Proof.
  intros [A G].
  split.
  - unfold is_compatible, provides.
    simpl.
    intros [s s_in_A].
    exists {s}.
    split.
    + exists s.
      unfold In, singleton, add.
      tauto.
    + intros x.
      unfold singleton, add, In.
      intros [xs_eq | x_in_empty].
      * subst ; assumption.
      * exfalso ; assumption.
  - unfold provides, is_compatible.
    simpl.
    intros [e [e_non_empty Hincl]].
    destruct e_non_empty as [s s_in_e].
    exists s.
    apply Hincl.
    assumption.
Qed.

End one_alphabet.

(* Definition extend_assert {d1 d2 : alphabet} (a1 : assertion d1) : assertion (d1 ∪ d2):= *)
(*     fun (e : behavior (d1 ∪ d2)) => exists e1 : behavior d1, e1 ∈ a1 -> *)
(*       forall v : ident, forall (pv12 : v ∈ d1 ∪ d2) (pv1 : v ∈ d1), *)
(*         e (exist _ v pv12) = e1 (exist _ v pv1). *)

Section two_alphabets.

Context {d1 d2 : alphabet}.
Variable H12 : d1 ⊆ d2.

Definition H'12 (v1 : var d1) : var d2 := let (i,H1) := v1 in exist _ i (H12 i H1).

Definition project (e2 : behavior d2) : behavior d1 :=
  fun v1 => e2 (H'12 v1).

Definition extend_behavior (e1 : behavior d1) : assertion d2 :=
  fun e2 => project e2 = e1.

Definition project_assertion_forall (a : assertion d2) : assertion d1 :=
  fun e1 => extend_behavior e1 ⊆ a.

Definition project_assertion (a : assertion d2) : assertion d1 :=
  fun e1 => exists e2,  e2 ∈ a /\ project e2 = e1.

Definition project_component (σ : component d2) : component d1 :=
  project_assertion σ.

Definition extend_assertion (a1 : assertion d1) : assertion d2 :=
  fun e2 => project e2 ∈ a1.

Definition extend_behavior_default (e1 : behavior d1) : behavior d2 :=
  fun x => let (v, pd2) := x in match in_dec_ident v d1 with
                                | left in_proof => e1 (exist _ v in_proof)
                                | right _ => any_value
                                end
.

Definition project_contract (c2 : contract d2)  : contract d1 :=
  let c2' := saturate _ c2 in
  mkContract _ (project_assertion_forall (c2'.(A _))) (project_assertion (G _ c2')).

Definition extend_contract (c1 : contract d1) : contract d2 :=
  let c1' := saturate _ c1 in
  mkContract _ (extend_assertion (A _ c1')) (extend_assertion (G _ c1')).


(* Lemma project_extend_behavior : forall (e1 : behavior d1), *)
(*   project (extend_behavior_default e1) = e1. *)
(* Proof. *)
(*   intros e1. *)
(*   unfold extend_behavior_default, project. *)
(*   extensionality x. *)
(*   destruct x. *)
(*   simpl. *)
(*   case (in_dec_ident x d1). *)
(*   intro i0. *)
(*   cut (i = i0). *)
(*   intro H ; rewrite H ; tauto. *)
(*   apply proof_irrelevance. *)
(*   tauto. *)
(* Qed. *)

(* Lemma extend_project_1 : forall (a1 : assertion d1), *)
(*   a1 ⊆ project_assertion (extend_assertion a1). *)
(* Proof. *)
(*   intros. *)
(*   unfold SubsetEq. *)
(*   intros e1 Hea. *)
(*   unfold project_assertion, In, extend_assertion. *)
(*   exists (extend_behavior_default e1). *)
(*   rewrite project_extend_behavior. *)
(*   tauto. *)
(* Qed. *)

Lemma extend_project_2 : forall (a1 : assertion d1),
  project_assertion (extend_assertion a1) ⊆ a1.
Proof.
  intros a1 e1 [e2 [H1 H2]].
  rewrite <- H2.
  tauto.
Qed.

(* Lemma extend_project : forall (a1 : assertion d1), *)
(*   project_assertion (extend_assertion a1) = a1. *)
(* Proof. *)
(*   intros a1. *)
(*   apply Eq_extensionality. *)
(*   apply SubsetEq_Asym. *)
(*   apply extend_project_2. *)
(*   apply extend_project_1. *)
(* Qed. *)

Lemma extend_project_forall_1 : forall (a1 : assertion d1),
  a1 ⊆ project_assertion_forall (extend_assertion a1).
Proof.
  unfold SubsetEq.
  intros a1 e1 H1.
  unfold project_assertion_forall, In, extend_behavior, extend_assertion, SubsetEq, In.
  intros  e2 Hr.
  rewrite Hr.
  assumption.
Qed.

(* Lemma extend_project_forall_2 : forall (a1 : assertion d1), *)
(*   project_assertion_forall (extend_assertion a1) ⊆ a1. *)
(* Proof. *)
(*   intros a1 e1. *)
(*   unfold project_assertion_forall, extend_assertion, In. *)
(*   cut (exists e2 : behavior d2, project e2 = e1). *)
(*   intros [e2 Hr] Hin. *)
(*   rewrite <- Hr. *)
(*   apply Hin ; tauto. *)
(*   exists (extend_behavior_default e1). *)
(*   apply project_extend_behavior. *)
(* Qed. *)

(* Lemma extend_project_forall : forall (a1 : assertion d1), *)
(*   project_assertion_forall (extend_assertion a1) = a1. *)
(* Proof. *)
(*   intros a1. *)
(*   apply Eq_extensionality. *)
(*   apply SubsetEq_Asym. *)
(*   apply extend_project_forall_2. *)
(*   apply extend_project_forall_1. *)
(* Qed. *)

Lemma extend_union_1 : forall (a b : assertion d1),
  extend_assertion (a ∪ b) ⊆ extend_assertion a ∪ extend_assertion b.
Proof.
  firstorder.
Qed.

Lemma extend_union_2 : forall (a b : assertion d1),
  extend_assertion a ∪ extend_assertion b ⊆ extend_assertion (a ∪ b).
Proof.
  firstorder.
Qed.

Lemma extend_union : forall (a b : assertion d1),
  extend_assertion a ∪ extend_assertion b = extend_assertion (a ∪ b).
Proof.
  intros a b.
  apply Eq_extensionality.
  apply SubsetEq_Asym.
  apply extend_union_2.
  apply extend_union_1.
Qed.

Lemma extend_neg_1 : forall (a : assertion d1),
  extend_assertion (¬ a) ⊆ ¬ (extend_assertion a).
Proof.
  firstorder.
Qed.

Lemma extend_neg_2 : forall (a : assertion d1),
  ¬ (extend_assertion a) ⊆ extend_assertion (¬ a).
Proof.
  firstorder.
Qed.

Lemma extend_neg : forall (a : assertion d1),
  ¬ (extend_assertion a) = extend_assertion (¬ a).
Proof.
  intros a.
  apply Eq_extensionality.
  apply SubsetEq_Asym.
  apply extend_neg_2.
  apply extend_neg_1.
Qed.


(* Lemma project_extend_contract : forall (c1 : contract d1), *)
(*   (project_contract (extend_contract c1)) = saturate _ c1. *)
(* Proof. *)
(*   intros[a1 g1]. *)
(*   unfold project_contract, extend_contract, saturate. *)
(*   simpl. *)
(*   f_equal. *)
(*   apply extend_project_forall. *)
(*   rewrite extend_neg, extend_union, extend_project. *)
(*   apply Eq_extensionality. *)
(*   firstorder. *)
(* Qed. *)

Lemma extend_subset : forall (a b : assertion d1),
  a ⊆ b -> extend_assertion a ⊆ extend_assertion b.
Proof.
  firstorder.
Qed.

(* Lemma implements_extension : forall (c : contract d1) (σ : component d1), *)
(*   implements d1 σ c <-> implements d2 (extend_assertion σ) (extend_contract c). *)
(* Proof. *)
(*   split. *)
(*   - firstorder. *)
(*   - unfold extend_contract, extend_assertion. *)
(*     destruct c as [A G]. *)
(*     unfold implements, satisfies, In. *)
(*     simpl. *)
(*     intros H. *)
(*     intros b b_in_σ. *)
(*     specialize (H (extend_behavior_default b)). *)
(*     unfold union, compl, In in H . *)
(*     rewrite (project_extend_behavior b) in H. *)
(*     firstorder. *)
(* Qed. *)

End two_alphabets.

Section three_alphabets.
Context {d1 d2 D : alphabet}.
Variable H1 : d1 ⊆ D.
Variable H2 : d2 ⊆ D.

Definition implements_ext (σ : component D) (c1 : contract d1) : Prop :=
  implements D σ (extend_contract H1 c1).

Definition provides_ext (e : environment D) (c1 : contract d1)  : Prop :=
  provides _ e (extend_contract H1 c1).

Definition compose_ext (c1 : contract d1) (c2 : contract d2) : contract D :=
  compose _ (extend_contract H1 c1) (extend_contract H2 c2).

Definition glb_ext (c1 : contract d1) (c2 : contract d2) : contract D :=
  glb _ (extend_contract H1 c1) (extend_contract H2 c2).

Definition refines_ext (c1 : contract d1) (c2: contract d2) : Prop :=
  refines _ (extend_contract H1 c1) (extend_contract H2 c2).

End three_alphabets.

Section any_alphabets.

Context {d1 d2 d3 d4 d5 d6 D: alphabet}.
Context { H1 : d1 ⊆ D}.
Variable H2 : d2 ⊆ D.
Variable H3 : d3 ⊆ D.
Variable H4 : d4 ⊆ D.
Variable H5 : d5 ⊆ D.
Variable HD : D ⊆ D.

Notation "c1 ≼ c2" := (@refines_ext _ _ D _ _ c1 c2) (at level 70, no associativity).
Notation "σ ⊢ c" := (implements_ext _ _ c σ)(at level 70, no associativity).

(* Theorem implement_extended_correct : forall (c1 : contract d1) (σ2 : compoent d2), *)

Theorem satifie_ext_proj : forall (s : behavior D) (c2 : contract d2),
  satisfies D s (extend_contract H2 c2) <->
  satisfies d2 (project H2 s) c2.
Proof.
  intros s [A G].
  unfold extend_contract, satisfies.
  simpl.
  split.
  - intros.
    destruct H as [H | H].
    + left.
      assumption.
    + assumption.
  - intros.
    right.
    assumption.
Qed.


Theorem implements_ext_proj : forall (c2 : contract d2) (σ : component D),
  implements D σ (extend_contract H2 c2) <-> implements d2 (project_assertion H2 σ) c2.
Proof.
  intros.
  split.
  - unfold implements.
    unfold project_assertion.
    unfold In.
    intros Himpl s2.
    intros [sD [sD_in_σ proj_sD_s2jj]].
    specialize (Himpl sD sD_in_σ).
    subst.
    rewrite <- satifie_ext_proj.
    assumption.
  -  unfold implements.
    intros.
    specialize (H (project H2 s)).
    rewrite satifie_ext_proj.
    apply H.
    unfold project_assertion, In.
    exists s.
    tauto.
Qed.

Theorem refines_ext_correct : forall (c1 : contract d1) (c2 : contract d2),
  refines_ext H1 H2 c1 c2 <->
  (forall σ : component D, implements_ext H1 σ c1 -> implements_ext H2 σ c2) /\
  (forall e : environment D, provides_ext H2 e c2 -> provides_ext H1 e c1).
Proof.
  clear H5 H4 H3.
  unfold refines_ext.
  intros.
  rewrite refines_correct.
  reflexivity.
Qed.

Theorem compose_ext_correct : forall (c1 : contract d1) (c2 : contract d2)
  (σ1 : component D) (σ2 : component D) (e : environment D),
  implements_ext H1 σ1 c1 -> implements_ext H2 σ2 c2 ->
  provides D e (compose_ext H1 H2 c1 c2) ->
  (implements D (σ1 ∩ σ2) (compose_ext H1 H2 c1 c2) /\
   provides_ext H1 (e ∩ σ2) c1 /\ provides_ext H2 (e ∩ σ1) c2).
Proof.
  intros.
  apply compose_correct ; assumption.
Qed.

Theorem glb_ext_correct : forall (c1 : contract d1) (c2 : contract d2),
       refines D (glb_ext H1 H2 c1 c2) (extend_contract H1 c1) /\
       refines D (glb_ext H1 H2 c1 c2) (extend_contract H2 c2) /\
       (forall c : contract D,
        refines D c (extend_contract H1 c1) ->
        refines D c (extend_contract H2 c2) ->
        refines D c (glb_ext H1 H2 c1 c2)).
Proof.
  clear H3 H4 H5.
  intros.
  generalize (glb_correct D (extend_contract H1 c1) (extend_contract H2 c2)).
  intros [Href1 [Href2 Hlow]].
  split.
  - assumption.
  - split.
    + assumption.
    + assumption.
Qed.

Theorem project_abstract : forall (c : contract D),
  refines D c (extend_contract H1 (project_contract H1 c)).
Proof.
  intros [A G].
  split.
  - simpl.
    unfold extend_assertion, project_assertion_forall, In.
    intros b.
    unfold In.
    intros Hinc.
    apply Hinc.
    reflexivity.
  - simpl.
    intros b H.
    right.
    right.
    unfold project_assertion.
    unfold In.
    simpl.
    exists b.
    tauto.
Qed.

Theorem project_smallest_abstract : forall (c : contract D) (c1 : contract d1),
  refines D c (extend_contract H1 c1) ->
  refines d1 (project_contract H1 c) c1.
Proof.
  intros.
  unfold refines.
  split.
  - unfold saturate.
    simpl.
    intros s1 s1_in_A.
    unfold project_assertion_forall, In.
    intros s s_ext_s1.
    apply H.
    unfold saturate.
    simpl.
    unfold extend_assertion, In.
    unfold extend_behavior, In in s_ext_s1.
    subst.
    assumption.
  - unfold saturate.
    simpl.
    intros s1 s1_in_G.
    destruct s1_in_G as [s1_in_A |s1_in_G].
    + left.
      revert H.
      unfold refines.
      unfold saturate.
      simpl.
      intros [? _].
      intro.
      apply s1_in_A.
      unfold project_assertion_forall, In.
      unfold extend_behavior.
      intros s s_ext_s1.
      apply H.
      unfold In in s_ext_s1.
      subst.
      assumption.
    + revert H.
      unfold refines, saturate.
      simpl.
      intros [_ ?].
      unfold project_assertion, In in s1_in_G.
      destruct s1_in_G as [s [HS ?]].
      subst.
      specialize (H s HS).
      destruct H as [H | H].
      * left.
        intro.
        apply H.
        assumption.
      * assumption.
Qed.

(* Lemma extend_assertion_refl : forall (a1 : assertion d1), *)
(*   extend_assertion (SubsetEq_Refl d1) a1 = a1. *)
(* Proof. *)
(*   (1* intros a1. *1) *)
(*   (1* apply Eq_extensionality. *1) *)
(*   unfold Eq. *)
(*   unfold extend_assertion, project, In. *)
(*   intro e1. *)
(*   cut ((fun v1 : {v : ident | d1 v} => e1 (H'12 (SubsetEq_Refl d1) v1)) = e1). *)
(*    intros Hr. *)
(*    rewrite Hr. *)
(*    tauto. *)
(*    apply behavior_extensionality. *)
(*    unfold behavior_equiv. *)
(*    intros [v pv]. *)
(*    f_equal. *)
(*    unfold H'12. *)
(*    f_equal. *)
(*    apply proof_irrelevance. *)
(* Qed. *)

(* Lemma extension_contract_refl : forall (c1 : contract d1), *)
(*   equiv d1 (extend_contract (SubsetEq_Refl d1) c1) c1. *)
(* Proof. *)
(*   intros [a1 g1]. *)
(*   unfold equiv, refines, extend_contract. *)
(*   simpl. *)
(*   rewrite extend_assertion_refl. *)
(*   rewrite extend_assertion_refl. *)
(*   repeat split ; apply SubsetEq_Refl ; firstorder. *)
(* Qed. *)

End any_alphabets.

End theory_defined.


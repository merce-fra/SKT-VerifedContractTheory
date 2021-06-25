Require Import Sets.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Classical.
Include CoqSet.

Definition set := @τ.

Class Theory := {
  B : Type ;
  ident : Type ;
  any_B : B ;
  eq_dec_ident : forall x y : ident, {x = y} + {x <> y} ;
  in_dec_ident : forall (v : ident) (d : set ident), {v ∈ d} + {v ∉ d}
}.


Section theory_defined.

Context {theo : Theory}.

Instance discr_ident : Discr ident := {eq_dec := eq_dec_ident}.

Definition domain : Type := set ident.

Section one_domain.

Variable d : domain.
Definition var := { v : ident | v ∈ d }.
Definition state : Type :=  forall x : {v : ident | v ∈ d}, B.
Definition assertion : Type := set state.
Definition component := assertion.
Definition environment := component.
Record contract : Type := mkContract {A : assertion ; G : assertion}.

Definition state_equiv (s1 : state) (s2 : state) : Prop :=
  forall x : {v : ident | v ∈ d}, s1 x = s2 x.

Theorem state_extensionality : forall (s1 s2 : state),
  state_equiv s1 s2 -> s1 = s2.
Proof.
  unfold state_equiv, state, domain.
  intros.
  extensionality x.
  apply H.
Qed.

Definition satisfies (s : state) (c : contract) : Prop :=
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

Definition is_consistent (c : contract) : Prop := exists s : state, satisfies s c.

Definition is_compatible (c : contract) : Prop := exists s : state, s ∈ (c.(A)).

Lemma is_satured_sature : forall c : contract, is_saturated (saturate c).
Proof.
  firstorder.
Qed.

Lemma implements_saturate_implements : forall (σ : component) (c : contract),
  σ ⊢ (saturate c) -> σ ⊢ c.
Proof.
  firstorder.
Qed.

Theorem saturate_sound : forall (s : state) (c : contract),
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
  unfold SubsetEq.
  intros s Hs.
  generalize (H2 {s}).
  unfold provides.
  simpl.
  unfold singleton, add, SubsetEq, In.
  intro Hx.
  apply Hx.
  firstorder.
  rewrite H.
  exact Hs.
  left ; reflexivity.
  unfold SubsetEq.
  intros s Hs.
  generalize (H1 {s}).
  unfold implements.
  simpl.
  unfold singleton, add, SubsetEq, In.
  intro Hx.
  apply Hx.
  intros x [Hxs | Hnul].
  subst.
  exact Hs.
  exfalso.
  exact Hnul.
  left ; reflexivity.
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
  firstorder.
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

Theorem saturate_satisfies : forall (s : state) (c : contract),
  satisfies s c <-> satisfies s (saturate c).
Proof.
  firstorder.
Qed.

Theorem glb_refines_l : forall c1 c2 : contract, (c1 ⊓ c2) ≼ c2.
Proof.
  firstorder.
Qed.

Theorem glb_refines_r : forall c1 c2 : contract, (c1 ⊓ c2) ≼ c1.
Proof.
  firstorder.
Qed.

Theorem glb_greatest : forall c c1 c2 : contract, c ≼ c1 -> c ≼ c2 -> c ≼ (c1 ⊓ c2).
Proof.
  intros [a g] [a1 g1] [a2 g2].
  unfold refines ; simpl ; split.
  firstorder.
  unfold SubsetEq, inter, union, compl, In in *.
  intro x.
  firstorder.
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
  firstorder.
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
  unfold inter, union, compl, SubsetEq, In.
  intro s.
  firstorder.
  classical_right.
  firstorder.
Qed.

Lemma morgan : forall a b : assertion,  ¬ a ∩ ¬ b = ¬ (a ∪ b).
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma morgan2 : forall a b : assertion, ¬ (a ∩ b) = ¬ a ∪ ¬ b.
Proof.
  intros.
  apply Eq_extensionality.
  split ; try firstorder.
  case classic with (x ∈ a).
  intro.
  right.
  tauto.
  left.
  tauto.
Qed.

Lemma inter_commut_eq : forall s₁ s₂: assertion, s₁ ∩ s₂ = s₂ ∩ s₁.
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma inter_distrib : forall a b c : assertion, a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c).
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma inter_anoa : forall a : assertion, a ∩ ¬ a = emptyset.
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma comp_comp : forall a : assertion, ¬ (¬ a) = a.
Proof.
  intro.
  apply Eq_extensionality.
  split ;
  case classic with (x ∈ a) ; firstorder.
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
  firstorder.
  split.
  apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ σ2).
  firstorder.
  apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ (¬ A2 ∪ G2)).
  firstorder.
  rewrite inter_commut_eq.
  rewrite inter_distrib.
  rewrite morgan2.
  rewrite inter_distrib.
  rewrite inter_anoa.
  rewrite <- morgan.
  rewrite comp_comp.
  firstorder.
  apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ σ1).
  firstorder.
  apply SubsetEq_Trans with ((A1 ∩ A2 ∪ ¬ ((¬ A1 ∪ G1) ∩ (¬ A2 ∪ G2))) ∩ (¬ A1 ∪ G1)).
  firstorder.
  rewrite inter_commut_eq.
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

Lemma inter_add : forall (s e : state), e  ∈ inter {s} {s} -> e = s.
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

Lemma union_distrib : forall (a b c : assertion), (a ∩ b) ∪ c = (a ∪ c) ∩ (b ∪ c).
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma union_anoa : forall a : assertion, a ∪ ¬ a = Univ.
Proof.
  intros.
  apply Eq_extensionality.
  split.
  firstorder.
  firstorder.
  case classic with (x ∈ a) ; firstorder.
Qed.

Lemma inter_univ : forall a : assertion, a ∩ Univ = a.
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma inter_abac : forall (a b c : assertion), a ∩ b ∩ a ∩ c = a ∩ (b ∩ c).
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma inter_inter_commut : forall (a b c : assertion), a ∩ (b ∩ c) = a ∩ (c ∩ b).
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma inter_union_abb : forall (a b : assertion), (a ∩ b) ∪ b =  b.
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma inter_monotonic_lr : forall (a b c d : assertion), a ⊆ b -> c ⊆ d -> a ∩ c ⊆ b ∩ d.
Proof.
  firstorder.
Qed.

Lemma inter_assoc_eq : forall (a b c : assertion), a ∩ b ∩ c = a ∩ (b ∩ c).
Proof.
  intros.
  apply Eq_extensionality.
  firstorder.
Qed.

Theorem compose_lowest : forall (c1 c2 c : contract),
  (forall (σ1 σ2 : component) (e : environment), σ1 ⊢ c1 -> σ2 ⊢ c2 -> provides e c ->
  (σ1 ∩ σ2 ⊢ c /\ provides (e ∩ σ2) c1 /\ provides (e ∩ σ1) c2)) -> c1 ⊗ c2 ≼ c.
Proof.
  intros c1 c2 c H0.
  apply compose_set in H0.
  unfold saturate in H0.
  generalize H0.
  simpl.
  intros [H1 [H2 H3]].
  unfold refines, compose.
  simpl.
  assert (A c ∩ (¬ A c2 ∪ G c2) ∩ A c ∩ (¬ A c1 ∪ G c1) = A c ∩ ((¬ A c1 ∪ G c1) ∩ (¬ A c2 ∪ G c2))).
  rewrite inter_abac.
  rewrite inter_inter_commut.
  reflexivity.
  split.
  apply SubsetEq_Trans with
    ((A c ∩ (¬ A c2 ∪ G c2) ∩ A c ∩ (¬ A c1 ∪ G c1)) ∪ ¬ ((¬ A c1 ∪ G c1) ∩ (¬ A c2 ∪ G c2))).
  rewrite H.
  rewrite union_distrib.
  rewrite union_anoa.
  rewrite inter_univ.
  apply union_monotonic_l.
  apply union_monotonic_lr.
  rewrite inter_assoc_eq.
  apply inter_monotonic_lr ; assumption.
  apply SubsetEq_Refl.
  rewrite <- morgan.
  rewrite comp_comp.
  rewrite inter_union_abb.
  firstorder.
Qed.

End one_domain.

(* Definition extend_assert {d1 d2 : domain} (a1 : assertion d1) : assertion (d1 ∪ d2):= *)
(*     fun (e : state (d1 ∪ d2)) => exists e1 : state d1, e1 ∈ a1 -> *)
(*       forall v : ident, forall (pv12 : v ∈ d1 ∪ d2) (pv1 : v ∈ d1), *)
(*         e (exist _ v pv12) = e1 (exist _ v pv1). *)

Section two_domains.

Context {d1 d2 : domain}.
Variable H12 : d1 ⊆ d2.

Definition H'12 (v1 : var d1) : var d2 := let (i,H1) := v1 in exist _ i (H12 i H1).

Definition project (e2 : state d2) : state d1 :=
  fun v1 => e2 (H'12 v1).

Definition extend_state (e1 : state d1) : assertion d2 :=
  fun e2 => project e2 = e1.

Definition project_assertion_forall (a : assertion d2) : assertion d1 :=
  fun e1 => extend_state e1 ⊆ a.

Definition project_assertion (a : assertion d2) : assertion d1 :=
  fun e1 => exists e2,  e2 ∈ a /\ project e2 = e1.

Definition extend_assertion (a1 : assertion d1) : assertion d2 :=
  fun e2 => project e2 ∈ a1.

Definition extend_state_default (e1 : state d1) : state d2 :=
  fun x => let (v, pd2) := x in match in_dec_ident v d1 with
                                | left in_proof => e1 (exist _ v in_proof)
                                | right _ => any_B
                                end
.

Definition project_contract (c2 : contract d2)  : contract d1 :=
  let c2' := saturate _ c2 in
  mkContract _ (project_assertion_forall (c2'.(A _))) (project_assertion (G _ c2')).

Definition extend_contract (c1 : contract d1) : contract d2 :=
  let c1' := saturate _ c1 in
  mkContract _ (extend_assertion (A _ c1')) (extend_assertion (G _ c1')).


Lemma project_extend_state : forall (e1 : state d1),
  project (extend_state_default e1) = e1.
Proof.
  intros e1.
  unfold extend_state_default, project.
  extensionality x.
  destruct x.
  simpl.
  case (in_dec_ident x d1).
  intro i0.
  cut (i = i0).
  intro H ; rewrite H ; tauto.
  apply proof_irrelevance.
  tauto.
Qed.

Lemma extend_project_1 : forall (a1 : assertion d1),
  a1 ⊆ project_assertion (extend_assertion a1).
Proof.
  intros.
  unfold SubsetEq.
  intros e1 Hea.
  unfold project_assertion, In, extend_assertion.
  exists (extend_state_default e1).
  rewrite project_extend_state.
  tauto.
Qed.

Lemma extend_project_2 : forall (a1 : assertion d1),
  project_assertion (extend_assertion a1) ⊆ a1.
Proof.
  intros a1 e1 [e2 [H1 H2]].
  rewrite <- H2.
  tauto.
Qed.

Lemma extend_project : forall (a1 : assertion d1),
  project_assertion (extend_assertion a1) = a1.
Proof.
  intros a1.
  apply Eq_extensionality.
  apply SubsetEq_Asym.
  apply extend_project_2.
  apply extend_project_1.
Qed.

Lemma extend_project_forall_1 : forall (a1 : assertion d1),
  a1 ⊆ project_assertion_forall (extend_assertion a1).
Proof.
  unfold SubsetEq.
  intros a1 e1 H1.
  unfold project_assertion_forall, In, extend_state, extend_assertion, SubsetEq, In.
  intros  e2 Hr.
  rewrite Hr.
  assumption.
Qed.

Lemma extend_project_forall_2 : forall (a1 : assertion d1),
  project_assertion_forall (extend_assertion a1) ⊆ a1.
Proof.
  intros a1 e1.
  unfold project_assertion_forall, extend_assertion, In.
  cut (exists e2 : state d2, project e2 = e1).
  intros [e2 Hr] Hin.
  rewrite <- Hr.
  apply Hin ; tauto.
  exists (extend_state_default e1).
  apply project_extend_state.
Qed.

Lemma extend_project_forall : forall (a1 : assertion d1),
  project_assertion_forall (extend_assertion a1) = a1.
Proof.
  intros a1.
  apply Eq_extensionality.
  apply SubsetEq_Asym.
  apply extend_project_forall_2.
  apply extend_project_forall_1.
Qed.

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


Lemma project_extend_contract : forall (c1 : contract d1),
  (project_contract (extend_contract c1)) = saturate _ c1.
Proof.
  intros[a1 g1].
  unfold project_contract, extend_contract, saturate.
  simpl.
  f_equal.
  apply extend_project_forall.
  rewrite extend_neg, extend_union, extend_project.
  apply Eq_extensionality.
  firstorder.
Qed.

Lemma extend_subset : forall (a b : assertion d1),
  a ⊆ b -> extend_assertion a ⊆ extend_assertion b.
Proof.
  firstorder.
Qed.

Lemma implements_extension : forall (c : contract d1) (σ : component d1),
  implements d1 σ c -> implements d2 (extend_assertion σ) (extend_contract c).
Proof.
  firstorder.
Qed.

End two_domains.

Section three_domains.
Context {d1 d2 d3 : domain}.
Variable H1 : d1 ⊆ d3.
Variable H2 : d2 ⊆ d3.

Definition extended_compose (c1 : contract d1) (c2 : contract d2) : contract d3 :=
  compose _ (extend_contract H1 c1) (extend_contract H2 c2).

Definition refines_extended (c1 : contract d1) (c2: contract d2) : Prop :=
  refines _ (extend_contract H1 c1) (extend_contract H2 c2).

Notation "c1 ≼ c2" := (refines_extended c1 c2) (at level 70, no associativity).

(* Relation d'ordre *)

Definition implements_extended (c1 : contract d1) (σ2 : component d2) : Prop :=
  implements _ (extend_assertion H2 σ2) (extend_contract H1 c1).

Notation "σ ⊢ c" := (implements_extended σ c) (at level 70, no associativity).

Theorem extended_compose_correct : forall (c1 : contract d1) (c2 : contract d2)
  (σ1 : component d1) (σ2 : component d2),
  implements _ σ1 c1 -> implements _ σ2 c2 ->
  implements _ (extend_assertion H1 σ1 ∩ extend_assertion H2 σ2) (extended_compose c1 c2).
Proof.
  intros.
  apply compose_correct_implements.
  apply implements_extension ; exact H.
  apply implements_extension ; assumption.
Qed.

Lemma extend_assertion_refl : forall (a1 : assertion d1),
  extend_assertion (SubsetEq_Refl d1) a1 = a1.
Proof.
  intros a1.
  apply Eq_extensionality.
  unfold Eq.
  unfold extend_assertion, project, In.
  intro e1.
  cut ((fun v1 : {v : ident | d1 v} => e1 (H'12 (SubsetEq_Refl d1) v1)) = e1).
   intros Hr.
   rewrite Hr.
   tauto.
   apply state_extensionality.
   unfold state_equiv.
   intros [v pv].
   f_equal.
   unfold H'12.
   f_equal.
   apply proof_irrelevance.
Qed.

Lemma extension_contract_refl : forall (c1 : contract d1),
  equiv d1 (extend_contract (SubsetEq_Refl d1) c1) c1.
Proof.
  intros [a1 g1].
  unfold equiv, refines, extend_contract.
  simpl.
  rewrite extend_assertion_refl.
  rewrite extend_assertion_refl.
  repeat split ; apply SubsetEq_Refl ; firstorder.
Qed.
End three_domains.

End theory_defined.


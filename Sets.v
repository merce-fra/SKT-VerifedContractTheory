(* Set.v ---
 *
 * Filename: Set.v
 * Description: Draft of Set Library
 * Author: Benoît Boyer
 * Maintainer:
 * Created: ven. janv. 29 08:49:43 2021 (+0100)
 * Version:
 *)



(* The type Γ is the type of the elements in the set.
 * We assume The type is provided as type inhabited with discriminable elements.
 * In particular, it is useful to prove the last Theorem [add_remove].
 *)

Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Class Discr(Γ: Type) := {
      eq_dec : forall x y: Γ, { x = y } + { x <> y }
  }.

(* TODO: Classes for Groups, Ordered sets, Monoids lattices? *)

Module CoqSet.

  Definition τ {Γ: Type} := Γ -> Prop.

  Definition In {Γ: Type} (x: Γ) (s: τ) : Prop := s x.
  Notation "x ∈ s" := (@In _ x s) (at level 70, no associativity).
  Notation "x ∉ s" := (~ @In _ x s) (at level 70, no associativity).

  Definition SubsetEq {Γ: Type} (s₁ s₂: τ) : Prop :=
    forall x: Γ, x ∈ s₁ -> x ∈ s₂.
  Notation "u ⊆ v" := (@SubsetEq _ u v) (at level 70, no associativity).

  Definition Eq {Γ: Type} (s₁ s₂: τ) : Prop :=
    forall x: Γ, x ∈ s₁ <-> x ∈ s₂.
  Notation "u == v" := (@Eq _ u v) (at level 70, no associativity).

  Theorem Eq_extensionality: forall {Γ: Type} (s₁ s₂ : @τ Γ),
    s₁ == s₂ -> s₁ = s₂.
  Proof.
    unfold τ, Eq, In.
    intros.
    apply functional_extensionality.
    intro x.
    apply propositional_extensionality.
    auto.
  Qed.

  Theorem SubsetEq_Refl {Γ: Type} :
    forall s: @τ Γ,     s ⊆ s.
  Proof.
    firstorder.
  Qed.

  Theorem SubsetEq_Trans {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,      s₁ ⊆ s₂ -> s₂ ⊆ s₃ -> s₁ ⊆ s₃.
  Proof.
    firstorder.
  Qed.

  Theorem SubsetEq_Asym {Γ: Type} :
    forall s₁ s₂: @τ Γ, s₁ ⊆ s₂ -> s₂ ⊆ s₁ -> s₁ == s₂.
  Proof.
    firstorder.
  Qed.

  Theorem Eq_Refl {Γ: Type} :
    forall s: @τ Γ,   s == s.
  Proof.
    firstorder.
  Qed.

  Theorem Eq_Sym {Γ: Type} :
    forall s₁ s₂: @τ Γ, s₁ == s₂ -> s₂ == s₁.
  Proof.
    firstorder.
  Qed.

  Theorem Eq_Trans {Γ: Type} :
    forall  s₁ s₂ s₃: @τ Γ,     s₁ == s₂ -> s₂ == s₃ -> s₁ == s₃.
  Proof.
    firstorder.
  Qed.
  (** TODO: Once we proved Eq is an equivalence relation (RST), it could be
            nice to register a monoid with the Boolean operations: helpful for
            manual rewriting in proof. *)

  (** The empty set *)
  Definition emptyset {Γ: Type} : τ := fun _: Γ => False.

  Notation "∅" := (@emptyset _).
  (* TODO: No need to set the level here. To be confirmed by looking
     at the definition of the notation for List.nil ([]) for
     instance... *)

  Theorem emptyset_is_empty {Γ: Type} :
    forall x: Γ,        x ∉ ∅.
  Proof.
    firstorder.
  Qed.

  (** The universe set *)
  Definition Univ {Γ: Type} : τ :=
    fun (_: Γ) => True.

  Theorem Univ_is_full {Γ: Type} :
    forall x: Γ,        x ∈ Univ.
  Proof.
    firstorder.
  Qed.

  Theorem emptyset_is_bot {Γ: Type} :
    forall s: @τ Γ,        ∅ ⊆ s.
  Proof.
    firstorder.
  Qed.

  Theorem Univ_is_top {Γ: Type} :
    forall s: @τ Γ,     s ⊆ Univ.
  Proof.
    firstorder.
  Qed.

  (** Boolean [union] and [inter]section *)
  Definition union {Γ: Type} (s₁ s₂: τ) : τ :=
    fun x: Γ => x ∈ s₁ \/ x ∈ s₂.
  Notation "u ∪ v" := (@union _ u v) (at level 61, left associativity).
  (* TODO: Level 61 is set arbitrarily, must be checked against ( + ) for instance... *)

  Definition inter {Γ: Type} (s₁ s₂: τ) : τ :=
    fun x: Γ => x ∈ s₁ /\ x ∈ s₂.
  Notation "u ∩ v" := (@inter _ u v) (at level 51, left associativity).
  (* TODO: Level 50 is set arbitrarily, must be checked against ( * ) for instance... *)

  Theorem union_commut {Γ: Type} :
    forall s₁ s₂: @τ Γ,         s₁ ∪ s₂ == s₂ ∪ s₁.
  Proof.
    firstorder.
  Qed.

  Theorem union_assoc {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,      s₁ ∪ (s₂ ∪ s₃) == (s₁ ∪ s₂) ∪ s₃.
  Proof.
    firstorder.
  Qed.

  Theorem union_emptyset {Γ: Type} :
    forall s: @τ Γ,   s ∪ ∅ == s.
  Proof.
    firstorder.
  Qed.

  Theorem union_Univ {Γ: Type} :
    forall s: @τ Γ,   s ∪ Univ == Univ.
  Proof.
    firstorder.
  Qed.

  Theorem union_idem {Γ: Type} :
    forall s: @τ Γ,   s ∪ s == s.
  Proof.
    firstorder.
  Qed.

  Theorem union_monotonic_l {Γ: Type} :
    forall s₁ s₂: @τ Γ,       s₁ ⊆ s₁ ∪ s₂.
  Proof.
    firstorder.
  Qed.

  Theorem union_monotonic_r {Γ: Type} :
    forall s₁ s₂: @τ Γ,       s₂ ⊆ s₁ ∪ s₂.
  Proof.
    firstorder.
  Qed.

  Theorem union_monotonic_lr {Γ: Type} :
    forall s₁ s₂ s₃ s₄: @τ Γ, s₁ ⊆ s₃ -> s₂ ⊆ s₄ -> s₁ ∪ s₂ ⊆ s₃ ∪ s₄.
  Proof.
    firstorder.
  Qed.

  Theorem in_union_monotonic_l {Γ: Type} :
    forall (s₁ s₂: @τ Γ) (x : Γ),       x ∈ s₁ -> x ∈ s₁ ∪ s₂.
  Proof.
    firstorder.
  Qed.

  Theorem inter_commut {Γ: Type} :
    forall s₁ s₂: @τ Γ,       s₁ ∩ s₂ == s₂ ∩ s₁.
  Proof.
    firstorder.
  Qed.

  Theorem inter_assoc {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,    s₁ ∩ (s₂ ∩ s₃) == (s₁ ∩ s₂) ∩ s₃.
  Proof.
    firstorder.
  Qed.

  Theorem inter_emptyset {Γ: Type} :
    forall s: @τ Γ,   s ∩ ∅ == ∅.
  Proof.
    firstorder.
  Qed.

  Theorem inter_Univ {Γ: Type} :
    forall s: @τ Γ,   s ∩ Univ == s.
  Proof.
    firstorder.
  Qed.

  Theorem inter_idem {Γ: Type} :
    forall s: @τ Γ,   s ∩ s == s.
  Proof.
    firstorder.
  Qed.

  Theorem inter_monotonic_l {Γ: Type} :
    forall s₁ s₂: @τ Γ,       s₁ ∩ s₂ ⊆ s₁.
  Proof.
    firstorder.
  Qed.

  (** Boolean *)
  Definition diff {Γ: Type} (s₁ s₂: τ) : τ :=
    fun x: Γ => x ∈ s₁ /\ x ∉ s₂.
  Notation "u \ v" :=  (@diff _ u v) (at level 61, left associativity).

  Theorem diff_emptyset₁ {Γ: Type} :
    forall s: @τ Γ,     s \ ∅ == s.
  Proof.
    firstorder.
  Qed.

  Theorem diff_emptyset₂ {Γ: Type} :
    forall s: @τ Γ,     ∅ \ s == ∅.
  Proof.
    firstorder.
  Qed.

  Theorem union_diff {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,      (s₁ ∪ s₂) \ s₃ == (s₁ \ s₃) ∪ (s₂ \ s₃).
  Proof.
    firstorder.
  Qed.

  Theorem diff_union {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,      s₁ \ (s₂ ∪ s₃) ⊆ (s₁ \ s₂) ∪ (s₁ \ s₃).
  Proof.
    firstorder.
  Qed.

  Theorem diff_inter {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,      (s₁ \ s₂) ∩ (s₁ \ s₃) ⊆ s₁ \ (s₂ ∩ s₃).
  Proof.
    firstorder.
  Qed.

  Theorem inter_diff {Γ: Type} :
    forall s₁ s₂ s₃: @τ Γ,      (s₁ ∩ s₂) \ s₃ == (s₁ \ s₃) ∩ (s₂ \ s₃).
  Proof.
    firstorder.
  Qed.

  (* Boolean [compl]] *)
  Definition compl {Γ: Type} (s: τ) : τ :=
    fun (x: Γ) => x ∉ s.
  Notation "¬ s" := (@compl _ s) (at level 41, no associativity).
  (* TODO: check level *)


  Theorem compl_Univ {Γ: Type} : ¬ (@Univ Γ) == ∅.
  Proof.
    firstorder.
  Qed.

  Theorem compl_emptyset {Γ: Type} : ¬ ∅ == @Univ Γ.
  Proof.
    firstorder.
  Qed.

  (** Operator [add] and [singleton] *)
  Definition add {Γ: Type} (x: Γ) (s: τ) : τ :=
    fun y => y = x \/ y ∈ s.

  Definition singleton {Γ: Type} (x: Γ) : τ := add x ∅.

  Notation "{ x }" := (@singleton _ x).
  (* TODO: evaluation the term "{ x } ∪ s" returns undefined notation :-(
           See the theorems [add_union] and [remove_diff] below *)

  Theorem In_add {Γ: Type} :
    forall (x: Γ) (s: τ),       x ∈ (add x s).
  Proof.
    firstorder.
  Qed.

  Theorem add_union  {Γ: Type} :
    forall (x: Γ) (s: τ),       add x s == union {x} s. (* { x } ∪ s *)
  Proof.
    firstorder.
  Qed.

  Theorem add_commut {Γ: Type} :
    forall (x y: Γ) (s: τ),     add x (add y s) == add y (add x s).
  Proof.
    firstorder.
  Qed.

  Theorem add_idem {Γ: Type} :
    forall (x: Γ) (s: τ),       add x (add x s) == add x s.
  Proof.
    firstorder.
  Qed.


  (** Operator [remove] *)
  Definition remove {Γ: Type} (x: Γ) (s: τ) : τ :=
    fun y => y <> x /\ y ∈ s.


  Theorem In_remove {Γ: Type} :
    forall (x: Γ) (s: τ),       x ∉ (remove x s).
  Proof.
    firstorder.
  Qed.

  Theorem remove_diff {Γ: Type} :
    forall (x: Γ) (s: τ),       remove x s == diff s {x}.
  Proof.
    firstorder.
  Qed.

  Theorem remove_commut {Γ: Type} :
    forall (x y: Γ) (s: τ),     remove x (remove y s) == remove y (remove x s).
  Proof.
    firstorder.
  Qed.

  Theorem remove_idem {Γ: Type} :
    forall (x: Γ) (s: τ),       remove x (remove x s) == remove x s.
  Proof.
    firstorder.
  Qed.

  Theorem remove_add {Γ: Type} :
    forall (x: Γ) (s: τ),       remove x (add x s) == remove x s.
  Proof.
    firstorder.
  Qed.

  Theorem add_remove {Γ} {discr: Discr Γ} :
    forall (x: Γ) (s: τ),       add x (remove x s) == add x s.
  Proof.
    intros x s y; split.
    firstorder.
    destruct (eq_dec x y);
      firstorder.
  Qed.

End CoqSet.
(* Set.v ends here *)

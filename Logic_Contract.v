Require Import Contracts.
Require Import Sets.
Require Import Simple_Logic.
Require Import Classical.
Include CoqSet.

Section domain_defined.

Variable d : domain.

Definition formula_to_assert (formula : expr) : assertion d :=
  fun e => sat e formula.
Definition mkContractF (a g : @expr d): contract d :=
  mkContract d (formula_to_assert a) (formula_to_assert g).

Record contractF := ContractF {A : @expr d ; G : @expr d}.


Definition sat_contract (s : state d) (cf : contractF) :=
  sat s (cf.(A)) -> sat s (cf.(G)).

Definition provides_contract (s : state d) (cf : contractF) :=
  sat s (cf.(A)).

Definition f_or (e1 e2 : expr): @expr d := f_not (f_and (f_not e1) (f_not e2)).

Definition saturateF (cf1 : contractF) : contractF :=
  ContractF (cf1.(A)) (f_or (cf1.(G)) (f_not (cf1.(A)))).

(* Ici on a besoin d'environment *)
Definition refinesF (cf1 cf2 : contractF) :=
  let cf1' := saturateF cf1 in
  let cf2' := saturateF cf2 in
  forall (s : state d), (sat s cf2'.(A) -> sat s cf1'.(A)) /\ (sat s cf1'.(G) -> sat s cf2'.(G)).
  (* (forall (s : state d), sat_contract s cf1 -> sat_contract s cf2) *)
  (* /\ (forall (s : state d), provides_contract s cf2 -> provides_contract s cf1). *)


Definition composeF (cf1 cf2 : contractF) : contractF :=
  let cf1' := saturateF cf1 in
  let cf2' := saturateF cf2 in
  let g := f_and (cf1'.(G)) (cf2'.(G)) in
  let a := f_or (f_and (cf1'.(A)) (cf2'.(A))) (f_not g) in
  ContractF a g.

Definition glbF (cf1 cf2 : contractF) : contractF :=
  let cf1' := saturateF cf1 in
  let cf2' := saturateF cf2 in
  let a := f_or cf1'.(A) cf2'.(A) in
  let g := f_and cf1'.(G) cf2'.(G) in
  ContractF a g.

Definition c2c (cf : contractF) : contract d :=
  mkContractF cf.(A) cf.(G).

Lemma f2a_sat : forall (f : expr) (s : state d), formula_to_assert f s <-> sat s f.
Proof.
  firstorder.
Qed.
Lemma f2a_neg : forall (f : expr) (s : state d),
  (formula_to_assert (f_not f)) s <-> ( ¬ (formula_to_assert f)) s.
Proof.
  split ; rewrite f2a_sat ; apply not_sat_not.
Qed.

Lemma f2a_and : forall (f1 f2 : expr) (s : state d),
  (formula_to_assert (f_and f1 f2)) s <-> ((formula_to_assert f1) s /\ (formula_to_assert f2) s).
Proof.
  split ; repeat rewrite f2a_sat ; apply and_sat_and.
Qed.

Notation "c1 == c2" := (equiv _ c1 c2).

Lemma Morgan2 : forall P Q, ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof.
  firstorder.
  case classic with (P) ; case classic with (Q) ; tauto.
Qed.

Theorem saturateF_correct : forall (cf : contractF) (s : state d),
  satisfies d s (c2c (saturateF cf))  <-> satisfies d s (saturate d (c2c cf)).
Proof.
  split.
  unfold c2c, saturateF, f_or, saturate, satisfies.
  unfold union, inter, compl, In.
  simpl.
  rewrite f2a_neg ; unfold compl, In ; rewrite f2a_and ; simpl.
  firstorder.
  case classic with (formula_to_assert (G cf) s).
  intro.
  right.
  right.
  assumption.
  intro.
  left.
  intro.
  apply H.
  rewrite f2a_neg.
  assumption.
  rewrite f2a_neg.
  unfold compl, In.
  rewrite f2a_neg.
  unfold compl, In.
  tauto.
  unfold c2c, saturateF, f_or, saturate, satisfies.
  unfold union, inter, compl, In.
  simpl.
  rewrite f2a_neg ; unfold compl, In ; rewrite f2a_and ; simpl.
  rewrite Morgan2.
  repeat rewrite f2a_neg ; unfold compl, In.
  firstorder.
Qed.

Lemma sat_contract_c2c : forall (s : state d) (cf : contractF),
  sat_contract s cf <-> s ∈ ¬ formula_to_assert (cf.(A)) ∪ formula_to_assert (cf.(G)).
Proof.
  unfold formula_to_assert, sat_contract, union, compl, In.
  intros s [af gf].
  simpl.
  split.
  intro H.
  case (sat_dec s af) ; tauto.
  tauto.
Qed.

Lemma providesF_c2c : forall (s : state d) (cf : contractF),
 provides_contract s cf <-> s ∈ formula_to_assert (cf.(A)).
Proof.
 firstorder.
Qed.

Theorem refinesF_correct : forall (cf1 cf2 : contractF),
  refines d (c2c cf1) (c2c cf2) <-> refinesF cf1 cf2.
Proof.
  split.
  unfold c2c, refines, refinesF, saturateF.
  simpl.
  intros [Ha Hg] s.
  split.
  intros.
  rewrite <- f2a_sat.
  apply Ha.
  assumption.
  unfold f_or.
  repeat rewrite <- f2a_sat.
  repeat rewrite  f2a_neg.
  unfold union, inter, compl, In.
  repeat rewrite  f2a_and.
  repeat rewrite  f2a_neg.
  unfold union, inter, compl, In.
  repeat rewrite  f2a_neg.
  unfold union, inter, compl, In.
  repeat rewrite Morgan2.
  intro.
  cut (s ∈ ¬ formula_to_assert (A cf2) ∪ formula_to_assert (G cf2)).
  unfold union, inter, compl, In.
  tauto.
  apply Hg.
  unfold union, inter, compl, In.
  tauto.
  unfold c2c, refines, refinesF, saturateF.
  simpl.
  unfold f_or.
  intros H.
  split.
  intros s.
  destruct (H s).
  unfold In.
  repeat rewrite f2a_sat.
  assumption.
  intros s.
  destruct (H s).
  unfold union, inter, compl, In.
  repeat rewrite f2a_sat.
  generalize H1.
  repeat rewrite <- not_sat_not.
  repeat rewrite <- and_sat_and.
  repeat rewrite <- not_sat_not.
  repeat rewrite Morgan2.
  tauto.
Qed.

Theorem composeF_correct : forall (cf1 cf2 : contractF),
  c2c (composeF cf1 cf2) == compose d (c2c cf1) (c2c cf2).
Proof.
  intros [a1 g1] [a2 g2].
  unfold composeF, compose, c2c, f_or.
  simpl.
  apply refines_antisym.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
Qed.

Theorem glbF_correct : forall (cf1 cf2 : contractF),
  c2c (glbF cf1 cf2) == glb _ (c2c cf1) (c2c cf2).
Proof.
  intros [a1 g1] [a2 g2].
  unfold glbF, glb, c2c, f_or.
  simpl.
  apply refines_antisym.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold f_or.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
Qed.

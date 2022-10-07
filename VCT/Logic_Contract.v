Require Import Sets.
(* Require Import Classical. *)
Require Import Contracts.
Include CoqSet.

Definition set := @τ.

Section class_ag.

Class AG_ContractF  (bt : Base_Types) (expr : set ident -> Type)  := {
  e_and : forall d : set ident, expr d -> expr d -> expr d ;
  e_or : forall d : set ident, expr d -> expr d -> expr d ;
  e_not : forall d : set ident, expr d -> expr d ;
  sat : forall d : set ident, behavior d -> expr d -> Prop ;

  sat_e_not : forall (d : set ident) (s : behavior d) (e : expr d),
    ~ sat d s e <-> sat d s (e_not d e) ;
  sat_e_and : forall (d : set ident) (s : behavior d) (e1 e2 : expr d),
    sat d s e1 /\ sat d s e2 <-> sat d s (e_and d e1 e2) ;
  sat_e_or : forall (d : set ident) (s : behavior d) (e1 e2 : expr d),
    sat d s e1 \/ sat d s e2 <-> sat d s (e_or d e1 e2) ;
  sat_dec : forall (d : set ident) (s : behavior d) (e : expr d),
    sat d s e \/ ~ sat d s e ;
}.

End class_ag.

(* Section class_both. *)

(* Class both_theo := { *)
(*   B : Type ; *)
(*   ident' : Type ; *)

(*   any_B : B ; *)
(*   eq_dec_ident : forall x y : ident', {x = y} + {x <> y} ; *)
(*   in_dec_ident : forall (v : ident') (d : set ident'), {v ∈ d} + {v ∉ d} ; *)

(*   expr' : set ident' -> Type ; *)
(*   e_and' : forall d : set ident', expr' d -> expr' d -> expr' d ; *)
(*   e_or' : forall d : set ident', expr' d -> expr' d -> expr' d ; *)
(*   e_not' : forall d : set ident', expr' d -> expr' d ; *)
(*   behavior' : set ident' -> Type ; *)
(*   sat' : forall d : set ident', behavior' d -> expr' d -> Prop *)
(* }. *)

(* End class_both. *)

Section define_contractF.

Context {bt : Base_Types}.
Context {expr : set ident -> Type}.
Context {agcf : AG_ContractF bt expr}.

Variable d : set ident.

Record contractF := ContractF {A : expr d ; G : expr d}.

Definition sat_contract (s : behavior d) (cf : contractF) :=
  sat d s (cf.(A)) -> sat d s (cf.(G)).

Definition provides_contract (s : behavior d) (cf : contractF) :=
  sat d s (cf.(A)).

Definition saturateF (cf1 : contractF) : contractF :=
  ContractF (cf1.(A)) (e_or d (cf1.(G)) (e_not d (cf1.(A)))).

(* Ici on a besoin d'environment *)
Definition refinesF (cf1 cf2 : contractF) :=
  let cf1' := saturateF cf1 in
  let cf2' := saturateF cf2 in
  forall (s : behavior d), (sat d s cf2'.(A) -> sat d s cf1'.(A)) /\ (sat d s cf1'.(G) -> sat d s cf2'.(G)).
  (* (forall (s : behavior d), sat_contract s cf1 -> sat_contract s cf2) *)
  (* /\ (forall (s : behavior d), provides_contract s cf2 -> provides_contract s cf1). *)


Definition composeF (cf1 cf2 : contractF) : contractF :=
  let cf1' := saturateF cf1 in
  let cf2' := saturateF cf2 in
  let g := e_and d (cf1'.(G)) (cf2'.(G)) in
  let a := e_or d (e_and d (cf1'.(A)) (cf2'.(A))) (e_not d g) in
  ContractF a g.

Definition glbF (cf1 cf2 : contractF) : contractF :=
  let cf1' := saturateF cf1 in
  let cf2' := saturateF cf2 in
  let a := e_or d cf1'.(A) cf2'.(A) in
  let g := e_and d cf1'.(G) cf2'.(G) in
  ContractF a g.

End define_contractF.

Section both_theo_def.

Context {bt : Base_Types}.
Context {expr : set ident -> Type}.

Variable theo : Theory bt.

Variable ag_contract : AG_ContractF  bt expr.

Variable d : alphabet.

Definition formula_to_assert (formula : expr d) : assertion d :=
  fun e => sat d e formula.

Definition mkContractF (a g : expr d): contract d :=
  mkContract d (formula_to_assert a) (formula_to_assert g).

Definition c2c (cf : contractF d) : contract d :=
  mkContractF cf.(A d) cf.(G d).

Lemma f2a_sat : forall (f : expr d) (s : behavior d), formula_to_assert f s <-> sat d s f.
Proof.
  firstorder.
Qed.

Lemma f2a_neg : forall (f : expr d) (s : behavior d),
  (formula_to_assert (e_not d f)) s <-> ( ¬ (formula_to_assert f)) s.
Proof.
  split ; rewrite f2a_sat ; apply sat_e_not.
Qed.

Lemma f2a_and : forall (f1 f2 : expr d) (s : behavior d),
  (formula_to_assert (e_and d f1 f2)) s <-> ((formula_to_assert f1) s /\ (formula_to_assert f2) s).
Proof.
  split ; repeat rewrite f2a_sat ; apply sat_e_and.
Qed.

Lemma f2a_or : forall (f1 f2 : expr d) (s : behavior d),
  (formula_to_assert (e_or d f1 f2)) s <-> ((formula_to_assert f1) s \/ (formula_to_assert f2) s).
Proof.
  split ; repeat rewrite f2a_sat ; apply sat_e_or.
Qed.

Notation "c1 == c2" := (equiv _ c1 c2).

(* Lemma Morgan2 : forall P Q, ~ (P /\ Q) <-> ~ P \/ ~ Q. *)
(* Proof. *)
(*   firstorder. *)
(*   case classic with (P) ; case classic with (Q) ; tauto. *)
(* Qed. *)

Theorem saturateF_correct : forall (cf : contractF d) ,
  (c2c (saturateF d cf)) == (saturate d (c2c cf)).
  (* satisfies d s (c2c (saturateF d cf))  <-> satisfies d s (saturate d (c2c cf)). *)
Proof.
  intros cf.
  cut ((forall (s : behavior d), satisfies d s (c2c (saturateF d cf))  <->
  satisfies d s (saturate d (c2c cf))) /\
  forall (s : behavior d), s ∈ Contracts.A d (c2c (saturateF d cf)) <->
  s ∈ Contracts.A d (saturate d (c2c cf))).
  { intros [H He].
    unfold equiv.
    split.
    - rewrite refines_correct.
      split.
      + unfold implements.
        intros σ Hs s s_in_σ.
        apply H.
        apply Hs.
        assumption.
      + intros e Hs s s_in_e.
        apply He.
        apply Hs.
        assumption.
    - rewrite refines_correct.
      split.
      + unfold implements.
        intros σ Hs s s_in_σ.
        apply H.
        apply Hs.
        assumption.
      + intros e Hs s s_in_e.
        apply He.
        apply Hs.
        assumption.
 }
  split.
  - split.
    + unfold c2c, saturateF, saturate, satisfies.
      unfold union, inter, compl, In.
      simpl.
      rewrite f2a_or.
      rewrite f2a_neg.
      unfold compl, In.
      tauto.
    + unfold c2c, saturateF, saturate, satisfies.
      unfold union, inter, compl, In.
      simpl.
      rewrite f2a_or.
      rewrite f2a_neg.
      unfold compl, In.
      tauto.
  - unfold c2c, saturateF, saturate, satisfies.
    unfold union, inter, compl, In.
    simpl.
    tauto.
Qed.

Lemma sat_contract_c2c : forall (s : behavior d) (cf : contractF d),
  (* sat_contract d s cf <-> s ∈ ¬ formula_to_assert (cf.(A d)) ∪ formula_to_assert (cf.(G d)). *)
  sat_contract d s cf <-> satisfies d s (c2c cf).
Proof.
  unfold satisfies, c2c, sat_contract, union, compl, In.
  intros s [af gf].
  simpl.
  unfold formula_to_assert.
  split.
  intro H.
  case (sat_dec d s af) ; tauto.
  tauto.
Qed.

Lemma providesF_c2c : forall (s : behavior d) (cf : contractF d),
 provides_contract d s cf <-> s ∈ formula_to_assert (cf.(A d)).
Proof.
 firstorder.
Qed.

Theorem refinesF_correct : forall (cf1 cf2 : contractF d),
  refines d (c2c cf1) (c2c cf2) <-> refinesF d cf1 cf2.
Proof.
  split.
  unfold c2c, refines, refinesF, saturateF.
  simpl.
  intros [Ha Hg] s.
  split.
  + intros.
    rewrite <- f2a_sat.
    apply Ha.
    assumption.
  + repeat rewrite <- sat_e_or.
    repeat rewrite <- f2a_sat.
    repeat rewrite  f2a_neg.
    unfold union, inter, compl, In.
    intro.
    cut (s ∈ ¬ formula_to_assert (A d cf2) ∪ formula_to_assert (G d cf2)).
    - unfold union, inter, compl, In.
      tauto.
    - apply Hg.
      unfold union, inter, compl, In.
      tauto.
  + unfold c2c, refines, refinesF, saturateF.
    simpl.
    intros H.
    split.
    - intros s.
      destruct (H s).
      unfold In.
      repeat rewrite f2a_sat.
      assumption.
    - intros s.
      destruct (H s).
      unfold union, inter, compl, In.
      repeat rewrite f2a_sat.
      generalize H1.
      repeat rewrite <- sat_e_or.
      repeat rewrite <- sat_e_not.
      tauto.
Qed.

Theorem composeF_correct : forall (cf1 cf2 : contractF d),
  c2c (composeF d cf1 cf2) == compose d (c2c cf1) (c2c cf2).
Proof.
  intros [a1 g1] [a2 g2].
  unfold composeF, compose, c2c.
  simpl.
  apply refines_antisym.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
Qed.

Theorem glbF_correct : forall (cf1 cf2 : contractF d),
  c2c (glbF d cf1 cf2) == glb _ (c2c cf1) (c2c cf2).
Proof.
  intros [a1 g1] [a2 g2].
  unfold glbF, glb, c2c.
  simpl.
  apply refines_antisym.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
    - unfold refines.
      simpl.
      split.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
        + intro s.
          unfold inter, union, SubsetEq, compl, In.
          repeat (try rewrite f2a_neg ; try rewrite f2a_and ; try rewrite f2a_or ;
          unfold inter, union, SubsetEq, compl, In).
          tauto.
Qed.

End both_theo_def.

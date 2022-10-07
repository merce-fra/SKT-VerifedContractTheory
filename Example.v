Require Import dynamic_semantics.
Require Import static_sem.
Require Import checker.
Require Import VCT.Contracts.
Require Import VCT.Logic_Contract.
Require Import DifferentialContracts.
Require Import AbstractPrograms.


Section Example.

Variable I : interpretation.

Definition h : KAssignable := variable "h".
Definition h' : KAssignable := KAssignDiff h.
Definition v : KAssignable := variable "v".
Definition d : alphabet := add v ( add h' (add h (@emptyset KAssignable))).

Axiom fd : Finite d.

Lemma h_in_d : h ∈ d.
Proof.
  firstorder.
Qed.

Lemma v_in_d : v ∈ d.
Proof.
  firstorder.
Qed.

Definition h_v := exist _ h h_in_d.
Definition h'_v := exist _ h h_in_d.
Definition v_v := exist _ v v_in_d.
Definition HMax : Term := KTnumber (KTNreal 20).

Definition alpha : Program := KPcompose
                                (KPassignAny h)
                                (KPchoice
                                  (KPtest (KFless (KTread h) HMax))
                                  (KPassign v (KTnumber (KTNreal 0)))).

Lemma alpha_in_dom : FCset2sets (all_vars_program alpha) ⊆ d.
Proof.
  intros x .
  unfold In.
  simpl.
  firstorder.
Qed.

Definition ca_assume  := sTrue d.
Definition ca_guarantee := ((postF d ((KFimply
      (KFgreaterEqual (KTread h) HMax)
      (KFequal v (KTnumber (KTNreal 0))))) )::nil)::nil.

Definition ca_contract : contractF d := ContractF d ca_assume ca_guarantee.

Theorem ca_implements_alpha :
  implement_abstract_hybrid I d fd alpha alpha_in_dom ca_contract.
Proof.
  apply proof_trans.
  generalize proof_trans.
  admit.
  unfold KFrefine.
  admit.
Admitted.

Definition beta : Program := KPcompose
  (KPassignAny v)
  (KPodeSystem
    (ODEatomic (ODEsing (KAssignDiff h) (KTread v)))
    (KFtrue)
  ).

Definition cb_assume : sprogram d :=
  (preF d (KFlessEqual h HMax) ::
  postF d ((KFimply (KFgreaterEqual (KTread h) HMax) (KFequal v (KTnumber (KTNreal 0)))))
  :: nil )
  :: nil
.

Definition cb_guarantee : sprogram d:=
    ((postF d (KFlessEqual h HMax)) :: nil) :: nil
.

Definition cb_contract :=
  ContractF d cb_assume cb_guarantee.

Lemma beta_in_dom : FCset2sets (all_vars_program beta) ⊆ d.
Proof.
Admitted.

Theorem beta_implements_cb :
  implement_abstract_hybrid I d fd beta beta_in_dom cb_contract.
Proof.
  apply proof_trans.
  admit.
  admit.
Admitted.

Definition gamma :=
  KPloop
    (KPcompose
      (KPchoice
        (KPtest (KFlessEqual (KTread h) HMax))
        (KPassign v (KTnumber (KTNreal 0%R)))
      )
      (KPodeSystem
        (ODEatomic (ODEsing (KAssignDiff h) (KTread v)))
        (KFless h HMax)
      )
    ).

Definition cg_assume : sprogram d := (preF d (KFlessEqual h HMax)::nil)::nil.

Definition cg_guarantee : sprogram d := (postF d (KFimply
          (KFlessEqual h HMax)
          (KFequal v (KTnumber (KTNreal 0%R)))
        )
        ::
        postF d (KFlessEqual h HMax) :: nil)::nil.

Definition cg_contract : contractF d :=
  ContractF d cg_assume cg_guarantee.

Lemma gamma_in_dom : FCset2sets (all_vars_program gamma) ⊆ d.
Proof.
Admitted.

Definition gamma_assert := ContractF d cg_assume cg_guarantee.

Theorem gamma_implments_cg :
  implement_abstract_hybrid I d fd gamma gamma_in_dom cg_contract.
Proof.
  apply proof_trans.
  admit.
  admit.
Admitted.

End Example.


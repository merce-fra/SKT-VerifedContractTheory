Require Sets.
Require Import Contracts.
Require Import Logic_Contract.

(** It should be already defined in the std lib *)
Lemma eq_dec_nat : forall x y : nat, {x = y} + {x <> y}.
Proof.
  induction x ;
    destruct y.
    + left ; reflexivity.
    + right ; discriminate.
    + right ; discriminate.
    + destruct (IHx y) as [Heq| Hnq];
        clear IHx.
      - left; subst; reflexivity.
      - right; intro Hn; elim Hnq.
        inversion Hn; subst; reflexivity.
Defined.

(* TODO I have to fix the scope issue for notations: including the CoqSet modules is
   not good enough...  *)
Include Sets.CoqSet.

(** The set of variables is a set of identifiers *)
Definition ident := nat.
Definition domain := @τ ident.
Definition var (d : domain) := {x : ident | x ∈ d}.
Axiom in_dec_ident : forall (v : ident) (d : domain), {v ∈ d} + {v ∉ d}.
(* Finally, a variable is an ident, with a proof it belongs to the variable set:
    e.g. { x : ident | x ∈ Vars }
*)

Instance bt : Base_Types := {
  ident := nat ; (* Rename V -> varid ? *)
  value := Prop ;  (* Why B? for Boolean ?*)
}.


(** Now, we define some logic formulas over vars, a set of variables  *)
Inductive expr {d : domain} : Type :=
  | f_tt : expr
  | f_var : var d -> expr
  | f_not : expr -> expr
  | f_and : expr -> expr -> expr.

Definition state (d : domain) : Type :=  forall x : var d, value.

Definition f_or {d : domain} (f1 f2 : expr) := @f_not d (f_and (f_not f1) (f_not f2)).

Definition f_eq {d : domain} (f_1 : expr) (f_2 : expr) := @f_or d (f_and f_1 f_2) (f_and (f_not f_1)
  (f_not f_2)).

(** Useful for establishing the decidability of formulas satisfiability *)
Axiom state_eval : forall {d : domain} (s : state d) (x : var d), {s x} + {~s x}.

Inductive sat {d : domain} : state d -> @expr d  -> Prop :=
| Sat_tt s : sat s f_tt
| Sat_var (s: state d) x : s x -> sat s (f_var x)
| Sat_not s f : unsat s f -> sat s (f_not f)
| Sat_and s f1 f2 : sat s f1 -> sat s f2 -> sat s (f_and f1 f2)

with unsat {d : domain} : state d -> @expr d -> Prop :=
| Unsat_var s x : ~ (s x) -> unsat s (f_var x)
| Unsat_not s f : sat s f -> unsat s (f_not f)
| Unsat_and1 s f1 f2 : unsat s f1 -> unsat s (f_and f1 f2)
| Unsat_and2 s f1 f2 : unsat s f2 -> unsat s (f_and f1 f2).

(* Scheme sat_ind1 := Induction for sat Sort Prop
   with unsat_ind1 := Induction for unsat Sort Prop.
 *)

Lemma Sat_and_inv : forall {d : domain} (s : state d) f1 f2,
    sat s (f_and f1 f2) <-> sat s f1 /\ sat s f2.
Proof.
  split; intro H.
  - inversion H; tauto.
  - apply Sat_and; tauto.
Qed.


(** We prove decidability of sat, we need to deal with decidability of both sat and unsat at a time.
    It could be optimized using a stronger induction principle alternating decidability of sat and unsat.
    Here, we compute both in paralell. *)
Lemma sat_unsat_dec: forall {d : domain} (s : state d) f,
  ({sat s f} + {~ sat s f}) * ({unsat s f} + {~ unsat s f}).
Proof.
  induction f.
  - split.
    + left; apply Sat_tt.
    + right; intro Hn; inversion Hn.

  - destruct (state_eval s v); split.
    + left; apply Sat_var; assumption.
    + right; intro Hn; inversion Hn; contradiction.
    + right; intro Hn; inversion Hn; contradiction.
    + left; apply Unsat_var; assumption.
  - destruct IHf as [IHs IHu]; split.
    + destruct IHu as [Hu | Hn].
      left; apply Sat_not; assumption.
      right; intro Sat; inversion Sat; contradiction.
    + destruct IHs as [Hs | Hn].
      left; apply Unsat_not; assumption.
      right; intro Unsat; inversion Unsat; contradiction.
  - destruct IHf1 as [Sat1 Unsat1];
      destruct IHf2 as [Sat2 Unsat2]; split.
    + clear Unsat1 Unsat2.
      destruct Sat1 as [Sat1 | nSat1].
      destruct Sat2 as [Sat2 | nSat2].
      left; apply Sat_and; assumption.
      right; intro nSat; inversion nSat; contradiction.
      right; intro nSat; inversion nSat; contradiction.
    + clear Sat1 Sat2.
      destruct Unsat1 as [Unsat1 | nUnsat1].
      left; apply Unsat_and1; assumption.
      destruct Unsat2 as [Unsat2 | nUnsat2].
      left; apply Unsat_and2; assumption.
      right; intro Unsat; inversion Unsat; contradiction.
Defined.

(* Thus, we separate in 2 distinct lemmas. *)
Lemma sat_dec: forall {d : domain} (s: state d) f, { sat s f } + { ~ sat s f }.
Proof.
  intros d s f.
  destruct (sat_unsat_dec s f) as [sat_dec _].
  exact sat_dec.
Defined.

Lemma sat_dec_prop: forall {d : domain} (s: state d) f, sat s f \/ ~ sat s f.
Proof.
  intros.
  case (sat_dec s f) ; tauto.
Qed.

Lemma unsat_dec: forall {d : domain} (s: state d) f, { unsat s f } + { ~ unsat s f }.
Proof.
  intros d s f.
   destruct (sat_unsat_dec s f) as [_ unsat_dec].
   exact unsat_dec.
Defined.

Lemma unsat_sat: forall {d : domain} (s : state d) f, unsat s f <-> sat s (f_not f).
Proof.
  split; intro H.
  - apply Sat_not; assumption.
  - inversion H; subst; assumption.
Qed.

Lemma not_sat_unsat: forall {d : domain} (s : state d) f, ~ sat s f <-> unsat s f.
Proof.
  induction f ; split; intro H.
  + elim H; apply Sat_tt.
  + inversion H.
  + destruct (state_eval s v).
    - elim H; apply Sat_var; assumption.
    - apply Unsat_var; assumption.

  + inversion H; subst; clear H.
    intro Hn; inversion Hn; subst; clear Hn.
    contradiction.
  + apply Unsat_not.
    assert (H_: ~ unsat s f) by
        (intros Hn; elim H; apply Sat_not; assumption);
      clear H.
    destruct (sat_dec s f).
    assumption.
    rewrite IHf in n; contradiction.

  + intros Hn; inversion Hn; subst; clear Hn.
    inversion H; subst; clear H.
    rewrite <- IHf in H2; contradiction.
  + destruct (sat_dec s f1).
    - destruct (sat_dec s f2).
      * elim H; apply Sat_and; assumption.
      * apply Unsat_and2; tauto.
    - apply Unsat_and1; tauto.
  + intro Hn; inversion Hn; subst; clear Hn.
    inversion H; subst; clear H.
    - rewrite <- IHf1 in H2; contradiction.
    - rewrite <- IHf2 in H2; contradiction.
Qed.

Lemma not_sat_not : forall {d : domain} (s : state d) f, ~ sat s f <-> sat s (f_not f).
Proof.
  intros; rewrite not_sat_unsat; rewrite unsat_sat.
  tauto.
Qed.

Lemma and_sat_and : forall {d : domain} (s : state d) f1 f2, sat s f1 /\ sat s f2 <-> sat s (f_and f1 f2).
Proof.
  split.
  - intros (H1, H2); apply Sat_and; assumption.
  - intro Hand; inversion Hand; subst; tauto.
Qed.

Lemma sat_not_not :  forall {d : domain} (s : state d) f, sat s (f_not (f_not f)) <-> sat s f.
Proof.
  split; intro H.
  inversion H; subst; clear H.
  inversion H2; subst; clear H2.
  assumption.
  apply Sat_not; apply Unsat_not; assumption.
Qed.

Lemma or_sat_or : forall {d : domain} (s : state d) f1 f2,
    (sat s f1 \/ sat s f2) <-> sat s (f_not (f_and (f_not f1) (f_not f2))).
Proof.
  split; intros H.
  - destruct H;
      apply Sat_not;
      [ apply Unsat_and1 |
        apply Unsat_and2 ];
      apply Unsat_not;
      assumption.
  - inversion H; subst; clear H;
      inversion H2; subst; clear H2;
        inversion H1; subst; clear H1;
          tauto.
Qed.

Lemma implies_sat : forall {d : domain} (s : state d) f1 f2,
    (sat s f1 -> sat s f2) <-> sat s (f_not (f_and f1 (f_not f2)) ).
Proof.
  split; intros H.
  - apply Sat_not.
    destruct (sat_dec s f1).
    + apply Unsat_and2; apply Unsat_not; tauto.
    + apply Unsat_and1; apply not_sat_unsat; assumption.
  - inversion H; subst; clear H;
      inversion H2; subst; clear H2.
    + apply not_sat_unsat in H1; contradiction.
    + inversion H1; subst; clear H1;
        tauto.
Qed.

Definition state_predicate {vs: domain} (f: expr) : assertion vs :=
  fun e => sat e f.

Section theo_instances.
  Instance theo : Theory bt := {
  any_value := True ;
  eq_dec_ident := eq_dec_nat ;
  in_dec_ident := in_dec_ident ;
  }.

Instance lf : AG_ContractF bt (@expr) := {
  e_and := @f_and ;
  e_or := @f_or ;
  e_not := @f_not ;
  sat := @sat ;
  sat_e_not := @not_sat_not ;
  sat_e_and := @and_sat_and ;
  sat_e_or := @or_sat_or ;
  sat_dec := @sat_dec_prop ;
  }.
End theo_instances.

(* Example *) 
Definition id1 : ident := 1.
Definition id2 : ident :=  2.

Definition Ω : domain :=
  let single1 : domain := { id1 } in
  let single2 : domain := { id2 } in
    single1 ∪ single2.

Definition v1 : { id1 | id1 ∈ Ω }.
  exists id1; firstorder.
Defined.

Definition v2 : { id2 | id2 ∈ Ω }.
  exists id2; firstorder.
Defined.


Definition v1_holds := state_predicate (@f_var Ω v1).
Definition v2_holds := state_predicate (@f_var Ω v2).

Definition c1 := mkContract Ω v1_holds v2_holds.
Definition c2 := mkContract Ω v2_holds v1_holds.

Definition c3 := compose Ω c1 c2.

Definition true_forall : assertion Ω := state_predicate (f_and (f_var v1) (f_var v2)).
Definition false_forall : assertion Ω := state_predicate (f_and (f_not (f_var v1)) (f_not (f_var v2))).
Definition not_false : assertion Ω := ¬ false_forall.
Definition contract_all_true := mkContract Ω not_false true_forall.


Lemma Morgan1: forall A B: Prop, ~A /\ ~B <-> ~(A \/ B).
Proof.
  tauto.
Qed.

Lemma and_not_not: forall {d} (s: state d) f g, sat s (f_and (f_not (f_not f)) g) <-> sat s (f_and f g).
Proof.
  split;
    intro H; inversion H; subst; clear H.
  rewrite sat_not_not in H3;
    apply Sat_and; assumption.
  apply Sat_and;
    try rewrite sat_not_not; assumption.
Qed.


Lemma plop : saturate _ c3 = saturate _ contract_all_true.
Proof.
  (* Contracts --> set definitions *)
  apply contract_extensionality.
  split; (* equiv *)
    split; (* refines. *)
    simpl; (* contracts accessors & saturate *)
    (* unfold definitions of alias/macro *)
    unfold not_false, false_forall, true_forall, v1_holds, v2_holds;
    unfold state_predicate;
  (* Back to our toy logic: done in 2 steps:
     1- unfolding set operators => Prop because of the set definition
     2- converting non atomic Proposition into our logic
 *)
    unfold inter, union, compl;
    unfold SubsetEq, In;
    intros s.
  - repeat rewrite and_sat_and.
    repeat rewrite or_sat_or.
    repeat rewrite not_sat_not.
    repeat rewrite or_sat_or.
    rewrite and_sat_and.
    rewrite not_sat_not.
    rewrite or_sat_or.
    (* rewrite implies_sat. *)
  (* This should be also done for -> *)
  (* Thus, we can start to reason in our logic *)
    (* rewrite <- implies_sat. *)
    intro Sat.
    (* rewrite <- not_sat_not in Sat;
      rewrite <- and_sat_and in Sat. *)
    inversion Sat; subst; clear Sat;
      inversion H1; subst; clear H1;
        inversion H2; subst; clear H2.
    repeat rewrite <- or_sat_or.
    do 2 rewrite and_not_not.
    destruct (sat_dec s (f_var v2)).
    left; apply Sat_and; assumption.
    rewrite not_sat_not in n.
    right; left; apply Sat_and; assumption.
    repeat rewrite <- or_sat_or.
    do 2 rewrite and_not_not.
    destruct (sat_dec s (f_var v1)).
    left; apply Sat_and; assumption.
    rewrite not_sat_not in n.
    right; right; apply Sat_and; assumption.
  - repeat rewrite not_sat_not.
    rewrite sat_not_not.
    intros [ H | [H1 H2]].
    rewrite <- Morgan1 in H.
    destruct H as [H1 H2].
    do 2 rewrite or_sat_or in H2;
      rewrite and_sat_and in H2;
      do 2 rewrite not_sat_not in H2;
      rewrite sat_not_not in H2;
      rewrite <- and_sat_and in H2;
      do 2 rewrite <- or_sat_or in H2;
      do 2 rewrite <- not_sat_not in H2;
      destruct H2 as [H2 H3].
    destruct(sat_dec s (f_var v1));
      destruct(sat_dec s (f_var v2)); try tauto.
    left; apply Sat_and; rewrite <- not_sat_not; tauto.
    rewrite <- not_sat_not in H1, H2.
    destruct(sat_dec s (f_var v1));
      destruct(sat_dec s (f_var v2)); try tauto.
    right; apply Sat_and; tauto.
    left; apply Sat_and; rewrite <- not_sat_not; tauto.
  - intros [[H0 H1]| H1];
      intro H; inversion H; subst; clear H.
    rewrite <- not_sat_not in H5, H6;
      contradiction.
    rewrite <- not_sat_not in H4, H5; tauto.
  - intros H;
      do 2 rewrite not_sat_not in H at 1;
      rewrite sat_not_not in H;
      destruct H as [H | H];
      inversion H; subst; clear H.
    rewrite <- not_sat_not in H3, H4;
      tauto.
    tauto.
Qed.


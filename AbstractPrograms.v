Require Import CoqDL.syntax.expressions.
Require Import CoqDL.semantics.dynamic_semantics.
Require Import CoqDL.semantics.static_sem.
Require Import CoqDL.checker.checker.
Require Import List.
Require Import Contracts.
Require Import Logic_Contract.
Require Import DifferentialContracts.
Require Import Classical.

Set Printing Coercions.

Section AbstractProgram.

Lemma in_dec_KAssignable : forall (x : KAssignable) (d : alphabet), {x ∈ d} + { x ∉ d}.
Proof.
  admit.
Admitted.

Variable  I : interpretation.

Definition list_alphabet (l : list ident) : alphabet :=
  fun (x : ident) => List.In x l.

Fixpoint assignAny_aux (l : list ident) : Program :=
  match l with
  | nil => KPtest KFtrue
  | h :: t => KPcompose (KPassignAny h) (assignAny_aux t)
  end.

Definition assignAny (d : alphabet) (fd : Finite d) : Program :=
  assignAny_aux (elements_of d fd).

Lemma assignAny_dsp_strong_list : forall (l : list ident) (d : alphabet) (preS postS : KState),
  (forall (x : KAssignable), x ∉ d -> preS x = postS x) ->
  (forall (x : KAssignable), x ∈ d <-> List.In x l) ->
  (forall (y  : KAssignable), ~ List.In y  l -> preS y = postS y)
  -> dynamic_semantics_program I (assignAny_aux l) preS postS.
Proof.
  induction l.
  + unfold dynamic_semantics_program.
    simpl.
    intros.
    split.
    apply functional_extensionality.
    intros x.
    apply H1.
    tauto.
    unfold TrueFormulaSem.
    tauto.
  + intros.
    simpl.
    exists (upd_state preS a (postS a)).
    split.
    exists (postS a).
    unfold differ_state_except.
    split.
    - intros y ay_neq.
      rewrite (upd_state_diff _ a _ _ ay_neq).
      reflexivity.
    - rewrite (upd_state_same _ a _).
      reflexivity.
    apply (IHl (list_alphabet l)).
    * intros x x_nin_dl.
      case (KAssignable_dec a x).
        + intros ax_eq.
          rewrite ax_eq.
          rewrite upd_state_same.
          reflexivity.
        + intros ax_neq.
          rewrite (upd_state_diff _ a _ _ ax_neq).
          apply H1.
          intros [xa_eq | x_in_l].
          tauto.
          apply x_nin_dl.
          unfold list_alphabet, In.
          assumption.
    * unfold list_alphabet, In.
      reflexivity.
    * intros y y_nin_l.
      case (KAssignable_dec a y).
      + intros ay_eq.
        rewrite ay_eq.
        apply upd_state_same.
      + intros ay_neq.
        rewrite (upd_state_diff _ a _ _ ay_neq).
        apply H1.
        intros [ay_eq | y_in_l].
        apply ay_neq ; assumption.
        apply y_nin_l ; assumption.
Qed.

Lemma assignAny_dsp_strong : forall (d : alphabet) (fd : Finite d) (t : behavior d),
  let (preS, postS) := getbehaviorKStates d t in
  (forall ( y : ident), ~ List.In y  (elements_of d fd) -> preS y = postS y)
  -> dynamic_semantics_program I (assignAny d fd) preS postS.
Proof.
  intros d fd.
  generalize (Enum _ d fd).
  intro Henum.
  simpl in Henum.
  intros t.
  assert (exists (pres posts : KState), getbehaviorKStates d t = (pres, posts)).
    eexists.
    eexists.
    reflexivity.
  destruct H as [preS [postS Hrt]].
  rewrite Hrt.
  apply (assignAny_dsp_strong_list (elements_of d fd) d) .
  intros x x_nin_d.
  assert (getbehaviorValue d t x = any_value).
    unfold getbehaviorValue.
    destruct in_dec_ident.
    intuition.
    reflexivity.
  unfold getbehaviorKStates in Hrt.
  inversion Hrt.
  rewrite H.
  simpl.
  reflexivity.
  assumption.
Qed.

Lemma assignAny_dsp : forall (d : alphabet) (fd : Finite d) (t : behavior d),
  let (preS, postS) := getbehaviorKStates d t in
  dynamic_semantics_program I (assignAny d fd) preS postS.
Proof.
  intros d fd t.
  apply assignAny_dsp_strong.
  unfold getbehaviorValue.
  intros y Hy.
  destruct in_dec_ident.
  + exfalso.
    apply Hy.
    apply (Enum _ d fd).
    intuition.
  + reflexivity.
Qed.

Inductive elem (d : alphabet) :=
  | preF : Formula -> elem d
  | postF : Formula -> elem d.

Definition sprogram (d : alphabet) :=
 list (list (elem d)).

Definition sTrue (d : alphabet) : sprogram d := (@nil (elem d))::nil.
Definition sFalse (d : alphabet) : sprogram d := (@nil (list (elem d))).

Definition sprogram_sat_elem (d : alphabet) (t : behavior d) (e : elem d) : Prop :=
  let (prestate, poststate) := getbehaviorKStates d t in
  match e with
  | preF f => DSF f I prestate
  | postF f => DSF f I poststate
  end.

Fixpoint sprogram_sat_aux (d : alphabet) (t : behavior d) (sp_and : list (elem d)) : Prop :=
  match sp_and with
  | nil => True
  | h :: q =>  sprogram_sat_elem d t h /\ sprogram_sat_aux d t q
  end.

Fixpoint sprogram_sat (d : alphabet) (s : behavior d) (sp : sprogram d) : Prop :=
  match sp with
  | nil => False
  | h :: t => sprogram_sat_aux d s h \/ sprogram_sat d s t
  end.

Definition sor (d : alphabet) (a b : sprogram d) : sprogram d :=
  a ++ b.

Fixpoint sand_aux (d : alphabet) (l : list ( elem d)) (prog : sprogram d) : sprogram d :=
  match prog with
  | nil => nil
  | h :: t => (l ++ h) :: sand_aux d l t
  end.

Fixpoint sand (d : alphabet) (a b : sprogram d) : sprogram d :=
  match a with
  | nil => []
  | h :: t => sor d (sand_aux d h b)  (sand d t b)
  end.

Definition snot_elem (d : alphabet) (e : (elem d)) : elem d :=
  match e with
  | preF f => preF d (KFnot f)
  | postF f => postF d (KFnot f)
  end.

Fixpoint snot_aux (d : alphabet) (l : list (elem d)) : sprogram d :=
  match l with
  | nil => []
  | h :: t => ((snot_elem d h)::nil) :: (snot_aux d t)
  end.

Fixpoint snot (d : alphabet) (sp : sprogram d) : sprogram d :=
  match sp with
  | nil => nil :: nil
  | h :: t => sand d (snot_aux d h) (snot d t)
  end.

Lemma sat_s_or : forall (d : alphabet) (s : behavior d) (sp1 sp2 : sprogram d),
  sprogram_sat d s sp1 \/ sprogram_sat d s sp2 <-> sprogram_sat d s (sor d sp1 sp2).
Proof.
  intros.
  induction sp1.
  + simpl.
    tauto.
  + unfold sor.
    simpl.
    tauto.
Qed.

Lemma sataux_and : forall (d : alphabet) (s : behavior d) (a b : list ( elem d)),
  sprogram_sat_aux d s (a ++ b) <-> sprogram_sat_aux d s a /\ sprogram_sat_aux d s b.
Proof.
  intros.
  induction a.
  + simpl ; tauto.
  + simpl.
    rewrite IHa.
    tauto.
Qed.

Lemma sat_sand_aux :
  forall (d : alphabet) (s : behavior d) (sp : sprogram d) (a : list ( elem d)),
  sprogram_sat d s (sand_aux d a sp) <-> (sprogram_sat_aux d s a /\ sprogram_sat d s sp).
Proof.
  intros.
  induction sp.
  + simpl ; tauto.
  + simpl.
    rewrite sataux_and.
    rewrite IHsp.
    tauto.
Qed.

Lemma sat_s_and : forall (d : alphabet) (s : behavior d) (sp1 sp2 : sprogram d),
  sprogram_sat d s sp1 /\ sprogram_sat d s sp2 <-> sprogram_sat d s (sand d sp1 sp2).
Proof.
  intros.
  induction sp1.
  + simpl.
    tauto.
  + simpl.
    rewrite <- sat_s_or.
    rewrite <- IHsp1.
    rewrite sat_sand_aux.
    tauto.
Qed.

Lemma sat_snot_elem :
  forall (d : alphabet) (s : behavior d) (a : list ( elem d)) (e :  elem d),
  sprogram_sat d s (snot_aux d (e :: a)) <->
  sprogram_sat_elem d s (snot_elem d e) \/ sprogram_sat d s (snot_aux d a).
Proof.
  intros.
  simpl.
  tauto.
Qed.

Lemma sat_aux_sat_elem :
  forall (d : alphabet) (s : behavior d) (a : list ( elem d)) (e :  elem d),
  sprogram_sat_aux d s (e :: a) <-> sprogram_sat_elem d s e /\ sprogram_sat_aux d s a.
Proof.
  simpl.
  tauto.
Qed.

Lemma sat_elem_not :
  forall (d : alphabet) (s : behavior d) (e :  elem d),
  sprogram_sat_elem d s (snot_elem d e) <-> ~ sprogram_sat_elem d s e.
Proof.
  intros.
  induction e.
  + unfold sprogram_sat_elem.
    simpl.
    tauto.
  + unfold sprogram_sat_elem.
    simpl.
    tauto.
Qed.

Lemma sat_aux_not : forall (d : alphabet) (s : behavior d) (a : list ( elem d)),
  sprogram_sat d s (snot_aux d a) <-> ~ sprogram_sat_aux d s a.
Proof.
  intros.
  induction a.
  + simpl ; tauto.
  + rewrite sat_snot_elem.
    rewrite IHa.
    rewrite sat_aux_sat_elem.
    rewrite sat_elem_not.
    tauto.
Qed.

Lemma sat_s_not : forall (d : alphabet) (s : behavior d) (sp : sprogram d),
  ~ sprogram_sat d s sp <-> sprogram_sat d s (snot d sp).
Proof.
  intros.
  induction sp.
  + simpl.
    tauto.
  + simpl.
    rewrite <- sat_s_and.
    rewrite sat_aux_not.
    tauto.
Qed.

Lemma sat_s_dec : forall (d : alphabet) (s : behavior d) (sp : sprogram d),
  sprogram_sat d s sp \/ ~ sprogram_sat d s sp.
Proof.
Admitted.

Instance sprogram_contracts : AG_ContractF BT sprogram := {
  e_and := sand ;
  e_or := sor ;
  e_not := snot ;
  sat := sprogram_sat ;
  sat_e_not := sat_s_not ;
  sat_e_or := sat_s_or ;
  sat_e_and := sat_s_and ;
  sat_dec := sat_s_dec ;
}.

Definition elem_in_d (d : alphabet) (e : elem d) : Prop :=
  match e with
  | preF f => FCset2sets (all_vars_formula f) ⊆ d
  | postF f => FCset2sets (all_vars_formula f) ⊆ d
  end.

Definition list_in_d (d : alphabet) (l : list (elem d)) : Prop :=
  fold_left and (map (elem_in_d d) l) True.

Definition sprogram_in_d (d : alphabet) (a : sprogram d) : Prop :=
  fold_left and (map (list_in_d d) a) True.

Definition contract_in_d (d : alphabet) (c : contractF d) : Prop :=
  sprogram_in_d d (A d c) /\ sprogram_in_d d (G d c).

Fixpoint flatten (d : alphabet) (l : list (elem d)) : (Formula * Formula) :=
  match l with
  | nil => (KFtrue, KFtrue)
  | (preF f) :: t => let (a,b) := flatten d t in (KFand f a, b)
  | (postF f) :: t => let (a,b) := flatten d t in (a, KFand f b)
  end.

Fixpoint flatten_pre (d : alphabet) (l : list (elem d)) : Formula :=
  match l with
  | nil => KFtrue
  | (preF f) :: t => KFand f (flatten_pre d t)
  | (postF _) :: t => flatten_pre d t
  end.

Fixpoint flatten_post (d : alphabet) (l : list (elem d)) : Formula :=
  match l with
  | nil => KFtrue
  | (preF _) :: t => flatten_post d t
  | (postF f) :: t => KFand f (flatten_post d t)
  end.

Definition sprog2prog_aux (d : alphabet) (fd : Finite d) (s : list (elem d)) : Program :=
      KPcompose
        (KPcompose
          (KPtest (flatten_pre d s))
          (assignAny d fd))
        (KPtest (flatten_post d s))
        .

Fixpoint sprog2prog (d : alphabet) (fd : Finite d) (s : sprogram d) : Program :=
  match s with
  | nil => KPtest KFfalse
  | h :: t => KPchoice (sprog2prog_aux d fd h) (sprog2prog d fd t)
  end.

Lemma sat_sprogr2prog_sound_aux : forall (d : alphabet) (fd : Finite d) (a : list (elem d)) (t : behavior d),
    let (preS, postS) := getbehaviorKStates d t in
    dynamic_semantics_program I (sprog2prog_aux d fd a) preS postS <->
    sprogram_sat_aux d t a.
Proof.
  intros.
  assert (exists (pres posts : KState), getbehaviorKStates d t = (pres, posts)).
    destruct (getbehaviorKStates d t) as (preS, postS).
    exists preS.
    exists postS.
    reflexivity.
  destruct H as [preS [postS Hrt]].
  rewrite Hrt.
  induction a.
  +  simpl.
    split ; auto.
    intros _.
    unfold TrueFormulaSem.
    exists postS.
    split ; auto.
    exists preS.
    split ; auto.
    generalize (assignAny_dsp d fd t).
    rewrite Hrt.
    tauto.
  + induction a.
    - intros.
      simpl.
      rewrite <- IHa.
      unfold sprogram_sat_elem.
      rewrite Hrt.
      split.
      * intros [? [H0 [Hrpost ?]]].
        destruct H0 as [? [[Hrpre [? ?]] ?]].
        rewrite <- Hrpre in *.
        rewrite Hrpost in *.
        split.
        assumption.
        exists postS.
        split.
        exists preS.
        split.
        simpl; tauto.
        assumption.
        simpl; tauto.
      * simpl.
        intros [? [? H0]].
        destruct H0 as [H0 [Hrpost ?]].
        destruct H0 as [? [[Hrpre ?] ?]].
        rewrite <- Hrpre in *.
        rewrite Hrpost in *.
        exists postS.
        split.
        exists preS.
        split.
        tauto.
        assumption.
        tauto.
    - intros.
      simpl.
      rewrite <- IHa.
      unfold sprogram_sat_elem.
      rewrite Hrt.
      split.
      * intros [? [H0 [Hrpost [? ?]]]].
        destruct H0 as [? [[Hrpre ?] ?]].
        rewrite <- Hrpre in *.
        rewrite -> Hrpost in *.
        split.
          assumption.
        exists postS.
        split.
          exists preS.
        split.
        simpl.
        tauto.
        assumption.
        simpl.
        tauto.
      * simpl.
        intros [? [? H0]].
        destruct H0 as [H0 [Hrpost ?]].
        destruct H0 as [? [[Hrpre ?] ?]].
        rewrite <- Hrpre in *.
        rewrite Hrpost in *.
        exists postS.
        split.
        exists preS.
        split.
        tauto.
        assumption.
        tauto.
Qed.

Theorem sat_sprog2prog_sound : forall (d : alphabet) (fd : Finite d) (sp : sprogram d) (t : behavior d),
  let (preS, postS) := getbehaviorKStates d t in
  dynamic_semantics_program I (sprog2prog d fd sp) preS postS <-> sprogram_sat d t sp.
Proof.
  intros.
  induction sp.
  + unfold sprogram_sat.
    destruct (getbehaviorKStates d t) as [preS postS].
    unfold dynamic_semantics_program.
    simpl.
    tauto.
  + unfold sprogram_sat.
    generalize (sat_sprogr2prog_sound_aux d fd a t).
    destruct (getbehaviorKStates d t) as [preS postS].
    intro Ha.
    rewrite <- IHsp.
    assert (dynamic_semantics_program I (sprog2prog d fd (a :: sp)) preS postS <->
    dynamic_semantics_program I (sprog2prog_aux d fd a) preS postS \/
    dynamic_semantics_program I (sprog2prog d fd sp) preS postS).
      unfold sprog2prog.
      simpl.
      tauto.
    rewrite H.
    rewrite Ha.
    reflexivity.
Qed.

Definition implement_abstract_hybrid
  (d : alphabet) (fd : Finite d) (a : Program) (a_in_d : prog_in_d d a) (c : contractF d) :=
  implements d (program2component d I a a_in_d) (c2c _ d c).

Theorem proof_trans
  (d : alphabet) (fd : Finite d) (a : Program) (a_in_d : prog_in_d d a)
  (c : contractF d) (c_in_d : contract_in_d d c):
  (forall preS : KState,
  (dynamic_semantics_formula I (KFrefine d fd a (sprog2prog d fd (G d (saturateF d c)))) preS)) ->
  implement_abstract_hybrid d fd a a_in_d c.
Proof.
  intros H.
  assert (FCset2sets (all_vars_program (sprog2prog d fd (G d (saturateF d c)))) ⊆ d) as Hvarsc.
  {
    admit.
    }
  assert (refine d I a (sprog2prog d fd (G d (saturateF d c))) a_in_d Hvarsc) as Href.
    apply (refine_KFrefine d I fd a (sprog2prog d fd (G d (saturateF d c)))) ;
    assumption.
  intros t.
  unfold program2component, In.
  assert (exists preS postS, getbehaviorKStates d t = (preS, postS)) as Hrt.
    eexists.
    eexists.
    reflexivity.
  destruct Hrt as [preS [postS Hrt]].
  rewrite Hrt.
  intros dspa.
  apply sat_contract_c2c.
  unfold sat_contract.
  assert (sprogram_sat d t (G d (saturateF d c))) as H1.
    generalize (sat_sprog2prog_sound d fd (G d (saturateF d c)) t).
    rewrite Hrt.
    intros H1.
    rewrite <- H1.
    (* unfold refine, component_refines, program2component in Href. *)
    (* unfold SubsetEq, In in Href. *)
    specialize (Href t).
    unfold In, program2component in Href.
    rewrite Hrt in Href.
    apply Href.
    assumption.
  revert H1.
  unfold saturateF.
  simpl.
  rewrite <- sat_s_or.
  rewrite <- sat_s_not.
  intuition.
Admitted.

End AbstractProgram.

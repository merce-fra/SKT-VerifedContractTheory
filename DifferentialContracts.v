Require Import CoqDL.syntax.expressions.
Require Import CoqDL.semantics.dynamic_semantics.
Require Import CoqDL.semantics.static_sem.
Require Import CoqDL.checker.checker.
Require Export Contracts.

Set Printing Coercions.

Instance BT: Base_Types := {
  ident := KAssignable ;
  value := R * R ;
}.
Axiom in_dec_KAssignable : forall (x : KAssignable) (d : alphabet), {x ∈ d} + { x ∉ d}.

Instance theo : Theory BT := {
  any_value := (0 , 0)%R ;
  eq_dec_ident := KAssignable_dec ;
  in_dec_ident := in_dec_KAssignable ;
}.

Definition FCset2sets {T : Type} (f : @FCset T) : @τ T :=
  match f with
  | FCS_finite l => fun (t : T) => List.In t l
  | FCS_infinite l => fun (t : T) => ~ List.In t l
  end.

Section alphabet_defined.

Variable d : alphabet.
Variable I : interpretation.

Definition assertion := assertion d.
Definition contract := contract d.
Definition behavior := behavior d.
Definition KState := (KAssignable -> R).
Definition prog_in_d (p : Program) := FCset2sets (all_vars_program p) ⊆ d.

Definition getbehaviorValue (t : behavior) (x : KAssignable) : value :=
  match in_dec_ident x d with
                     | left x_in_d => t (exist _ x x_in_d)
                     | right _ => any_value
  end.

Definition getbehaviorKStates (t : behavior) : KState * KState:=
  (fun (x : KAssignable) => fst (getbehaviorValue t x),
  fun (x : KAssignable) => snd (getbehaviorValue t x)).

Definition mkbehavior (prestate poststate : KState) : behavior :=
  fun var => let (x, _ ):= var in (prestate x, poststate x).

Definition program2component
  (p : Program) (p_in_d : prog_in_d p) : component d :=
  fun (t : behavior) =>
  let (prestate, poststate) := getbehaviorKStates t in
  dynamic_semantics_program I p (prestate) (poststate).

Definition prog2contracts
  (a g : Program) (a_in_d : prog_in_d a) (g_in_d : prog_in_d g) : contract :=
  mkContract d (program2component a a_in_d) (program2component g g_in_d).

Lemma satisfies_DSF  (p : Program) (F : Formula) (p_in_d : prog_in_d p) :
  sequent_true_I {| seq_hyps := emHyps ; seq_concl := KFbox  p F |} I ->
  forall t : behavior, t ∈ (program2component p p_in_d) ->
  DSF F I (snd (getbehaviorKStates t)).
Proof.
  unfold program2component, In.
  intros H t.
  destruct (getbehaviorKStates t) as [prestate poststate].
  assert (DSF (KFbox p F) I prestate) as H0.
    apply H.
    simpl.
    tauto.
  apply H0.
Qed.

Lemma satisfies_DSF2 (p : Program) (F : Formula) (p_in_d : prog_in_d p) :
  sequent_true_I {| seq_hyps := emHyps ; seq_concl := KFimply (KFbox p KFtrue) F |} I ->
  forall t : behavior, t ∈ (program2component p p_in_d) ->
  DSF F I (fst (getbehaviorKStates t)).
Proof.
  unfold program2component, In.
  intros H t.
  destruct (getbehaviorKStates t) as [prestate poststate].
  assert (DSF (KFimply (KFbox p KFtrue) F) I prestate) as H0.
    apply H.
    simpl.
    tauto.
  assert ((DSF (KFbox p KFtrue) I prestate) -> (DSF F I prestate)) as H1.
    generalize H0.
    unfold DSF.
    unfold dynamic_semantics_formula.
    tauto.
  intros H5.
  apply H1.
  generalize H5.
  unfold DSF.
  unfold dynamic_semantics_formula.
  unfold TrueFormulaSem.
  simpl.
  tauto.
Qed.

Lemma nin_dom_const (t : behavior) :
  let (prestate, poststate) := getbehaviorKStates t in
  forall y : KAssignable,
  y ∉ d -> prestate y = poststate y.
Proof.
  intros y y_not_in_d.
  unfold getbehaviorValue.
  simpl.
  case (in_dec_KAssignable y d).
  + intro y_in_d.
    exfalso.
    apply y_not_in_d ; assumption.
  + tauto.
Qed.

Definition refine
  (a b : Program) (a_in_d : prog_in_d a) (b_in_d : prog_in_d b) : Prop :=
  component_refines d (program2component a a_in_d) (program2component b b_in_d).

Fixpoint fresh_kassignable_list (n : nat) (l : list KAssignable) : list KAssignable :=
  match n with
  | 0 => nil
  | S m => let (x, _):= (fresh_kassignable l) in x :: (fresh_kassignable_list m ( x :: l))
  end.

  Section finite_alphabet.

Variable (fd : Finite d).

Definition fresh_alphabet_a : list KAssignable :=
   fresh_kassignable_list (length (elements_of d fd)) (elements_of d fd).

Definition fresh_alphabet : list KVariable :=
   map KAssignable2variable fresh_alphabet_a.

Lemma KAssignVar_fresh_alphabet_aux : forall n l,
  map KAssignVar (map KAssignable2variable (fresh_kassignable_list n l)) =
  fresh_kassignable_list n l.
Proof.
  intros n.
  induction n.
  simpl ; tauto.
  simpl.
  intros l.
  rewrite (IHn (KAssignVar
        (variable
           (String (Ascii.Ascii false false false true true true true false)
             (append_string_list (map KAssignable2string l)))) :: l)).
             reflexivity.
Qed.

Lemma KAssignVar_fresh_alphabet : (map KAssignVar fresh_alphabet) = fresh_alphabet_a.
Proof.
  exact (KAssignVar_fresh_alphabet_aux (Datatypes.length (elements_of d fd)) (elements_of d fd)).
Qed.
Lemma fresh_notin_alphabet_aux : forall (x : KAssignable) (l : list KAssignable) (n : nat),
  List.In x (fresh_kassignable_list n l) -> ~ List.In x l.
Proof.
  intros.
  revert l H.
  induction n.
  simpl.
  intuition.
  intros l.
  unfold fresh_kassignable_list.
  destruct (fresh_kassignable l) as [y yp].
  simpl.
  intros [ yx_eq |Hl].
  subst.
  assumption.
  assert (~ List.In x (y :: l)).
    apply IHn.
    assumption.
  intro.
  apply H.
  right.
  assumption.
Qed.

Lemma fresh_notin_alphabet : forall x : KAssignable, List.In x fresh_alphabet_a -> x ∉ d.
Proof.
  intros.
  unfold fresh_alphabet_a in H.
  generalize (Enum _ d fd).
  generalize (fresh_notin_alphabet_aux x (elements_of d fd) (length (elements_of d fd))).
  intros.
  apply H0 in H.
  intro.
  rewrite H1 in H2.
  apply H.
  assumption.
Qed.

Lemma ndp_fresh_list : forall n l,
  NoDup (fresh_kassignable_list n l).
Proof.
  intros n.
  induction n.
  - simpl.
    intros _.
    apply NoDup_nil.
  - intros l.
    unfold fresh_kassignable_list.
    assert (exists y yp, existT _ y yp = fresh_kassignable l) as [y [yp Hy]].
    { eexists.
      eexists.
      tauto.
    }
    rewrite <- Hy.
    apply NoDup_cons_iff.
    split.
    + fold fresh_kassignable_list.
      intro.
      apply fresh_notin_alphabet_aux in H.
      apply H.
      simpl ; tauto.
    + fold fresh_kassignable_list.
      apply IHn.
Qed.

Lemma ndp_fresh_alphabet : NoDup fresh_alphabet_a.
Proof.
  apply ndp_fresh_list.
Qed.

Fixpoint KFeq_list (la : list KAssignable) ( lb : list KAssignable) : Formula :=
  match (la, lb) with
  | (nil, _::_) => KFfalse
  | (_::_, nil) => KFfalse
  | (nil, nil) => KFtrue
  | (h1::t1, h2::t2) => KFand (KFequal h1 h2) (KFeq_list t1 t2)
  end.

Definition value_d (s : KState) : list R :=
  map (fun (x : KAssignable) => s x) (elements_of d fd).

Definition KFrefine(a b : Program) : Formula :=
   (KFforallVars (fresh_alphabet)
   (KFimply (KFdiamond a (KFeq_list (elements_of d fd) (fresh_alphabet_a)))
   (KFdiamond b (KFeq_list (elements_of d fd) (fresh_alphabet_a))))).

Axiom nin_vars : forall (a : Program) (s f : KState) (x : KAssignable),
   ~(x ∈ (FCset2sets (all_vars_program a))) -> dynamic_semantics_program I a s f -> s x = f x.

Lemma nin_dom : forall (a : Program) (s f : KState) (x : KAssignable),
  FCset2sets (all_vars_program a) ⊆ d ->
  ~(x ∈ d) -> dynamic_semantics_program I a s f -> s x = f x.
Proof.
  intros a s f x Ha Hx.
  apply nin_vars.
  intros x_in_a.
  apply Hx.
  apply Ha.
  assumption.
Qed.

Lemma upd_state_eq_list (f : KState) : forall l l',
  Datatypes.length l = Datatypes.length l' ->
  dynamic_semantics_formula I (KFeq_list l l') f <->
  map f l = map f l'.
Proof.
  induction l.
  - intros l' l'_nil.
    symmetry in l'_nil.
    rewrite length_zero_iff_nil in l'_nil.
    subst.
    simpl.
    unfold TrueFormulaSem.
    tauto.
  - intros l' ll'_len.
    induction l'.
    + simpl.
      unfold FalseFormulaSem.
      split ; try tauto.
      intro H.
      symmetry in H.
      apply nil_cons in H.
      assumption.
    + simpl.
      assert (Datatypes.length l = Datatypes.length l') as Hll'_len.
      { simpl in ll'_len.
        injection ll'_len.
        tauto. }
      split.
      * intros [fa_fa0_eq dsfl].
        f_equal.
        assumption.
        rewrite <- IHl ; assumption.
      * intros Heq.
        injection Heq.
        rewrite IHl ; try assumption.
        tauto.
Qed.

Lemma FCset_app_or : forall (a1 a2 : EAssignables) (x : KAssignable),
        x ∈ FCset2sets (EAssignables_app a1 a2) <->
        x ∈ FCset2sets a1 \/ x ∈ FCset2sets a2.
Proof.
 unfold EAssignables_app, fcset_app, In.
 intros a1 a2 x.
 destruct a1.
 - destruct a2.
   + simpl.
     split.
     * apply in_app_or.
     * apply in_or_app.
   + simpl.
     rewrite in_minus_dec.
     tauto.
 - destruct a2.
   + simpl.
     rewrite in_minus_dec.
     tauto.
   + simpl.
     rewrite in_inter_dec.
     tauto.
Qed.

Lemma FC_set_app_subset : forall (a1 a2 : EAssignables),
  FCset2sets (EAssignables_app a1 a2) ⊆ d <-> FCset2sets a1 ⊆ d /\ FCset2sets a2 ⊆ d.
Proof.
  intros.
  split.
  - intros H1.
    split; 
      intros x x_in_a1;
      apply H1;
      apply FCset_app_or;
      tauto.
  - intros [H1 H2].
    intros x x_in_app.
    apply FCset_app_or in x_in_app.
    destruct x_in_app ; [apply H1 | apply H2] ; assumption.
Qed.

Definition EAssignables_d : EAssignables :=
  FCS_finite (elements_of d fd).

Lemma fcset_subset_Subseteq :
  forall f g, fcset_subset KAssignable_dec f g = true <-> FCset2sets f ⊆ FCset2sets g.
Proof.
  intros f g.
  unfold fcset_subset.
  destruct f.
  - destruct g.
    + simpl.
      rewrite included_dec_prop.
      reflexivity.
    + simpl.
      rewrite disj_dec_prop.
      reflexivity.
  - destruct g.
    + simpl.
      unfold SubsetEq, In.
      split.
      * intuition.
      * intros x_sub.
        exfalso.
        cut (exists x, ~ List.In x l /\ ~ List.In x l0).
        { intros [x [x_nin_l x_nin_l0]] ; intuition. }
        generalize (fresh_kassignable (List.app l l0)).
        intros [x xp].
        exists x.
        intuition.
    + simpl.
      rewrite included_dec_prop.
      unfold SubsetEq, In.
      split.
      * intuition.
      * intros Hsub x x_in_l0.
        admit.
Admitted.

Lemma fcset_subset_d:
  forall f,  FCset2sets f ⊆ d -> fcset_subset KAssignable_dec f EAssignables_d = true .
Proof.
  intros f f_sub_d.
  apply fcset_subset_Subseteq.
  intros x x_in_f.
  apply (Enum _ d fd).
  apply (f_sub_d x x_in_f).
Qed.

Lemma fresh_list_notin : forall(x : KAssignable) (n : nat) (l : list KAssignable),
  List.In x (fresh_kassignable_list n l) -> ~ List.In x l.
Proof.
  intros x n.
  induction n.
  - simpl.
    tauto.
  - intros l.
    unfold fresh_kassignable_list.
    assert (exists y yp, existT _ y yp = fresh_kassignable l) as [y [yp Hy]].
    { eexists.
      eexists.
      tauto.
    }
    rewrite <- Hy.
    intros x_in_f.
    apply in_inv in x_in_f.
    destruct x_in_f.
    + subst.
      assumption.
    + specialize (IHn _ H).
      intros x_in_l.
      apply IHn.
      apply in_cons.
      assumption.
Qed.

Lemma disjoint_fresh_d :
  disjoint (vars2assign fresh_alphabet) (elements_of d fd).
Proof.
  unfold disjoint.
  unfold vars2assign.
  rewrite KAssignVar_fresh_alphabet.
  intros x x_in_f.
  apply (fresh_list_notin x _ (elements_of d fd) x_in_f).
Qed.

Theorem coincidence_program_d : forall s f w P,
  FCset2sets (all_vars_program P) ⊆ d ->
  dynamic_semantics_program I P (upd_list_state s (combine fresh_alphabet (value_d f))) w ->
  (forall x, x ∈ d -> w x = f x) ->
  (forall x, ~(x ∈ d) -> s x = f x) ->
  dynamic_semantics_program I P s f.
Proof.
  introv Hav Hdsp Hd Hnd.
  generalize (coincidence_program P (upd_list_state s (combine fresh_alphabet (value_d f))) s w I I EAssignables_d).
  intros H.
  destruct H as [w' [Hdsp_sx eq_ww']].
  - apply fcset_subset_d.
    apply FC_set_app_subset in Hav.
    tauto.
  - apply equal_states_on_ea_assigns2ext.
    apply equal_states_on_upd_list_state_if_disjoint.
    apply disjoint_fresh_d.
  - apply equal_interpretations_on_ext_refl.
  - assumption.
  - assert (f = w').
    + apply functional_extensionality.
      intros x.
      case (in_dec_KAssignable x d).
      * intros x_in_d.
        rewrite <- (Hd x x_in_d).
        apply eq_ww'.
        unfold in_eassignables.
        rewrite in_fcset_app_true_iff.
        left.
        unfold EAssignables_d.
        simpl.
        case (in_dec KAssignable_dec).
        { reflexivity. }
        { rewrite <- (Enum _ d fd).
          intuition. }
      * intros x_nin_d.
        rewrite <- (Hnd x x_nin_d).
        apply nin_vars with P.
        { intros x_in_P.
          apply x_nin_d.
          apply Hav.
          assumption. }
        assumption.
    + rewrite H.
      assumption.
Qed.

Lemma upd_list_state_diff : forall s sub x,
  ~(List.In x (map KAssignVar (map  fst sub))) ->
  s x = upd_list_state s sub x.
Proof.
  intros.
  induction sub.
  - simpl ; tauto.
  -
  simpl.
  destruct a as [v r].
  rewrite upd_state_diff.
  apply IHsub.
  revert H.
  simpl.
  intuition.
  revert H.
  simpl.
  intuition.
Qed.

Lemma map_combine : forall (A B : Type) (al : list A) (bl : list B),
  Datatypes.length al = Datatypes.length bl -> map fst (combine al bl) = al.
Proof.
  intros A B al.
  induction al.
    simpl ; tauto.
  intros bl.
  induction bl.
    simpl.
    intuition.
  simpl.
  intros Hlen.
  rewrite IHal.
  reflexivity.
  auto.
Qed.



Lemma len_fresh_kassignable_list : forall (n : nat) (l : list KAssignable),
  Datatypes.length (fresh_kassignable_list n l) = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - intros l.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma len_value_d_fresh: forall f : KState,
  Datatypes.length (value_d f) = Datatypes.length fresh_alphabet.
Proof.
  intros f.
  unfold value_d, fresh_alphabet, fresh_alphabet_a.
  rewrite map_length.
  rewrite map_length.
  rewrite len_fresh_kassignable_list.
  reflexivity.
Qed.

Lemma map_upd_list_state_combine :
  forall (v w : KState) (l : list KVariable) (l': list KAssignable),
  NoDup (map KAssignVar l) ->
  Datatypes.length l = Datatypes.length l' ->
  map (upd_list_state v (combine l (map w l'))) (map KAssignVar l) =
  map w l'.
Proof.
  intros v w l l' ndl Hlen.
  apply eq_maps3.
    rewrite map_length.
    assumption.
  intros x y xy_in.
  revert l Hlen xy_in ndl.
  induction l'.
  - simpl.
    intros.
    apply length_zero_iff_nil in Hlen.
    subst.
    simpl in xy_in.
    tauto.
  - intros.
    destruct l.
    + simpl in Hlen.
      exfalso.
      tauto.
    + simpl.
      simpl in xy_in.
      destruct xy_in.
      * inversion H .
        subst.
        apply upd_state_same.
      * rewrite upd_state_diff.
        rewrite IHl'.
        reflexivity.
        simpl in Hlen.
        injection Hlen.
        tauto.
        assumption.
        apply NoDup_cons_iff in ndl.
        tauto.
        {
          apply NoDup_map_inv in ndl.
          apply NoDup_cons_iff in ndl.
          destruct ndl as [k_nin_l _].
          apply in_combine_l in H.
          intro k_eq_x.
          subst.
          apply k_nin_l.
          apply in_map_iff in H.
          destruct H.
          destruct H.
          injection H.
          intros xk_eq.
          subst.
          simpl.
          fold map.
          tauto.
          }
Qed.

Open Scope list_scope.
Lemma fcset_sub : forall (fs : EAssignables),
  FCset2sets fs ⊆ d <->
  eassignables_subset fs EAssignables_d = true.
Proof.
  intros fs.
  unfold eassignables_subset, fcset_subset, EAssignables_d.
  destruct fs.
  - unfold SubsetEq.
    simpl.
    rewrite included_dec_prop.
    unfold subset.
    split ; intros.
    + rewrite <- (Enum _ d fd).
      apply H ; assumption.
    + rewrite (Enum _ d fd).
      apply H ; assumption.
  - simpl.
    split; intros.
    + exfalso.
      unfold SubsetEq in H.
      assert (exists x xp, existT _ x xp = fresh_kassignable (l ++ (elements_of d fd))) as [x [xp Hr]].
        eexists.
        eexists.
        tauto.
      specialize (H  x).
      rewrite (Enum _ d fd x) in H.
      unfold In in H.
      apply xp.
      rewrite in_app_iff.
      right.
      apply H.
      intro.
      apply xp.
      rewrite in_app_iff.
      left.
      assumption.
    + exfalso.
      apply diff_false_true ; assumption.
Qed.

Theorem refine_KFrefine
  (a b : Program) (a_in_d : prog_in_d a) (b_in_d : prog_in_d b) :
  (forall preS : KState, dynamic_semantics_formula  I (KFrefine a b) preS) ->
  refine a b a_in_d b_in_d.
Proof.
  intros HKref.
  unfold refine, component_refines, program2component.
  intros t.
  unfold In.
  assert (exists s f,getbehaviorKStates t = (s,f)) as [s [f Ht]].
    { eexists ; eexists ; tauto. }
  rewrite Ht.
  intros dspa.
  specialize (HKref s (value_d f)).
  fold dynamic_semantics_formula in HKref.
  destruct HKref.
  - exact (len_value_d_fresh f).
  - fold dynamic_semantics_formula.
    fold dynamic_semantics_program.
    generalize (coincidence_program a s
    (upd_list_state s (combine fresh_alphabet (map f (elements_of d fd))))
    f I I EAssignables_d).
    intros H.
    destruct H as  [w [Hasfw eq_fw]].
    + apply fcset_sub.
      unfold prog_in_d, all_vars_program in a_in_d.
      apply FC_set_app_subset in a_in_d.
      tauto.
    + admit. (* upd s = s on d *)
    + exact (equal_interpretations_on_ext_refl _ _).
    + assumption.
    + exists w.
      split.
      * rewrite upd_state_eq_list.
        assert (map w (elements_of d fd) = map f (elements_of d fd)) as eq_fw_map.
        { apply map_ext_in.
          intros x x_in_d.
          symmetry.
          apply eq_fw.
          rewrite in_eassignables_app_true_iff.
          left.
          unfold EAssignables_d.
          simpl.
          destruct in_dec ; intuition.
          }
        rewrite eq_fw_map.
        assert (map (upd_list_state s (combine fresh_alphabet (map f (elements_of d fd)))) fresh_alphabet_a = map w fresh_alphabet_a) as eq_sw_map.
        { apply map_ext_in.
          intros x x_in_fresh.
          apply (nin_dom a _ _ x a_in_d).
          exact (fresh_notin_alphabet x x_in_fresh).
          assumption.
        }
        rewrite <- eq_sw_map.
        symmetry.
        rewrite <-  KAssignVar_fresh_alphabet.
        rewrite  map_upd_list_state_combine.
        reflexivity.
        { rewrite KAssignVar_fresh_alphabet.
          apply ndp_fresh_alphabet.
          }
        { admit. (* length *) }
        { admit. (* length *) }
      * assumption.
  - fold dynamic_semantics_formula in H.
    fold dynamic_semantics_program in H.
    destruct H as [Heq H].
    apply (coincidence_program_d s f x b).
    + assumption.
    + assumption.
    + intros y.
      rewrite (Enum _ d fd).
      cut (map x (elements_of d fd) = map f (elements_of d fd)).
        admit.
      rewrite (upd_state_eq_list x (elements_of d fd) fresh_alphabet_a) in Heq.
      rewrite Heq.
      assert (map x fresh_alphabet_a = map (upd_list_state s (combine fresh_alphabet (value_d f))) fresh_alphabet_a).
        admit.
      rewrite H0.
      admit.
      admit.
    + intros y y_nin_d.
      apply nin_dom with a ; assumption.
Admitted.

End finite_alphabet.

End alphabet_defined.

(**
  Complexity-bounded generated models.

  This ports Foundation/Modal/Kripke/ComplexityLimited.lean.  A target formula
  of complexity [d] only needs worlds reachable from its distinguished root
  in at most [d] steps.  The strengthened truth lemma records the remaining
  syntactic budget explicitly as [n + complexity p <= complexity target].
  That form avoids truncated subtraction and makes the modal induction
  constructive.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From FoundationModal Require Import Syntax Kripke.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma complexity_subformula_le :
  forall (AtomType : Type) (target p : formula AtomType),
    In p (subformulas target) -> complexity p <= complexity target.
Proof.
  intros AtomType target; induction target as [a | | q IHq r IHr | q IHq];
    intros p Hp; simpl in Hp |- *.
  - destruct Hp as [Hp | []]. subst p. reflexivity.
  - destruct Hp as [Hp | []]. subst p. reflexivity.
  - destruct Hp as [Hp | Hp].
    + subst p. reflexivity.
    + apply in_app_iff in Hp. destruct Hp as [Hp | Hp].
      * specialize (IHq p Hp). lia.
      * specialize (IHr p Hp). lia.
  - destruct Hp as [Hp | Hp].
    + subst p. reflexivity.
    + specialize (IHq p Hp). lia.
Qed.

Definition complexity_limited_member {AtomType}
    (F : frame) (root : World F) (target : formula AtomType)
    (x : World F) : Prop :=
  exists n, n <= complexity target /\ rel_iter (Rel F) n root x.

Arguments complexity_limited_member {AtomType} F root target x.

Definition complexity_limited_frame {AtomType}
    (F : frame) (root : World F) (target : formula AtomType) : frame :=
  {| World := { x : World F |
                 complexity_limited_member F root target x };
     Rel := fun x y => Rel F (proj1_sig x) (proj1_sig y) |}.

Arguments complexity_limited_frame {AtomType} F root target.

Definition complexity_limited_valuation {AtomType}
    (F : frame) (V : valuation AtomType F) (root : World F)
    (target : formula AtomType)
    : valuation AtomType (complexity_limited_frame F root target) :=
  fun a x => V a (proj1_sig x).

Arguments complexity_limited_valuation {AtomType F} V root target.

Definition complexity_limited_root {AtomType}
    (F : frame) (root : World F) (target : formula AtomType)
    : World (complexity_limited_frame F root target).
Proof.
  exists root. exists 0. split; [lia | reflexivity].
Defined.

Arguments complexity_limited_root {AtomType} F root target.

Lemma complexity_limited_truth_aux :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (root : World F) (target p : formula AtomType),
    In p (subformulas target) ->
    forall (x : World (complexity_limited_frame F root target)),
      (exists n,
          n + complexity p <= complexity target /\
          rel_iter (Rel F) n root (proj1_sig x)) ->
      satisfies F V (proj1_sig x) p <->
      satisfies (complexity_limited_frame F root target)
        (complexity_limited_valuation V root target) x p.
Proof.
  intros AtomType F V root target p.
  revert target.
  induction p as [a | | p IHp q IHq | p IHp];
    intros target Hsub x Hbudget; simpl.
  - reflexivity.
  - tauto.
  - assert (Hp_sub : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left. apply subformulas_self. }
    assert (Hq_sub : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right. apply subformulas_self. }
    assert (Hp_budget :
      exists n, n + complexity p <= complexity target /\
                rel_iter (Rel F) n root (proj1_sig x)).
    { destruct Hbudget as [n [Hn Hreach]].
      simpl in Hn.
      pose proof (Nat.le_max_l (complexity p) (complexity q)).
      exists n. split; [lia | exact Hreach]. }
    assert (Hq_budget :
      exists n, n + complexity q <= complexity target /\
                rel_iter (Rel F) n root (proj1_sig x)).
    { destruct Hbudget as [n [Hn Hreach]].
      simpl in Hn.
      pose proof (Nat.le_max_r (complexity p) (complexity q)).
      exists n. split; [lia | exact Hreach]. }
    specialize (IHp target Hp_sub x Hp_budget).
    specialize (IHq target Hq_sub x Hq_budget).
    tauto.
  - assert (Hp_sub : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box. apply subformulas_self. }
    destruct Hbudget as [n [Hn Hreach]].
    simpl in Hn.
    split.
    + intros Hbox y Rxy.
      assert (Hy_budget :
        exists m, m + complexity p <= complexity target /\
                  rel_iter (Rel F) m root (proj1_sig y)).
      { exists (S n). split; [lia |].
        eapply rel_iter_step_right; eauto. }
      apply (proj1 (IHp target Hp_sub y Hy_budget)).
      apply Hbox. exact Rxy.
    + intros Hbox y Rxy.
      assert (Hy_member : complexity_limited_member F root target y).
      { exists (S n). split; [lia |].
        eapply rel_iter_step_right; eauto. }
      set (ly := exist
        (fun z : World F => complexity_limited_member F root target z)
        y Hy_member).
      assert (Hly_budget :
        exists m, m + complexity p <= complexity target /\
                  rel_iter (Rel F) m root (proj1_sig ly)).
      { exists (S n). split; [lia |].
        simpl. eapply rel_iter_step_right; eauto. }
      apply (proj2 (IHp target Hp_sub ly Hly_budget)).
      apply Hbox. exact Rxy.
Qed.

Theorem complexity_limited_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (root : World F) (target : formula AtomType),
    satisfies F V root target <->
    satisfies (complexity_limited_frame F root target)
      (complexity_limited_valuation V root target)
      (complexity_limited_root F root target) target.
Proof.
  intros AtomType F V root target.
  refine (@complexity_limited_truth_aux
    AtomType F V root target target (subformulas_self target)
    (complexity_limited_root F root target) _).
  exists 0. split; [lia | reflexivity].
Qed.

Theorem complexity_limited_subformula_closed_aux :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (root : World F) (p target1 target2 : formula AtomType),
    In p (subformulas target1) ->
    In p (subformulas target2) ->
    satisfies (complexity_limited_frame F root target1)
      (complexity_limited_valuation V root target1)
      (complexity_limited_root F root target1) p ->
    satisfies (complexity_limited_frame F root target2)
      (complexity_limited_valuation V root target2)
      (complexity_limited_root F root target2) p.
Proof.
  intros AtomType F V root p target1 target2 Hsub1 Hsub2 Hsat.
  assert (Hbudget1 :
    exists n,
      n + complexity p <= complexity target1 /\
      rel_iter (Rel F) n root
        (proj1_sig (complexity_limited_root F root target1))).
  { exists 0. split.
    - simpl. apply complexity_subformula_le. exact Hsub1.
    - reflexivity. }
  assert (Hbudget2 :
    exists n,
      n + complexity p <= complexity target2 /\
      rel_iter (Rel F) n root
        (proj1_sig (complexity_limited_root F root target2))).
  { exists 0. split.
    - simpl. apply complexity_subformula_le. exact Hsub2.
    - reflexivity. }
  apply (proj1 (@complexity_limited_truth_aux
    AtomType F V root target2 p Hsub2
    (complexity_limited_root F root target2) Hbudget2)).
  apply (proj2 (@complexity_limited_truth_aux
    AtomType F V root target1 p Hsub1
    (complexity_limited_root F root target1) Hbudget1)).
  exact Hsat.
Qed.

Theorem complexity_limited_subformula_closed :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (root : World F) (p target : formula AtomType),
    In p (subformulas target) ->
    satisfies (complexity_limited_frame F root p)
      (complexity_limited_valuation V root p)
      (complexity_limited_root F root p) p <->
    satisfies (complexity_limited_frame F root target)
      (complexity_limited_valuation V root target)
      (complexity_limited_root F root target) p.
Proof.
  intros AtomType F V root p target Hsub.
  split; intro H.
  - exact (@complexity_limited_subformula_closed_aux
      AtomType F V root p p target (subformulas_self p) Hsub H).
  - exact (@complexity_limited_subformula_closed_aux
      AtomType F V root p target p Hsub (subformulas_self p) H).
Qed.

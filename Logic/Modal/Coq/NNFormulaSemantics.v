(**
  Direct Kripke semantics for negation-normal modal formulas.

  This ports Foundation/Modal/Kripke/NNFormula.lean at read-only source revision
  32e1a0956a8622fad067328ca1959729a7634428.  Unlike the upstream file, the
  development is polymorphic in the atom type.  The two representation
  translations are shown to preserve truth at worlds, validity on models,
  and validity on frames.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import Syntax Kripke NNFormula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint nn_satisfies {AtomType} (F : frame) (V : valuation AtomType F)
    (w : World F) (p : nnformula AtomType) : Prop :=
  match p with
  | NAtom a => V a w
  | NNegAtom a => ~ V a w
  | NBottom => False
  | NTop => True
  | NOr q r => @nn_satisfies AtomType F V w q \/
               @nn_satisfies AtomType F V w r
  | NAnd q r => @nn_satisfies AtomType F V w q /\
                @nn_satisfies AtomType F V w r
  | NBox q => forall u, Rel F w u -> @nn_satisfies AtomType F V u q
  | NDia q => exists u, Rel F w u /\ @nn_satisfies AtomType F V u q
  end.

Arguments nn_satisfies {AtomType} F V w p.

Definition nn_model_valid {AtomType} (F : frame)
    (V : valuation AtomType F) (p : nnformula AtomType) : Prop :=
  forall w, nn_satisfies F V w p.

Definition nn_valid {AtomType} (F : frame) (p : nnformula AtomType) : Prop :=
  forall (V : valuation AtomType F) w, nn_satisfies F V w p.

Definition nn_frame_class_valid {AtomType} (C : frame -> Prop)
    (p : nnformula AtomType) : Prop :=
  forall F, C F -> nn_valid F p.

Arguments nn_model_valid {AtomType} F V p.
Arguments nn_valid {AtomType} F p.
Arguments nn_frame_class_valid {AtomType} C p.

Lemma nn_satisfies_atom :
  forall AtomType F (V : valuation AtomType F) w a,
    nn_satisfies F V w (NAtom a) <-> V a w.
Proof. reflexivity. Qed.

Lemma nn_satisfies_natom :
  forall AtomType F (V : valuation AtomType F) w a,
    nn_satisfies F V w (NNegAtom a) <-> ~ V a w.
Proof. reflexivity. Qed.

Lemma nn_satisfies_bottom :
  forall AtomType F (V : valuation AtomType F) w,
    ~ nn_satisfies F V w (@NBottom AtomType).
Proof. intros; simpl; auto. Qed.

Lemma nn_satisfies_top :
  forall AtomType F (V : valuation AtomType F) w,
    nn_satisfies F V w (@NTop AtomType).
Proof. intros; simpl; auto. Qed.

Lemma nn_satisfies_or :
  forall AtomType F (V : valuation AtomType F) w
         (p q : nnformula AtomType),
    nn_satisfies F V w (NOr p q) <->
      nn_satisfies F V w p \/ nn_satisfies F V w q.
Proof. reflexivity. Qed.

Lemma nn_satisfies_and :
  forall AtomType F (V : valuation AtomType F) w
         (p q : nnformula AtomType),
    nn_satisfies F V w (NAnd p q) <->
      nn_satisfies F V w p /\ nn_satisfies F V w q.
Proof. reflexivity. Qed.

Lemma nn_satisfies_box :
  forall AtomType F (V : valuation AtomType F) w
         (p : nnformula AtomType),
    nn_satisfies F V w (NBox p) <->
      forall u, Rel F w u -> nn_satisfies F V u p.
Proof. reflexivity. Qed.

Lemma nn_satisfies_dia :
  forall AtomType F (V : valuation AtomType F) w
         (p : nnformula AtomType),
    nn_satisfies F V w (NDia p) <->
      exists u, Rel F w u /\ nn_satisfies F V u p.
Proof. reflexivity. Qed.

(** Negation in the normal-form syntax has exactly its intended classical
    meaning.  Classical reasoning is needed for the conjunction and box
    cases, where a failed universal statement yields a counterexample. *)
Theorem nn_satisfies_neg :
  forall AtomType F (V : valuation AtomType F) w
         (p : nnformula AtomType),
    nn_satisfies F V w (nn_neg p) <-> ~ nn_satisfies F V w p.
Proof.
  intros AtomType F V w p; revert w.
  induction p as [a | a | | | p IHp q IHq | p IHp q IHq | p IHp | p IHp];
    intro w; simpl.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - rewrite IHp, IHq. tauto.
  - rewrite IHp, IHq. tauto.
  - split.
    + intros [u [Rwu Hneg]] Hbox.
      apply (proj1 (IHp u) Hneg). now apply Hbox.
    + intro Hnotbox. apply NNPP. intro Hnone.
      apply Hnotbox. intros u Rwu.
      apply NNPP. intro Hnotp.
      apply Hnone. exists u; split; [exact Rwu |].
      apply (proj2 (IHp u)); exact Hnotp.
  - split.
    + intros Hbox [u [Rwu Hp]].
      apply (proj1 (IHp u) (Hbox u Rwu)); exact Hp.
    + intros Hnotdia u Rwu.
      apply (proj2 (IHp u)). intro Hp.
      apply Hnotdia. exists u; auto.
Qed.

Corollary nn_satisfies_imp :
  forall AtomType F (V : valuation AtomType F) w
         (p q : nnformula AtomType),
    nn_satisfies F V w (nn_imp p q) <->
      (nn_satisfies F V w p -> nn_satisfies F V w q).
Proof.
  intros; unfold nn_imp; simpl. rewrite nn_satisfies_neg. tauto.
Qed.

Corollary nn_satisfies_iff :
  forall AtomType F (V : valuation AtomType F) w
         (p q : nnformula AtomType),
    nn_satisfies F V w (nn_iff p q) <->
      (nn_satisfies F V w p <-> nn_satisfies F V w q).
Proof.
  intros; unfold nn_iff.
  rewrite nn_satisfies_and, !nn_satisfies_imp. tauto.
Qed.

(** Interpreting an NN formula as ordinary modal syntax preserves truth. *)
Theorem nn_to_formula_correct :
  forall AtomType (F : frame) (V : valuation AtomType F) w
         (p : nnformula AtomType),
    nn_satisfies F V w p <-> satisfies F V w (nn_to_formula p).
Proof.
  intros AtomType F V w p; revert w.
  induction p as [a | a | | | p IHp q IHq | p IHp q IHq | p IHp | p IHp];
    intro w.
  - reflexivity.
  - reflexivity.
  - cbn; tauto.
  - cbn; tauto.
  - change
      ((nn_satisfies F V w p \/ nn_satisfies F V w q) <->
       satisfies F V w (Or (nn_to_formula p) (nn_to_formula q))).
    rewrite satisfies_or, <- IHp, <- IHq. reflexivity.
  - change
      ((nn_satisfies F V w p /\ nn_satisfies F V w q) <->
       satisfies F V w (And (nn_to_formula p) (nn_to_formula q))).
    rewrite satisfies_and, <- IHp, <- IHq. reflexivity.
  - split; intros H u Rwu.
    + apply (proj1 (IHp u)); now apply H.
    + apply (proj2 (IHp u)); now apply H.
  - change
      ((exists u, Rel F w u /\ nn_satisfies F V u p) <->
       satisfies F V w (Dia (nn_to_formula p))).
    rewrite satisfies_dia. split.
    + intros [u [Rwu Hu]]. exists u; split; auto.
      apply (proj1 (IHp u)); exact Hu.
    + intros [u [Rwu Hu]]. exists u; split; auto.
      apply (proj2 (IHp u)); exact Hu.
Qed.

Corollary nn_to_formula_model_valid :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (p : nnformula AtomType),
    nn_model_valid F V p <->
      @model_valid AtomType F V (nn_to_formula p).
Proof.
  intros; unfold nn_model_valid, model_valid; split; intros H w.
  - apply (proj1 (@nn_to_formula_correct AtomType F V w p)); apply H.
  - apply (proj2 (@nn_to_formula_correct AtomType F V w p)); apply H.
Qed.

Corollary nn_to_formula_valid :
  forall AtomType (F : frame) (p : nnformula AtomType),
    nn_valid F p <-> valid F (nn_to_formula p).
Proof.
  intros; unfold nn_valid, valid; split; intros H V w.
  - apply (proj1 (@nn_to_formula_correct AtomType F V w p)); apply H.
  - apply (proj2 (@nn_to_formula_correct AtomType F V w p)); apply H.
Qed.

(** Translating ordinary syntax into negation normal form also preserves
    truth.  The implication case is precisely [nn_satisfies_imp]. *)
Theorem formula_to_nnf_correct :
  forall AtomType (F : frame) (V : valuation AtomType F) w
         (p : formula AtomType),
    satisfies F V w p <-> nn_satisfies F V w (formula_to_nnf p).
Proof.
  intros AtomType F V w p; revert w.
  induction p as [a | | p IHp q IHq | p IHp]; intro w.
  - reflexivity.
  - cbn; tauto.
  - change
      ((satisfies F V w p -> satisfies F V w q) <->
       nn_satisfies F V w
         (nn_imp (formula_to_nnf p) (formula_to_nnf q))).
    rewrite nn_satisfies_imp, <- IHp, <- IHq. reflexivity.
  - split; intros H u Rwu.
    + apply (proj1 (IHp u)); now apply H.
    + apply (proj2 (IHp u)); now apply H.
Qed.

Corollary formula_to_nnf_model_valid :
  forall AtomType (F : frame) (V : valuation AtomType F)
         (p : formula AtomType),
    @model_valid AtomType F V p <->
      nn_model_valid F V (formula_to_nnf p).
Proof.
  intros; unfold nn_model_valid, model_valid; split; intros H w.
  - apply (proj1 (@formula_to_nnf_correct AtomType F V w p)); apply H.
  - apply (proj2 (@formula_to_nnf_correct AtomType F V w p)); apply H.
Qed.

Corollary formula_to_nnf_valid :
  forall AtomType (F : frame) (p : formula AtomType),
    valid F p <-> nn_valid F (formula_to_nnf p).
Proof.
  intros; unfold nn_valid, valid; split; intros H V w.
  - apply (proj1 (@formula_to_nnf_correct AtomType F V w p)); apply H.
  - apply (proj2 (@formula_to_nnf_correct AtomType F V w p)); apply H.
Qed.

(** The two representation round trips are semantic retractions. *)
Corollary formula_nnf_round_trip :
  forall AtomType (F : frame) (V : valuation AtomType F) w
         (p : formula AtomType),
    satisfies F V w (nn_to_formula (formula_to_nnf p)) <->
      satisfies F V w p.
Proof.
  intros. rewrite <- nn_to_formula_correct, <- formula_to_nnf_correct.
  reflexivity.
Qed.

Corollary nn_formula_round_trip :
  forall AtomType (F : frame) (V : valuation AtomType F) w
         (p : nnformula AtomType),
    nn_satisfies F V w (formula_to_nnf (nn_to_formula p)) <->
      nn_satisfies F V w p.
Proof.
  intros. rewrite <- formula_to_nnf_correct, <- nn_to_formula_correct.
  reflexivity.
Qed.

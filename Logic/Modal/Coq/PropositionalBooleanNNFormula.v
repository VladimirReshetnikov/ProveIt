(**
  Algebraic and Boolean evaluation of propositional NNF.

  This module ports [Propositional/Boolean/NNFormula.lean].  Its generic
  evaluator targets any carrier with involutive De Morgan connectives and is
  packaged as a full connective homomorphism.  The Prop-valued specialization
  then supplies ordinary truth-functional semantics.
*)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  GenericSemantics GenericLogicSymbol PropositionalFormula
  PropositionalNNFormula PropositionalTranslation PropositionalBoolean.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint pnn_eval_aux {Atom F : Type}
    (C : generic_connectives F) (v : Atom -> F)
    (p : pnnformula Atom) : F :=
  match p with
  | PNNTop => generic_top C
  | PNNBottom => generic_bottom C
  | PNNAtom a => v a
  | PNNNegAtom a => generic_neg C (v a)
  | PNNAnd q r => generic_and C (pnn_eval_aux C v q) (pnn_eval_aux C v r)
  | PNNOr q r => generic_or C (pnn_eval_aux C v q) (pnn_eval_aux C v r)
  end.

Lemma pnn_eval_aux_neg :
  forall (Atom F : Type) (C : generic_connectives F)
         (Hdm : generic_de_morgan_laws C)
         (Hinv : generic_neg_involutive_law C)
         (v : Atom -> F) (p : pnnformula Atom),
    pnn_eval_aux C v (pnn_neg p) = generic_neg C (pnn_eval_aux C v p).
Proof.
  intros Atom F C Hdm Hinv v p.
  induction p as [| |a|a|p IHp q IHq|p IHp q IHq]; simpl.
  - symmetry. apply (generic_de_morgan_neg_top Hdm).
  - symmetry. apply (generic_de_morgan_neg_bottom Hdm).
  - reflexivity.
  - symmetry. apply Hinv.
  - rewrite IHp, IHq. symmetry.
    apply (generic_de_morgan_neg_and Hdm).
  - rewrite IHp, IHq. symmetry.
    apply (generic_de_morgan_neg_or Hdm).
Qed.

Definition pnn_eval_hom {Atom F : Type}
    (C : generic_connectives F)
    (Hdm : generic_de_morgan_laws C)
    (Hinv : generic_neg_involutive_law C)
    (v : Atom -> F) :
    generic_connective_hom (pnnformula_connectives Atom) C.
Proof.
  refine {| generic_connective_hom_apply := pnn_eval_aux C v |}.
  - reflexivity.
  - reflexivity.
  - intro p. apply pnn_eval_aux_neg; assumption.
  - intros p q. simpl.
    rewrite (@pnn_eval_aux_neg Atom F C Hdm Hinv v p).
    symmetry. apply (generic_de_morgan_imp Hdm).
  - reflexivity.
  - reflexivity.
Defined.

Lemma pnn_eval_atom :
  forall (Atom F : Type) (C : generic_connectives F)
         (Hdm : generic_de_morgan_laws C)
         (Hinv : generic_neg_involutive_law C)
         (v : Atom -> F) (a : Atom),
    generic_connective_hom_apply
      (@pnn_eval_hom Atom F C Hdm Hinv v) (PNNAtom a) =
    v a.
Proof. reflexivity. Qed.

Lemma pnn_eval_neg_atom :
  forall (Atom F : Type) (C : generic_connectives F)
         (Hdm : generic_de_morgan_laws C)
         (Hinv : generic_neg_involutive_law C)
         (v : Atom -> F) (a : Atom),
    generic_connective_hom_apply
      (@pnn_eval_hom Atom F C Hdm Hinv v) (PNNNegAtom a) =
    generic_neg C (v a).
Proof. reflexivity. Qed.

(** * Prop-valued Boolean semantics *)

Definition pnn_prop_connectives : generic_connectives Prop :=
  {| generic_top := True;
     generic_bottom := False;
     generic_and := and;
     generic_or := or;
     generic_imp := fun P Q => P -> Q;
     generic_neg := not |}.

Definition pnn_boolean_eval {Atom : Type}
    (v : pvaluation Atom) (p : pnnformula Atom) : Prop :=
  pnn_eval_aux pnn_prop_connectives v p.

Definition pnn_boolean_semantics (Atom : Type) :
    generic_semantics (pvaluation Atom) (pnnformula Atom) :=
  {| generic_models := pnn_boolean_eval |}.

Lemma pnn_boolean_models_iff_eval :
  forall (Atom : Type) (v : pvaluation Atom) (p : pnnformula Atom),
    generic_models (pnn_boolean_semantics Atom) v p <->
    pnn_boolean_eval v p.
Proof. reflexivity. Qed.

Lemma pnn_boolean_eval_neg :
  forall (Atom : Type) (v : pvaluation Atom) (p : pnnformula Atom),
    pnn_boolean_eval v (pnn_neg p) <-> ~ pnn_boolean_eval v p.
Proof.
  intros Atom v p.
  induction p as [| |a|a|p IHp q IHq|p IHp q IHq];
    unfold pnn_boolean_eval in *; simpl in *.
  - tauto.
  - tauto.
  - tauto.
  - destruct (classic (v a)); tauto.
  - rewrite IHp, IHq. tauto.
  - rewrite IHp, IHq. tauto.
Qed.

Lemma pnn_boolean_tarski_top :
  forall Atom : Type,
    generic_semantics_top
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof. intros Atom; constructor; intros v; exact I. Qed.

Lemma pnn_boolean_tarski_bottom :
  forall Atom : Type,
    generic_semantics_bottom
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof. intros Atom; constructor; intros v H; exact H. Qed.

Lemma pnn_boolean_tarski_and :
  forall Atom : Type,
    generic_semantics_and
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof. intros Atom; constructor; reflexivity. Qed.

Lemma pnn_boolean_tarski_or :
  forall Atom : Type,
    generic_semantics_or
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof. intros Atom; constructor; reflexivity. Qed.

Lemma pnn_boolean_tarski_neg :
  forall Atom : Type,
    generic_semantics_neg
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof.
  intros Atom; constructor; intros v p.
  apply pnn_boolean_eval_neg.
Qed.

Lemma pnn_boolean_tarski_imp :
  forall Atom : Type,
    generic_semantics_imp
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof.
  intros Atom; constructor; intros v p q.
  change (pnn_boolean_eval v (pnn_neg p) \/ pnn_boolean_eval v q <->
          (pnn_boolean_eval v p -> pnn_boolean_eval v q)).
  rewrite pnn_boolean_eval_neg. destruct (classic (pnn_boolean_eval v p)); tauto.
Qed.

Lemma pnn_boolean_tarski :
  forall Atom : Type,
    generic_tarski
      (pnnformula_connectives Atom) (pnn_boolean_semantics Atom).
Proof.
  intro Atom. constructor.
  - apply pnn_boolean_tarski_top.
  - apply pnn_boolean_tarski_bottom.
  - apply pnn_boolean_tarski_and.
  - apply pnn_boolean_tarski_or.
  - apply pnn_boolean_tarski_imp.
  - apply pnn_boolean_tarski_neg.
Qed.

Lemma pnn_boolean_models_atom :
  forall (Atom : Type) (v : pvaluation Atom) (a : Atom),
    generic_models (pnn_boolean_semantics Atom) v (PNNAtom a) <-> v a.
Proof. reflexivity. Qed.

Lemma pnn_boolean_models_neg_atom :
  forall (Atom : Type) (v : pvaluation Atom) (a : Atom),
    generic_models (pnn_boolean_semantics Atom) v (PNNNegAtom a) <-> ~ v a.
Proof. reflexivity. Qed.

(** The explicit translation bridge preserves the Boolean interpretation. *)
Lemma pnn_to_pformula_eval :
  forall (Atom : Type) (v : pvaluation Atom) (p : pnnformula Atom),
    pboolean_eval v (pnn_to_pformula p) <-> pnn_boolean_eval v p.
Proof.
  intros Atom v p.
  induction p as [| |a|a|p IHp q IHq|p IHp q IHq];
    unfold pnn_boolean_eval in *; simpl in *; tauto.
Qed.

Lemma pformula_to_pnn_eval :
  forall (Atom : Type) (v : pvaluation Atom) (p : pformula Atom),
    pnn_boolean_eval v (pformula_to_pnn p) <-> pboolean_eval v p.
Proof.
  intros Atom v p.
  induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq].
  - reflexivity.
  - reflexivity.
  - change
      (pnn_boolean_eval v (pformula_to_pnn p) /\
       pnn_boolean_eval v (pformula_to_pnn q) <->
       pboolean_eval v p /\ pboolean_eval v q).
    rewrite IHp, IHq. tauto.
  - change
      (pnn_boolean_eval v (pformula_to_pnn p) \/
       pnn_boolean_eval v (pformula_to_pnn q) <->
       pboolean_eval v p \/ pboolean_eval v q).
    rewrite IHp, IHq. tauto.
  - change
      (pnn_boolean_eval v (pnn_neg (pformula_to_pnn p)) \/
       pnn_boolean_eval v (pformula_to_pnn q) <->
       (pboolean_eval v p -> pboolean_eval v q)).
    rewrite pnn_boolean_eval_neg, IHp, IHq.
    destruct (classic (pboolean_eval v p)); tauto.
Qed.

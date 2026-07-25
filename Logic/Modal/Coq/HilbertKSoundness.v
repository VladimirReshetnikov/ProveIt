(**
  Kripke soundness of the concrete Hilbert calculus K.

  This is the K-specialized core of Foundation/Modal/Kripke/Hilbert.lean.
  Keeping it separate from [HilbertK] lets the proof calculus remain
  independent of any semantic presentation.
*)

From FoundationModal Require Import Syntax Axioms Kripke HilbertK.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma valid_Hilbert_imply_K :
  forall (AtomType : Type) (F : frame) (p q : formula AtomType),
    valid F (Hilbert_imply_K p q).
Proof. intros AtomType F p q V w; simpl; tauto. Qed.

Lemma valid_Hilbert_imply_S :
  forall (AtomType : Type) (F : frame) (p q r : formula AtomType),
    valid F (Hilbert_imply_S p q r).
Proof. intros AtomType F p q r V w; simpl; tauto. Qed.

Lemma valid_Hilbert_elim_contra :
  forall (AtomType : Type) (F : frame) (p q : formula AtomType),
    valid F (Hilbert_elim_contra p q).
Proof. intros AtomType F p q V w; simpl; tauto. Qed.

Lemma valid_mp :
  forall (AtomType : Type) (F : frame) (p q : formula AtomType),
    valid F (Imp p q) -> valid F p -> valid F q.
Proof.
  intros AtomType F p q Hpq Hp V w.
  exact (Hpq V w (Hp V w)).
Qed.

Lemma valid_nec :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    valid F p -> valid F (Box p).
Proof. intros AtomType F p Hp V w u Rwu; apply Hp. Qed.

Theorem K_proves_sound_on_frame :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    K_proves p -> valid F p.
Proof.
  intros AtomType F p Hp.
  induction Hp.
  - apply valid_Hilbert_imply_K.
  - apply valid_Hilbert_imply_S.
  - apply valid_Hilbert_elim_contra.
  - apply valid_K.
  - eapply valid_mp; eauto.
  - apply valid_nec; assumption.
Qed.

Definition satisfies_theory {AtomType}
    (F : frame) (V : valuation AtomType F) (w : World F)
    (Gamma : theory AtomType) : Prop :=
  forall p, Gamma p -> satisfies F V w p.

Arguments satisfies_theory {AtomType} F V w Gamma.

Theorem K_derives_sound :
  forall (AtomType : Type) (Gamma : theory AtomType)
         (p : formula AtomType),
    K_derives Gamma p ->
    forall (F : frame) (V : valuation AtomType F) (w : World F),
      satisfies_theory F V w Gamma -> satisfies F V w p.
Proof.
  intros AtomType Gamma p Hp.
  induction Hp; intros F V w Hgamma.
  - apply Hgamma; assumption.
  - apply K_proves_sound_on_frame; assumption.
  - apply IHHp1; [exact Hgamma |].
    apply IHHp2; exact Hgamma.
Qed.

Definition irreflexive_singleton_frame : frame :=
  {| World := unit;
     Rel := fun _ _ => False |}.

Theorem K_is_consistent :
  forall AtomType, ~ K_proves (@Bottom AtomType).
Proof.
  intros AtomType Hbottom.
  pose proof
    (@K_proves_sound_on_frame AtomType irreflexive_singleton_frame Bottom
      Hbottom (fun _ _ => False) tt) as Hfalse.
  exact Hfalse.
Qed.

Theorem K_empty_theory_consistent :
  forall AtomType, @theory_consistent AtomType empty_theory.
Proof.
  intros AtomType Hbottom.
  apply (@K_is_consistent AtomType).
  apply K_derives_empty_iff. exact Hbottom.
Qed.

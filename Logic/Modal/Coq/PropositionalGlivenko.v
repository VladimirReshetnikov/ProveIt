(** Glivenko's theorem for the concrete intuitionistic and classical
    propositional Hilbert systems.

    The proof follows the mathematical induction in Foundation while
    factoring its only special axiom case: every minimal Hilbert system
    proves the double negation of excluded middle.  No formula equality or
    semantic completeness is needed. *)

From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert PropositionalEntailmentMinimal.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition ph_hilbert_double_neg_intro_raw {Atom : Type}
    (H : ph_hilbert Atom) {p : pformula Atom}
    (d : ph_hilbert_proof H p) :
    ph_hilbert_proof H (pneg (pneg p)) :=
  generic_minimal_dni_elim_raw (ph_hilbert_generic_minimal H) p d.

(** [~(p \/ ~p)] implies both [~p] and [~~p], hence absurdity. *)
Definition ph_hilbert_double_neg_lem_raw {Atom : Type}
    (H : ph_hilbert Atom) (p : pformula Atom) :
    ph_hilbert_proof H (pneg (pneg (ph_axiom_lem p))).
Proof.
  set (HM := ph_hilbert_generic_minimal H).
  set (lem := ph_axiom_lem p).
  set (h := pneg lem).
  assert (hnp : ph_hilbert_proof H (PImp h (pneg p))).
  { exact (generic_minimal_contraposition_raw HM p lem
      (generic_minimal_or1 HM p (pneg p))). }
  assert (hnnp : ph_hilbert_proof H (PImp h (pneg (pneg p)))).
  { exact (generic_minimal_contraposition_raw HM (pneg p) lem
      (generic_minimal_or2 HM p (pneg p))). }
  exact (generic_minimal_under_apply_raw HM h (pneg p) PFalsum
    hnnp hnp).
Defined.

(** The source statement is proposition-valued.  Keeping this direction in
    [inhabited] form also respects Coq's proof-elimination discipline for the
    Prop-valued classical schema. *)
Lemma ph_glivenko_classical_to_int_double_neg :
  forall (Atom : Type) (p : pformula Atom),
    ph_hilbert_proof (ph_hilbert_cl Atom) p ->
    ph_hilbert_provable (ph_hilbert_int Atom) (pneg (pneg p)).
Proof.
  intros Atom p d. induction d.
  - destruct p0.
    + constructor. apply ph_hilbert_double_neg_intro_raw.
      exact (ph_hilbert_int_efq p).
    + constructor. apply ph_hilbert_double_neg_lem_raw.
  - destruct IHd1 as [di1]. destruct IHd2 as [di2]. constructor.
    exact (PHPModusPonens
      (PHPModusPonens
        (ph_hilbert_double_neg_imp_distribution
          (ph_hilbert_int Atom) p q) di1) di2).
  - constructor. apply ph_hilbert_double_neg_intro_raw. exact PHPVerum.
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPImplyS p q r).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPImplyK p q).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPAndElimL p q).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPAndElimR p q).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPAndIntro p q).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPOrIntroL p q).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPOrIntroR p q).
  - constructor. apply ph_hilbert_double_neg_intro_raw.
    exact (PHPOrElim p q r).
Qed.

Definition ph_glivenko_int_double_neg_to_classical_raw {Atom : Type}
    {p : pformula Atom}
    (d : ph_hilbert_proof (ph_hilbert_int Atom) (pneg (pneg p))) :
    ph_hilbert_proof (ph_hilbert_cl Atom) p :=
  PHPModusPonens (ph_hilbert_cl_dne p)
    (ph_hilbert_proof_of_schema_inclusion
      (@ph_hilbert_int_le_cl Atom) d).

Theorem ph_glivenko :
  forall (Atom : Type) (p : pformula Atom),
    ph_hilbert_provable (ph_hilbert_int Atom) (pneg (pneg p)) <->
    ph_hilbert_provable (ph_hilbert_cl Atom) p.
Proof.
  intros Atom p; split; intros [d].
  - constructor. exact (ph_glivenko_int_double_neg_to_classical_raw d).
  - exact (ph_glivenko_classical_to_int_double_neg d).
Qed.

Theorem ph_neg_provable_int_iff_cl :
  forall (Atom : Type) (p : pformula Atom),
    ph_hilbert_provable (ph_hilbert_int Atom) (pneg p) <->
    ph_hilbert_provable (ph_hilbert_cl Atom) (pneg p).
Proof.
  intros Atom p; split; intros [d].
  - constructor. exact (ph_hilbert_proof_of_schema_inclusion
      (@ph_hilbert_int_le_cl Atom) d).
  - destruct (ph_glivenko_classical_to_int_double_neg d) as [dnnn].
    constructor. apply (generic_minimal_mdp_raw
      (ph_hilbert_generic_minimal (ph_hilbert_int Atom))
      (pneg (pneg (pneg p))) (pneg p)).
    + exact (generic_minimal_triple_neg_elim_raw
        (ph_hilbert_generic_minimal (ph_hilbert_int Atom)) p).
    + exact dnnn.
Qed.

(** Superintuitionistic logics and Post completeness of classical logic.

    This ports Foundation's [Propositional/Logic/Superintuitionistic.lean]
    and [Propositional/Logic/PostComplete.lean].  Classical logic is shown in
    a strengthened maximal-consistency form: every consistent propositional
    logic containing Cl is contained in Cl.  The explicit assumption that it
    also extends Int is therefore unnecessary.

    As in the Boolean completeness development, one executable atom codec
    replaces the source's separate encodability and equality assumptions. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  PropositionalFormula PropositionalLogic PropositionalHilbert
  PropositionalBoolean PropositionalBooleanZeroSubst
  PropositionalBooleanHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pformula_logic_consistent {Atom : Type}
    (L : pformula_logic Atom) : Prop :=
  ~ pformula_logic_theorems L PFalsum.

Definition pformula_logic_strict_subset {Atom : Type}
    (L K : pformula_logic Atom) : Prop :=
  pformula_logic_subset L K /\
  exists p, pformula_logic_theorems K p /\
    ~ pformula_logic_theorems L p.

Definition ph_superintuitionistic_logic (Atom : Type) : Type :=
  pformula_logic_extension (ph_logic_int Atom).

Lemma ph_superintuitionistic_contains_int :
  forall (Atom : Type) (L : ph_superintuitionistic_logic Atom),
    pformula_logic_subset (ph_logic_int Atom)
      (pformula_logic_extension_logic L).
Proof.
  intros Atom L p Hp.
  exact (pformula_logic_extension_includes L p Hp).
Qed.

Lemma ph_superintuitionistic_trivial_of_bottom :
  forall (Atom : Type) (L : ph_superintuitionistic_logic Atom),
    pformula_logic_theorems
      (pformula_logic_extension_logic L) PFalsum ->
    pformula_logic_is_trivial (pformula_logic_extension_logic L).
Proof.
  intros Atom L Hbottom p.
  eapply pformula_logic_mdp; [| exact Hbottom].
  apply pformula_logic_extension_includes.
  change (ph_hilbert_provable (ph_hilbert_int Atom) (ph_axiom_efq p)).
  constructor. exact (ph_hilbert_int_efq p).
Qed.

Theorem ph_superintuitionistic_strictly_below_trivial :
  forall (Atom : Type) (L : ph_superintuitionistic_logic Atom),
    pformula_logic_consistent (pformula_logic_extension_logic L) ->
    pformula_logic_strict_subset
      (pformula_logic_extension_logic L) pformula_logic_trivial.
Proof.
  intros Atom L Hconsistent. split.
  - intros p _. exact I.
  - exists PFalsum. split; [exact I | exact Hconsistent].
Qed.

(** A consistent logic cannot properly extend Cl.  The proof substitutes a
    countervaluation's truth constants into a hypothetical new theorem.  The
    substituted formula and its classically provable negation then make the
    extension inconsistent. *)
Theorem ph_logic_cl_maximal_consistent :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (L : pformula_logic Atom),
    pformula_logic_subset (ph_logic_cl Atom) L ->
    pformula_logic_consistent L ->
    pformula_logic_subset L (ph_logic_cl Atom).
Proof.
  intros Atom K L Hcontains Hconsistent p Hp.
  change (ph_hilbert_provable (ph_hilbert_cl Atom) p).
  apply (@ph_cl_provable_complete Atom K p).
  apply NNPP. intro Hnot.
  destruct (pboolean_exists_neg_zero_subst_of_not_tautology Hnot)
    as [sigma Hneg].
  set (p' := pformula_substitute (pzero_substitution_apply sigma) p).
  assert (HnegL : pformula_logic_theorems L (pneg p')).
  { apply Hcontains. change (ph_hilbert_provable
      (ph_hilbert_cl Atom) (pneg p')).
    apply (@ph_cl_provable_complete Atom K (pneg p')).
    exact Hneg. }
  assert (HpL : pformula_logic_theorems L p').
  { unfold p'. eapply pformula_logic_substitute. exact Hp. }
  apply Hconsistent.
  exact (pformula_logic_mdp L p' PFalsum HnegL HpL).
Qed.

Corollary ph_logic_cl_post_complete :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (L : pformula_logic Atom),
    pformula_logic_consistent L ->
    ~ pformula_logic_strict_subset (ph_logic_cl Atom) L.
Proof.
  intros Atom K L Hconsistent [Hcontains [p [Hp Hnot]]].
  apply Hnot.
  exact (@ph_logic_cl_maximal_consistent Atom K L
    Hcontains Hconsistent p Hp).
Qed.

Corollary ph_superintuitionistic_cl_post_complete :
  forall (Atom : Type) (K : pformula_atom_codec Atom)
      (L : ph_superintuitionistic_logic Atom),
    pformula_logic_consistent (pformula_logic_extension_logic L) ->
    ~ pformula_logic_strict_subset
        (ph_logic_cl Atom) (pformula_logic_extension_logic L).
Proof.
  intros Atom K L Hconsistent.
  exact (@ph_logic_cl_post_complete Atom K
    (pformula_logic_extension_logic L) Hconsistent).
Qed.

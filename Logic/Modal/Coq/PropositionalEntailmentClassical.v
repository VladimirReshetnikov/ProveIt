(** Generic derived rules for classical propositional entailment.

    This module ports the system-independent core of
    [Propositional/Entailment/Cl/Basic.lean].  Classical entailment is exposed
    through the existing minimal-plus-DNE capability; ex falso and the
    intuitionistic interface are consequences rather than extra assumptions.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal
  PropositionalEntailmentInt.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Double negation and inverse contraposition *)

Definition generic_classical_double_neg_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p : F) :
    generic_proof E s
      (generic_formula_iff C p (generic_neg C (generic_neg C p))) :=
  generic_minimal_iff_intro_raw (generic_minimal_of_classical H) _ _
    (generic_minimal_dni_raw (generic_minimal_of_classical H) p)
    (generic_classical_dne H p).

Arguments generic_classical_double_neg_iff_raw {S F E C s} _ _.

Definition generic_classical_or_of_double_neg_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F)
    (d : generic_proof E s
      (generic_or C (generic_neg C (generic_neg C p))
        (generic_neg C (generic_neg C q)))) :
    generic_proof E s (generic_or C p q) :=
  generic_minimal_or_map_raw (generic_minimal_of_classical H)
    (generic_neg C (generic_neg C p)) p
    (generic_neg C (generic_neg C q)) q d
    (generic_classical_dne H p) (generic_classical_dne H q).

Arguments generic_classical_or_of_double_neg_or_raw {S F E C s}
  _ _ _ _.

(** This first inverse form is the source theorem
    [(~p -> q) -> (~q -> p)]. *)
Definition generic_classical_neg_imp_converse_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F)
    (d : generic_proof E s
      (generic_imp C (generic_neg C p) q)) :
    generic_proof E s
      (generic_imp C (generic_neg C q) p) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_imp_trans_raw Hm (generic_neg C q)
    (generic_neg C (generic_neg C p)) p
    (generic_minimal_contraposition_raw Hm (generic_neg C p) q d)
    (generic_classical_dne H p).

Arguments generic_classical_neg_imp_converse_raw {S F E C s}
  _ _ _ _.

Definition generic_classical_neg_imp_converse_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_imp C (generic_neg C p) q)
        (generic_imp C (generic_neg C q) p)) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_imp_trans_raw Hm
    (generic_imp C (generic_neg C p) q)
    (generic_imp C (generic_neg C q)
      (generic_neg C (generic_neg C p)))
    (generic_imp C (generic_neg C q) p)
    (generic_minimal_contraposition_axiom_raw Hm (generic_neg C p) q)
    (generic_minimal_imp_lift_right_raw Hm
      (generic_neg C (generic_neg C p)) p (generic_neg C q)
      (generic_classical_dne H p)).

Arguments generic_classical_neg_imp_converse_axiom_raw {S F E C s}
  _ _ _.

(** The usual elimination-of-contraposition form
    [(~p -> ~q) -> (q -> p)]. *)
Definition generic_classical_contraposition_inverse_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F)
    (d : generic_proof E s
      (generic_imp C (generic_neg C p) (generic_neg C q))) :
    generic_proof E s (generic_imp C q p) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_imp_trans_raw Hm q
    (generic_neg C (generic_neg C q)) p
    (generic_minimal_dni_raw Hm q)
    (generic_classical_neg_imp_converse_raw H p (generic_neg C q) d).

Arguments generic_classical_contraposition_inverse_raw {S F E C s}
  _ _ _ _.

(** Moving a negation across either side of a biconditional. *)
Definition generic_classical_neg_iff_move_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F)
    (d : generic_proof E s
      (generic_formula_iff C p (generic_neg C q))) :
    generic_proof E s
      (generic_formula_iff C (generic_neg C p) q) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_iff_intro_raw Hm _ _
    (generic_classical_neg_imp_converse_raw H q p
      (generic_minimal_iff_elim_right_raw Hm p (generic_neg C q) d))
    (generic_minimal_negated_imp_swap_raw Hm p q
      (generic_minimal_iff_elim_left_raw Hm p (generic_neg C q) d)).

Arguments generic_classical_neg_iff_move_right_raw {S F E C s}
  _ _ _ _.

Definition generic_classical_neg_iff_move_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F)
    (d : generic_proof E s
      (generic_formula_iff C (generic_neg C p) q)) :
    generic_proof E s
      (generic_formula_iff C p (generic_neg C q)) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_iff_symm_raw Hm (generic_neg C q) p
    (generic_classical_neg_iff_move_right_raw H q p
      (generic_minimal_iff_symm_raw Hm (generic_neg C p) q d)).

Arguments generic_classical_neg_iff_move_left_raw {S F E C s}
  _ _ _ _.

Definition generic_classical_expanded_double_neg_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p : F) :
    generic_proof E s
      (generic_formula_iff C p
        (generic_imp C (generic_imp C p (generic_bottom C))
          (generic_bottom C))) :=
  generic_minimal_iff_trans_raw (generic_minimal_of_classical H) p
    (generic_neg C (generic_neg C p))
    (generic_imp C (generic_imp C p (generic_bottom C))
      (generic_bottom C))
    (generic_classical_double_neg_iff_raw H p)
    (generic_minimal_double_neg_expansion_iff_raw
      (generic_minimal_of_classical H) p).

Arguments generic_classical_expanded_double_neg_iff_raw {S F E C s}
  _ _.

(** * Classical entailment contains intuitionistic entailment *)

Definition generic_classical_efq_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p : F) :
    generic_proof E s (generic_axiom_efq C p) :=
  let Hm := generic_minimal_of_classical H in
  generic_classical_contraposition_inverse_raw H p (generic_bottom C)
    (generic_minimal_dhyp_raw Hm (generic_neg C (generic_bottom C))
      (generic_neg C p) (generic_minimal_neg_bottom_raw Hm)).

Arguments generic_classical_efq_raw {S F E C s} _ _.

Definition generic_has_axiom_efq_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_has_axiom_efq E C s :=
  {| generic_efq_raw := generic_classical_efq_raw H |}.

Definition generic_intuitionistic_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_intuitionistic_entailment E C s :=
  {| generic_intuitionistic_minimal := generic_minimal_of_classical H;
     generic_intuitionistic_has_efq := generic_has_axiom_efq_of_classical H |}.

(** * Classical De Morgan and implication laws *)

Definition generic_classical_neg_and_to_or_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_neg C (generic_and C p q))
        (generic_or C (generic_neg C p) (generic_neg C q))) :=
  let Hm := generic_minimal_of_classical H in
  generic_classical_neg_imp_converse_raw H
    (generic_or C (generic_neg C p) (generic_neg C q))
    (generic_and C p q)
    (generic_minimal_imp_trans_raw Hm
      (generic_neg C
        (generic_or C (generic_neg C p) (generic_neg C q)))
      (generic_and C
        (generic_neg C (generic_neg C p))
        (generic_neg C (generic_neg C q)))
      (generic_and C p q)
      (generic_minimal_neg_or_to_and_neg_raw Hm
        (generic_neg C p) (generic_neg C q))
      (generic_minimal_and_map_axiom_raw Hm
        (generic_neg C (generic_neg C p)) p
        (generic_neg C (generic_neg C q)) q
        (generic_classical_dne H p) (generic_classical_dne H q))).

Arguments generic_classical_neg_and_to_or_neg_raw {S F E C s}
  _ _ _.

Definition generic_classical_neg_and_iff_or_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_formula_iff C
        (generic_neg C (generic_and C p q))
        (generic_or C (generic_neg C p) (generic_neg C q))) :=
  generic_minimal_iff_intro_raw (generic_minimal_of_classical H) _ _
    (generic_classical_neg_and_to_or_neg_raw H p q)
    (generic_minimal_or_neg_to_neg_and_raw
      (generic_minimal_of_classical H) p q).

Arguments generic_classical_neg_and_iff_or_neg_raw {S F E C s}
  _ _ _.

Definition generic_classical_imp_to_neg_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_imp C p q)) :
    generic_proof E s (generic_or C (generic_neg C p) q) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_or_map_raw Hm
    (generic_neg C p) (generic_neg C p)
    (generic_neg C (generic_neg C q)) q
    (generic_minimal_mdp_raw Hm
      (generic_neg C (generic_and C p (generic_neg C q)))
      (generic_or C (generic_neg C p)
        (generic_neg C (generic_neg C q)))
      (generic_classical_neg_and_to_or_neg_raw H p (generic_neg C q))
      (generic_minimal_imp_to_neg_and_raw Hm p q d))
    (generic_minimal_identity_raw Hm (generic_neg C p))
    (generic_classical_dne H q).

Arguments generic_classical_imp_to_neg_or_raw {S F E C s}
  _ _ _ _.

Definition generic_classical_imp_to_neg_or_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p q)
        (generic_or C (generic_neg C p) q)) :=
  generic_minimal_imp_trans_raw (generic_minimal_of_classical H)
    (generic_imp C p q)
    (generic_neg C (generic_and C p (generic_neg C q)))
    (generic_or C (generic_neg C p) q)
    (generic_minimal_imp_to_neg_and_axiom_raw
      (generic_minimal_of_classical H) p q)
    (generic_minimal_imp_trans_raw (generic_minimal_of_classical H)
      (generic_neg C (generic_and C p (generic_neg C q)))
      (generic_or C (generic_neg C p)
        (generic_neg C (generic_neg C q)))
      (generic_or C (generic_neg C p) q)
      (generic_classical_neg_and_to_or_neg_raw H p (generic_neg C q))
      (generic_minimal_or_map_axiom_raw (generic_minimal_of_classical H)
        (generic_neg C p) (generic_neg C p)
        (generic_neg C (generic_neg C q)) q
        (generic_minimal_identity_raw (generic_minimal_of_classical H)
          (generic_neg C p))
        (generic_classical_dne H q))).

Arguments generic_classical_imp_to_neg_or_axiom_raw {S F E C s}
  _ _ _.

Definition generic_classical_imp_iff_neg_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_formula_iff C (generic_imp C p q)
        (generic_or C (generic_neg C p) q)) :=
  generic_minimal_iff_intro_raw (generic_minimal_of_classical H) _ _
    (generic_classical_imp_to_neg_or_axiom_raw H p q)
    (generic_intuitionistic_neg_or_to_imp_raw
      (generic_intuitionistic_of_classical H) p q).

Arguments generic_classical_imp_iff_neg_or_raw {S F E C s}
  _ _ _.

(** Excluded middle follows from the implication/disjunction correspondence
    by applying it to identity and swapping the two disjuncts. *)
Definition generic_classical_lem_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p : F) :
    generic_proof E s (generic_axiom_lem C p) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_mdp_raw Hm
    (generic_or C (generic_neg C p) p)
    (generic_or C p (generic_neg C p))
    (generic_minimal_or_elim_raw Hm (generic_neg C p) p
      (generic_or C p (generic_neg C p))
      (generic_minimal_or2 Hm p (generic_neg C p))
      (generic_minimal_or1 Hm p (generic_neg C p)))
    (generic_classical_imp_to_neg_or_raw H p p
      (generic_minimal_identity_raw Hm p)).

Arguments generic_classical_lem_raw {S F E C s} _ _.

Definition generic_has_axiom_lem_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_has_axiom_lem E C s :=
  {| generic_lem_raw := generic_classical_lem_raw H |}.

(** * Standard classical axiom packages *)

Definition generic_classical_elim_contra_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s (generic_axiom_elim_contra C p q) :=
  let Hm := generic_minimal_of_classical H in
  generic_minimal_imp_trans_raw Hm
    (generic_imp C (generic_neg C q) (generic_neg C p))
    (generic_imp C
      (generic_neg C (generic_neg C p))
      (generic_neg C (generic_neg C q)))
    (generic_imp C p q)
    (generic_minimal_contraposition_axiom_raw Hm
      (generic_neg C q) (generic_neg C p))
    (generic_minimal_imp_trans_raw Hm
      (generic_imp C
        (generic_neg C (generic_neg C p))
        (generic_neg C (generic_neg C q)))
      (generic_imp C p (generic_neg C (generic_neg C q)))
      (generic_imp C p q)
      (generic_minimal_imp_lift_left_raw Hm
        (generic_neg C (generic_neg C p)) p
        (generic_neg C (generic_neg C q))
        (generic_minimal_dni_raw Hm p))
      (generic_minimal_imp_lift_right_raw Hm
        (generic_neg C (generic_neg C q)) q p
        (generic_classical_dne H q))).

Arguments generic_classical_elim_contra_axiom_raw {S F E C s}
  _ _ _.

Definition generic_classical_contraposition_inverse_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C
        (generic_imp C (generic_neg C p) (generic_neg C q))
        (generic_imp C q p)) :=
  generic_classical_elim_contra_axiom_raw H q p.

Arguments generic_classical_contraposition_inverse_axiom_raw
  {S F E C s} _ _ _.

Definition generic_has_axiom_elim_contra_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_has_axiom_elim_contra E C s :=
  {| generic_elim_contra_raw :=
       generic_classical_elim_contra_axiom_raw H |}.

Definition generic_classical_dummett_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s (generic_axiom_dummett C p q) :=
  let Hm := generic_minimal_of_classical H in
  let Hi := generic_intuitionistic_of_classical H in
  generic_minimal_mdp_raw Hm
    (generic_or C p (generic_neg C p))
    (generic_axiom_dummett C p q)
    (generic_minimal_or_elim_raw Hm p (generic_neg C p)
      (generic_axiom_dummett C p q)
      (generic_minimal_imp_trans_raw Hm p (generic_imp C q p)
        (generic_axiom_dummett C p q)
        (generic_minimal_K Hm p q)
        (generic_minimal_or2 Hm
          (generic_imp C p q) (generic_imp C q p)))
      (generic_minimal_imp_trans_raw Hm (generic_neg C p)
        (generic_imp C p q) (generic_axiom_dummett C p q)
        (generic_intuitionistic_neg_imp_explosion_raw Hi p q)
        (generic_minimal_or1 Hm
          (generic_imp C p q) (generic_imp C q p))))
    (generic_classical_lem_raw H p).

Arguments generic_classical_dummett_raw {S F E C s} _ _ _.

Definition generic_has_axiom_dummett_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_has_axiom_dummett E C s :=
  {| generic_dummett_raw := generic_classical_dummett_raw H |}.

Definition generic_classical_peirce_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (p q : F) :
    generic_proof E s (generic_axiom_peirce C p q).
Proof.
  set (Hm := generic_minimal_of_classical H).
  set (Hi := generic_intuitionistic_of_classical H).
  set (np := generic_neg C p).
  set (f := generic_imp C p q).
  set (g := generic_imp C f p).
  set (r := generic_imp C g p).
  assert (dg : generic_list_derivation E s C [g; np] g).
  { exact (GLD_assumption (GRLM_here [np])). }
  assert (dnp : generic_list_derivation E s C [g; np] np).
  { exact (GLD_assumption (GRLM_there g (GRLM_here []))). }
  pose (df := GLD_mdp
    (GLD_theorem (generic_intuitionistic_neg_imp_explosion_raw Hi p q)) dnp).
  pose (dp := GLD_mdp dg df).
  pose (dgp := generic_list_deduction (generic_minimal_mdp Hm)
    (generic_minimal_K Hm) (generic_minimal_S Hm) dp).
  pose (dnpr := generic_empty_derivation_raw (generic_minimal_mdp Hm)
    (generic_list_deduction (generic_minimal_mdp Hm)
      (generic_minimal_K Hm) (generic_minimal_S Hm) dgp)).
  exact (generic_minimal_mdp_raw Hm (generic_or C p np) r
    (generic_minimal_or_elim_raw Hm p np r
      (generic_minimal_K Hm p g) dnpr)
    (generic_classical_lem_raw H p)).
Defined.

Arguments generic_classical_peirce_raw {S F E C s} _ _ _.

Definition generic_has_axiom_peirce_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_has_axiom_peirce E C s :=
  {| generic_peirce_raw := generic_classical_peirce_raw H |}.

(** * Finite classical De Morgan law *)

(** Foundation states only this direction.  Positional membership removes
    its ambient formula-equality and finite-set assumptions. *)
Definition generic_classical_neg_disj2_map_to_conj2_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) (gamma : list F) :
    generic_proof E s
      (generic_imp C
        (generic_neg C
          (generic_list_disj2 C (map (generic_neg C) gamma)))
        (generic_list_conj2 C gamma)).
Proof.
  set (Hm := generic_minimal_of_classical H).
  set (Hi := generic_intuitionistic_of_classical H).
  set (a := generic_neg C
    (generic_list_disj2 C (map (generic_neg C) gamma))).
  apply (generic_minimal_list_conj2_right_intro_raw Hm a gamma).
  intros p hp.
  exact (generic_minimal_imp_trans_raw Hm a
    (generic_neg C (generic_neg C p)) p
    (generic_minimal_imp_trans_raw Hm a
      (generic_list_conj_map C (generic_neg C)
        (map (generic_neg C) gamma))
      (generic_neg C (generic_neg C p))
      (generic_intuitionistic_neg_disj2_to_conj2_neg_raw Hi
        (map (generic_neg C) gamma))
      (generic_minimal_list_conj_map_elim_raw Hm (generic_neg C)
        (generic_raw_list_member_map (generic_neg C) hp)))
    (generic_classical_dne H p)).
Defined.

Arguments generic_classical_neg_disj2_map_to_conj2_raw
  {S F E C s} _ _.

(** * Transport across a connective homomorphism and proof equivalence *)

(** A connective homomorphism preserves every formula schema used by the
    classical-entailment dictionary.  Keeping these equations separate makes
    the transport below reusable for other proof interfaces. *)
Lemma generic_connective_hom_axiom_neg_equiv :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p : FT),
    generic_connective_hom_apply f (generic_axiom_neg_equiv CT p) =
    generic_axiom_neg_equiv CS (generic_connective_hom_apply f p).
Proof.
  intros FT FS CT CS f p. unfold generic_axiom_neg_equiv.
  rewrite (generic_connective_hom_iff f),
    (generic_connective_hom_neg f),
    (generic_connective_hom_imp f),
    (generic_connective_hom_bottom f).
  reflexivity.
Qed.

Lemma generic_connective_hom_axiom_K :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q : FT),
    generic_connective_hom_apply f (generic_axiom_K CT p q) =
    generic_axiom_K CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros FT FS CT CS f p q. unfold generic_axiom_K.
  now rewrite !generic_connective_hom_imp.
Qed.

Lemma generic_connective_hom_axiom_S :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q r : FT),
    generic_connective_hom_apply f (generic_axiom_S CT p q r) =
    generic_axiom_S CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q)
      (generic_connective_hom_apply f r).
Proof.
  intros FT FS CT CS f p q r. unfold generic_axiom_S.
  now rewrite !generic_connective_hom_imp.
Qed.

Lemma generic_connective_hom_axiom_and1 :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q : FT),
    generic_connective_hom_apply f (generic_axiom_and1 CT p q) =
    generic_axiom_and1 CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros FT FS CT CS f p q. unfold generic_axiom_and1.
  now rewrite generic_connective_hom_imp, generic_connective_hom_and.
Qed.

Lemma generic_connective_hom_axiom_and2 :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q : FT),
    generic_connective_hom_apply f (generic_axiom_and2 CT p q) =
    generic_axiom_and2 CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros FT FS CT CS f p q. unfold generic_axiom_and2.
  now rewrite generic_connective_hom_imp, generic_connective_hom_and.
Qed.

Lemma generic_connective_hom_axiom_and3 :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q : FT),
    generic_connective_hom_apply f (generic_axiom_and3 CT p q) =
    generic_axiom_and3 CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros FT FS CT CS f p q. unfold generic_axiom_and3.
  now rewrite !generic_connective_hom_imp, generic_connective_hom_and.
Qed.

Lemma generic_connective_hom_axiom_or1 :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q : FT),
    generic_connective_hom_apply f (generic_axiom_or1 CT p q) =
    generic_axiom_or1 CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros FT FS CT CS f p q. unfold generic_axiom_or1.
  now rewrite generic_connective_hom_imp, generic_connective_hom_or.
Qed.

Lemma generic_connective_hom_axiom_or2 :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q : FT),
    generic_connective_hom_apply f (generic_axiom_or2 CT p q) =
    generic_axiom_or2 CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q).
Proof.
  intros FT FS CT CS f p q. unfold generic_axiom_or2.
  now rewrite generic_connective_hom_imp, generic_connective_hom_or.
Qed.

Lemma generic_connective_hom_axiom_or3 :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p q r : FT),
    generic_connective_hom_apply f (generic_axiom_or3 CT p q r) =
    generic_axiom_or3 CS
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q)
      (generic_connective_hom_apply f r).
Proof.
  intros FT FS CT CS f p q r. unfold generic_axiom_or3.
  now rewrite !generic_connective_hom_imp, generic_connective_hom_or.
Qed.

Lemma generic_connective_hom_axiom_dne :
  forall (FT FS : Type)
         (CT : generic_connectives FT) (CS : generic_connectives FS)
         (f : generic_connective_hom CT CS) (p : FT),
    generic_connective_hom_apply f (generic_axiom_dne CT p) =
    generic_axiom_dne CS (generic_connective_hom_apply f p).
Proof.
  intros FT FS CT CS f p. unfold generic_axiom_dne.
  now rewrite generic_connective_hom_imp, !generic_connective_hom_neg.
Qed.

(** Transport a source proof of a homomorphic image back to the target. *)
Definition generic_proof_equiv_transport_raw
    {SS ST FS FT : Type}
    {ES : generic_entailment SS FS} {ET : generic_entailment ST FT}
    {CS : generic_connectives FS} {CT : generic_connectives FT}
    {ss : SS} {st : ST}
    (f : generic_connective_hom CT CS)
    (e : forall p : FT,
      generic_type_equiv
        (generic_proof ES ss (generic_connective_hom_apply f p))
        (generic_proof ET st p))
    (p : FT) (q : FS)
    (Heq : generic_connective_hom_apply f p = q)
    (d : generic_proof ES ss q) :
    generic_proof ET st p :=
  generic_equiv_to (e p)
    (@generic_proof_cast SS FS ES ss q
      (generic_connective_hom_apply f p) d (eq_sym Heq)).

Arguments generic_proof_equiv_transport_raw
  {SS ST FS FT ES ET CS CT ss st} _ _ _ _ _ _.

(** Foundation's [Cl.ofEquiv], generalized to unrelated source and target
    formula types, system types, and proof representations.  The equivalence
    laws themselves are retained, although construction consumes only its two
    maps. *)
Definition generic_classical_of_proof_equiv
    {SS ST FS FT : Type}
    {ES : generic_entailment SS FS} {ET : generic_entailment ST FT}
    {CS : generic_connectives FS} {CT : generic_connectives FT}
    {ss : SS} {st : ST}
    (H : generic_classical_entailment ES CS ss)
    (f : generic_connective_hom CT CS)
    (e : forall p : FT,
      generic_type_equiv
        (generic_proof ES ss (generic_connective_hom_apply f p))
        (generic_proof ET st p)) :
    generic_classical_entailment ET CT st.
Proof.
  constructor.
  - refine {| generic_modus_ponens_raw := _ |}.
    intros p q dpq dp.
    apply (generic_equiv_to (e q)).
    apply (generic_modus_ponens_raw (generic_classical_mdp H)
      (generic_connective_hom_apply f p)
      (generic_connective_hom_apply f q)).
    + exact (@generic_proof_cast SS FS ES ss
        (generic_connective_hom_apply f (generic_imp CT p q))
        (generic_imp CS
          (generic_connective_hom_apply f p)
          (generic_connective_hom_apply f q))
        (generic_equiv_from (e (generic_imp CT p q)) dpq)
        (generic_connective_hom_imp f p q)).
    + exact (generic_equiv_from (e p) dp).
  - intro p.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_neg_equiv CT p)
      (generic_axiom_neg_equiv CS (generic_connective_hom_apply f p))
      (generic_connective_hom_axiom_neg_equiv f p)
      (generic_classical_neg_equiv H (generic_connective_hom_apply f p))).
  - exact (generic_proof_equiv_transport_raw f e
      (generic_top CT) (generic_top CS)
      (generic_connective_hom_top f) (generic_classical_verum H)).
  - intros p q.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_K CT p q)
      (generic_axiom_K CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))
      (generic_connective_hom_axiom_K f p q)
      (generic_classical_K H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))).
  - intros p q r.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_S CT p q r)
      (generic_axiom_S CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q)
        (generic_connective_hom_apply f r))
      (generic_connective_hom_axiom_S f p q r)
      (generic_classical_S H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q)
        (generic_connective_hom_apply f r))).
  - intros p q.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_and1 CT p q)
      (generic_axiom_and1 CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))
      (generic_connective_hom_axiom_and1 f p q)
      (generic_classical_and1 H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))).
  - intros p q.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_and2 CT p q)
      (generic_axiom_and2 CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))
      (generic_connective_hom_axiom_and2 f p q)
      (generic_classical_and2 H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))).
  - intros p q.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_and3 CT p q)
      (generic_axiom_and3 CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))
      (generic_connective_hom_axiom_and3 f p q)
      (generic_classical_and3 H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))).
  - intros p q.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_or1 CT p q)
      (generic_axiom_or1 CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))
      (generic_connective_hom_axiom_or1 f p q)
      (generic_classical_or1 H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))).
  - intros p q.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_or2 CT p q)
      (generic_axiom_or2 CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))
      (generic_connective_hom_axiom_or2 f p q)
      (generic_classical_or2 H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q))).
  - intros p q r.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_or3 CT p q r)
      (generic_axiom_or3 CS
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q)
        (generic_connective_hom_apply f r))
      (generic_connective_hom_axiom_or3 f p q r)
      (generic_classical_or3 H
        (generic_connective_hom_apply f p)
        (generic_connective_hom_apply f q)
        (generic_connective_hom_apply f r))).
  - intro p.
    exact (generic_proof_equiv_transport_raw f e
      (generic_axiom_dne CT p)
      (generic_axiom_dne CS (generic_connective_hom_apply f p))
      (generic_connective_hom_axiom_dne f p)
      (generic_classical_dne H (generic_connective_hom_apply f p))).
Defined.

Arguments generic_classical_of_proof_equiv
  {SS ST FS FT ES ET CS CT ss st} _ _ _.

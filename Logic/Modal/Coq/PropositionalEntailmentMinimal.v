(** Generic derived rules for minimal propositional entailment.

    This module ports the foundational, system-independent part of
    [Propositional/Entailment/Minimal/Basic.lean].  Foundation presents each
    primitive rule as a typeclass.  Coq packages the same eleven raw-proof
    operations in one explicit capability record and derives the common
    proof algebra from it.

    All constructions stay in [Type]: they neither choose witnesses from
    inhabited theoremhood nor require decidable formula equality.  The
    finite-context arguments use positional membership and the constructive
    deduction machinery from [PropositionalEntailmentAxioms].
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Minimal capability *)

Record generic_minimal_entailment {S F : Type}
    (E : generic_entailment S F)
    (C : generic_connectives F) (s : S) : Type := {
  generic_minimal_mdp : generic_modus_ponens E C s;
  generic_minimal_neg_equiv :
    forall p, generic_proof E s (generic_axiom_neg_equiv C p);
  generic_minimal_verum : generic_proof E s (generic_top C);
  generic_minimal_K :
    forall p q, generic_proof E s (generic_axiom_K C p q);
  generic_minimal_S :
    forall p q r, generic_proof E s (generic_axiom_S C p q r);
  generic_minimal_and1 :
    forall p q, generic_proof E s (generic_axiom_and1 C p q);
  generic_minimal_and2 :
    forall p q, generic_proof E s (generic_axiom_and2 C p q);
  generic_minimal_and3 :
    forall p q, generic_proof E s (generic_axiom_and3 C p q);
  generic_minimal_or1 :
    forall p q, generic_proof E s (generic_axiom_or1 C p q);
  generic_minimal_or2 :
    forall p q, generic_proof E s (generic_axiom_or2 C p q);
  generic_minimal_or3 :
    forall p q r, generic_proof E s (generic_axiom_or3 C p q r)
}.

Arguments generic_minimal_mdp {S F E C s} _.
Arguments generic_minimal_neg_equiv {S F E C s} _ _.
Arguments generic_minimal_verum {S F E C s} _.
Arguments generic_minimal_K {S F E C s} _ _ _.
Arguments generic_minimal_S {S F E C s} _ _ _ _.
Arguments generic_minimal_and1 {S F E C s} _ _ _.
Arguments generic_minimal_and2 {S F E C s} _ _ _.
Arguments generic_minimal_and3 {S F E C s} _ _ _.
Arguments generic_minimal_or1 {S F E C s} _ _ _.
Arguments generic_minimal_or2 {S F E C s} _ _ _.
Arguments generic_minimal_or3 {S F E C s} _ _ _ _.

(** Classical entailment is minimal entailment plus double-negation
    elimination. *)
Definition generic_minimal_of_classical {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_classical_entailment E C s) :
    generic_minimal_entailment E C s.
Proof.
  constructor.
  - exact (generic_classical_mdp H).
  - exact (generic_classical_neg_equiv H).
  - exact (generic_classical_verum H).
  - exact (generic_classical_K H).
  - exact (generic_classical_S H).
  - exact (generic_classical_and1 H).
  - exact (generic_classical_and2 H).
  - exact (generic_classical_and3 H).
  - exact (generic_classical_or1 H).
  - exact (generic_classical_or2 H).
  - exact (generic_classical_or3 H).
Defined.

(** * Primitive rules and theoremhood views *)

Definition generic_minimal_mdp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (dpq : generic_proof E s (generic_imp C p q))
    (dp : generic_proof E s p) : generic_proof E s q :=
  generic_modus_ponens_raw (generic_minimal_mdp H) p q dpq dp.

Arguments generic_minimal_mdp_raw {S F E C s} _ _ _ _ _.

Lemma generic_minimal_mdp_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p q,
      generic_provable E s (generic_imp C p q) ->
      generic_provable E s p -> generic_provable E s q.
Proof.
  intros S F E C s H p q [dpq] [dp]. constructor.
  exact (generic_minimal_mdp_raw H p q dpq dp).
Qed.

Lemma generic_minimal_axioms_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    generic_provable E s (generic_top C) /\
    (forall p, generic_provable E s (generic_axiom_neg_equiv C p)) /\
    (forall p q, generic_provable E s (generic_axiom_K C p q)) /\
    (forall p q r, generic_provable E s (generic_axiom_S C p q r)) /\
    (forall p q, generic_provable E s (generic_axiom_and1 C p q)) /\
    (forall p q, generic_provable E s (generic_axiom_and2 C p q)) /\
    (forall p q, generic_provable E s (generic_axiom_and3 C p q)) /\
    (forall p q, generic_provable E s (generic_axiom_or1 C p q)) /\
    (forall p q, generic_provable E s (generic_axiom_or2 C p q)) /\
    (forall p q r, generic_provable E s (generic_axiom_or3 C p q r)).
Proof.
  intros S F E C s H.
  repeat match goal with |- _ /\ _ => split end; intros; constructor.
  - exact (generic_minimal_verum H).
  - exact (generic_minimal_neg_equiv H p).
  - exact (generic_minimal_K H p q).
  - exact (generic_minimal_S H p q r).
  - exact (generic_minimal_and1 H p q).
  - exact (generic_minimal_and2 H p q).
  - exact (generic_minimal_and3 H p q).
  - exact (generic_minimal_or1 H p q).
  - exact (generic_minimal_or2 H p q).
  - exact (generic_minimal_or3 H p q r).
Qed.

(** * Implication algebra *)

Definition generic_minimal_identity_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s (generic_imp C p p) :=
  generic_imp_identity_raw (generic_minimal_mdp H)
    (generic_minimal_K H) (generic_minimal_S H) p.

Arguments generic_minimal_identity_raw {S F E C s} _ _.

Definition generic_minimal_dhyp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s p) :
    generic_proof E s (generic_imp C q p) :=
  @generic_dhyp_raw S F E C s
    (generic_minimal_mdp H) (generic_minimal_K H) p q d.

Arguments generic_minimal_dhyp_raw {S F E C s} _ _ _ _.

Definition generic_minimal_under_apply_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (a b c : F)
    (df : generic_proof E s (generic_imp C a (generic_imp C b c)))
    (dx : generic_proof E s (generic_imp C a b)) :
    generic_proof E s (generic_imp C a c) :=
  @generic_under_apply_raw S F E C s (generic_minimal_mdp H)
    (generic_minimal_S H) a b c df dx.

Arguments generic_minimal_under_apply_raw {S F E C s} _ _ _ _ _ _.

Definition generic_minimal_imp_trans_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (a b c : F)
    (dab : generic_proof E s (generic_imp C a b))
    (dbc : generic_proof E s (generic_imp C b c)) :
    generic_proof E s (generic_imp C a c) :=
  @generic_imp_trans_raw S F E C s (generic_minimal_mdp H)
    (generic_minimal_K H) (generic_minimal_S H) a b c dab dbc.

Arguments generic_minimal_imp_trans_raw {S F E C s} _ _ _ _ _ _.

Definition generic_minimal_imp_replace_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    (p1 p2 q1 q2 : F)
    (dq1p1 : generic_proof E s (generic_imp C q1 p1))
    (dp2q2 : generic_proof E s (generic_imp C p2 q2))
    (dp1p2 : generic_proof E s (generic_imp C p1 p2)) :
    generic_proof E s (generic_imp C q1 q2) :=
  generic_minimal_imp_trans_raw H q1 p2 q2
    (generic_minimal_imp_trans_raw H q1 p1 p2 dq1p1 dp1p2) dp2q2.

Arguments generic_minimal_imp_replace_raw {S F E C s} _ _ _ _ _ _ _ _.

(** Constructive deduction gives antecedent exchange and contraction without
    postulating either as an additional combinator. *)
Definition generic_minimal_imp_swap_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (d : generic_proof E s
      (generic_imp C p (generic_imp C q r))) :
    generic_proof E s (generic_imp C q (generic_imp C p r)).
Proof.
  assert (dp : generic_list_derivation E s C [p; q] p).
  { exact (GLD_assumption (GRLM_here [q])). }
  assert (dq : generic_list_derivation E s C [p; q] q).
  { exact (GLD_assumption (GRLM_there p (GRLM_here []))). }
  assert (df : generic_list_derivation E s C [p; q]
      (generic_imp C p (generic_imp C q r))).
  { exact (GLD_theorem d). }
  pose (dqr := GLD_mdp df dp).
  pose (dr := GLD_mdp dqr dq).
  exact (generic_empty_derivation_raw (generic_minimal_mdp H)
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H)
      (generic_list_deduction (generic_minimal_mdp H)
        (generic_minimal_K H) (generic_minimal_S H) dr))).
Defined.

Definition generic_minimal_imp_contract_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s
      (generic_imp C p (generic_imp C p q))) :
    generic_proof E s (generic_imp C p q).
Proof.
  assert (dp : generic_list_derivation E s C [p] p).
  { exact (GLD_assumption (GRLM_here [])). }
  assert (df : generic_list_derivation E s C [p]
      (generic_imp C p (generic_imp C p q))).
  { exact (GLD_theorem d). }
  exact (@generic_singleton_deduction_raw S F E s C
    (generic_minimal_mdp H) (generic_minimal_K H) (generic_minimal_S H) p q
    (GLD_mdp (GLD_mdp df dp) dp)).
Defined.

(** * Conjunction, disjunction, and formula equivalence *)

Definition generic_minimal_and_elim_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_and C p q)) : generic_proof E s p :=
  generic_minimal_mdp_raw H _ _ (generic_minimal_and1 H p q) d.

Arguments generic_minimal_and_elim_left_raw {S F E C s} _ _ _ _.

Definition generic_minimal_and_elim_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_and C p q)) : generic_proof E s q :=
  generic_minimal_mdp_raw H _ _ (generic_minimal_and2 H p q) d.

Arguments generic_minimal_and_elim_right_raw {S F E C s} _ _ _ _.

Definition generic_minimal_and_intro_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (dp : generic_proof E s p) (dq : generic_proof E s q) :
    generic_proof E s (generic_and C p q) :=
  generic_minimal_mdp_raw H q (generic_and C p q)
    (generic_minimal_mdp_raw H p
      (generic_imp C q (generic_and C p q))
      (generic_minimal_and3 H p q) dp) dq.

Arguments generic_minimal_and_intro_raw {S F E C s} _ _ _ _ _.

Definition generic_minimal_or_intro_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s p) : generic_proof E s (generic_or C p q) :=
  generic_minimal_mdp_raw H p (generic_or C p q)
    (generic_minimal_or1 H p q) d.

Arguments generic_minimal_or_intro_left_raw {S F E C s} _ _ _ _.

Definition generic_minimal_or_intro_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s q) : generic_proof E s (generic_or C p q) :=
  generic_minimal_mdp_raw H q (generic_or C p q)
    (generic_minimal_or2 H p q) d.

Arguments generic_minimal_or_intro_right_raw {S F E C s} _ _ _ _.

Definition generic_minimal_or_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (dpr : generic_proof E s (generic_imp C p r))
    (dqr : generic_proof E s (generic_imp C q r)) :
    generic_proof E s (generic_imp C (generic_or C p q) r) :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_mdp_raw H _ _ (generic_minimal_or3 H p q r) dpr) dqr.

Arguments generic_minimal_or_elim_raw {S F E C s} _ _ _ _ _ _.

Definition generic_minimal_or_cases_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (dpr : generic_proof E s (generic_imp C p r))
    (dqr : generic_proof E s (generic_imp C q r))
    (dpq : generic_proof E s (generic_or C p q)) : generic_proof E s r :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_or_elim_raw H p q r dpr dqr) dpq.

Arguments generic_minimal_or_cases_raw {S F E C s} _ _ _ _ _ _ _.

Definition generic_minimal_iff_intro_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (dpq : generic_proof E s (generic_imp C p q))
    (dqp : generic_proof E s (generic_imp C q p)) :
    generic_proof E s (generic_formula_iff C p q) :=
  generic_minimal_and_intro_raw H _ _ dpq dqp.

Arguments generic_minimal_iff_intro_raw {S F E C s} _ _ _ _ _.

Definition generic_minimal_iff_elim_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_formula_iff C p q)) :
    generic_proof E s (generic_imp C p q) :=
  generic_minimal_and_elim_left_raw H _ _ d.

Arguments generic_minimal_iff_elim_left_raw {S F E C s} _ _ _ _.

Definition generic_minimal_iff_elim_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_formula_iff C p q)) :
    generic_proof E s (generic_imp C q p) :=
  generic_minimal_and_elim_right_raw H _ _ d.

Arguments generic_minimal_iff_elim_right_raw {S F E C s} _ _ _ _.

Definition generic_minimal_iff_refl_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s (generic_formula_iff C p p) :=
  generic_minimal_iff_intro_raw H p p
    (generic_minimal_identity_raw H p) (generic_minimal_identity_raw H p).

Arguments generic_minimal_iff_refl_raw {S F E C s} _ _.

Definition generic_minimal_iff_symm_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_formula_iff C p q)) :
    generic_proof E s (generic_formula_iff C q p) :=
  generic_minimal_iff_intro_raw H q p
    (generic_minimal_iff_elim_right_raw H p q d)
    (generic_minimal_iff_elim_left_raw H p q d).

Arguments generic_minimal_iff_symm_raw {S F E C s} _ _ _ _.

Definition generic_minimal_iff_trans_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (dpq : generic_proof E s (generic_formula_iff C p q))
    (dqr : generic_proof E s (generic_formula_iff C q r)) :
    generic_proof E s (generic_formula_iff C p r) :=
  generic_minimal_iff_intro_raw H p r
    (generic_minimal_imp_trans_raw H p q r
      (generic_minimal_iff_elim_left_raw H p q dpq)
      (generic_minimal_iff_elim_left_raw H q r dqr))
    (generic_minimal_imp_trans_raw H r q p
      (generic_minimal_iff_elim_right_raw H q r dqr)
      (generic_minimal_iff_elim_right_raw H p q dpq)).

Arguments generic_minimal_iff_trans_raw {S F E C s} _ _ _ _ _ _.

(** Negation equivalence is consumed only through conjunction elimination. *)
Definition generic_minimal_imp_bottom_of_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F)
    (d : generic_proof E s (generic_neg C p)) :
    generic_proof E s (generic_imp C p (generic_bottom C)) :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H p)) d.

Arguments generic_minimal_imp_bottom_of_neg_raw {S F E C s} _ _ _.

Definition generic_minimal_neg_of_imp_bottom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F)
    (d : generic_proof E s (generic_imp C p (generic_bottom C))) :
    generic_proof E s (generic_neg C p) :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_iff_elim_right_raw H _ _
      (generic_minimal_neg_equiv H p)) d.

Arguments generic_minimal_neg_of_imp_bottom_raw {S F E C s} _ _ _.

(** * Derived connective schemata *)

Definition generic_minimal_right_and_intro_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (dpq : generic_proof E s (generic_imp C p q))
    (dpr : generic_proof E s (generic_imp C p r)) :
    generic_proof E s (generic_imp C p (generic_and C q r)) :=
  generic_minimal_under_apply_raw H p r (generic_and C q r)
    (generic_minimal_under_apply_raw H p q
      (generic_imp C r (generic_and C q r))
      (generic_minimal_dhyp_raw H _ p (generic_minimal_and3 H q r)) dpq)
    dpr.

Arguments generic_minimal_right_and_intro_raw {S F E C s} _ _ _ _ _ _.

Definition generic_minimal_and_swap_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_and C p q) (generic_and C q p)) :=
  generic_minimal_right_and_intro_raw H (generic_and C p q) q p
    (generic_minimal_and2 H p q) (generic_minimal_and1 H p q).

Arguments generic_minimal_and_swap_axiom_raw {S F E C s} _ _ _.

Definition generic_minimal_and_swap_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_and C p q)) :
    generic_proof E s (generic_and C q p) :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_and_swap_axiom_raw H p q) d.

Arguments generic_minimal_and_swap_raw {S F E C s} _ _ _ _.

Definition generic_minimal_iff_swap_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_formula_iff C p q)
        (generic_formula_iff C q p)) :=
  generic_minimal_and_swap_axiom_raw H
    (generic_imp C p q) (generic_imp C q p).

Arguments generic_minimal_iff_swap_axiom_raw {S F E C s} _ _ _.

Definition generic_minimal_to_verum_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s (generic_imp C p (generic_top C)) :=
  generic_minimal_dhyp_raw H (generic_top C) p (generic_minimal_verum H).

Arguments generic_minimal_to_verum_raw {S F E C s} _ _.

(** The source proves currying through its finite-context API.  Positional
    contexts make the same construction fully constructive in Coq. *)
Definition generic_minimal_curry_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (d : generic_proof E s
      (generic_imp C (generic_and C p q) r)) :
    generic_proof E s (generic_imp C p (generic_imp C q r)).
Proof.
  assert (dp : generic_list_derivation E s C [q; p] p).
  { exact (GLD_assumption (GRLM_there q (GRLM_here []))). }
  assert (dq : generic_list_derivation E s C [q; p] q).
  { exact (GLD_assumption (GRLM_here [p])). }
  assert (dand3 : generic_list_derivation E s C [q; p]
      (generic_axiom_and3 C p q)).
  { exact (GLD_theorem (generic_minimal_and3 H p q)). }
  pose (dand := GLD_mdp (GLD_mdp dand3 dp) dq).
  assert (df : generic_list_derivation E s C [q; p]
      (generic_imp C (generic_and C p q) r)).
  { exact (GLD_theorem d). }
  pose (dr := GLD_mdp df dand).
  exact (generic_empty_derivation_raw (generic_minimal_mdp H)
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H)
      (generic_list_deduction (generic_minimal_mdp H)
        (generic_minimal_K H) (generic_minimal_S H) dr))).
Defined.

Arguments generic_minimal_curry_raw {S F E C s} _ _ _ _ _.

Definition generic_minimal_uncurry_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (d : generic_proof E s
      (generic_imp C p (generic_imp C q r))) :
    generic_proof E s (generic_imp C (generic_and C p q) r).
Proof.
  set (pq := generic_and C p q).
  assert (dpq : generic_list_derivation E s C [pq] pq).
  { exact (GLD_assumption (GRLM_here [])). }
  assert (dp : generic_list_derivation E s C [pq] p).
  { exact (GLD_mdp (GLD_theorem (generic_minimal_and1 H p q)) dpq). }
  assert (dq : generic_list_derivation E s C [pq] q).
  { exact (GLD_mdp (GLD_theorem (generic_minimal_and2 H p q)) dpq). }
  assert (df : generic_list_derivation E s C [pq]
      (generic_imp C p (generic_imp C q r))).
  { exact (GLD_theorem d). }
  exact (@generic_singleton_deduction_raw S F E s C
    (generic_minimal_mdp H) (generic_minimal_K H) (generic_minimal_S H) pq r
    (GLD_mdp (GLD_mdp df dp) dq)).
Defined.

Arguments generic_minimal_uncurry_raw {S F E C s} _ _ _ _ _.

Definition generic_minimal_curry_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F) :
    generic_proof E s
      (generic_imp C (generic_imp C (generic_and C p q) r)
        (generic_imp C p (generic_imp C q r))).
Proof.
  set (a := generic_imp C (generic_and C p q) r).
  assert (dq : generic_list_derivation E s C [q; p; a] q).
  { exact (GLD_assumption (GRLM_here [p; a])). }
  assert (dp : generic_list_derivation E s C [q; p; a] p).
  { exact (GLD_assumption (GRLM_there q (GRLM_here [a]))). }
  assert (da : generic_list_derivation E s C [q; p; a] a).
  { exact (GLD_assumption
      (GRLM_there q (GRLM_there p (GRLM_here [])))). }
  pose (dand := GLD_mdp
    (GLD_mdp (GLD_theorem (generic_minimal_and3 H p q)) dp) dq).
  pose (dr := GLD_mdp da dand).
  exact (generic_empty_derivation_raw (generic_minimal_mdp H)
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H)
      (generic_list_deduction (generic_minimal_mdp H)
        (generic_minimal_K H) (generic_minimal_S H)
        (generic_list_deduction (generic_minimal_mdp H)
          (generic_minimal_K H) (generic_minimal_S H) dr)))).
Defined.

Arguments generic_minimal_curry_axiom_raw {S F E C s} _ _ _ _.

Definition generic_minimal_uncurry_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p (generic_imp C q r))
        (generic_imp C (generic_and C p q) r)).
Proof.
  set (b := generic_imp C p (generic_imp C q r)).
  set (pq := generic_and C p q).
  assert (dpq : generic_list_derivation E s C [pq; b] pq).
  { exact (GLD_assumption (GRLM_here [b])). }
  assert (db : generic_list_derivation E s C [pq; b] b).
  { exact (GLD_assumption (GRLM_there pq (GRLM_here []))). }
  pose (dp := GLD_mdp (GLD_theorem (generic_minimal_and1 H p q)) dpq).
  pose (dq := GLD_mdp (GLD_theorem (generic_minimal_and2 H p q)) dpq).
  pose (dr := GLD_mdp (GLD_mdp db dp) dq).
  exact (generic_empty_derivation_raw (generic_minimal_mdp H)
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H)
      (generic_list_deduction (generic_minimal_mdp H)
        (generic_minimal_K H) (generic_minimal_S H) dr))).
Defined.

Arguments generic_minimal_uncurry_axiom_raw {S F E C s} _ _ _ _.

Definition generic_minimal_curry_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F) :
    generic_proof E s
      (generic_formula_iff C
        (generic_imp C (generic_and C p q) r)
        (generic_imp C p (generic_imp C q r))) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_curry_axiom_raw H p q r)
    (generic_minimal_uncurry_axiom_raw H p q r).

Arguments generic_minimal_curry_iff_raw {S F E C s} _ _ _ _.

(** * Provability views for the most-used derived rules *)

Lemma generic_minimal_connective_rules_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s ->
    (forall p q,
      generic_provable E s (generic_and C p q) ->
      generic_provable E s p /\ generic_provable E s q) /\
    (forall p q,
      generic_provable E s p -> generic_provable E s q ->
      generic_provable E s (generic_and C p q)) /\
    (forall p q r,
      generic_provable E s (generic_imp C p r) ->
      generic_provable E s (generic_imp C q r) ->
      generic_provable E s (generic_or C p q) ->
      generic_provable E s r).
Proof.
  intros S F E C s H. split; [|split].
  - intros p q [d]. split; constructor.
    + exact (generic_minimal_and_elim_left_raw H p q d).
    + exact (generic_minimal_and_elim_right_raw H p q d).
  - intros p q [dp] [dq]. constructor.
    exact (generic_minimal_and_intro_raw H p q dp dq).
  - intros p q r [dpr] [dqr] [dpq]. constructor.
    exact (generic_minimal_or_cases_raw H p q r dpr dqr dpq).
Qed.

Lemma generic_minimal_negation_provable_iff :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p,
      generic_provable E s (generic_neg C p) <->
      generic_provable E s (generic_imp C p (generic_bottom C)).
Proof.
  intros S F E C s H p. split; intros [d]; constructor.
  - exact (generic_minimal_imp_bottom_of_neg_raw H p d).
  - exact (generic_minimal_neg_of_imp_bottom_raw H p d).
Qed.

Lemma generic_minimal_curry_provable_iff :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p q r,
      generic_provable E s
        (generic_imp C (generic_and C p q) r) <->
      generic_provable E s
        (generic_imp C p (generic_imp C q r)).
Proof.
  intros S F E C s H p q r. split; intros [d]; constructor.
  - exact (generic_minimal_curry_raw H p q r d).
  - exact (generic_minimal_uncurry_raw H p q r d).
Qed.

(** * Functoriality of implication and binary connectives *)

Definition generic_minimal_imp_lift_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q c : F)
    (d : generic_proof E s (generic_imp C p q)) :
    generic_proof E s
      (generic_imp C (generic_imp C c p) (generic_imp C c q)) :=
  generic_minimal_mdp_raw H _ _ (generic_minimal_S H c p q)
    (generic_minimal_dhyp_raw H _ c d).

Arguments generic_minimal_imp_lift_right_raw {S F E C s} _ _ _ _ _.

Definition generic_minimal_imp_lift_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q r : F)
    (d : generic_proof E s (generic_imp C q p)) :
    generic_proof E s
      (generic_imp C (generic_imp C p r) (generic_imp C q r)).
Proof.
  set (f := generic_imp C p r).
  assert (dq : generic_list_derivation E s C [q; f] q).
  { exact (GLD_assumption (GRLM_here [f])). }
  assert (df : generic_list_derivation E s C [q; f] f).
  { exact (GLD_assumption (GRLM_there q (GRLM_here []))). }
  pose (dp := GLD_mdp (GLD_theorem d) dq).
  pose (dr := GLD_mdp df dp).
  exact (generic_empty_derivation_raw (generic_minimal_mdp H)
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H)
      (generic_list_deduction (generic_minimal_mdp H)
        (generic_minimal_K H) (generic_minimal_S H) dr))).
Defined.

Arguments generic_minimal_imp_lift_left_raw {S F E C s} _ _ _ _ _.

Definition generic_minimal_imp_iff_congr_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (hp : generic_proof E s (generic_formula_iff C p1 p2))
    (hq : generic_proof E s (generic_formula_iff C q1 q2)) :
    generic_proof E s
      (generic_formula_iff C
        (generic_imp C p1 q1) (generic_imp C p2 q2)).
Proof.
  apply (generic_minimal_iff_intro_raw H).
  - exact (generic_minimal_imp_trans_raw H _ _ _
      (generic_minimal_imp_lift_left_raw H p1 p2 q1
        (generic_minimal_iff_elim_right_raw H p1 p2 hp))
      (generic_minimal_imp_lift_right_raw H q1 q2 p2
        (generic_minimal_iff_elim_left_raw H q1 q2 hq))).
  - exact (generic_minimal_imp_trans_raw H _ _ _
      (generic_minimal_imp_lift_left_raw H p2 p1 q2
        (generic_minimal_iff_elim_left_raw H p1 p2 hp))
      (generic_minimal_imp_lift_right_raw H q2 q1 p1
        (generic_minimal_iff_elim_right_raw H q1 q2 hq))).
Defined.

Arguments generic_minimal_imp_iff_congr_raw {S F E C s}
  _ _ _ _ _ _ _.

Definition generic_minimal_and_map_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (d : generic_proof E s (generic_and C p1 q1))
    (hp : generic_proof E s (generic_imp C p1 p2))
    (hq : generic_proof E s (generic_imp C q1 q2)) :
    generic_proof E s (generic_and C p2 q2) :=
  generic_minimal_and_intro_raw H p2 q2
    (generic_minimal_mdp_raw H p1 p2 hp
      (generic_minimal_and_elim_left_raw H p1 q1 d))
    (generic_minimal_mdp_raw H q1 q2 hq
      (generic_minimal_and_elim_right_raw H p1 q1 d)).

Arguments generic_minimal_and_map_raw {S F E C s}
  _ _ _ _ _ _ _ _.

Definition generic_minimal_and_map_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (hp : generic_proof E s (generic_imp C p1 p2))
    (hq : generic_proof E s (generic_imp C q1 q2)) :
    generic_proof E s
      (generic_imp C (generic_and C p1 q1) (generic_and C p2 q2)) :=
  generic_minimal_right_and_intro_raw H (generic_and C p1 q1) p2 q2
    (generic_minimal_imp_trans_raw H _ p1 p2
      (generic_minimal_and1 H p1 q1) hp)
    (generic_minimal_imp_trans_raw H _ q1 q2
      (generic_minimal_and2 H p1 q1) hq).

Arguments generic_minimal_and_map_axiom_raw {S F E C s}
  _ _ _ _ _ _ _.

Definition generic_minimal_and_iff_congr_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (hp : generic_proof E s (generic_formula_iff C p1 p2))
    (hq : generic_proof E s (generic_formula_iff C q1 q2)) :
    generic_proof E s
      (generic_formula_iff C
        (generic_and C p1 q1) (generic_and C p2 q2)) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_and_map_axiom_raw H p1 p2 q1 q2
      (generic_minimal_iff_elim_left_raw H p1 p2 hp)
      (generic_minimal_iff_elim_left_raw H q1 q2 hq))
    (generic_minimal_and_map_axiom_raw H p2 p1 q2 q1
      (generic_minimal_iff_elim_right_raw H p1 p2 hp)
      (generic_minimal_iff_elim_right_raw H q1 q2 hq)).

Arguments generic_minimal_and_iff_congr_raw {S F E C s}
  _ _ _ _ _ _ _.

Definition generic_minimal_or_map_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (hp : generic_proof E s (generic_imp C p1 p2))
    (hq : generic_proof E s (generic_imp C q1 q2)) :
    generic_proof E s
      (generic_imp C (generic_or C p1 q1) (generic_or C p2 q2)) :=
  generic_minimal_or_elim_raw H p1 q1 (generic_or C p2 q2)
    (generic_minimal_imp_trans_raw H p1 p2 _ hp
      (generic_minimal_or1 H p2 q2))
    (generic_minimal_imp_trans_raw H q1 q2 _ hq
      (generic_minimal_or2 H p2 q2)).

Arguments generic_minimal_or_map_axiom_raw {S F E C s}
  _ _ _ _ _ _ _.

Definition generic_minimal_or_map_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (d : generic_proof E s (generic_or C p1 q1))
    (hp : generic_proof E s (generic_imp C p1 p2))
    (hq : generic_proof E s (generic_imp C q1 q2)) :
    generic_proof E s (generic_or C p2 q2) :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_or_map_axiom_raw H p1 p2 q1 q2 hp hq) d.

Arguments generic_minimal_or_map_raw {S F E C s}
  _ _ _ _ _ _ _ _.

Definition generic_minimal_or_iff_congr_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p1 p2 q1 q2 : F)
    (hp : generic_proof E s (generic_formula_iff C p1 p2))
    (hq : generic_proof E s (generic_formula_iff C q1 q2)) :
    generic_proof E s
      (generic_formula_iff C
        (generic_or C p1 q1) (generic_or C p2 q2)) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_or_map_axiom_raw H p1 p2 q1 q2
      (generic_minimal_iff_elim_left_raw H p1 p2 hp)
      (generic_minimal_iff_elim_left_raw H q1 q2 hq))
    (generic_minimal_or_map_axiom_raw H p2 p1 q2 q1
      (generic_minimal_iff_elim_right_raw H p1 p2 hp)
      (generic_minimal_iff_elim_right_raw H q1 q2 hq)).

Arguments generic_minimal_or_iff_congr_raw {S F E C s}
  _ _ _ _ _ _ _.

Definition generic_minimal_or_swap_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s (generic_imp C (generic_or C p q) (generic_or C q p)) :=
  generic_minimal_or_elim_raw H p q (generic_or C q p)
    (generic_minimal_or2 H q p) (generic_minimal_or1 H q p).

Arguments generic_minimal_or_swap_axiom_raw {S F E C s} _ _ _.

Definition generic_minimal_inner_mdp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_and C p (generic_imp C p q)) q) :=
  generic_minimal_under_apply_raw H (generic_and C p (generic_imp C p q))
    p q (generic_minimal_and2 H p (generic_imp C p q))
    (generic_minimal_and1 H p (generic_imp C p q)).

Arguments generic_minimal_inner_mdp_raw {S F E C s} _ _ _.

(** * Constructive negation algebra *)

Definition generic_minimal_neg_mdp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F)
    (dn : generic_proof E s (generic_neg C p))
    (dp : generic_proof E s p) : generic_proof E s (generic_bottom C) :=
  generic_minimal_mdp_raw H p (generic_bottom C)
    (generic_minimal_imp_bottom_of_neg_raw H p dn) dp.

Arguments generic_minimal_neg_mdp_raw {S F E C s} _ _ _ _.

(** Foundation's proof uses equality-decided finite contexts.  Raw positional
    membership shows that double-negation introduction is valid over every
    minimal entailment, with no equality or classical hypothesis. *)
Definition generic_minimal_dni_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s (generic_imp C p (generic_neg C (generic_neg C p))).
Proof.
  set (n := generic_neg C p).
  assert (dn : generic_list_derivation E s C [n; p] n).
  { exact (GLD_assumption (GRLM_here [p])). }
  assert (dp : generic_list_derivation E s C [n; p] p).
  { exact (GLD_assumption (GRLM_there n (GRLM_here []))). }
  pose (dnpb := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H p))) dn).
  pose (dbot := GLD_mdp dnpb dp).
  pose (dnb := generic_list_deduction (generic_minimal_mdp H)
    (generic_minimal_K H) (generic_minimal_S H) dbot).
  pose (dnn := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_right_raw H _ _
      (generic_minimal_neg_equiv H n))) dnb).
  exact (@generic_empty_derivation_raw S F E s C
    (generic_minimal_mdp H) _
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H) dnn)).
Defined.

Arguments generic_minimal_dni_raw {S F E C s} _ _.

Definition generic_minimal_dni_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F)
    (d : generic_proof E s p) :
    generic_proof E s (generic_neg C (generic_neg C p)) :=
  generic_minimal_mdp_raw H p _ (generic_minimal_dni_raw H p) d.

Arguments generic_minimal_dni_elim_raw {S F E C s} _ _ _.

(** Contraposition likewise needs only positional deduction and the two
    directions of negation equivalence. *)
Definition generic_minimal_contraposition_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_imp C p q)) :
    generic_proof E s
      (generic_imp C (generic_neg C q) (generic_neg C p)).
Proof.
  set (nq := generic_neg C q).
  assert (dp : generic_list_derivation E s C [p; nq] p).
  { exact (GLD_assumption (GRLM_here [nq])). }
  assert (dnq : generic_list_derivation E s C [p; nq] nq).
  { exact (GLD_assumption (GRLM_there p (GRLM_here []))). }
  pose (dq := GLD_mdp (GLD_theorem d) dp).
  pose (dqbot := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H q))) dnq).
  pose (dbot := GLD_mdp dqbot dq).
  pose (dpbot := generic_list_deduction (generic_minimal_mdp H)
    (generic_minimal_K H) (generic_minimal_S H) dbot).
  pose (dnp := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_right_raw H _ _
      (generic_minimal_neg_equiv H p))) dpbot).
  exact (@generic_singleton_deduction_raw S F E s C
    (generic_minimal_mdp H) (generic_minimal_K H) (generic_minimal_S H)
    nq (generic_neg C p) dnp).
Defined.

Arguments generic_minimal_contraposition_raw {S F E C s} _ _ _ _.

Definition generic_minimal_contraposition_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p q)
        (generic_imp C (generic_neg C q) (generic_neg C p))).
Proof.
  set (f := generic_imp C p q).
  set (nq := generic_neg C q).
  assert (dp : generic_list_derivation E s C [p; nq; f] p).
  { exact (GLD_assumption (GRLM_here [nq; f])). }
  assert (dnq : generic_list_derivation E s C [p; nq; f] nq).
  { exact (GLD_assumption (GRLM_there p (GRLM_here [f]))). }
  assert (df : generic_list_derivation E s C [p; nq; f] f).
  { exact (GLD_assumption
      (GRLM_there p (GRLM_there nq (GRLM_here [])))). }
  pose (dq := GLD_mdp df dp).
  pose (dqbot := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H q))) dnq).
  pose (dbot := GLD_mdp dqbot dq).
  pose (dpbot := generic_list_deduction (generic_minimal_mdp H)
    (generic_minimal_K H) (generic_minimal_S H) dbot).
  pose (dnp := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_right_raw H _ _
      (generic_minimal_neg_equiv H p))) dpbot).
  exact (generic_empty_derivation_raw (generic_minimal_mdp H)
    (generic_list_deduction (generic_minimal_mdp H)
      (generic_minimal_K H) (generic_minimal_S H)
      (generic_list_deduction (generic_minimal_mdp H)
        (generic_minimal_K H) (generic_minimal_S H) dnp))).
Defined.

Arguments generic_minimal_contraposition_axiom_raw {S F E C s} _ _ _.

Definition generic_minimal_double_neg_map_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_imp C p q)) :
    generic_proof E s
      (generic_imp C (generic_neg C (generic_neg C p))
        (generic_neg C (generic_neg C q))) :=
  generic_minimal_contraposition_raw H (generic_neg C q) (generic_neg C p)
    (generic_minimal_contraposition_raw H p q d).

Arguments generic_minimal_double_neg_map_raw {S F E C s} _ _ _ _.

Definition generic_minimal_double_neg_map_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p q)
        (generic_imp C (generic_neg C (generic_neg C p))
          (generic_neg C (generic_neg C q)))) :=
  generic_minimal_imp_trans_raw H _
    (generic_imp C (generic_neg C q) (generic_neg C p)) _
    (generic_minimal_contraposition_axiom_raw H p q)
    (generic_minimal_contraposition_axiom_raw H
      (generic_neg C q) (generic_neg C p)).

Arguments generic_minimal_double_neg_map_axiom_raw {S F E C s} _ _ _.

Definition generic_minimal_neg_iff_congr_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_formula_iff C p q)) :
    generic_proof E s
      (generic_formula_iff C (generic_neg C p) (generic_neg C q)) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_contraposition_raw H q p
      (generic_minimal_iff_elim_right_raw H p q d))
    (generic_minimal_contraposition_raw H p q
      (generic_minimal_iff_elim_left_raw H p q d)).

Arguments generic_minimal_neg_iff_congr_raw {S F E C s} _ _ _ _.

Definition generic_minimal_negated_imp_swap_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_imp C p (generic_neg C q))) :
    generic_proof E s (generic_imp C q (generic_neg C p)) :=
  generic_minimal_imp_trans_raw H q
    (generic_neg C (generic_neg C q)) (generic_neg C p)
    (generic_minimal_dni_raw H q)
    (generic_minimal_contraposition_raw H p (generic_neg C q) d).

Arguments generic_minimal_negated_imp_swap_raw {S F E C s} _ _ _ _.

Definition generic_minimal_negated_imp_swap_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_imp C p (generic_neg C q))
        (generic_imp C q (generic_neg C p))) :=
  generic_minimal_imp_trans_raw H _
    (generic_imp C (generic_neg C (generic_neg C q)) (generic_neg C p)) _
    (generic_minimal_contraposition_axiom_raw H p (generic_neg C q))
    (generic_minimal_imp_lift_left_raw H
      (generic_neg C (generic_neg C q)) q (generic_neg C p)
      (generic_minimal_dni_raw H q)).

Arguments generic_minimal_negated_imp_swap_axiom_raw {S F E C s} _ _ _.

Definition generic_minimal_triple_neg_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s
      (generic_imp C (generic_neg C (generic_neg C (generic_neg C p)))
        (generic_neg C p)) :=
  generic_minimal_contraposition_raw H p
    (generic_neg C (generic_neg C p)) (generic_minimal_dni_raw H p).

Arguments generic_minimal_triple_neg_elim_raw {S F E C s} _ _.

Definition generic_minimal_triple_neg_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s
      (generic_formula_iff C
        (generic_neg C (generic_neg C (generic_neg C p)))
        (generic_neg C p)) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_triple_neg_elim_raw H p)
    (generic_minimal_dni_raw H (generic_neg C p)).

Arguments generic_minimal_triple_neg_iff_raw {S F E C s} _ _.

Definition generic_minimal_neg_bottom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) :
    generic_proof E s (generic_neg C (generic_bottom C)) :=
  generic_minimal_neg_of_imp_bottom_raw H (generic_bottom C)
    (generic_minimal_identity_raw H (generic_bottom C)).

Definition generic_minimal_double_neg_bottom_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) :
    generic_proof E s
      (generic_imp C
        (generic_neg C (generic_neg C (generic_bottom C)))
        (generic_bottom C)) :=
  generic_minimal_under_apply_raw H
    (generic_neg C (generic_neg C (generic_bottom C)))
    (generic_neg C (generic_bottom C)) (generic_bottom C)
    (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H
        (generic_neg C (generic_bottom C))))
    (generic_minimal_dhyp_raw H _ _ (generic_minimal_neg_bottom_raw H)).

Definition generic_minimal_double_neg_bottom_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) :
    generic_proof E s
      (generic_formula_iff C
        (generic_neg C (generic_neg C (generic_bottom C)))
        (generic_bottom C)) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_double_neg_bottom_elim_raw H)
    (generic_minimal_dni_raw H (generic_bottom C)).

Definition generic_minimal_double_neg_expansion_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s
      (generic_formula_iff C
        (generic_neg C (generic_neg C p))
        (generic_imp C (generic_imp C p (generic_bottom C))
          (generic_bottom C))) :=
  generic_minimal_iff_trans_raw H _ (generic_neg C
    (generic_imp C p (generic_bottom C))) _
    (generic_minimal_neg_iff_congr_raw H _ _
      (generic_minimal_neg_equiv H p))
    (generic_minimal_neg_equiv H
      (generic_imp C p (generic_bottom C))).

Arguments generic_minimal_double_neg_expansion_iff_raw {S F E C s} _ _.

(** * Constructive contradiction and De Morgan directions *)

Definition generic_minimal_contradiction_axiom_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F) :
    generic_proof E s
      (generic_imp C (generic_and C p (generic_neg C p))
        (generic_bottom C)) :=
  generic_minimal_under_apply_raw H (generic_and C p (generic_neg C p))
    p (generic_bottom C)
    (generic_minimal_imp_trans_raw H _ (generic_neg C p) _
      (generic_minimal_and2 H p (generic_neg C p))
      (generic_minimal_iff_elim_left_raw H _ _
        (generic_minimal_neg_equiv H p)))
    (generic_minimal_and1 H p (generic_neg C p)).

Arguments generic_minimal_contradiction_axiom_raw {S F E C s} _ _.

Definition generic_minimal_contradiction_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p : F)
    (d : generic_proof E s (generic_and C p (generic_neg C p))) :
    generic_proof E s (generic_bottom C) :=
  generic_minimal_mdp_raw H _ _
    (generic_minimal_contradiction_axiom_raw H p) d.

Arguments generic_minimal_contradiction_raw {S F E C s} _ _ _.

Definition generic_minimal_or_neg_to_neg_and_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_or C (generic_neg C p) (generic_neg C q))
        (generic_neg C (generic_and C p q))) :=
  generic_minimal_or_elim_raw H (generic_neg C p) (generic_neg C q)
    (generic_neg C (generic_and C p q))
    (generic_minimal_contraposition_raw H (generic_and C p q) p
      (generic_minimal_and1 H p q))
    (generic_minimal_contraposition_raw H (generic_and C p q) q
      (generic_minimal_and2 H p q)).

Arguments generic_minimal_or_neg_to_neg_and_raw {S F E C s} _ _ _.

Definition generic_minimal_and_neg_to_neg_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_and C (generic_neg C p) (generic_neg C q))
        (generic_neg C (generic_or C p q))).
Proof.
  set (a := generic_and C (generic_neg C p) (generic_neg C q)).
  pose (dpb := generic_minimal_imp_trans_raw H a (generic_neg C p)
    (generic_imp C p (generic_bottom C))
    (generic_minimal_and1 H (generic_neg C p) (generic_neg C q))
    (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H p))).
  pose (dqb := generic_minimal_imp_trans_raw H a (generic_neg C q)
    (generic_imp C q (generic_bottom C))
    (generic_minimal_and2 H (generic_neg C p) (generic_neg C q))
    (generic_minimal_iff_elim_left_raw H _ _
      (generic_minimal_neg_equiv H q))).
  pose (d0 := generic_minimal_dhyp_raw H _ a
    (generic_minimal_or3 H p q (generic_bottom C))).
  pose (d1 := generic_minimal_under_apply_raw H a
    (generic_imp C p (generic_bottom C))
    (generic_imp C (generic_imp C q (generic_bottom C))
      (generic_imp C (generic_or C p q) (generic_bottom C))) d0 dpb).
  pose (dorbot := generic_minimal_under_apply_raw H a
    (generic_imp C q (generic_bottom C))
    (generic_imp C (generic_or C p q) (generic_bottom C)) d1 dqb).
  exact (generic_minimal_imp_trans_raw H a _ _ dorbot
    (generic_minimal_iff_elim_right_raw H _ _
      (generic_minimal_neg_equiv H (generic_or C p q)))).
Defined.

Arguments generic_minimal_and_neg_to_neg_or_raw {S F E C s} _ _ _.

Definition generic_minimal_neg_or_to_and_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_neg C (generic_or C p q))
        (generic_and C (generic_neg C p) (generic_neg C q))) :=
  generic_minimal_right_and_intro_raw H (generic_neg C (generic_or C p q))
    (generic_neg C p) (generic_neg C q)
    (generic_minimal_contraposition_raw H p (generic_or C p q)
      (generic_minimal_or1 H p q))
    (generic_minimal_contraposition_raw H q (generic_or C p q)
      (generic_minimal_or2 H p q)).

Arguments generic_minimal_neg_or_to_and_neg_raw {S F E C s} _ _ _.

Definition generic_minimal_neg_or_iff_and_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_formula_iff C (generic_neg C (generic_or C p q))
        (generic_and C (generic_neg C p) (generic_neg C q))) :=
  generic_minimal_iff_intro_raw H _ _
    (generic_minimal_neg_or_to_and_neg_raw H p q)
    (generic_minimal_and_neg_to_neg_or_raw H p q).

Arguments generic_minimal_neg_or_iff_and_neg_raw {S F E C s} _ _ _.

Definition generic_minimal_or_double_neg_map_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_or C p q)) :
    generic_proof E s
      (generic_or C (generic_neg C (generic_neg C p))
        (generic_neg C (generic_neg C q))) :=
  generic_minimal_or_map_raw H p (generic_neg C (generic_neg C p))
    q (generic_neg C (generic_neg C q)) d
    (generic_minimal_dni_raw H p) (generic_minimal_dni_raw H q).

Arguments generic_minimal_or_double_neg_map_raw {S F E C s} _ _ _ _.

Definition generic_minimal_and_double_neg_map_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s) (p q : F)
    (d : generic_proof E s (generic_and C p q)) :
    generic_proof E s
      (generic_and C (generic_neg C (generic_neg C p))
        (generic_neg C (generic_neg C q))) :=
  generic_minimal_and_map_raw H p (generic_neg C (generic_neg C p))
    q (generic_neg C (generic_neg C q)) d
    (generic_minimal_dni_raw H p) (generic_minimal_dni_raw H q).

Arguments generic_minimal_and_double_neg_map_raw {S F E C s} _ _ _ _.

(** * Inhabited theorem views *)

Lemma generic_minimal_dni_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p,
      generic_provable E s
        (generic_imp C p (generic_neg C (generic_neg C p))).
Proof.
  intros S F E C s H p. constructor. exact (generic_minimal_dni_raw H p).
Qed.

Lemma generic_minimal_contraposition_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p q,
      generic_provable E s (generic_imp C p q) ->
      generic_provable E s
        (generic_imp C (generic_neg C q) (generic_neg C p)).
Proof.
  intros S F E C s H p q [d]. constructor.
  exact (generic_minimal_contraposition_raw H p q d).
Qed.

Lemma generic_minimal_double_neg_map_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p q,
      generic_provable E s (generic_imp C p q) ->
      generic_provable E s
        (generic_imp C (generic_neg C (generic_neg C p))
          (generic_neg C (generic_neg C q))).
Proof.
  intros S F E C s H p q [d]. constructor.
  exact (generic_minimal_double_neg_map_raw H p q d).
Qed.

Lemma generic_minimal_binary_iff_congruence_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p1 p2 q1 q2,
      generic_provable E s (generic_formula_iff C p1 p2) ->
      generic_provable E s (generic_formula_iff C q1 q2) ->
      generic_provable E s
        (generic_formula_iff C (generic_and C p1 q1)
          (generic_and C p2 q2)) /\
      generic_provable E s
        (generic_formula_iff C (generic_or C p1 q1)
          (generic_or C p2 q2)) /\
      generic_provable E s
        (generic_formula_iff C (generic_imp C p1 q1)
          (generic_imp C p2 q2)).
Proof.
  intros S F E C s H p1 p2 q1 q2 [hp] [hq].
  split; [|split]; constructor.
  - exact (generic_minimal_and_iff_congr_raw H p1 p2 q1 q2 hp hq).
  - exact (generic_minimal_or_iff_congr_raw H p1 p2 q1 q2 hp hq).
  - exact (generic_minimal_imp_iff_congr_raw H p1 p2 q1 q2 hp hq).
Qed.

Lemma generic_minimal_neg_or_iff_and_neg_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall p q,
      generic_provable E s
        (generic_formula_iff C (generic_neg C (generic_or C p q))
          (generic_and C (generic_neg C p) (generic_neg C q))).
Proof.
  intros S F E C s H p q. constructor.
  exact (generic_minimal_neg_or_iff_and_neg_raw H p q).
Qed.

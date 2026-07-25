import BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor
import BoundedPAConsistency.QuantifierFreeTransport
import BoundedPAConsistency.FinFunext

/-!
# Countermodel audit for the current structural successor context

The two-predicate source theory gives no axioms to its predicate placeholders.
This file interprets both placeholders by the deliberately non-semantic
polarity choice `neg p < p`, while the three named levels are `0`, `1`, and
`2`.  On every well-formed formula this choice is self-dual under represented
negation, so the prior coherence context is true at level zero.  The requested
successor invariant nevertheless fails at the code of verum, because every
successor certificate accepts true quantifier-free formulas whereas the
chosen current placeholder rejects it.

Besides auditing the exact obstruction, this demonstrates that a derivation
of the literal `sourceSuccessorSentence` cannot be filled without strengthening
its source context.  No consistency assumption is used: ordinary soundness is
applied to an explicit standard model of the lifted source theory.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorCountermodel

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth
open LeanProofs.BoundedPAConsistency.QuantifierFreeTransport
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TwoPredicateSourceContextInductionKernel
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessor

/-! ## The expanded standard structure -/

/-- Interpret the ternary placeholder by an orientation of each coded
negation pair.  The environments are deliberately ignored.  The same
instance is used for both copies of `placeholderLanguage 3`, so the positive
half of prior coherence is immediate; involutivity of negation supplies its
negative half. -/
private noncomputable instance orientedPlaceholderStructure :
    Structure (placeholderLanguage 3) ℕ where
  func := fun _ f _ ↦ nomatch f
  rel := fun _ r v ↦ by
    cases r with
    | predicate =>
        exact Bootstrapping.neg ℒₒᵣ (v 2) < v 2

/-- Interpret the three named source constants by the intended standard
levels `0`, `1`, and `2`. -/
private noncomputable instance standardLevelParameterStructure :
    Structure (parameterLanguage 3) ℕ where
  func := fun _ f _ ↦ by
    cases f with
    | parameter i => exact ![0, 1, 2] i
  rel := fun _ r _ ↦ nomatch r

private noncomputable instance sourceCountermodelStructure :
    Structure SourceLanguage ℕ := inferInstance

@[simp] private theorem eval_firstAtom_oriented {n : ℕ}
    (terms : Fin 3 → ClosedSemiterm SourceLanguage n)
    (e : Fin n → ℕ) :
    (firstAtom terms).Evalb (M := ℕ) e ↔
      Bootstrapping.neg ℒₒᵣ ((terms 2).valb e) <
        (terms 2).valb e := by
  rfl

@[simp] private theorem eval_secondAtom_oriented {n : ℕ}
    (terms : Fin 3 → ClosedSemiterm SourceLanguage n)
    (e : Fin n → ℕ) :
    (secondAtom terms).Evalb (M := ℕ) e ↔
      Bootstrapping.neg ℒₒᵣ ((terms 2).valb e) <
        (terms 2).valb e := by
  rfl

@[simp] private theorem val_namedParameter_standard {n : ℕ}
    (i : Fin 3) (e : Fin n → ℕ) :
    (namedParameterTerm (arity₀ := 3) (arity₁ := 3)
      (n := n) i).valb e = ![0, 1, 2] i := by
  rfl

@[simp] private theorem eval_liftArithmetic_standard {n : ℕ}
  (p : ArithmeticSemisentence n) (e : Fin n → ℕ) :
    (liftArithmeticFormula p).Evalb (M := ℕ) e ↔
      p.Evalb (M := ℕ) e := by
  simp [liftArithmeticFormula,
    ModelCodedTwoPredicateParameters.arithmeticHom]

private theorem sourceCountermodel_arithmeticReduct :
    sourceCountermodelStructure.lMap
        (ModelCodedTwoPredicateParameters.arithmeticHom 3 3 3) =
      (inferInstance : Structure ℒₒᵣ ℕ) := by
  ext <;> rfl

@[simp] private theorem val_successorTerm_standard
    (e : Fin 1 → ℕ) :
    (successorTerm 3 3 3).valb (M := ℕ) e = e 0 + 1 := by
  simp [successorTerm,
    ModelCodedTwoPredicateParameters.arithmeticHom]

@[simp] private theorem eval_priorSigmaDomain_standard
    (e : Fin 3 → ℕ) :
    sourcePriorSigmaDomain.Evalb (M := ℕ) e ↔
      OrientedHierarchy.IsSigmaCode ℒₒᵣ 0 (e 2) := by
  simp [sourcePriorSigmaDomain, apply₂, levelTerm]

@[simp] private theorem eval_priorPiDomain_standard
    (e : Fin 3 → ℕ) :
    sourcePriorPiDomain.Evalb (M := ℕ) e ↔
      OrientedHierarchy.IsPiCode ℒₒᵣ 0 (e 2) := by
  simp [sourcePriorPiDomain, apply₂, levelTerm]

@[simp] private theorem eval_currentSigmaDomain_standard
    (e : Fin 3 → ℕ) :
    sourceCurrentSigmaDomain.Evalb (M := ℕ) e ↔
      OrientedHierarchy.IsSigmaCode ℒₒᵣ 1 (e 2) := by
  simp [sourceCurrentSigmaDomain, apply₂, levelTerm]

@[simp] private theorem eval_currentPiDomain_standard
    (e : Fin 3 → ℕ) :
    sourceCurrentPiDomain.Evalb (M := ℕ) e ↔
      OrientedHierarchy.IsPiCode ℒₒᵣ 1 (e 2) := by
  simp [sourceCurrentPiDomain, apply₂, levelTerm]

/-- The expanded structure satisfies every lifted PA axiom, since its
arithmetic reduct is the standard natural-number structure. -/
private theorem sourceCountermodel_models_peano :
    ℕ↓[SourceLanguage] ⊧* twoPredicateParameterPeano 3 3 3 := by
  constructor
  intro sigma hsigma
  rcases hsigma with ⟨tau, htau, rfl⟩
  rw [Semiformula.models_lMap]
  have hreduct :
      sourceCountermodelStructure.lMap
          (ModelCodedTwoPredicateParameters.arithmeticHom 3 3 3) =
        (inferInstance : Structure ℒₒᵣ ℕ) := by
    exact sourceCountermodel_arithmeticReduct
  rw [hreduct]
  exact
    (show ℕ↓[ℒₒᵣ] ⊧ tau from
      (inferInstance : ℕ↓[ℒₒᵣ] ⊧* Peano).models _ htau)

/-- Coded negation has no fixed point on well-formed formulas.  The proof is
structural and remains internal to the standard countermodel audit. -/
private theorem neg_ne_self {p : ℕ} (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.neg ℒₒᵣ p ≠ p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
      (P := fun p : ℕ ↦ Bootstrapping.neg ℒₒᵣ p ≠ p)
      (L := ℒₒᵣ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R terms hR hterms
    rw [neg_rel hR hterms]
    simp [qqRel, qqNRel]
  · intro k R terms hR hterms
    rw [neg_nrel hR hterms]
    simp [qqRel, qqNRel]
  · rw [neg_verum]
    simp [qqVerum, qqFalsum]
  · rw [neg_falsum]
    simp [qqVerum, qqFalsum]
  · intro p q hp hq ihp ihq
    rw [neg_and hp hq]
    simp [qqAnd, qqOr]
  · intro p q hp hq ihp ihq
    rw [neg_or hp hq]
    simp [qqAnd, qqOr]
  · intro p hp ihp
    rw [neg_all hp]
    simp [qqAll, qqExs]
  · intro p hp ihp
    rw [neg_ex hp]
    simp [qqAll, qqExs]

/-- The oriented placeholder satisfies the prior two-polarity coherence law
at level zero. -/
private theorem sourceCountermodel_models_prior :
    ℕ↓[SourceLanguage] ⊧ sourcePriorCrossLevelContext := by
  simp [models_iff, sourcePriorCrossLevelContext,
    sourcePriorCrossLevelPredicate, sourcePriorCrossLevelBody,
    sourcePredecessorPiTruth, predecessorAtom, currentAtom,
    Semiformula.eval_rew,
    Function.comp_def]
  intro p hpi
  have hp : IsUFormula ℒₒᵣ p := hpi.isUFormula
  have hnegneg : Bootstrapping.neg ℒₒᵣ
      (Bootstrapping.neg ℒₒᵣ p) = p := hp.neg_neg
  have hne : Bootstrapping.neg ℒₒᵣ p ≠ p := neg_ne_self hp
  rw [hnegneg]
  constructor
  · intro h
    exact ⟨hpi, Nat.le_of_lt h⟩
  · rintro ⟨_, hle⟩
    exact Nat.lt_of_le_of_ne hle hne

/-! ## Failure of the requested successor sentence -/

/-- The dynamically assembled successor predicate accepts verum, independently
of the deliberately pathological interpretation of its recursive placeholder. -/
private theorem eval_sourceCurrentSuccessorTruth_verum
    (bound free : ℕ) :
    sourceCurrentSuccessorTruth.Evalb (M := ℕ)
      ![bound, free, (^⊤ : ℕ)] := by
  simp [sourceCurrentSuccessorTruth, sourceCurrentSuccessorRecordValid,
    sourceCurrentUniversalRecordBranch,
    DynamicTruthCrossLevelSourceTemplate.apply₂,
    DynamicTruthCrossLevelSourceTemplate.apply₃,
    DynamicTruthFormula.RecordDomain,
    DynamicTruthFormula.PositiveRecordBranches,
    DynamicTruthFormula.UniversalRecordPrefix,
    levelTerm,
    Semiformula.eval_rew,
    Function.comp_def]
  let r : ℕ := FixedLevelTruth.truthRecord bound free (^⊤ : ℕ) 0
  let C : ℕ := insert r ∅
  have hr : r ∈ C := by simp [C]
  refine ⟨C, ?_, ?_⟩
  · refine ⟨0, ?_, hr⟩
    simpa [r, FixedLevelTruth.truthRecord] using
      (lt_of_mem_rng hr)
  · intro r' hr'
    have hrr : r' = r := by simpa [C] using hr'
    subst r'
    constructor
    · simp [r]
    · exact Or.inl <| Or.inl <| by
        simp [r, QuantifierFreeTruth.QFTrue,
          QuantifierFreeTruth.IsQuantifierFreeCode]

/-- The oriented placeholder rejects verum because its coded negation,
falsum, has the larger standard code. -/
private theorem not_eval_currentAtom_verum (bound free : ℕ) :
    ¬(currentAtom (#0) (#1) (#2)).Evalb (M := ℕ)
      ![bound, free, (^⊤ : ℕ)] := by
  change ¬Bootstrapping.neg ℒₒᵣ (^⊤ : ℕ) < (^⊤ : ℕ)
  rw [neg_verum]
  norm_num [qqVerum, qqFalsum, pair]
  omega

/-- The number immediately preceding the code of verum is not itself a
well-formed arithmetic formula code. -/
private lemma natPair_mono {a₁ a₂ b₁ b₂ : ℕ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    Nat.pair a₁ b₁ ≤ Nat.pair a₂ b₂ := by
  rcases ha.eq_or_lt with rfl | ha
  · rcases hb.eq_or_lt with rfl | hb
    · exact Nat.le_refl _
    · exact (Nat.pair_lt_pair_right _ hb).le
  · exact le_trans (Nat.pair_lt_pair_left _ ha).le <|
      match hb.eq_or_lt with
      | Or.inl h => by simp [h]
      | Or.inr h => (Nat.pair_lt_pair_right _ h).le

private lemma verumPredecessor_lt_tagged (tag tail : ℕ)
    (htag : 2 ≤ tag) :
    (⟪2, 0⟫ : ℕ) < ⟪tag, tail⟫ + 1 := by
  have hpair : (⟪2, 0⟫ : ℕ) ≤ ⟪tag, tail⟫ := by
    simpa only [nat_pair_eq] using
      (natPair_mono htag (Nat.zero_le tail))
  exact Nat.lt_succ_of_le hpair

private theorem verumPredecessor_not_uformula :
    ¬IsUFormula ℒₒᵣ (⟪2, 0⟫ : ℕ) := by
  intro hp
  rcases hp.case with
    (⟨k, R, terms, hR, hterms, hcode⟩ |
     ⟨k, R, terms, hR, hterms, hcode⟩ |
     hcode | hcode | ⟨p, q, hp, hq, hcode⟩ |
     ⟨p, q, hp, hq, hcode⟩ |
     ⟨p, hp, hcode⟩ | ⟨p, hp, hcode⟩)
  · rcases Arithmetic.isRel_iff_LOR.mp hR with
      ⟨rfl, _⟩ | ⟨rfl, _⟩
    all_goals
      have hinner := pair_le_pair_right (V := ℕ) 2
        (by
          change (0 : ℕ) = (⟪R, terms⟫ : ℕ) ∨
            (0 : ℕ) < (⟪R, terms⟫ : ℕ)
          omega)
      have houter := le_pair_right (V := ℕ) 0
        (⟪2, R, terms⟫ : ℕ)
      have hcontra :=
        @Preorder.le_trans ℕ
          (@PartialOrder.toPreorder ℕ
            (@LinearOrder.toPartialOrder ℕ
              (@LO.FirstOrder.Arithmetic.instLinearOrder_foundation ℕ
                inferInstance inferInstance)))
          _ _ _ hinner houter
      rw [hcode] at hcontra
      simp [qqRel] at hcontra
      exact Arithmetic.lt_irrefl _ (succ_le_iff_lt.mp hcontra)
  · rcases Arithmetic.isRel_iff_LOR.mp hR with
      ⟨rfl, _⟩ | ⟨rfl, _⟩
    all_goals
      have hinner := pair_le_pair_right (V := ℕ) 2
        (by
          change (0 : ℕ) = (⟪R, terms⟫ : ℕ) ∨
            (0 : ℕ) < (⟪R, terms⟫ : ℕ)
          omega)
      have houter := le_pair_right (V := ℕ) 1
        (⟪2, R, terms⟫ : ℕ)
      have hcontra :=
        @Preorder.le_trans ℕ
          (@PartialOrder.toPreorder ℕ
            (@LinearOrder.toPartialOrder ℕ
              (@LO.FirstOrder.Arithmetic.instLinearOrder_foundation ℕ
                inferInstance inferInstance)))
          _ _ _ hinner houter
      rw [hcode] at hcontra
      simp [qqNRel] at hcontra
      exact Arithmetic.lt_irrefl _ (succ_le_iff_lt.mp hcontra)
  · exact (Nat.ne_of_lt
      (verumPredecessor_lt_tagged 2 0 (by omega))) hcode
  · exact (Nat.ne_of_lt
      (verumPredecessor_lt_tagged 3 0 (by omega))) hcode
  · exact (Nat.ne_of_lt
      (verumPredecessor_lt_tagged 4 (⟪p, q⟫ : ℕ) (by omega))) hcode
  · exact (Nat.ne_of_lt
      (verumPredecessor_lt_tagged 5 (⟪p, q⟫ : ℕ) (by omega))) hcode
  · exact (Nat.ne_of_lt
      (verumPredecessor_lt_tagged 6 p (by omega))) hcode
  · exact (Nat.ne_of_lt
      (verumPredecessor_lt_tagged 7 p (by omega))) hcode

/-- At the predecessor of verum, the induction hypothesis is vacuous: the
number is not a formula code and hence lies in neither oriented domain. -/
private theorem eval_sourceNextCrossLevelInvariant_verumPredecessor :
    sourceNextCrossLevelInvariant.Evalb (M := ℕ)
      ![(⟪2, 0⟫ : ℕ)] := by
  simp [sourceNextCrossLevelInvariant, sourceNextCrossLevelBody,
    OrientedHierarchy.IsSigmaCode, OrientedHierarchy.IsPiCode,
    verumPredecessor_not_uformula]

/-- The literal structural successor sentence fails in the explicit standard
source model. -/
theorem sourceSuccessorSentence_not_valid :
    ¬(ℕ↓[SourceLanguage] ⊧ sourceSuccessorSentence) := by
  intro h
  simp [models_iff, sourceSuccessorSentence, successorSentence,
    sourceNextCrossLevelInvariant] at h
  have hbody := h sourceCountermodel_models_prior
    (⟪2, 0⟫ : ℕ)
    eval_sourceNextCrossLevelInvariant_verumPredecessor 0 0
  let successorEnvironment : Fin 3 → ℕ := fun x ↦
    FirstOrder.Semiterm.val ![0, 0, (⟪2, 0⟫ : ℕ)] Empty.elim
      ((Rew.subst ![successorTerm 3 3 3]).q.q #x)
  have successorEnvironment_eq :
      successorEnvironment = ![0, 0, (^⊤ : ℕ)] := by
    refine funext_fin3 ?_ ?_ ?_
    · change FirstOrder.Semiterm.val
        ![0, 0, (⟪2, 0⟫ : ℕ)] Empty.elim
          ((Rew.subst ![successorTerm 3 3 3]).q.q
            (#(0 : Fin 3))) = 0
      rw [Rew.q_bvar_zero]
      rfl
    · change FirstOrder.Semiterm.val
        ![0, 0, (⟪2, 0⟫ : ℕ)] Empty.elim
          ((Rew.subst ![successorTerm 3 3 3]).q.q
            (#(1 : Fin 3))) = 0
      rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl,
        Rew.q_bvar_succ, Semiterm.val_bShift,
        Rew.q_bvar_zero]
      rfl
    · change FirstOrder.Semiterm.val
        ![0, 0, (⟪2, 0⟫ : ℕ)] Empty.elim
          ((Rew.subst ![successorTerm 3 3 3]).q.q
            (#(2 : Fin 3))) = (^⊤ : ℕ)
      rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl,
        Rew.q_bvar_succ, Semiterm.val_bShift,
        show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,
        Rew.q_bvar_succ, Semiterm.val_bShift,
        Rew.subst_bvar]
      simpa [qqVerum] using
        (val_successorTerm_standard
          ![(⟪2, 0⟫ : ℕ)])
  have hsigma := hbody.1
  rw [Semiformula.eval_rew] at hsigma
  change sourceNextSigmaClause.Evalb (M := ℕ)
    successorEnvironment at hsigma
  rw [successorEnvironment_eq] at hsigma
  simp [sourceNextSigmaClause] at hsigma
  exact not_eval_currentAtom_verum 0 0
    (hsigma.mp (eval_sourceCurrentSuccessorTruth_verum 0 0))

/-- Consequently there is no derivation of the literal successor sentence
from lifted PA.  This is an ordinary soundness argument in the explicit
standard countermodel above, not a consistency assumption. -/
theorem sourceSuccessorSentence_unprovable :
    twoPredicateParameterPeano 3 3 3 ⊬ sourceSuccessorSentence := by
  intro h
  exact sourceSuccessorSentence_not_valid
    (models_of_provable sourceCountermodel_models_peano h)

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceSuccessorCountermodel

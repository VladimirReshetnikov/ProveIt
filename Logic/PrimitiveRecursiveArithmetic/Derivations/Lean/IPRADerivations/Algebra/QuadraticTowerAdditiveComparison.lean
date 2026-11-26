import IPRADerivations.Algebra.QuadraticTowerComparisonSymmetry

/-!
# Actual additive comparison identities at every numerical depth

Negation reverses the SAME constructed difference and actual order;
comparison is preserved by actual common translation and literal zero
addition. The original raw translation array needs no height bound,
because its constructed differences cancel literally. Sign-zero
negation congruence uses the proved original difference cap. Semantic
zero-addition closure and full quotient transitivity remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerAdditiveComparison

open_ipra
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficientArithmetic (added negated added_congr)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerScalarArrays (zeroArray)
open QuadraticTowerScalarBudget (amp)
open QuadraticTowerDifferenceIdentities (difference signDifference equivalent less)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Raw double negation yields normalization; only actual add outputs
are subsequently identified as literal canonical differences. -/
theorem negative_difference (h A C : PTm n) : Γ ⊢[PRAAx] difference h (negated h A) (negated h C) ≐ difference h C A :=
  (added_congr (.eqRefl h) (.eqRefl _) (QuadraticTowerMultiplicationNegative.negative_involution h C)).eqTrans
    ((added_congr (.eqRefl h) (QuadraticTowerArrayNormalization.normalized_negated h A).eqSymm (.eqRefl _)).eqTrans
      ((QuadraticTowerAdditionLaws.added_normalized h (negated h A) C).eqTrans
        (QuadraticTowerMultiplicationCommutativity.added_commutative h (negated h A) C)))

theorem negative_sign (h B D A C : PTm n) : Γ ⊢[PRAAx]
    signDifference h B D (negated h A) (negated h C) ≐ signDifference h B D C A :=
  QuadraticTowerSignRecipe.read_operand_congr h B (QuadraticTowerSignTable.table h B D) _ _ (negative_difference h A C)

theorem order_negation (h B D A C : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (less h B D (negated h A) (negated h C)) (less h B D C A) :=
  .andI (.impI ((negative_sign h B D C A).eqSymm.eqTrans Prf.hyp0))
    (.impI ((negative_sign h B D C A).eqTrans Prf.hyp0))

theorem equivalence_negation (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    Fm.iff (equivalent h B D (negated h A) (negated h C)) (equivalent h B D A C) :=
  .andI (.impI (QuadraticTowerComparisonSymmetry.equivalent_symmetric h B D C A b hb.wk hD.wk hc.wk ha.wk
    ((negative_sign h B D A C).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((negative_sign h B D A C).eqTrans
      (QuadraticTowerComparisonSymmetry.equivalent_symmetric h B D A C b hb.wk hD.wk ha.wk hc.wk Prf.hyp0)))

/-- The actual sign query normalizes coefficient values even on raw codes. -/
theorem zero_addition_query (h B D A : PTm n) : Γ ⊢[PRAAx]
    QuadraticTowerSignTable.query h B D (added h A (zeroArray h)) ≐ QuadraticTowerSignTable.query h B D A :=
  (QuadraticTowerSignRecipe.read_operand_congr h B (QuadraticTowerSignTable.table h B D) _ _
    (QuadraticTowerMultiplicationUnit.added_zero_normalized h A)).eqTrans
      (QuadraticTowerSignCoherence.read_values_proper h B _ _ A (QuadraticTowerOperandProperness.normalized_values h A))

theorem translated_sign (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    signDifference h B D (added h A E) (added h C E) ≐ signDifference h B D A C :=
  QuadraticTowerDifferenceIdentities.sign_translation h B D A C E

/-- The ORIGINAL raw common translation cancels before any sign reading. -/
theorem translated_negative_sign (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    signDifference h B D (negated h (added h A E)) (negated h (added h C E)) ≐ signDifference h B D C A :=
  (negative_sign h B D (added h A E) (added h C E)).eqTrans (translated_sign h B D C A E)
theorem translated_order_negation (h B D A C E : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (less h B D (negated h (added h A E)) (negated h (added h C E))) (less h B D C A) :=
  .andI (.impI ((translated_negative_sign h B D C A E).eqSymm.eqTrans Prf.hyp0))
    (.impI ((translated_negative_sign h B D C A E).eqTrans Prf.hyp0))

theorem translated_equivalence_negation (h B D A C E b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    Fm.iff (equivalent h B D (negated h (added h A E)) (negated h (added h C E))) (equivalent h B D A C) :=
  .andI (.impI (QuadraticTowerComparisonSymmetry.equivalent_symmetric h B D C A b hb.wk hD.wk hc.wk ha.wk
    ((translated_negative_sign h B D A C E).eqSymm.eqTrans Prf.hyp0)))
    (.impI ((translated_negative_sign h B D A C E).eqTrans
      (QuadraticTowerComparisonSymmetry.equivalent_symmetric h B D A C b hb.wk hD.wk ha.wk hc.wk Prf.hyp0)))


/-- Actual tags of the original, translated and negated translated differences. -/
def output (h b D A C E : PTm n) : PTm n := pairT (signDifference h (amp b) D A C)
  (pairT (signDifference h (amp b) D (added h A E) (added h C E))
    (pairT (signDifference h (amp b) D (negated h (added h A E)) (negated h (added h C E))) (amp b)))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (h b D A C E : PTm n) : PTm n := PTm.app outputF ![h,b,D,A,C,E]
ipra_subst output
ipra_subst run

theorem program_at (h b D A C E : PTm n) : Γ ⊢[PRAAx] run h b D A C E ≐ output h b D A C E := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![h,b,D,A,C,E]
theorem returned_original (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (run h b D A C E) ≐ signDifference h (amp b) D A C :=
  (program_at _ _ _ _ _ _).fstE
theorem returned_tail (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (run h b D A C E) ≐
    pairT (signDifference h (amp b) D (added h A E) (added h C E))
      (pairT (signDifference h (amp b) D (negated h (added h A E)) (negated h (added h C E))) (amp b)) :=
  (program_at _ _ _ _ _ _).sndE
theorem returned_translation (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h b D A C E)) ≐
    signDifference h (amp b) D (added h A E) (added h C E) :=
  (returned_tail _ _ _ _ _ _).fstE
theorem returned_negative_pair (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h b D A C E)) ≐
    pairT (signDifference h (amp b) D (negated h (added h A E)) (negated h (added h C E))) (amp b) :=
  (returned_tail _ _ _ _ _ _).sndE
theorem returned_negative (h b D A C E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h b D A C E))) ≐
    signDifference h (amp b) D (negated h (added h A E)) (negated h (added h C E)) :=
  (returned_negative_pair _ _ _ _ _ _).fstE
theorem returned_cap (h b D A C E : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h b D A C E))) ≐ amp b :=
  (returned_negative_pair _ _ _ _ _ _).sndE

theorem returned_translation_equal (h b D A C E : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run h b D A C E)) ≐ fstT (run h b D A C E) :=
  (returned_translation _ _ _ _ _ _).eqTrans ((translated_sign h (amp b) D A C E).eqTrans (returned_original _ _ _ _ _ _).eqSymm)
theorem returned_negative_zero_iff (h b D A C E : PTm n)
    (p : Γ ⊢[PRAAx] QuadraticTowerMultiplicationNegative.source h D A C b) : Γ ⊢[PRAAx]
    Fm.iff (fstT (sndT (sndT (run h b D A C E))) ≐ zero) (fstT (run h b D A C E) ≐ zero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (returned_original _ _ _ _ _ _).eqTrans
      (.impE (translated_equivalence_negation h (amp b) D A C E b (le_refl _) p.andE₁.wk p.andE₂.andE₁.wk p.andE₂.andE₂.wk).andE₁
        ((returned_negative _ _ _ _ _ _).eqSymm.eqTrans Prf.hyp0))
  · exact (returned_negative _ _ _ _ _ _).eqTrans
      (.impE (translated_equivalence_negation h (amp b) D A C E b (le_refl _) p.andE₁.wk p.andE₂.andE₁.wk p.andE₂.andE₂.wk).andE₂
        ((returned_original _ _ _ _ _ _).eqSymm.eqTrans Prf.hyp0))

theorem actual_uniform_negative_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (difference (var 0) (negated (var 0) (var 1)) (negated (var 0) (var 2)) ≐ difference (var 0) (var 2) (var 1)) :=
  closeUniv 3 (negative_difference _ _ _)
theorem actual_uniform_negative_order_reversal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (less (var 0) (var 1) (var 2) (negated (var 0) (var 3)) (negated (var 0) (var 4)))
      (less (var 0) (var 1) (var 2) (var 4) (var 3))) := closeUniv 5 (order_negation _ _ _ _ _)
theorem original_uniform_negative_equivalence_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (QuadraticTowerComparisonSymmetry.input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      Fm.iff (equivalent (var 0) (var 1) (var 2) (negated (var 0) (var 3)) (negated (var 0) (var 4)))
        (equivalent (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (equivalence_negation _ _ _ _ _ (var 5) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_uniform_zero_addition_query_preservation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (added (var 0) (var 3) (zeroArray (var 0))) ≐
      QuadraticTowerSignTable.query (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (zero_addition_query _ _ _ _)
theorem actual_uniform_translated_negative_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (Fm.iff (less (var 0) (var 1) (var 2) (negated (var 0) (added (var 0) (var 3) (var 5)))
      (negated (var 0) (added (var 0) (var 4) (var 5)))) (less (var 0) (var 1) (var 2) (var 4) (var 3))) :=
  closeUniv 6 (translated_order_negation _ _ _ _ _ _)
theorem actual_additive_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_additive_comparison_returned_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ≐
      fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) := closeUniv 6 (returned_translation_equal _ _ _ _ _ _)
theorem actual_additive_comparison_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ amp (var 1)) := closeUniv 6 (returned_cap _ _ _ _ _ _)
theorem original_additive_comparison_returned_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (QuadraticTowerMultiplicationNegative.source (var 0) (var 2) (var 3) (var 4) (var 1) ⟶
      Fm.iff (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))) ≐ zero)
        (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ zero)) :=
  closeUniv 6 (.impI (returned_negative_zero_iff _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerAdditiveComparison

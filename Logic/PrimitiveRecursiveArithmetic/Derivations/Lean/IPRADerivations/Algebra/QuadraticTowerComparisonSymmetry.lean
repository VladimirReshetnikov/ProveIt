import IPRADerivations.Algebra.QuadraticTowerSignNegation

/-!
# Actual comparisons at every numerical tower depth

The SAME constructed opposite differences are literal coefficientwise
negatives. The actual sign-negation law therefore gives symmetry of
sign-zero equality, reversal and strict asymmetry, and total comparison
at every internal depth. The real difference-height bound determines
the sign cap. Transitivity and the general ordered-quotient provider
remain separate; no coefficient-code equality for semantic zero is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerComparisonSymmetry

open_ipra
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficientArithmetic (added negated added_congr)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerScalarArrays (zeroArray)
open QuadraticTowerScalarBudget (amp)
open QuadraticTowerDifferenceIdentities (difference signDifference equivalent less)
open QuadraticTowerSignNegation (opposite opposite_congr opposite_zero opposite_two opposite_one opposite_involution)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem difference_sum_zero (h A C : PTm n) : Γ ⊢[PRAAx]
    added h (difference h A C) (difference h C A) ≐ zeroArray h :=
  (added_congr (.eqRefl h) (.eqRefl _) (QuadraticTowerMultiplicationCommutativity.added_commutative h C (negated h A))).eqTrans
    ((QuadraticTowerAdditionLaws.added_four h A (negated h C) (negated h A) C).eqTrans
      ((added_congr (.eqRefl h) (QuadraticTowerDifferenceIdentities.difference_self h A)
        ((QuadraticTowerMultiplicationCommutativity.added_commutative h (negated h C) C).eqTrans
          (QuadraticTowerDifferenceIdentities.difference_self h C))).eqTrans (QuadraticTowerMultiplicationZero.added_zero h)))

/-- Only actual constructed differences are identified by CODE equality. -/
theorem difference_swapped (h A C : PTm n) : Γ ⊢[PRAAx] difference h C A ≐ negated h (difference h A C) :=
  (QuadraticTowerArrayNormalization.normalized_added h C (negated h A)).eqSymm.eqTrans
    (QuadraticTowerMultiplicationNegative.inverse_unique h _ _ (difference_sum_zero h A C))

theorem difference_height (h A C b : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx] arrayHeight h (difference h A C) (amp b) :=
  QuadraticTowerMultiplicationHeight.added_height h A _ b ha (QuadraticTowerSignRecipe.negated_height h C b hc)

/-- Actual original comparisons use the SAME computed difference and cap. -/
theorem sign_swapped (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    signDifference h B D C A ≐ opposite (signDifference h B D A C) :=
  (QuadraticTowerSignRecipe.read_operand_congr h B (QuadraticTowerSignTable.table h B D) _ _ (difference_swapped h A C)).eqTrans
    (QuadraticTowerSignNegation.query_negative h B D _ (amp b) hb
      (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ hD (QuadraticTowerGrowth.amp_inflation b)) (difference_height h A C b ha hc))

theorem equivalent_symmetric (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (he : Γ ⊢[PRAAx] equivalent h B D A C) : Γ ⊢[PRAAx] equivalent h B D C A :=
  (sign_swapped h B D A C b hb hD ha hc).eqTrans ((opposite_congr he).eqTrans opposite_zero)

theorem equivalence_symmetry (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx] Fm.iff (equivalent h B D A C) (equivalent h B D C A) :=
  .andI (.impI (equivalent_symmetric h B D A C b hb.wk hD.wk ha.wk hc.wk Prf.hyp0))
    (.impI (equivalent_symmetric h B D C A b hb.wk hD.wk hc.wk ha.wk Prf.hyp0))

theorem less_negative_iff (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    Fm.iff (less h B D A C) (signDifference h B D A C ≐ two) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (opposite_involution _ (QuadraticTowerSignTable.query_bound _ _ _ _)).eqSymm.eqTrans
      ((opposite_congr ((sign_swapped h B D A C b hb.wk hD.wk ha.wk hc.wk).eqSymm.eqTrans Prf.hyp0)).eqTrans opposite_one)
  · exact (sign_swapped h B D A C b hb.wk hD.wk ha.wk hc.wk).eqTrans ((opposite_congr Prf.hyp0).eqTrans opposite_two)

theorem less_asymmetric (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) (hl : Γ ⊢[PRAAx] less h B D A C) : Γ ⊢[PRAAx] neg (less h B D C A) :=
  .impI (QuadraticIntegerOrder.one_two_absurd _ (Prf.hyp0.eqSymm.eqTrans
    (.impE (less_negative_iff h B D A C b hb.wk hD.wk ha.wk hc.wk).andE₁ hl.wk)))

theorem trichotomy (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx] less h B D A C ⋎ (less h B D C A ⋎ equivalent h B D A C) := by
  refine .orE (QuadraticTowerSignNegation.tag_cases (signDifference h B D A C) (QuadraticTowerSignTable.query_bound _ _ _ _)) ?_ ?_
  · exact .orI₂ (.orI₂ Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ Prf.hyp0)
    · exact .orI₁ ((sign_swapped h B D A C b hb.wk.wk hD.wk.wk ha.wk.wk hc.wk.wk).eqTrans
        ((opposite_congr Prf.hyp0).eqTrans opposite_two))


def input (h B D A C b : PTm n) : Fm PTm n := le (amp b) B ⋏ QuadraticTowerMultiplicationNegative.source h D A C b
ipra_subst input

/-- The comparison frontend computes B=amp(b) from original bounds. -/
def output (h b D A C : PTm n) : PTm n := pairT (difference h A C)
  (pairT (difference h C A) (pairT (signDifference h (amp b) D A C)
    (pairT (signDifference h (amp b) D C A) (amp b))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h b D A C : PTm n) : PTm n := PTm.app outputF ![h,b,D,A,C]
ipra_subst output
ipra_subst run

theorem program_at (h b D A C : PTm n) : Γ ⊢[PRAAx] run h b D A C ≐ output h b D A C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,b,D,A,C]
theorem returned_difference (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (run h b D A C) ≐ difference h A C :=
  (program_at _ _ _ _ _).fstE
theorem returned_tail (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (run h b D A C) ≐
    pairT (difference h C A) (pairT (signDifference h (amp b) D A C) (pairT (signDifference h (amp b) D C A) (amp b))) :=
  (program_at _ _ _ _ _).sndE
theorem returned_reverse (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h b D A C)) ≐ difference h C A :=
  (returned_tail _ _ _ _ _).fstE
theorem returned_tags (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h b D A C)) ≐
    pairT (signDifference h (amp b) D A C) (pairT (signDifference h (amp b) D C A) (amp b)) :=
  (returned_tail _ _ _ _ _).sndE
theorem returned_tag (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h b D A C))) ≐ signDifference h (amp b) D A C :=
  (returned_tags _ _ _ _ _).fstE
theorem returned_reverse_pair (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h b D A C))) ≐
    pairT (signDifference h (amp b) D C A) (amp b) :=
  (returned_tags _ _ _ _ _).sndE
theorem returned_reverse_tag (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run h b D A C)))) ≐ signDifference h (amp b) D C A :=
  (returned_reverse_pair _ _ _ _ _).fstE
theorem returned_cap (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run h b D A C)))) ≐ amp b :=
  (returned_reverse_pair _ _ _ _ _).sndE

theorem returned_trichotomy (h b D A C : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerMultiplicationNegative.source h D A C b) : Γ ⊢[PRAAx]
    (fstT (sndT (sndT (sndT (run h b D A C)))) ≐ one) ⋎
      ((fstT (sndT (sndT (run h b D A C))) ≐ one) ⋎ (fstT (sndT (sndT (run h b D A C))) ≐ zero)) := by
  refine .orE (trichotomy h (amp b) D A C b (le_refl _) p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂) ?_ ?_
  · exact .orI₁ ((returned_reverse_tag _ _ _ _ _).eqTrans Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ ((returned_tag _ _ _ _ _).eqTrans Prf.hyp0))
    · exact .orI₂ (.orI₂ ((returned_tag _ _ _ _ _).eqTrans Prf.hyp0))

theorem returned_zero_iff (h b D A C : PTm n) (p : Γ ⊢[PRAAx] QuadraticTowerMultiplicationNegative.source h D A C b) : Γ ⊢[PRAAx]
    Fm.iff (fstT (sndT (sndT (run h b D A C))) ≐ zero) (fstT (sndT (sndT (sndT (run h b D A C)))) ≐ zero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (returned_reverse_tag _ _ _ _ _).eqTrans
      (equivalent_symmetric h (amp b) D A C b (le_refl _) p.andE₁.wk p.andE₂.andE₁.wk p.andE₂.andE₂.wk
        ((returned_tag _ _ _ _ _).eqSymm.eqTrans Prf.hyp0))
  · exact (returned_tag _ _ _ _ _).eqTrans
      (equivalent_symmetric h (amp b) D C A b (le_refl _) p.andE₁.wk p.andE₂.andE₂.wk p.andE₂.andE₁.wk
        ((returned_reverse_tag _ _ _ _ _).eqSymm.eqTrans Prf.hyp0))

theorem actual_constructed_opposite_differences_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (difference (var 0) (var 2) (var 1) ≐ negated (var 0) (difference (var 0) (var 1) (var 2))) :=
  closeUniv 3 (difference_swapped _ _ _)
theorem original_uniform_comparison_sign_reversal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      signDifference (var 0) (var 1) (var 2) (var 4) (var 3) ≐ opposite (signDifference (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (sign_swapped _ _ _ _ _ (var 5) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_uniform_comparison_equivalence_symmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      Fm.iff (equivalent (var 0) (var 1) (var 2) (var 3) (var 4)) (equivalent (var 0) (var 1) (var 2) (var 4) (var 3))) :=
  closeUniv 6 (.impI (equivalence_symmetry _ _ _ _ _ (var 5) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_uniform_comparison_asymmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ less (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      neg (less (var 0) (var 1) (var 2) (var 4) (var 3))) :=
  closeUniv 6 (.impI (.impI (less_asymmetric _ _ _ _ _ (var 5) Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0)))
theorem original_uniform_comparison_trichotomy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      less (var 0) (var 1) (var 2) (var 3) (var 4) ⋎
        (less (var 0) (var 1) (var 2) (var 4) (var 3) ⋎ equivalent (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (trichotomy _ _ _ _ _ (var 5) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_uniform_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_uniform_comparison_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ amp (var 1)) := closeUniv 5 (returned_cap _ _ _ _ _)
theorem original_computed_uniform_comparison_trichotomy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerMultiplicationNegative.source (var 0) (var 2) (var 3) (var 4) (var 1) ⟶
      (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ one) ⋎
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ one) ⋎
          (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ zero))) :=
  closeUniv 5 (.impI (returned_trichotomy _ _ _ _ _ Prf.hyp0))
theorem original_computed_uniform_comparison_zero_symmetry_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (QuadraticTowerMultiplicationNegative.source (var 0) (var 2) (var 3) (var 4) (var 1) ⟶
      Fm.iff (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ zero)
        (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ zero)) :=
  closeUniv 5 (.impI (returned_zero_iff _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerComparisonSymmetry

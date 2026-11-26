import IPRADerivations.Algebra.QuadraticTowerMultiplicationRecurrence
import IPRADerivations.Algebra.QuadraticTowerMultiplicationDistributivity
import IPRADerivations.Algebra.QuadraticTowerDifferenceIdentities

/-!
# Actual numerical-tower multiplication by coefficientwise negatives

Literal identities concern the SAME checked array constructors and the
actual multiplication query. Raw operands are retained, while outputs
are normalized by proved query laws. Actual sufficient caps follow from
the original operation-height bounds. This supplies the actual norm
invariance needed for a later uniform sign-negation induction; no
arbitrary-depth mathematical sign correctness is claimed here.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationNegative

open_ipra
open LeanProofs.IPRA.Analysis
open QuadraticTowerArrayCodec (arrayHeight normalized)
open QuadraticTowerCoefficientArithmetic (added negated added_congr negated_congr)
open QuadraticTowerMultiplicationTable (query budget leftHalf rightHalf)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerScalarArrays (zeroArray)
open QuadraticTowerScalarBudget (amp)
open QuadraticTowerAdditionLaws (normalized_congr added_associative)
open QuadraticTowerMultiplicationCommutativity (added_commutative)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- This is a literal identity between actual constructed arrays. -/
theorem added_negative_cancel (h A C : PTm n) : Γ ⊢[PRAAx]
    added h (negated h A) (added h A C) ≐ normalized h C :=
  (added_associative h (negated h A) A C).eqSymm.eqTrans
    ((added_congr (.eqRefl h) (added_commutative h (negated h A) A) (.eqRefl C)).eqTrans
      ((added_congr (.eqRefl h) (QuadraticTowerDifferenceIdentities.difference_self h A) (.eqRefl C)).eqTrans
        ((added_commutative h (zeroArray h) C).eqTrans (QuadraticTowerMultiplicationUnit.added_zero_normalized h C))))

/-- Raw Q is normalized; no arbitrary-code additive-inverse eta is used. -/
theorem inverse_unique (h P Q : PTm n) (e : Γ ⊢[PRAAx] added h P Q ≐ zeroArray h) : Γ ⊢[PRAAx]
    normalized h Q ≐ negated h P :=
  (added_negative_cancel h P Q).eqSymm.eqTrans
    ((added_congr (.eqRefl h) (.eqRefl _) e).eqTrans
      ((QuadraticTowerMultiplicationUnit.added_zero_normalized h (negated h P)).eqTrans
        (QuadraticTowerArrayNormalization.normalized_negated h P)))

theorem negative_involution (h A : PTm n) : Γ ⊢[PRAAx] negated h (negated h A) ≐ normalized h A :=
  (inverse_unique h (negated h A) A
    ((added_commutative h (negated h A) A).eqTrans (QuadraticTowerDifferenceIdentities.difference_self h A))).eqSymm

theorem query_operands_congr (h B D : PTm n) {A A' C C' : PTm n}
    (ha : Γ ⊢[PRAAx] A ≐ A') (hc : Γ ⊢[PRAAx] C ≐ C') : Γ ⊢[PRAAx]
    query h B D A C ≐ query h B D A' C' :=
  QuadraticTowerMultiplicationCoherence.lookup_congr (.eqRefl h) (.eqRefl B) (.eqRefl _) ha hc

/-- The actual negative product follows from actual distributivity and
zero absorption, with a genuinely normalized returned array. -/
theorem query_right_negative (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    query h B D A (negated h C) ≐ negated h (query h B D A C) := by
  have small := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  have neg := QuadraticTowerSignRecipe.negated_height h C b hc
  have sum : Γ ⊢[PRAAx] added h (query h B D A C) (query h B D A (negated h C)) ≐ zeroArray h :=
    (QuadraticTowerMultiplicationDistributivity.query_right_distributive h B D A C (negated h C) b hb hD ha hc neg).eqSymm.eqTrans
      ((query_operands_congr h B D (.eqRefl A) (QuadraticTowerDifferenceIdentities.difference_self h C)).eqTrans
        (QuadraticTowerMultiplicationZero.query_right_zero h B D A b small
          (QuadraticTowerMultiplicationUnit.array_height_floor h A b ha) hD ha))
  exact (QuadraticTowerMultiplicationRecurrence.normalized_query h B D A (negated h C)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha small)
    (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ neg small)).eqSymm.eqTrans (inverse_unique h _ _ sum)

theorem query_left_negative (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    query h B D (negated h A) C ≐ negated h (query h B D A C) := by
  have small := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  exact (QuadraticTowerMultiplicationCommutativity.query_commutative h B D (negated h A) C b small hD
    (QuadraticTowerSignRecipe.negated_height h A b ha) hc).eqTrans
      ((query_right_negative h B D C A b hb hD hc ha).eqTrans
        (negated_congr (.eqRefl h) (QuadraticTowerMultiplicationCommutativity.query_commutative h B D C A b small hD hc ha)))

theorem query_double_negative (h B D A C b : PTm n) (hb : Γ ⊢[PRAAx] le (amp b) B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D h b) (ha : Γ ⊢[PRAAx] arrayHeight h A b)
    (hc : Γ ⊢[PRAAx] arrayHeight h C b) : Γ ⊢[PRAAx]
    query h B D (negated h A) (negated h C) ≐ query h B D A C := by
  have small := le_trans (QuadraticTowerGrowth.amp_inflation b) hb
  exact (query_right_negative h B D (negated h A) C b hb hD (QuadraticTowerSignRecipe.negated_height h A b ha) hc).eqTrans
    ((negated_congr (.eqRefl h) (query_left_negative h B D A C b hb hD ha hc)).eqTrans
      ((negative_involution h _).eqTrans (QuadraticTowerMultiplicationRecurrence.normalized_query h B D A C
        (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ ha small)
        (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ hc small))))


/-- True constructed half identities retain the original raw array. -/
theorem left_negative (h A : PTm n) : Γ ⊢[PRAAx]
    leftHalf h (negated (succ h) A) ≐ negated h (leftHalf h A) := by
  apply Foundations.SequenceEquality.sequence_equal Foundations.RealizerComposition.sliceBody
    QuadraticTowerCoefficientArithmetic.negativeBody (QuadraticTowerCoefficients.width h)
      (pairT zero (negated (succ h) A)) (leftHalf h A)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (QuadraticTowerCoefficients.width (Syn.shift h)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (QuadraticTowerCoefficients.width (succ (Syn.shift h))) :=
    lt_of_lt_of_le Prf.hyp0 (QuadraticTowerCoefficientArithmetic.width_le_next _)
  have actual := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ)
    (negated (succ (Syn.shift h)) (Syn.shift A)) zero (var 0)).eqTrans
      ((Foundations.SequenceComposition.entry_congr (.eqRefl _) (zero_add _)).eqTrans
        (QuadraticTowerCoefficientArithmetic.negated_lookup _ _ _ hi))
  have source : Δ ⊢[PRAAx] entry (leftHalf (Syn.shift h) (Syn.shift A)) (var 0) ≐ entry (Syn.shift A) (var 0) :=
    (Foundations.RealizerComposition.slice_lookup _ zero _ _ Prf.hyp0).eqTrans
      (Foundations.SequenceComposition.entry_congr (.eqRefl _) (zero_add _))
  simpa only [Δ,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    QuadraticTowerCoefficientArithmetic.subst_negated,QuadraticTowerCoefficientArithmetic.negative_body_at,
    QuadraticTowerMultiplicationTable.subst_leftHalf,QuadraticTowerCoefficients.subst_width] using
      actual.eqTrans (RationalAlgebra.negative_congr source.eqSymm)

theorem right_negative (h A : PTm n) : Γ ⊢[PRAAx]
    rightHalf h (negated (succ h) A) ≐ negated h (rightHalf h A) := by
  apply Foundations.SequenceEquality.sequence_equal Foundations.RealizerComposition.sliceBody
    QuadraticTowerCoefficientArithmetic.negativeBody (QuadraticTowerCoefficients.width h)
      (pairT (QuadraticTowerCoefficients.width h) (negated (succ h) A)) (rightHalf h A)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (QuadraticTowerCoefficients.width (Syn.shift h)) :: Γ.map Fm.shift
  have hi := QuadraticTowerCoefficientArithmetic.right_half_bound (Γ := Δ) (Syn.shift h) (var 0) Prf.hyp0
  have actual := (Foundations.RealizerComposition.sliceBody_at (Γ := Δ)
    (negated (succ (Syn.shift h)) (Syn.shift A)) (QuadraticTowerCoefficients.width (Syn.shift h)) (var 0)).eqTrans
      (QuadraticTowerCoefficientArithmetic.negated_lookup _ _ _ hi)
  have source : Δ ⊢[PRAAx] entry (rightHalf (Syn.shift h) (Syn.shift A)) (var 0) ≐
      entry (Syn.shift A) (QuadraticTowerCoefficients.width (Syn.shift h)+var 0) :=
    Foundations.RealizerComposition.slice_lookup _ _ _ _ Prf.hyp0
  simpa only [Δ,Syn.shift,subst_pairT,ConciseIPRA.PTm.subst_succ,QuadraticTowerCoefficients.subst_width,
    QuadraticTowerCoefficientArithmetic.subst_negated,QuadraticTowerCoefficientArithmetic.negative_body_at,
    QuadraticTowerMultiplicationTable.subst_rightHalf,QuadraticTowerMultiplicationTable.rightHalf,
    Foundations.RealizerComposition.subst_slice] using actual.eqTrans (RationalAlgebra.negative_congr source.eqSymm)

/-- The sign recipe's SAME actual norm is invariant under negation.
The actual lower cap covers amp(b) by its proved path budget. -/
theorem norm_negative (h B D A b : PTm n) (hb : Γ ⊢[PRAAx] le b B)
    (hD : Γ ⊢[PRAAx] radicandsHeight D (succ h) b) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A b) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.norm h B D (negated (succ h) A) ≐ QuadraticTowerSignRecipe.norm h B D A := by
  let K := budget h B D
  have lower := QuadraticTowerMultiplicationHeight.radicands_prefix D h (succ h) b hD (le_succ_self h)
  have left := QuadraticTowerMultiplicationHeight.left_height h A b ha
  have right := QuadraticTowerMultiplicationHeight.right_height h A b ha
  have kb : Γ ⊢[PRAAx] le (amp b) K :=
    le_trans (QuadraticTowerGrowth.amp_mono (QuadraticTowerGrowth.growth_inflation (QuadraticTowerGrowth.path h) b))
      (QuadraticTowerMultiplicationDistributivity.lower_sum_budget h B D b hb)
  have aa := (query_operands_congr h K D (left_negative h A) (left_negative h A)).eqTrans
    (query_double_negative h K D (leftHalf h A) (leftHalf h A) b kb lower left left)
  have bb := (query_operands_congr h K D (right_negative h A) (right_negative h A)).eqTrans
    (query_double_negative h K D (rightHalf h A) (rightHalf h A) b kb lower right right)
  exact added_congr (.eqRefl h) aa (negated_congr (.eqRefl h) (query_operands_congr h K D (.eqRefl (entry D h)) bb))


def source (h D A C b : PTm n) : Fm PTm n := radicandsHeight D h b ⋏ (arrayHeight h A b ⋏ arrayHeight h C b)
def input (h B D A C b : PTm n) : Fm PTm n := le (amp b) B ⋏ source h D A C b
ipra_subst source
ipra_subst input

theorem query_negatives (h B D A C b : PTm n) (p : Γ ⊢[PRAAx] input h B D A C b) : Γ ⊢[PRAAx]
    (query h B D A (negated h C) ≐ negated h (query h B D A C)) ⋏
      ((query h B D (negated h A) C ≐ negated h (query h B D A C)) ⋏
        (query h B D (negated h A) (negated h C) ≐ query h B D A C)) :=
  .andI (query_right_negative _ _ _ _ _ b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂.andE₁ p.andE₂.andE₂.andE₂)
    (.andI (query_left_negative _ _ _ _ _ b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂.andE₁ p.andE₂.andE₂.andE₂)
      (query_double_negative _ _ _ _ _ b p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂.andE₁ p.andE₂.andE₂.andE₂))

/-- Actual M=amp(b) frontend, retaining its SAME computed queries. -/
def output (h b D A C : PTm n) : PTm n := pairT (query h (amp b) D A (negated h C))
  (pairT (negated h (query h (amp b) D A C))
    (pairT (query h (amp b) D (negated h A) (negated h C)) (pairT (query h (amp b) D A C) (amp b))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (h b D A C : PTm n) : PTm n := PTm.app outputF ![h,b,D,A,C]
ipra_subst output
ipra_subst run

theorem program_at (h b D A C : PTm n) : Γ ⊢[PRAAx] run h b D A C ≐ output h b D A C := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![h,b,D,A,C]
theorem returned_right (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (run h b D A C) ≐ query h (amp b) D A (negated h C) :=
  (program_at _ _ _ _ _).fstE
theorem returned_tail (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (run h b D A C) ≐
    pairT (negated h (query h (amp b) D A C))
      (pairT (query h (amp b) D (negated h A) (negated h C)) (pairT (query h (amp b) D A C) (amp b))) :=
  (program_at _ _ _ _ _).sndE
theorem returned_negative (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h b D A C)) ≐ negated h (query h (amp b) D A C) :=
  (returned_tail _ _ _ _ _).fstE
theorem returned_products (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h b D A C)) ≐
    pairT (query h (amp b) D (negated h A) (negated h C)) (pairT (query h (amp b) D A C) (amp b)) :=
  (returned_tail _ _ _ _ _).sndE
theorem returned_double (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h b D A C))) ≐ query h (amp b) D (negated h A) (negated h C) :=
  (returned_products _ _ _ _ _).fstE
theorem returned_original_pair (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h b D A C))) ≐ pairT (query h (amp b) D A C) (amp b) :=
  (returned_products _ _ _ _ _).sndE
theorem returned_original (h b D A C : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run h b D A C)))) ≐ query h (amp b) D A C :=
  (returned_original_pair _ _ _ _ _).fstE
theorem returned_cap (h b D A C : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run h b D A C)))) ≐ amp b :=
  (returned_original_pair _ _ _ _ _).sndE

theorem returned_equalities (h b D A C : PTm n) (p : Γ ⊢[PRAAx] source h D A C b) : Γ ⊢[PRAAx]
    (fstT (run h b D A C) ≐ fstT (sndT (run h b D A C))) ⋏
      (fstT (sndT (sndT (run h b D A C))) ≐ fstT (sndT (sndT (sndT (run h b D A C))))) :=
  .andI ((returned_right _ _ _ _ _).eqTrans
    ((query_right_negative _ _ _ _ _ b (le_refl _) p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂).eqTrans (returned_negative _ _ _ _ _).eqSymm))
    ((returned_double _ _ _ _ _).eqTrans
      ((query_double_negative _ _ _ _ _ b (le_refl _) p.andE₁ p.andE₂.andE₁ p.andE₂.andE₂).eqTrans (returned_original _ _ _ _ _).eqSymm))

theorem actual_constructed_additive_inverse_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (added (var 0) (var 1) (var 2) ≐ zeroArray (var 0) ⟶ normalized (var 0) (var 2) ≐ negated (var 0) (var 1)) :=
  closeUniv 3 (.impI (inverse_unique _ _ _ Prf.hyp0))
theorem actual_constructed_negative_involution_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (negated (var 0) (negated (var 0) (var 1)) ≐ normalized (var 0) (var 1)) := closeUniv 2 (negative_involution _ _)
theorem original_actual_multiplication_negatives_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      (query (var 0) (var 1) (var 2) (var 3) (negated (var 0) (var 4)) ≐ negated (var 0) (query (var 0) (var 1) (var 2) (var 3) (var 4))) ⋏
        ((query (var 0) (var 1) (var 2) (negated (var 0) (var 3)) (var 4) ≐ negated (var 0) (query (var 0) (var 1) (var 2) (var 3) (var 4))) ⋏
          (query (var 0) (var 1) (var 2) (negated (var 0) (var 3)) (negated (var 0) (var 4)) ≐ query (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (query_negatives _ _ _ _ _ _ Prf.hyp0))
theorem actual_constructed_negative_halves_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((leftHalf (var 0) (negated (succ (var 0)) (var 1)) ≐ negated (var 0) (leftHalf (var 0) (var 1))) ⋏
      (rightHalf (var 0) (negated (succ (var 0)) (var 1)) ≐ negated (var 0) (rightHalf (var 0) (var 1)))) :=
  closeUniv 2 (.andI (left_negative _ _) (right_negative _ _))
theorem original_actual_sign_norm_negative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶ radicandsHeight (var 2) (succ (var 0)) (var 4) ⟶ arrayHeight (succ (var 0)) (var 3) (var 4) ⟶
      QuadraticTowerSignRecipe.norm (var 0) (var 1) (var 2) (negated (succ (var 0)) (var 3)) ≐ QuadraticTowerSignRecipe.norm (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (norm_negative _ _ _ _ (var 4) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem actual_negative_multiplication_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)
theorem actual_negative_multiplication_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))) ≐ amp (var 1)) := closeUniv 5 (returned_cap _ _ _ _ _)
theorem original_returned_negative_multiplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) (var 4) (var 1) ⟶
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ⋏
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.impI (returned_equalities _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Algebra.QuadraticTowerMultiplicationNegative

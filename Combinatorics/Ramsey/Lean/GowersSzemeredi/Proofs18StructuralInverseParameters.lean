import GowersSzemeredi.Proofs17LocalizationFromDimensionInduction
import GowersSzemeredi.Proofs18FejerCubicDiscrepancy

/-! Recursive quantitative parameters for the inverse induction starting at
the proved quadratic and Fejer cubic theorems. These definitions do not assume Section 16;
their positivity and the admissible exponent range hold unconditionally. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Weakening the input obstruction, discrepancy, average-size exponent, or
modulus threshold preserves the function inverse bound. -/
theorem FunctionDiscrepancyBound.mono {k : Nat}
    {alpha alpha' beta beta' sigma sigma' T T' : Real}
    (h : FunctionDiscrepancyBound k alpha beta sigma T)
    (hα : alpha ≤ alpha') (hβ : beta' ≤ beta) (hσ : sigma' ≤ sigma)
    (hT : T ≤ T') : FunctionDiscrepancyBound k alpha' beta' sigma' T' := by
  intro N _ _ hN f hf hnot
  obtain ⟨M, Q, hp, hproper, havg, hdis⟩ :=
    h N (hT.trans hN) f hf (fun hu => hnot (uniformOfDegree_mono_parameter hα hu))
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast (show 1 ≤ N from NeZero.one_le)
  exact ⟨M, Q, hp, hproper, (Real.rpow_le_rpow_of_exponent_le hN1 hσ).trans havg,
    (mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg N)).trans hdis⟩

/-- Clip only the obstruction parameter to the structural theorem's range. -/
def structuralInverseInput (alpha : Real) : Real := min alpha (1 / 2)

theorem structuralInverseInput_pos {alpha : Real} (hα : 0 < alpha) :
    0 < structuralInverseInput alpha := lt_min hα (by norm_num)

/-- Parameter passed to the lower-degree inverse theorem after localization. -/
def structuralInverseLowerInput (alpha : Real) (k : Nat) : Real :=
  (dimensionLocalizationParameter (structuralInverseInput alpha) k / 2) /
    (2 * (k + 2 : Nat) : Real) ^ (k + 2)

theorem structuralInverseLowerInput_pos {alpha : Real} (hα : 0 < alpha) (k : Nat) :
    0 < structuralInverseLowerInput alpha k := by
  have hp := dimensionLocalizationParameter_pos (structuralInverseInput_pos hα) k
  unfold structuralInverseLowerInput
  positivity

/-- Index n corresponds to uniformity degree n+2. All losses in discrepancy
are retained; the two base cases are the explicit quadratic and improved cubic bounds. -/
def structuralInverseParameter : Nat → Real → Real
  | 0, alpha => quadraticDiscrepancyParameter (structuralInverseInput alpha)
  | 1, alpha => fejerCubicDiscrepancyParameter (structuralInverseInput alpha)
  | n + 2, alpha =>
      dimensionLocalizationParameter (structuralInverseInput alpha) (n + 3) *
        structuralInverseParameter (n + 1) (structuralInverseLowerInput alpha (n + 3)) / 4

/-- The power of N retained by the recursive partition. Capping at one
ensures every induction step satisfies the local assembly's exponent range. -/
def structuralInverseExponent : Nat → Real → Real
  | 0, alpha => min (quadraticDiscrepancyExponent (structuralInverseInput alpha)) 1
  | 1, alpha => min (fejerCubicDiscrepancyExponent (structuralInverseInput alpha)) 1
  | n + 2, alpha => min
      (inverseStepExponent (n + 3) (section16ShortBoxExponent (structuralInverseInput alpha) (n + 3))
        (structuralInverseExponent (n + 1) (structuralInverseLowerInput alpha (n + 3)))) 1

theorem structuralInverseParameter_pos (n : Nat) {alpha : Real} (hα : 0 < alpha) :
    0 < structuralInverseParameter n alpha := by
  induction n generalizing alpha with
  | zero =>
      have hp := structuralInverseInput_pos hα
      dsimp [structuralInverseParameter, quadraticDiscrepancyParameter]
      positivity
  | succ n ih =>
    cases n with
    | zero => exact fejerCubicDiscrepancyParameter_pos (structuralInverseInput_pos hα)
    | succ n =>
      have hp := dimensionLocalizationParameter_pos (structuralInverseInput_pos hα) (n + 3)
      have hb := ih (structuralInverseLowerInput_pos hα (n + 3))
      simpa only [structuralInverseParameter] using div_pos (mul_pos hp hb) (by norm_num : (0 : Real) < 4)

theorem structuralInverseExponent_pos (n : Nat) {alpha : Real} (hα : 0 < alpha) :
    0 < structuralInverseExponent n alpha := by
  induction n generalizing alpha with
  | zero =>
      have he := (quadratic_frequency_exponent_bounds (structuralInverseInput_pos hα)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))).1
      exact lt_min (div_pos he (by norm_num)) zero_lt_one
  | succ n ih =>
    cases n with
    | zero =>
      exact lt_min (fejerCubicDiscrepancyExponent_pos (structuralInverseInput_pos hα)
        ((min_le_right _ _).trans (by norm_num : (1 : Real) / 2 ≤ 1))) zero_lt_one
    | succ n =>
      have hs := ih (structuralInverseLowerInput_pos hα (n + 3))
      have he := section16ShortBoxExponent_pos (structuralInverseInput_pos hα) (n + 3)
      have hK : (0 : Real) < polynomialPartitionConstant (n + 3 + 1) := by
        unfold polynomialPartitionConstant
        positivity
      apply lt_min _ zero_lt_one
      dsimp [inverseStepExponent, phaseInverseExponent]
      positivity

theorem structuralInverseExponent_le_one (n : Nat) (alpha : Real) :
    structuralInverseExponent n alpha ≤ 1 := by
  cases n with
  | zero => exact min_le_right _ _
  | succ n => cases n <;> exact min_le_right _ _

end LeanProofs.GowersSzemeredi

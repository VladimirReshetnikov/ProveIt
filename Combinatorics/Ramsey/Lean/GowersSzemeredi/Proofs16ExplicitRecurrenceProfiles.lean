import GowersSzemeredi.Proofs05ExplicitPartitionBounds
import GowersSzemeredi.Proofs16WeylBudgetGrowth
import GowersSzemeredi.Proofs16PolynomialRecurrenceProfile
import GowersSzemeredi.Proofs16FamilyLemma6
import GowersSzemeredi.Proofs13CoefficientExtraction
import GowersSzemeredi.Proofs13LargeScaleExtraction
import GowersSzemeredi.Proofs13UniformEdgeModels
import GowersSzemeredi.Proofs16FaceInduction
import GowersSzemeredi.Proofs16RoundedPowerWidth

/-! The explicit recurrence data used by the final quantitative theorem.

The partition construction and its numerical bounds need neither the
length-six Szemeredi theorem nor the older variety-structure route. Keeping
these inputs together lets the final covering proof import them directly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The explicit family recurrence profile in every dimension. -/
theorem section16RecurrenceProfileWith_explicit (k : Nat) :
    Section16RecurrenceProfileWith k
      (familyRecThr k (Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1))))
        ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))))
      (familyRecExp k ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))) := by
  have hK := two_le_multiaffinePartitionK (k + 1) (2 ^ (k + 1))
  have hp := multiaffinePartitionP_pos (k + 1) (2 ^ (k + 1))
  exact polynomialSection16RecurrenceProfileAt_of k hK (Nat.mul_pos (Nat.succ_pos k) hp)
    (commonDiffPartitionTwoBoundAt_of k hK hp
      (commonDiffPartitionBoundAt_of k hK hp
        (multilinearPartitionBoundAt_explicit (k + 1) (Nat.succ_pos k))))

theorem schmidtWeylD_le_gen (j : Nat) : schmidtWeylD j ≤ weylBudgetLog j + weylBudgetDeg j + 1 := by
  unfold schmidtWeylD
  have := weylBudgetPolynomial_natDegree_le_gen j
  omega

theorem schmidtWeylC_le_gen (j : Nat) :
    (schmidtWeylC j : Real) ≤ 2 ^ (weylBudgetLog j + 2 * schmidtWeylD j) := by
  have hA : schmidtWeylA j ≤ 2 ^ weylBudgetLog j := by
    unfold schmidtWeylA; exact weylBudgetPolynomial_eval_one_le_gen j
  have h3 : 3 ^ schmidtWeylD j ≤ 2 ^ (2 * schmidtWeylD j) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
  have hC : schmidtWeylC j ≤ 2 ^ (weylBudgetLog j + 2 * schmidtWeylD j) := by
    unfold schmidtWeylC
    rw [pow_add]
    exact Nat.mul_le_mul hA h3
  exact_mod_cast hC

/-- **The Schmidt base constant in every degree.** -/
theorem schmidtMonomialK_le_gen (j : Nat) : schmidtMonomialK j ≤ 2 ^ schmidtKExp j := by
  have hC := schmidtWeylC_le_gen j
  have hD := schmidtWeylD_le_gen j
  unfold schmidtMonomialK OAI.Erdos3.schmidtRecurrenceBase OAI.Erdos3.schmidtDegreeConstant
    OAI.Erdos3.schmidtRecurrenceExponent
  refine (schmidt_base_formula_le_gen _ _ _ hC).trans (pow_le_pow_right₀ (by norm_num) ?_)
  unfold schmidtKExp
  omega

/-- **The Schmidt exponent constant in every degree.** -/
theorem schmidtMonomialP_le_gen (j : Nat) : schmidtMonomialP j ≤ schmidtPBnd j := by
  have hD := schmidtWeylD_le_gen j
  unfold schmidtMonomialP OAI.Erdos3.schmidtRecurrenceExponent schmidtPBnd
  omega

/-- **The family-lemma constants are at most `2^(2^(2^(k+5)))`.** -/
theorem explicit_family_constants_le (k : Nat) :
    ((⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊ : Nat) : Real) +
        (((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)) : Nat) : Real) ≤
      2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) := by
  have hU : uniformSchmidtK (k + 1) ≤ 2 ^ (schmidtKExp k + k + 2) := by
    have h := uniformSchmidtK_le_of (k := k + 1) (B := 2 ^ schmidtKExp k) fun j =>
      (schmidtMonomialK_le_gen j).trans
        (pow_le_pow_right₀ (by norm_num) (schmidtKExp_mono (by have := j.isLt; omega)))
    push_cast at h
    exact h.trans (uniform_base_le k (schmidtKExp k)).1
  have hMK := multiaffinePartitionK_le_of hU (uniform_base_le k (schmidtKExp k)).2 (2 ^ (k + 1))
  have hPu : uniformSchmidtP (k + 1) ≤ 1 + (k + 1) * schmidtPBnd k :=
    uniformSchmidtP_le_of fun j =>
      (schmidtMonomialP_le_gen j).trans (schmidtPBnd_mono (by have := j.isLt; omega))
  exact family_constants_tower_le k hMK hPu (multiaffinePartitionP_le_pow (k + 1) (2 ^ (k + 1)))

end LeanProofs.GowersSzemeredi

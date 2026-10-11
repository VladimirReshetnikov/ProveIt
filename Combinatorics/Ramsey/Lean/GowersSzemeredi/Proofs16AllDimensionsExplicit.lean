import GowersSzemeredi.Proofs16AllDimensions
import GowersSzemeredi.Proofs16WeylBudgetGrowth
import GowersSzemeredi.Proofs16ExplicitConstantBounds
import GowersSzemeredi.Proofs18LengthSixExplicit

/-! **Theorem 16.2 and Corollary 16.11, unconditionally, in every dimension.**

This module is a bridge. `theorem_16_2_of_profiles_all` (light, kernel-checked
locally) needs:
* the recurrence profiles in every dimension `k ≥ 1`. These come from
  `section16RecurrenceProfileWith_explicit k`, at
  `Kc k = ⌈multiaffinePartitionK (k+1) (2^(k+1))⌉` and
  `pc k = (k+1)·multiaffinePartitionP (k+1) (2^(k+1))`;
* the bound `Kc k + pc k ≤ 2^(2^(2^(k+5)))` (`explicit_family_constants_le`).

The constant bound follows the Schmidt layer down to the Weyl budget:
* `schmidtWeylD_le_gen` and `schmidtWeylC_le_gen` come from the light bounds
  on `weylBudgetPolynomial` in every degree;
* `schmidtMonomialK_le_gen` uses the symbolic Schmidt formula
  `schmidt_base_formula_le_gen`; `schmidtMonomialP_le_gen` is direct;
* `uniformSchmidtK_le_of`, `uniformSchmidtP_le_of`,
  `multiaffinePartitionK_le_of` and `multiaffinePartitionP_le_pow` give the
  partition constants, and `family_constants_tower_le` closes the
  arithmetic.

The imports reach the port's Schmidt constants and the explicit profiles, so
this module is checked on the full-verification host. Every step is a
definitional unfolding or an instantiation of a kernel-checked statement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

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

/-- **Theorem 16.2 and Corollary 16.11 in every dimension.** -/
theorem theorem_16_2_and_corollary_16_11 : theorem_16_2 ∧ corollary_16_11 :=
  theorem_16_2_of_profiles_all
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k)

/-- **Theorem 16.2.** -/
theorem theorem_16_2_explicit : theorem_16_2 := theorem_16_2_and_corollary_16_11.1

/-- **Corollary 16.11.** -/
theorem corollary_16_11_explicit : corollary_16_11 := theorem_16_2_and_corollary_16_11.2

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16VarietyBudgetedPiece
import GowersSzemeredi.Proofs05WeylConstantBounds
import GowersSzemeredi.Proofs16VarietyEventualThree

/-! Theorem 16.2 and Corollary 16.11 in dimension three from deep variety structure.

`Proofs16VarietyBudgetedPiece` proves both statements from
`MilicevicDeepVarietyStructure D`, `D ≤ 2^64`, and numeric bounds on the four
named constants. This module discharges those bounds. Through the port's
definitions, each per-degree Schmidt constant is
`schmidtRecurrenceBase (A_j·3^{d_j}) d_j`, where
* `A_j < 2^192` and `d_j ≤ 256` (`Proofs05WeylConstantBounds`), so
  `C_j = A_j·3^{d_j} ≤ 2^704`;
* `schmidt_base_formula_le` then gives `schmidtMonomialK j ≤ 2^1600`, and
  `schmidtMonomialP j = 15(d_j+1)+23 ≤ 3878`;
* `explicit_constants_le_of` bounds the four constants by `2^1700`.

The eventual forms (`theorem_16_2_at_three_of_eventually`, the corollary) take
the deep structure as the corpus pipeline proves it: eventually in prime
moduli, with a polynomial bound `Bnd c ≤ (4/c)^K`, `K ≤ 2^64`.

The module unfolds the port's `schmidtRecurrenceBase`, so it is checked on the
full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem schmidtWeylD_le (j : Nat) (hj : j ≤ 2) : schmidtWeylD j ≤ 256 := by
  have := weylBudgetPolynomial_natDegree_lt j hj
  unfold schmidtWeylD
  omega

theorem schmidtWeylC_le (j : Nat) (hj : j ≤ 2) : schmidtWeylC j ≤ 2 ^ 704 := by
  have hA : schmidtWeylA j ≤ 2 ^ 192 := (weylBudgetPolynomial_eval_one_lt j hj).le
  have hd := schmidtWeylD_le j hj
  have h3 : 3 ^ schmidtWeylD j ≤ 2 ^ 512 :=
    calc 3 ^ schmidtWeylD j ≤ 4 ^ schmidtWeylD j := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * schmidtWeylD j) := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold schmidtWeylC
  calc schmidtWeylA j * 3 ^ schmidtWeylD j ≤ 2 ^ 192 * 2 ^ 512 := Nat.mul_le_mul hA h3
    _ = 2 ^ 704 := by rw [← pow_add]

/-- **The per-degree Schmidt base constants are at most `2^1600`.** -/
theorem schmidtMonomialK_le (j : Nat) (hj : j ≤ 2) : schmidtMonomialK j ≤ 2 ^ 1600 := by
  have hC : ((schmidtWeylC j : Nat) : Real) ≤ 2 ^ 704 := by
    exact_mod_cast schmidtWeylC_le j hj
  unfold schmidtMonomialK OAI.Erdos3.schmidtRecurrenceBase OAI.Erdos3.schmidtDegreeConstant
    OAI.Erdos3.schmidtRecurrenceExponent
  exact schmidt_base_formula_le _ _ hC (schmidtWeylD_le j hj)

/-- **The per-degree Schmidt exponent constants are at most `3878`.** -/
theorem schmidtMonomialP_le (j : Nat) (hj : j ≤ 2) : schmidtMonomialP j ≤ 3878 := by
  have hd := schmidtWeylD_le j hj
  unfold schmidtMonomialP OAI.Erdos3.schmidtRecurrenceExponent
  omega

/-- **The four named constants are at most `2^1700`.** -/
theorem explicit_constants_le :
    (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700 :=
  explicit_constants_le_of schmidtMonomialK_le schmidtMonomialP_le

/-- **Theorem 16.2 in dimension three, from deep variety structure with `D ≤ 2^64`.** -/
theorem theorem_16_2_at_three_of_deep {D : Nat} (hD : D ≤ 2 ^ 64)
    (hM : MilicevicDeepVarietyStructure D) : Theorem162At 3 :=
  theorem_16_2_at_three_of_deep_of_constants hD explicit_constants_le hM

/-- **Corollary 16.11 in dimension three, from deep variety structure with `D ≤ 2^64`.** -/
theorem corollary_16_11_at_three_of_deep {D : Nat} (hD : D ≤ 2 ^ 64)
    (hM : MilicevicDeepVarietyStructure D) : Corollary1611At 3 :=
  corollary_16_11_at_three_of_deep_of_constants hD explicit_constants_le hM

/-- **Theorem 16.2 in dimension three, from the eventual deep structure with a polynomial
bound `Bnd c ≤ (4/c)^K`, `K ≤ 2^64`**: the form the corpus pipeline proves. -/
theorem theorem_16_2_at_three_of_eventually {Bnd : Real → Real} {K : Nat} (hK : K ≤ 2 ^ 64)
    (hBnd : ∀ c : Real, 0 < c → c ≤ 1 → Bnd c ≤ (4 / c) ^ K)
    (hM : MilicevicDeepEventuallyPrime Bnd) : Theorem162At 3 :=
  theorem_16_2_at_three_of_eventually_of_constants hK hBnd hM explicit_constants_le

/-- **Corollary 16.11 in dimension three, from the eventual, polynomial-bound deep structure.** -/
theorem corollary_16_11_at_three_of_eventually {Bnd : Real → Real} {K : Nat} (hK : K ≤ 2 ^ 64)
    (hBnd : ∀ c : Real, 0 < c → c ≤ 1 → Bnd c ≤ (4 / c) ^ K)
    (hM : MilicevicDeepEventuallyPrime Bnd) : Corollary1611At 3 :=
  corollary_16_11_at_three_of_eventually_of_constants hK hBnd hM explicit_constants_le

end LeanProofs.GowersSzemeredi

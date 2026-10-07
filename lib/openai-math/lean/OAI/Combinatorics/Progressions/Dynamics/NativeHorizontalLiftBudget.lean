import OAI.Combinatorics.Progressions.Estimates.ImageRepresentatives

namespace OAI

section

namespace Erdos3

def absorbedInitialParameter (p : ℝ) : ℝ :=
  3 * p + 1 + (p + 2) ^ 36 + (p + 2) ^ 19

theorem absorbedInitialParameter_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ absorbedInitialParameter p ∧
    Real.exp p + Real.exp p * Real.exp ((p + 2) ^ 19) * Real.exp p ≤
      Real.exp (absorbedInitialParameter p) ∧
    Real.exp p * (Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 36))) ≤
      Real.exp (absorbedInitialParameter p) := by
  have h19 : 0 ≤ (p + 2) ^ 19 := by positivity
  have h36 : 0 ≤ (p + 2) ^ 36 := by positivity
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  refine ⟨by unfold absorbedInitialParameter; linarith, ?_, ?_⟩
  · calc
      _ = Real.exp p + Real.exp (2 * p + (p + 2) ^ 19) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (2 * p + (p + 2) ^ 19) + Real.exp (2 * p + (p + 2) ^ 19) := by
        gcongr
        linarith
      _ = 2 * Real.exp (2 * p + (p + 2) ^ 19) := (two_mul _).symm
      _ ≤ Real.exp 1 * Real.exp (2 * p + (p + 2) ^ 19) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (1 + (2 * p + (p + 2) ^ 19)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold absorbedInitialParameter; linarith)
  · rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold absorbedInitialParameter
    linarith

theorem absorbedInitialParameter_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ absorbedInitialParameter p := hp.trans (absorbedInitialParameter_bounds hp).1

theorem exists_absorbedInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      absorbedInitialParameter p ≤ (p + D) ^ D ∧
      (absorbedInitialParameter p + 2) ^ 2 ≤ (p + D) ^ D ∧
      (absorbedInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
  let P : Polynomial ℕ := 3 * Polynomial.X + 1 + (Polynomial.X + 2) ^ 36 + (Polynomial.X + 2) ^ 19
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + (P + 2) ^ 2 + (P + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have h := hbudget p hp
  change _ ≤ _ at h
  have hsum : absorbedInitialParameter p + (absorbedInitialParameter p + 2) ^ 2 +
      (absorbedInitialParameter p + C) ^ C ≤ (p + D) ^ D := by
    simpa [P, absorbedInitialParameter, Polynomial.eval₂_pow] using h
  have h0 := absorbedInitialParameter_nonneg hp
  have h1 : 0 ≤ (absorbedInitialParameter p + 2) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (absorbedInitialParameter p + C) ^ C := by positivity
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def imageDefiningHeight (d n H : ℕ) : ℕ :=
  2 * ((d + 1) * (H * rationalKernelHeight n H) ^ d)

theorem imageDefiningHeight_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (imageDefiningHeight d n H : ℝ) ≤ Real.exp ((p + 2) ^ 10) := by
  have hK := rationalKernelHeight_le_budget n H hp hn hH
  have hp7 : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  have hbase : (H : ℝ) * rationalKernelHeight n H ≤ Real.exp ((p + 2) ^ 8) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + 2) ^ 7) := mul_le_mul hH hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + (p + 2) ^ 7) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          p + (p + 2) ^ 7 ≤ 2 * (p + 2) ^ 7 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 7 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (p + 2) ^ 8 := by ring
  have hpow : (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    rw [Nat.cast_pow, Nat.cast_mul]
    apply (pow_le_pow_left₀ (by positivity) hbase d).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (d : ℝ) * (p + 2) ^ 8 ≤ (p + 2) * (p + 2) ^ 8 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ 9 := by ring
  have hfront : 2 * ((d : ℝ) + 1) ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul htwo ((by linarith : (d : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  change ((2 * ((d + 1) * (H * rationalKernelHeight n H) ^ d) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc
    2 * (((d : ℝ) + 1) * (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ)) =
        (2 * ((d : ℝ) + 1)) * (((H * rationalKernelHeight n H) ^ d : ℕ) : ℝ) := by ring
    _ ≤ Real.exp (p + 1) * Real.exp ((p + 2) ^ 9) := mul_le_mul hfront hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + 1 + (p + 2) ^ 9) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hp9 : p + 1 ≤ (p + 2) ^ 9 := by
        apply (show p + 1 ≤ p + 2 by linarith).trans
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 1 ≤ 9)
      calc
        p + 1 + (p + 2) ^ 9 ≤ 2 * (p + 2) ^ 9 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (p + 2) ^ 10 := by ring

theorem imageSection_bound_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (coordinateLipschitzBound d n (rationalKernelHeight n H) : ℝ) ≤ Real.exp ((p + 2) ^ 18) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 7)
  have h := coordinateLipschitzBound_le_exp d n (rationalKernelHeight n H)
    (by positivity : 0 ≤ (p + 2) ^ 7) (hd.trans hpp) (hn.trans hpp)
    (by exact_mod_cast rationalKernelHeight_le_budget n H hp hn hH)
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 7 2))

theorem imageDefiningDenominator_le_exp {ι : Type*} [Fintype ι]
    (Q : Matrix ι ι ℚ) (d H m : ℕ)
    (hQ : ∀ i j, RationalHeightLE (Q i j) (imageDefiningHeight d (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    ((matrixDenominator Q * m : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 48) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have h := matrixDenominator_allowance_le_exp Q m (imageDefiningHeight d (Fintype.card ι) H) hQ
    (by positivity : 0 ≤ (p + 2) ^ 10) (hn.trans hpp) (hn.trans hpp)
    (imageDefiningHeight_le_exp d _ H hp hd hn hH) (hm.trans (Real.exp_le_exp.mpr hpp))
  rw [Nat.mul_comm] at h
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 4))

theorem imageDefiningRow_bound_le_exp (d n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * ((imageDefiningHeight d n H : ℝ) + 1) ≤ Real.exp ((p + 2) ^ 24) := by
  have hpp := le_power_budget hp (by decide : 1 ≤ 10)
  have h := coordinateLipschitzBound_le_exp n n (imageDefiningHeight d n H)
    (by positivity : 0 ≤ (p + 2) ^ 10) (hn.trans hpp) (hn.trans hpp)
    (by exact_mod_cast imageDefiningHeight_le_exp d n H hp hd hn hH)
  apply le_trans _ (h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 10 2)))
  change _ ≤ ((n : ℝ) + n + 1) * ((imageDefiningHeight d n H : ℝ) + 1)
  gcongr
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem exists_bchLogMetricConstant_exp_bound (s : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ (n H : ℕ) (p : ℝ), 0 ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (bchLogMetricConstant s n H 1 : ℝ) ≤ Real.exp ((p + Z) ^ Z + 1) := by
  obtain ⟨Z, hZ, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  refine ⟨Z, hZ, ?_⟩
  intro n H p hp hn hH
  have h := (bchBoxCoordinateBound_le_bchBoxMetricConstant s n H 1).trans
    (hbox n H 1 p hp hn hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp (by norm_num)))
  change bchBoxCoordinateBound s n H 1 ≤ Real.exp ((p + Z) ^ Z) at h
  change bchBoxCoordinateBound s n H 1 + 1 ≤ _
  have h1 : 1 ≤ Real.exp ((p + Z) ^ Z) := Real.one_le_exp (by positivity)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.exp_pos ((p + Z) ^ Z)]

end Erdos3

end

section

namespace Erdos3

def separationBudget (p : ℝ) : ℝ := (p + 2) ^ 48 + (p + 2) ^ 24 + p + 1

theorem separationBudget_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ separationBudget p := by
  unfold separationBudget
  positivity

theorem separationBudget_small {p D K r : ℝ}
    (hD : D ≤ Real.exp ((p + 2) ^ 48)) (hK : K ≤ Real.exp ((p + 2) ^ 24))
    (hK0 : 0 ≤ K) (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp p / Real.exp (separationBudget p)) :
    D * K * r < 1 := by
  calc
    D * K * r ≤ Real.exp ((p + 2) ^ 48) * Real.exp ((p + 2) ^ 24) *
        (Real.exp p / Real.exp (separationBudget p)) :=
      mul_le_mul (mul_le_mul hD hK hK0 (Real.exp_nonneg _)) hr hr0 (by positivity)
    _ = Real.exp (-1) := by
      rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold separationBudget
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

theorem exists_separationBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → separationBudget p ≤ (p + C) ^ C := by
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + 2) ^ 48 + (Polynomial.X + 2) ^ 24 + Polynomial.X + 1)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [separationBudget, Polynomial.eval₂_pow] using h p hp

end Erdos3

end

section

namespace Erdos3

def extractedInitialParameter (p : ℝ) : ℝ := (p + 2) ^ 3 + 3 * p + 3

theorem extractedInitialParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ extractedInitialParameter p ∧ 3 * p ≤ extractedInitialParameter p ∧
      (p + 2) ^ 3 ≤ extractedInitialParameter p := by
  have h : 0 ≤ (p + 2) ^ 3 := by positivity
  unfold extractedInitialParameter
  exact ⟨by linarith, by linarith, by linarith⟩

theorem extractedInitialParameter_products {p B C : ℝ} (hp : 0 ≤ p)
    (hB : 0 ≤ B) (hBp : B ≤ Real.exp p) (hC : 0 ≤ C) (hCp : C ≤ Real.exp p)
    (δ l : ℕ) (hδ : (δ : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ B ^ 2) :
    B * C ≤ Real.exp (extractedInitialParameter p) ∧
      ((δ * l : ℕ) : ℝ) ≤ Real.exp (extractedInitialParameter p) := by
  have hq := (extractedInitialParameter_controls hp).2.1
  constructor
  · calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hBp hCp hC (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * (Real.exp p) ^ 2 := by
        apply mul_le_mul hδ _ (Nat.cast_nonneg _) (Real.exp_nonneg _)
        exact hl.trans (pow_le_pow_left₀ hB hBp 2)
      _ = Real.exp (3 * p) := by rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hq

theorem exists_extractedInitialParameter_budget (C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      separationBudget (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      absorbedInitialParameter (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 3 * Polynomial.X + 3
  let A : Polynomial ℕ := 3 * Q + 1 + (Q + 2) ^ 36 + (Q + 2) ^ 19
  let S : Polynomial ℕ := (Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (S + A + (A + 2) ^ 2 + (A + Polynomial.C C) ^ C)
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hq : 0 ≤ extractedInitialParameter p := hp.trans (extractedInitialParameter_controls hp).1
  have ha := absorbedInitialParameter_nonneg hq
  have hs := separationBudget_nonneg hq
  have h2 : 0 ≤ (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 := sq_nonneg _
  have hc : 0 ≤ (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C := by positivity
  have hsum : separationBudget (extractedInitialParameter p) +
      absorbedInitialParameter (extractedInitialParameter p) +
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 +
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D := by
    simpa [Q, A, S, extractedInitialParameter, absorbedInitialParameter, separationBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_native_horizontal_lift_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let Q := (p + a) ^ a
      let P := (Q + 3) ^ 4
      Q ≤ (p + C) ^ C ∧ separationBudget P ≤ (p + C) ^ C ∧
        (P + 2) ^ 3 + (P + 2) ^ 18 + P ≤ (p + C) ^ C ∧
        Q + s * (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let P := (Q + 3) ^ 4
  let B := (P + 2) ^ 48 + (P + 2) ^ 24 + P + 1
  let E := (P + 2) ^ 3 + (P + 2) ^ 18 + P
  let M := Q + Polynomial.C s * (P + ((P + 2) ^ 3 + (P + 2) ^ 36))
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + B + E + M)
  refine ⟨C, hC, ?_⟩
  intro p hp Q' P'
  have hQ : 0 ≤ Q' := by dsimp only [Q']; positivity
  have hP : 0 ≤ P' := by dsimp only [P']; positivity
  have hB := separationBudget_nonneg hP
  have hE : 0 ≤ (P' + 2) ^ 3 + (P' + 2) ^ 18 + P' := by positivity
  have hM : 0 ≤ Q' + s * (P' + ((P' + 2) ^ 3 + (P' + 2) ^ 36)) := by positivity
  have hsum : Q' + separationBudget P' + ((P' + 2) ^ 3 + (P' + 2) ^ 18 + P') +
      (Q' + s * (P' + ((P' + 2) ^ 3 + (P' + 2) ^ 36))) ≤ (p + C) ^ C := by
    simpa [X, Q, P, B, E, M, Q', P', separationBudget, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hB, hE, hM],
    by linarith only [hsum, hQ, hE, hM],
    by linarith only [hsum, hQ, hB, hM], by linarith only [hsum, hQ, hB, hE]⟩

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AllocatedJetRootAllowance

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedPhysicalChartRadius (C : Fin m → ℝ) (H : ℝ) (j : Fin m) : ℝ :=
  1 / (4 * (((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1) *
    ((2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ (j.val + 1)) *
    ((C j + 1) * ((Fintype.card (I j) : ℝ) + 1))))

theorem allocatedPhysicalChartRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H : ℝ} (hH : 1 ≤ H) (j : Fin m) :
    0 < allocatedPhysicalChartRadius (G := G) B α C H j := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hC0 := hC j
  unfold allocatedPhysicalChartRadius
  positivity

theorem allocatedPhysicalChartRadius_bound (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H : ℝ} (hH : 1 ≤ H) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C H j)
    {H' : ℝ} (hH' : 1 ≤ H') (hHH : H' ≤ H) (j : Fin m) :
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * (H' + Fintype.card α) ^ (j.val + 1)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) ≤ 1 / 4 := by
  let N := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ)
  let M := (2 : ℝ) ^ Fintype.card α * (H + Fintype.card α) ^ (j.val + 1)
  let D := (N + 1) * M * ((C j + 1) * ((Fintype.card (I j) : ℝ) + 1))
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hH'0 : 0 ≤ H' := zero_le_one.trans hH'
  have hC0 := hC j
  have hD : 0 < D := by dsimp [D, N, M]; positivity
  have hcoef : N * ((2 : ℝ) ^ Fintype.card α * (H' + Fintype.card α) ^ (j.val + 1)) *
      (C j * ((Fintype.card (I j) : ℝ) + 1)) ≤ D := by
    dsimp [D, N, M]
    gcongr <;> linarith
  calc
    _ = (N * ((2 : ℝ) ^ Fintype.card α * (H' + Fintype.card α) ^ (j.val + 1)) *
        (C j * ((Fintype.card (I j) : ℝ) + 1))) * R j := by ring
    _ ≤ D * R j := mul_le_mul_of_nonneg_right hcoef (hR j)
    _ ≤ D * (1 / (4 * D)) := mul_le_mul_of_nonneg_left (hsmall j) hD.le
    _ = 1 / 4 := by field_simp [hD.ne']

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedPhysicalChartRadius_inv_le_exp (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H P : ℝ} (hH : 1 ≤ H) (hP : 0 ≤ P) (hHP : H ≤ Real.exp P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedPhysicalChartRadius (G := G) B α C H j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1)) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hadd {a : ℝ} (ha : a ≤ Real.exp P) : a + 1 ≤ Real.exp (P + 1) := by
    calc
      _ ≤ Real.exp P + Real.exp P := add_le_add ha h1
      _ = 2 * Real.exp P := by ring
      _ ≤ Real.exp 1 * Real.exp P := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hq : H + Fintype.card α ≤ Real.exp (P + Fintype.card α + 1) := by
    have hq1 : (Fintype.card α : ℝ) + 1 ≤ Real.exp (Fintype.card α + 1) := by
      linarith [Real.add_one_le_exp ((Fintype.card α : ℝ) + 1)]
    calc
      _ ≤ Real.exp P + (Fintype.card α : ℝ) * Real.exp P :=
        add_le_add hHP (by simpa using mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (Fintype.card α)))
      _ = ((Fintype.card α : ℝ) + 1) * Real.exp P := by ring
      _ ≤ Real.exp (Fintype.card α + 1) * Real.exp P :=
        mul_le_mul_of_nonneg_right hq1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hN := hadd (hNP j)
  have hCj := hadd (hCP j)
  have hI := hadd (hIP j)
  have hC0 := hC j
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  simp only [allocatedPhysicalChartRadius, one_div, inv_inv]
  calc
    _ ≤ Real.exp 2 * (Real.exp (P + 1) *
        ((Real.exp 1) ^ Fintype.card α * (Real.exp (P + Fintype.card α + 1)) ^ (j.val + 1)) *
        (Real.exp (P + 1) * Real.exp (P + 1))) := by gcongr
    _ = _ := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring

end Erdos3.VectorPolynomial

end

end OAI

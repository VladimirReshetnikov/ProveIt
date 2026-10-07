import OAI.Combinatorics.Progressions.Dynamics.AllocatedReferenceIdealBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)

include h

theorem allocatedIdealCoefficientVolume_bound
    (J : Fin m → Type*) [∀ j, Fintype (J j)] (C : Fin m → ℝ≥0)
    {p : ℝ} (hp : 0 ≤ p) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) :
    (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) ≤
      Real.exp (allocatedIdealVolumeEnvelope m D p) := by
  have hD := h.nonneg
  have hsupport := allocatedSupportEnvelope_nonneg m hD hp
  by_cases hm : m = 0
  · subst m
    have hcard : Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) = 0 := by
      simp [LayerSamplerAxis]
    rw [hcard, pow_zero]
    apply Real.one_le_exp
    unfold allocatedIdealVolumeEnvelope
    positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hsum : (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) ≤
      Real.exp (p + 2 * D) := by
    calc
      _ ≤ ∑ _j : Fin m, Real.exp p * Real.exp D := Finset.sum_le_sum (fun j _ =>
        mul_le_mul (hC j) (by linarith [hJ j, Real.add_one_le_exp D])
          (by positivity) (Real.exp_pos _).le)
      _ = (m : ℝ) * (Real.exp p * Real.exp D) := by simp
      _ ≤ Real.exp D * (Real.exp p * Real.exp D) :=
        mul_le_mul_of_nonneg_right (h.degree.trans (by linarith [Real.add_one_le_exp D]))
          (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbox : 2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1 ≤
      Real.exp (p + 2 * D + 3) := by
    have htwice : 2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) ≤
        Real.exp (p + 2 * D + 2) := by
      calc
        _ ≤ Real.exp 2 * Real.exp (p + 2 * D) :=
          mul_le_mul (by linarith [Real.add_one_le_exp (2 : ℝ)]) hsum
            (by positivity) (by positivity)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hb := one_add_le_exp_succ (by positivity : 0 ≤ p + 2 * D + 2) htwice
    calc
      _ = 1 + 2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) := add_comm _ _
      _ ≤ Real.exp (p + 2 * D + 2 + 1) := hb
      _ = _ := by congr 1; ring
  have hden : 1 + p ≤ allocatedDensityEnvelope m D p := by
    have ho := kernelOutputEnvelope_nonneg hD (show 0 ≤ 4 * (p + 8) by positivity)
    have hfirst := mul_nonneg (Nat.cast_nonneg m (α := ℝ)) ho
    have hsecond : 0 ≤ (m : ℝ) * (D + 3 * D * D + D * (D + 1)) := by positivity
    unfold allocatedDensityEnvelope
    linarith
  have hdim : 2 * D ≤ (m : ℝ) * (D + D * (D + 1)) := by
    calc
      _ ≤ D + D * (D + 1) := by nlinarith [sq_nonneg D]
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hm1 (show 0 ≤ D + D * (D + 1) by positivity)
  have hvolume : p + 2 * D + 3 ≤ allocatedSupportEnvelope m D p + 2 := by
    unfold allocatedSupportEnvelope
    linarith
  apply (pow_le_exp_mul_of_le_exp (by positivity) hbox
    (show 0 ≤ p + 2 * D + 3 by positivity) _ h.outputs).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hvolume hD

theorem allocatedIdealCoefficientMass_bound
    (J Q : Fin m → Type*) [∀ j, Fintype (J j)] [∀ j, Fintype (Q j)]
    (C : Fin m → ℝ≥0) {p P E : ℝ} (hp : 0 ≤ p) (hP : 0 ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (hQ : ∀ j, (Fintype.card (Q j) : ℝ) ≤ D)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1)) (hM : (M : ℝ) ≤ Real.exp P) :
    physicalIdealErrorShare (allocatedReferenceIdealError m D P E) (allocatedIdealVolumeEnvelope m D p) *
        coefficientDeckPeriodCap O Q period *
        (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) ≤
      profileReferenceAccuracy P E := by
  have hper : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
      _ ≤ Real.exp P ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul P (m + 1)).symm
  have hdeck := coefficientDeckPeriodCap_exp_bound O Q period h.nonneg
    (show 0 ≤ ((m + 1 : ℕ) : ℝ) * P by positivity) h.degree h.rows hQ hper
  have hvol := allocatedIdealCoefficientVolume_bound B h J C hp hJ hC
  have hη := (physicalIdealErrorShare_pos (allocatedReferenceIdealError m D P E)
    (allocatedIdealVolumeEnvelope m D p)).le
  calc
    _ ≤ physicalIdealErrorShare (allocatedReferenceIdealError m D P E) (allocatedIdealVolumeEnvelope m D p) *
        Real.exp (D ^ 3 * ((m + 1 : ℕ) * P)) * Real.exp (allocatedIdealVolumeEnvelope m D p) := by
      gcongr
    _ = Real.exp (-profileReferenceErrorLog P E - 3) := by
      unfold physicalIdealErrorShare allocatedReferenceIdealError
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3.VectorPolynomial

end

end OAI

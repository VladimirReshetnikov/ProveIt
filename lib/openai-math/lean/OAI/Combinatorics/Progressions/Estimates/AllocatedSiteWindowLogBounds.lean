import OAI.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedSiteAxisWindowLog {A : Type*} [Semiring A] (D : A) : A :=
  D * (allocatedSiteCoefficientLog D + 4)

def allocatedSiteFamilyWindowLog {A : Type*} [Semiring A] (D : A) : A :=
  D * (D + D * allocatedSiteAxisWindowLog D + 1)

def allocatedSitePointToleranceLog {A : Type*} [Semiring A] (D E : A) : A :=
  allocatedSiteFamilyWindowLog D + 1 + E

theorem allocatedSiteAxisWindowLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedSiteAxisWindowLog D := by
  have hc := allocatedSiteCoefficientLog_nonneg hD
  unfold allocatedSiteAxisWindowLog
  positivity

theorem allocatedSiteFamilyWindowLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedSiteFamilyWindowLog D := by
  have ha := allocatedSiteAxisWindowLog_nonneg hD
  unfold allocatedSiteFamilyWindowLog
  positivity

theorem allocatedSitePointToleranceLog_nonneg {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) :
    0 ≤ allocatedSitePointToleranceLog D E := by
  have hv := allocatedSiteFamilyWindowLog_nonneg hD
  unfold allocatedSitePointToleranceLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedIntegerAxes_card_le :
    (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ D := by
  apply le_trans _ h.axes
  apply Nat.cast_le.mpr
  simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin]
  exact Finset.sum_le_sum (fun _ _ => Nat.le_add_left _ _)

theorem allocatedSiteAxisWindowVolume_exp_bound (a : Σ j : Fin m, Fin (n j)) :
    allocatedSiteAxisWindowVolume (G := G) B rowSets a ≤ Real.exp (allocatedSiteAxisWindowLog D) := by
  have hC := allocatedSiteCoefficientLog_nonneg h.nonneg
  have hr := allocatedSiteCoefficientRadius_exp_bound B rowSets h a
  have hrows : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using h.rows a.1
  have hbase := two_mul_add_three_exp_bound hC hr
  unfold allocatedSiteAxisWindowVolume allocatedSiteAxisWindowLog
  exact pow_le_exp_mul_of_le_exp
    (by have hn := allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets a; positivity)
    hbase (by positivity) _ hrows

theorem allocatedSiteFamilyWindowVolume_exp_bound :
    allocatedSiteFamilyWindowVolume (G := G) B rowSets ≤ Real.exp (allocatedSiteFamilyWindowLog D) := by
  have hD := h.nonneg
  have hA := allocatedSiteAxisWindowLog_nonneg hD
  have hn := allocatedIntegerAxes_card_le B rowSets h
  have hs := sum_le_exp_of_card_and_uniform_bound
    (allocatedSiteAxisWindowVolume (G := G) B rowSets) hA hn
    (allocatedSiteAxisWindowVolume_exp_bound B rowSets h)
  have hsum : 0 ≤ ∑ a, allocatedSiteAxisWindowVolume (G := G) B rowSets a :=
    Finset.sum_nonneg (fun a _ => allocatedSiteAxisWindowVolume_nonneg (G := G) B rowSets a)
  have hbase := one_add_le_exp_succ (by positivity : 0 ≤ D + D * allocatedSiteAxisWindowLog D) hs
  unfold allocatedSiteFamilyWindowVolume allocatedSiteFamilyWindowLog
  exact pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) _ hn

theorem allocatedSitePointTolerance_inverse_exp_bound {δ E : ℝ} (hδ : 0 < δ)
    (hδE : δ⁻¹ ≤ Real.exp E) :
    (allocatedSitePointTolerance (G := G) B rowSets δ)⁻¹ ≤
      Real.exp (allocatedSitePointToleranceLog D E) := by
  have hvolume := allocatedSiteFamilyWindowVolume_exp_bound B rowSets h
  have hbase : allocatedSiteFamilyWindowVolume (G := G) B rowSets + 1 ≤
      Real.exp (allocatedSiteFamilyWindowLog D + 1) := by
    rw [add_comm]
    exact one_add_le_exp_succ (allocatedSiteFamilyWindowLog_nonneg h.nonneg) hvolume
  unfold allocatedSitePointTolerance allocatedSitePointToleranceLog
  rw [inv_div, div_eq_mul_inv]
  exact (mul_le_mul hbase hδE (inv_nonneg.mpr hδ.le) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

end Erdos3.VectorPolynomial

end

end OAI

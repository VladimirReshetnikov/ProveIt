import OAI.Combinatorics.Progressions.Fourier.AllocatedSupportedResidueSpectrum

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem positiveModerateSpectrumCardBudget_nonneg (n j t : ℕ) {P V W ε : ℝ}
    (hP : 1 ≤ P) (hW : 0 ≤ W) (hε : 0 ≤ ε) :
    0 ≤ positiveModerateSpectrumCardBudget n j t P V W ε := by
  have hL := (positiveModerateLengthConstant_pos n hP).le
  have hC : 0 ≤ positiveModerateSpectrumConstant n j P V := by
    unfold positiveModerateSpectrumConstant
    positivity
  have hD := positiveModerateAccuracyScale_one_le n j t (V := V) hP hW
  have hζ : 0 ≤ positiveModerateRetainedBias n j t P V W ε :=
    div_nonneg hε (zero_le_one.trans hD)
  unfold positiveModerateSpectrumCardBudget
  positivity

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

noncomputable def allocatedGridTorusFactor (a : Σ j : Fin m, Fin (n j)) : ℕ :=
  blockTorusFactor (Fintype.card α) (a.1.val + 1) (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 4

variable {α}

noncomputable def allocatedGridPointCap (P : ℝ) (a : Σ j : Fin m, Fin (n j))
    (rows : Finset (Finset α)) : ℝ :=
  let H := allocatedGridTorusFactor B α a
  positiveModerateSpectrumCardBudget a.1.val rows.card ((layerTailDegree m + 2) * rows.card)
    P (H : ℝ) ((2 * (H : ℝ)) ^ rows.card) 1 + 1

theorem allocatedGridPointCap_one_le {P : ℝ} (hP : 1 ≤ P)
    (a : Σ j : Fin m, Fin (n j)) (rows : Finset (Finset α)) :
    1 ≤ allocatedGridPointCap B P a rows := by
  have h := positiveModerateSpectrumCardBudget_nonneg a.1.val rows.card
    ((layerTailDegree m + 2) * rows.card) (V := (allocatedGridTorusFactor B α a : ℝ))
    hP (by positivity : (0 : ℝ) ≤ (2 * (allocatedGridTorusFactor B α a : ℝ)) ^ rows.card) zero_le_one
  change 1 ≤ _ + 1
  linarith

variable (rowFamily : (Σ j : Fin m, Fin (n j)) → Finset (Finset α))

noncomputable def allocatedGridFamilyCap (P : ℝ) : ℝ :=
  ∑ a, allocatedGridPointCap B P a (rowFamily a)

theorem allocatedGridFamilyCap_nonneg {P : ℝ} (hP : 1 ≤ P) :
    0 ≤ allocatedGridFamilyCap B rowFamily P := by
  exact Finset.sum_nonneg (fun a _ => zero_le_one.trans (allocatedGridPointCap_one_le B hP a _))

theorem allocatedGridPointCap_le_family {P : ℝ} (hP : 1 ≤ P)
    (a : Σ j : Fin m, Fin (n j)) :
    allocatedGridPointCap B P a (rowFamily a) ≤ allocatedGridFamilyCap B rowFamily P := by
  exact Finset.single_le_sum
    (fun a _ => zero_le_one.trans (allocatedGridPointCap_one_le B hP a _)) (Finset.mem_univ a)

noncomputable def allocatedGridFamilyAccuracy (P δ : ℝ) : ℝ :=
  uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j)))
    (allocatedGridFamilyCap B rowFamily P) δ

theorem allocatedGridFamilyAccuracy_spec {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ) :
    0 < allocatedGridFamilyAccuracy B rowFamily P δ ∧
      allocatedGridFamilyAccuracy B rowFamily P δ ≤ 1 := by
  exact ⟨(uniformProductAccuracy_spec _ (allocatedGridFamilyCap_nonneg B rowFamily hP) hδ).1,
    (uniformProductAccuracy_spec _ (allocatedGridFamilyCap_nonneg B rowFamily hP) hδ).2.1⟩

end VectorPolynomial
end Erdos3

end

end OAI

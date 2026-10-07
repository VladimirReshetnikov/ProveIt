import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem two_mul_add_three_exp_bound {x P : ℝ} (hP : 0 ≤ P) (hx : x ≤ Real.exp P) :
    2 * x + 3 ≤ Real.exp (P + 4) := by
  have h1 := Real.one_le_exp_iff.mpr hP
  have h5 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 5 * Real.exp P := by linarith
    _ ≤ Real.exp 4 * Real.exp P := mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem blockJetScaleBound_four_exp (q h b : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hb : (b : ℝ) ≤ D) :
    blockJetScaleBound q h b 4 ≤ Real.exp (D ^ 2 + 2 * D + 4) := by
  have hbexp : (b : ℝ) ≤ Real.exp D := hb.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : ((q + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ h ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) h hh
  have hpowq := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (q + 1)) hqexp hD h hh
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  unfold blockJetScaleBound
  calc
    _ ≤ Real.exp D * Real.exp D * Real.exp (D * D) * Real.exp 4 := by
      gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

namespace VectorPolynomial

def allocatedNaturalSupportLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 3 * D + 7

def allocatedNaturalSiteLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 4 * D + 8

def allocatedSiteCoefficientLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 5 * D + 8

theorem allocatedNaturalSupportLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedNaturalSupportLog D := by unfold allocatedNaturalSupportLog; positivity

theorem allocatedNaturalSiteLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedNaturalSiteLog D := by unfold allocatedNaturalSiteLog; positivity

theorem allocatedSiteCoefficientLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedSiteCoefficientLog D := by unfold allocatedSiteCoefficientLog; positivity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedIntegerBlock_card_le (j : Fin m) (i : Fin (n j)) :
    (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D := by
  have hs : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (h.coefficients j)
  simpa only [layerIntegerPrincipalSlots_card] using hs

theorem allocatedGridTorusFactor_exp_bound (j : Fin m) (i : Fin (n j)) :
    (allocatedGridTorusFactor B α ⟨j, i⟩ : ℝ) ≤ Real.exp (D ^ 2 + 2 * D + 8) := by
  have hb := blockJetScaleBound_four_exp (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) h.nonneg h.cube (h.layer_degree B j)
    (allocatedIntegerBlock_card_le B rowSets h j i)
  have ht := (blockTorusFactor_upper (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) (by norm_num : (0 : ℝ) ≤ 4)).trans
      (two_mul_add_three_exp_bound (by have hD := h.nonneg; positivity) hb)
  calc
    _ = (blockTorusFactor (Fintype.card α) (j.val + 1)
        (Fintype.card (B ⟨j, Sum.inr i⟩)) 4 : ℝ) := rfl
    _ ≤ Real.exp (D ^ 2 + 2 * D + 4 + 4) := ht
    _ = _ := by congr 1; ring

theorem allocatedNaturalSupportRadius_exp_bound (j : Fin m) (i : Fin (n j)) :
    allocatedNaturalSupportRadius (G := G) B α j i ≤ Real.exp (allocatedNaturalSupportLog D) := by
  have hb := allocatedIntegerBlock_card_le B rowSets h j i
  have hs : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hblock := blockJetScaleBound_four_exp (Fintype.card α) (j.val + 1)
    (Fintype.card (B ⟨j, Sum.inr i⟩)) h.nonneg h.cube (h.layer_degree B j) hb
  have hD := h.nonneg
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hc : allocatedNaturalConstantRadius (G := G) B j i ≤ Real.exp (D + 1) := by
    unfold allocatedNaturalConstantRadius
    calc
      _ ≤ Real.exp 1 * Real.exp D := mul_le_mul htwo
        (by linarith [Real.add_one_le_exp D]) (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have ha := add_le_exp_add_one (by positivity : 0 ≤ D ^ 2 + 2 * D + 4)
    (by norm_num : (0 : ℝ) ≤ 0) hblock (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  have ht := add_le_exp_add_one (by positivity : 0 ≤ (D ^ 2 + 2 * D + 4) + 0 + 1)
    (by positivity : 0 ≤ D + 1) ha hc
  exact ht.trans_eq (by
    congr 1
    unfold allocatedNaturalSupportLog
    ring)

theorem allocatedNaturalSiteRadius_exp_bound (j : Fin m) (i : Fin (n j)) :
    allocatedNaturalSiteRadius (G := G) B j i (rowSets j) + 1 / 4 ≤
      Real.exp (allocatedNaturalSiteLog D) := by
  have hD := h.nonneg
  have hrow : ((rowSets j).card : ℝ) ≤ D := by
    simpa only [Fintype.card_coe] using h.rows j
  have hr : ((rowSets j).card : ℝ) ≤ Real.exp D :=
    hrow.trans (show D ≤ Real.exp D by linarith [Real.add_one_le_exp D])
  have hs := allocatedNaturalSupportRadius_exp_bound B rowSets h j i
  have hm : allocatedNaturalSiteRadius (G := G) B j i (rowSets j) ≤
      Real.exp (D + allocatedNaturalSupportLog D) := by
    unfold allocatedNaturalSiteRadius
    exact (mul_le_mul hr hs (allocatedNaturalSupportRadius_nonneg B α j i)
      (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have ht := add_le_exp_add_one (add_nonneg hD (allocatedNaturalSupportLog_nonneg hD))
    (by norm_num : (0 : ℝ) ≤ 0) hm (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  exact ht.trans_eq (by
    congr 1
    unfold allocatedNaturalSiteLog allocatedNaturalSupportLog
    ring)

theorem allocatedSiteCoefficientRadius_exp_bound (a : Σ j : Fin m, Fin (n j)) :
    allocatedSiteCoefficientRadius (G := G) B rowSets a ≤ Real.exp (allocatedSiteCoefficientLog D) := by
  have hD := h.nonneg
  have hs := allocatedNaturalSupportRadius_exp_bound B rowSets h a.1 a.2
  have ht := allocatedNaturalSiteRadius_exp_bound B rowSets h a.1 a.2
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ (a.1.val + 1) ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (a.1.val + 1) (h.layer_degree B a.1)
  unfold allocatedSiteCoefficientRadius
  refine max_le (hs.trans (Real.exp_le_exp.mpr ?_)) ?_
  · unfold allocatedNaturalSupportLog allocatedSiteCoefficientLog
    linarith
  · have hh := (mul_le_mul hp ht
      (by have hn := allocatedNaturalSiteRadius_nonneg (G := G) B a.1 a.2 (rowSets a.1); positivity)
      (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
    exact hh.trans_eq (by
      congr 1
      unfold allocatedSiteCoefficientLog allocatedNaturalSiteLog
      ring)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def allocatedInactiveSupportLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 4 * D + 9

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedInactiveLongRadius (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  (rowSets a.1).card * (blockJetScaleBound (Fintype.card α) (a.1.val + 1)
    (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 1 + allocatedNaturalConstantRadius (G := G) B a.1 a.2)

noncomputable def allocatedInactiveShortRadius (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  (rowSets a.1).card *
    ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (a.1.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (a.1.val + 1)) *
      (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B a.1 a.2) : ℝ) + 1)))

noncomputable def allocatedInactiveSiteRadius (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  max (allocatedInactiveLongRadius (G := G) B rowSets a)
    (allocatedInactiveShortRadius (G := G) B rowSets a) + 1 / 4

omit [Fintype G] [∀ j, Fintype (I j)] in
theorem allocatedInactiveLongRadius_le_natural (a : Σ j : Fin m, Fin (n j)) :
    allocatedInactiveLongRadius (G := G) B rowSets a ≤
      allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) := by
  have h14 : blockJetScaleBound (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 1 ≤
      blockJetScaleBound (Fintype.card α) (a.1.val + 1)
        (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 4 := by
    unfold blockJetScaleBound
    exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
  unfold allocatedInactiveLongRadius allocatedNaturalSiteRadius allocatedNaturalSupportRadius
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  linarith only [h14]

variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedInactiveShortRadius_exp_bound (a : Σ j : Fin m, Fin (n j)) :
    allocatedInactiveShortRadius (G := G) B rowSets a ≤ Real.exp (D ^ 2 + 4 * D + 8) := by
  have hD := h.nonneg
  have hrow : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using h.rows a.1
  have hrowexp : ((rowSets a.1).card : ℝ) ≤ Real.exp D :=
    hrow.trans (by linarith [Real.add_one_le_exp D])
  have hslots : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (a.1.val + 1)) : ℝ) ≤ Real.exp D :=
    (h.coefficients a.1).trans (by linarith [Real.add_one_le_exp D])
  have hprincipal : ((Finset.card (layerIntegerPrincipalSlots (G := G) B a.1 a.2) : ℝ) + 1) ≤
      Real.exp D := by
    have hb := allocatedIntegerBlock_card_le B rowSets h a.1 a.2
    rw [layerIntegerPrincipalSlots_card]
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have htwoc : (2 : ℝ) ^ Fintype.card α ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (Fintype.card α) h.cube
  have hc : (Fintype.card α : ℝ) + 1 ≤ Real.exp D := by
    have hc' := h.cube
    linarith [Real.add_one_le_exp D]
  have hcpow := pow_le_exp_mul_of_le_exp (by positivity) hc hD (a.1.val + 1) (h.layer_degree B a.1)
  have height : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hconstant := (mul_le_mul height hprincipal (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  unfold allocatedInactiveShortRadius
  calc
    _ ≤ Real.exp D * (Real.exp D * (Real.exp D * Real.exp (D * D)) * Real.exp (8 + D)) := by
      gcongr
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

theorem allocatedInactiveSiteRadius_exp_bound (a : Σ j : Fin m, Fin (n j)) :
    allocatedInactiveSiteRadius (G := G) B rowSets a ≤ Real.exp (allocatedInactiveSupportLog D) := by
  have hD := h.nonneg
  have hlong := (add_le_add (allocatedInactiveLongRadius_le_natural B rowSets a)
    (le_refl (1 / 4 : ℝ))).trans (allocatedNaturalSiteRadius_exp_bound B rowSets h a.1 a.2)
  have hlong' : allocatedInactiveLongRadius (G := G) B rowSets a + 1 / 4 ≤
      Real.exp (allocatedInactiveSupportLog D) := hlong.trans (Real.exp_le_exp.mpr (by
        unfold allocatedNaturalSiteLog allocatedInactiveSupportLog
        linarith))
  have hshort := add_le_exp_add_one (by positivity : 0 ≤ D ^ 2 + 4 * D + 8)
    (le_refl (0 : ℝ)) (allocatedInactiveShortRadius_exp_bound B rowSets h a)
    (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  have hshort' : allocatedInactiveShortRadius (G := G) B rowSets a + 1 / 4 ≤
      Real.exp (allocatedInactiveSupportLog D) :=
    hshort.trans_eq (by unfold allocatedInactiveSupportLog; congr 1; ring)
  rcases le_total (allocatedInactiveLongRadius (G := G) B rowSets a)
    (allocatedInactiveShortRadius (G := G) B rowSets a) with hls | hsl
  · simpa only [allocatedInactiveSiteRadius, max_eq_right hls] using hshort'
  · simpa only [allocatedInactiveSiteRadius, max_eq_left hsl] using hlong'

end Erdos3.VectorPolynomial

end

end OAI

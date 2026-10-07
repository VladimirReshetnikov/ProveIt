import OAI.Combinatorics.Progressions.Geometry.AllocatedSiteTermSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def allocatedSiteRootAllowance (α : Type*) [Fintype α] (m : ℕ) : ℝ :=
  1 + (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (m + 1) + idealSiteEnvelopeRadius α m

theorem allocatedSiteRootAllowance_one_le (α : Type*) [Fintype α] (m : ℕ) :
    1 ≤ allocatedSiteRootAllowance α m := by
  have h := (idealSiteEnvelopeRadius_pos α m).le
  unfold allocatedSiteRootAllowance
  have hp : 0 ≤ (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (m + 1) := by positivity
  linarith

theorem allocatedSiteRootAllowance_le_exp (α : Type*) [Fintype α] (m : ℕ) :
    allocatedSiteRootAllowance α m ≤ Real.exp (((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5) := by
  let q : ℝ := Fintype.card α
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ Fintype.card α ≤ Real.exp q := by
    calc
      _ ≤ (Real.exp 1) ^ Fintype.card α := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]; rfl
  have hmain : (2 : ℝ) ^ Fintype.card α * (q + 1) ^ (m + 1) ≤ Real.exp (((m : ℝ) + 2) * q) := by
    calc
      _ ≤ Real.exp q * (Real.exp q) ^ (m + 1) :=
        mul_le_mul hp (pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp q) _)
          (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  let L : ℝ := ((m : ℝ) + 2) * q + (((m : ℝ) + 3) * q + 3)
  have hmainL : ((m : ℝ) + 2) * q ≤ L := by
    dsimp [L]
    have h : 0 ≤ ((m : ℝ) + 3) * q := by positivity
    linarith
  have henvL : ((m : ℝ) + 3) * q + 3 ≤ L := by
    dsimp [L]
    have h : 0 ≤ ((m : ℝ) + 2) * q := by positivity
    linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have henv := (idealSiteEnvelopeRadius_le_exp α m).trans (Real.exp_le_exp.mpr henvL)
  have hunit : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp L := by
      unfold allocatedSiteRootAllowance
      have hm := hmain.trans (Real.exp_le_exp.mpr hmainL)
      change 1 + (2 : ℝ) ^ Fintype.card α * (q + 1) ^ (m + 1) + idealSiteEnvelopeRadius α m ≤ _
      linarith
    _ ≤ Real.exp 2 * Real.exp L := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [L, q]; push_cast; ring

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedSiteJetSize_root_allowance (j : Fin m) :
    (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ) * allocatedSiteJetSize (G := G) B α j ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * (allocatedSiteRootAllowance α m + Fintype.card α) ^ (j.val + 1)) := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  let H := allocatedSiteRootAllowance α m
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr
      ⟨constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1)⟩)
  have hH : 1 ≤ H := allocatedSiteRootAllowance_one_le α m
  have hcount : (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ) ≤ (2 : ℝ) ^ Fintype.card α := by
    exact_mod_cast (show Fintype.card (BoundedBooleanJet α (j.val + 1)) ≤ 2 ^ Fintype.card α from by
      simpa using Fintype.card_le_of_injective (fun r : BoundedBooleanJet α (j.val + 1) => r.val) Subtype.val_injective)
  have hpow : ((Fintype.card α : ℝ) + 1) ^ (j.val + 1) ≤ ((Fintype.card α : ℝ) + 1) ^ (m + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)])
      (Nat.succ_le_succ (Nat.le_of_lt j.isLt))
  have hsize : allocatedSiteJetSize (G := G) B α j ≤ N * H := by
    have he := (idealSiteEnvelopeRadius_pos α m).le
    have hm := mul_le_mul_of_nonneg_left hpow
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card α))
    dsimp only [allocatedSiteJetSize, H, allocatedSiteRootAllowance]
    change N * _ + _ ≤ N * _
    nlinarith [mul_le_mul_of_nonneg_left hm (zero_le_one.trans hN), mul_le_mul_of_nonneg_right hN he]
  have hbase : 1 ≤ H + Fintype.card α := hH.trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hHpow : H ≤ (H + Fintype.card α) ^ (j.val + 1) := by
    rw [pow_succ]
    have hp : (1 : ℝ) ≤ (H + Fintype.card α) ^ j.val := one_le_pow₀ hbase
    calc
      H ≤ H + Fintype.card α := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = 1 * (H + Fintype.card α) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (zero_le_one.trans hbase)
  calc
    _ ≤ (2 : ℝ) ^ Fintype.card α * (N * H) :=
      mul_le_mul hcount hsize (allocatedSiteJetSize_nonneg B α j) (by positivity)
    _ ≤ (2 : ℝ) ^ Fintype.card α * (N * (H + Fintype.card α) ^ (j.val + 1)) := by gcongr
    _ = _ := by ring

theorem allocatedSiteChartRadius_budget (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)
    (j : Fin m) :
    (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (allocatedSiteJetSize (G := G) B α j * R j))) ≤ 1 / 4 := by
  have hb := allocatedPhysicalChartRadius_bound (G := G) B α C hC
    (allocatedSiteRootAllowance_one_le α m) hR hsmall (allocatedSiteRootAllowance_one_le α m) le_rfl j
  have hw : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) :=
    (mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j)))
  have hf := mul_le_mul_of_nonneg_right (allocatedSiteJetSize_root_allowance (G := G) B α j) hw
  calc
    _ = (Fintype.card (BoundedBooleanJet α (j.val + 1)) * allocatedSiteJetSize (G := G) B α j) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by ring
    _ ≤ _ := hf
    _ ≤ 1 / 4 := hb

theorem allocatedSiteChartRadius_le_original (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (j : Fin m) :
    allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j ≤
      allocatedPhysicalChartRadius (G := G) B α C 1 j := by
  have hH := allocatedSiteRootAllowance_one_le α m
  have hCj := hC j
  unfold allocatedPhysicalChartRadius
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem allocatedSiteChartRadius_inv_le_exp (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    {P : ℝ} (hP : 0 ≤ P)
    (hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤ P)
    (hCP : ∀ j, C j ≤ Real.exp P)
    (hNP : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp P)
    (hIP : ∀ j, (Fintype.card (I j) : ℝ) ≤ Real.exp P) (j : Fin m) :
    (allocatedPhysicalChartRadius (G := G) B α C (allocatedSiteRootAllowance α m) j)⁻¹ ≤
      Real.exp (3 * (P + 1) + Fintype.card α + 2 +
        (j.val + 1 : ℕ) * (P + Fintype.card α + 1)) :=
  allocatedPhysicalChartRadius_inv_le_exp B α C hC (allocatedSiteRootAllowance_one_le α m) hP
    ((allocatedSiteRootAllowance_le_exp α m).trans (Real.exp_le_exp.mpr hallow)) hCP hNP hIP j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (α : Type*) [Fintype α]

theorem allocatedSiteJetSize_le_allowance (j : Fin m) :
    allocatedSiteJetSize (G := G) B α j ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        allocatedSiteRootAllowance α m := by
  let N : ℝ := Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr
      ⟨constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1)⟩)
  have hpow : ((Fintype.card α : ℝ) + 1) ^ (j.val + 1) ≤
      ((Fintype.card α : ℝ) + 1) ^ (m + 1) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)])
      (Nat.succ_le_succ (Nat.le_of_lt j.isLt))
  have he := (idealSiteEnvelopeRadius_pos α m).le
  have hm := mul_le_mul_of_nonneg_left hpow
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card α))
  unfold allocatedSiteJetSize allocatedSiteRootAllowance
  change N * _ + _ ≤ N * _
  nlinarith [mul_le_mul_of_nonneg_left hm (zero_le_one.trans hN),
    mul_le_mul_of_nonneg_right hN he]

noncomputable def allocatedFullSiteRadius : ℝ≥0 :=
  ⟨1 + (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j,
    add_nonneg zero_le_one (mul_nonneg (pow_nonneg (by norm_num) _)
      (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)))⟩

theorem allocatedFullSiteRadius_one_le : 1 ≤ allocatedFullSiteRadius (G := G) B α := by
  change (1 : ℝ) ≤ 1 + (2 : ℝ) ^ Fintype.card α * ∑ j : Fin m, allocatedSiteJetSize (G := G) B α j
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg (fun j _ => allocatedSiteJetSize_nonneg B α j)))

theorem allocatedFullSiteRadius_pos : 0 < allocatedFullSiteRadius (G := G) B α :=
  zero_lt_one.trans_le (allocatedFullSiteRadius_one_le B α)

theorem allocatedFullSiteRadius_dominates (j : Fin m) :
    (2 : ℝ) ^ Fintype.card α * allocatedSiteJetSize (G := G) B α j ≤
      allocatedFullSiteRadius (G := G) B α := by
  have h := Finset.single_le_sum (fun k _ => allocatedSiteJetSize_nonneg (G := G) B α k)
    (Finset.mem_univ j)
  exact (mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num) _)).trans
    (le_add_of_nonneg_left zero_le_one)

end Erdos3.VectorPolynomial

end

end OAI

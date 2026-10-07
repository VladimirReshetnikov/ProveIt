import OAI.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

theorem allocatedPrincipalSides_inactive
    (hsmall : height ≤ S.value ^ degree) (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :
    allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
  rw [layerIntegerPrincipalSlots_card]
  change integerAxisSideLength degree height S.value
    (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
  simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]

noncomputable def allocatedSlicedGridHeightCutoff (T : ℕ) : ℕ :=
  T ^ (layerTailDegree m + 1) + denom * 2 ^ degree * T ^ degree + 2 * denom

theorem allocatedSlicedGrid_cases
    (H : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (Q T : ℕ) (hQT : (Q : ℝ) / δ ≤ T) :
    height ≤ allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T ∨
      ((∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩) ∧
        ((S.value ^ degree < height ∧ ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∨
         (height ≤ S.value ^ degree ∧ 2 * denom ≤ height ∧
           ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)))) := by
  let K := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
  by_cases hK : height ≤ K
  · exact Or.inl hK
  have hlarge : 2 * denom ≤ height := by
    have : 2 * denom ≤ K := by dsimp [K, allocatedSlicedGridHeightCutoff]; omega
    omega
  have hside_bound {L h : ℕ} (hd : δ * L ≤ (h : ℝ)) (hh : h < Q) : L ≤ T := by
    have hl : (L : ℝ) ≤ (Q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh' : (h : ℝ) ≤ Q := Nat.cast_le.mpr hh.le
      simpa only [mul_comm] using hd.trans hh'
    exact_mod_cast hl.trans hQT
  have hsize : ∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    intro b v
    by_contra hh
    have hL := hside_bound (hdense b v) (Nat.lt_of_not_ge hh)
    apply hK
    by_cases ha : S.value ^ degree < height
    · rw [allocatedPrincipalSides_active B U basis S j i ha b v] at hL
      have hb := hgrid.trans (Nat.pow_le_pow_left hL (layerTailDegree m + 1))
      exact hb.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
    · rw [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] at hL
      have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val) (inactiveDenominator_pos _) hlarge).le
      have hc := hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree) (Nat.pow_le_pow_left hL degree))
      exact hc.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
  refine Or.inr ⟨hsize, ?_⟩
  by_cases ha : S.value ^ degree < height
  · refine Or.inl ⟨ha, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_active B U basis S j i ha b v] using hdense b v
  · refine Or.inr ⟨Nat.le_of_not_gt ha, hlarge, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] using hdense b v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem exists_denseSliceThreshold (c q : ℕ) {δ D v w : ℝ}
    (hδ : 0 < δ) (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hc : (c : ℝ) ≤ D) (hq : (q : ℝ) ≤ Real.exp v) (hδw : δ⁻¹ ≤ Real.exp w) :
    ∃ T : ℕ, (((c + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
      (T : ℝ) ≤ Real.exp (D + v + w + 1) := by
  let T : ℕ := ⌈(((c + 1) * q : ℕ) : ℝ) / δ⌉₊
  have hcp : ((c + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have hb : (((c + 1) * q : ℕ) : ℝ) / δ ≤ Real.exp (D + v + w) := by
    rw [Nat.cast_mul, div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul hcp hq (Nat.cast_nonneg _) (Real.exp_nonneg _))
      hδw (inv_nonneg.mpr hδ.le) (by positivity)).trans_eq (by rw [← Real.exp_add, ← Real.exp_add])
  exact ⟨T, Nat.le_ceil _, natCeil_le_exp_succ (by positivity) (by positivity) hb⟩

theorem principalProfileSize_exp_bounds (b : ℕ) {R D v : ℝ}
    (hR : 0 < R) (hb : (b : ℝ) ≤ D) (hRv : R ≤ Real.exp v) (hRi : R⁻¹ ≤ Real.exp v) :
    principalProfileSize R b ≤ Real.exp v ∧
      (principalProfileSize R b)⁻¹ ≤ Real.exp (D + v + 8) := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hden : (1 : ℝ) ≤ 8 * ((b : ℝ) + 1) := by linarith
  have hfirst : principalProfileSize R b ≤ R := div_le_self hR.le hden
  have hbexp : (b : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  refine ⟨hfirst.trans hRv, ?_⟩
  rw [principalProfileSize, inv_div, div_eq_mul_inv]
  have he := mul_le_mul (mul_le_mul h8 hbexp (by positivity) (Real.exp_nonneg _)) hRi
    (inv_nonneg.mpr hR.le) (by positivity)
  exact he.trans_eq (by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

omit [Fintype G] [∀ j, Fintype (I j)] in
theorem allocatedSlicedGridHeightCutoff_exp_bound [Fintype G] [∀ j, Fintype (I j)]
    (hR : 0 < R j) (T : ℕ) {v t : ℝ}
    (hv : 0 ≤ v) (ht : 0 ≤ t) (hγv : gamma⁻¹ ≤ Real.exp v) (hT : (T : ℝ) ≤ Real.exp t) :
    (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ≤
      Real.exp ((layerTailDegree m + 1 : ℕ) * t + (j.val + 1 : ℕ) * (t + 1) + 2 * v + 5) := by
  have hden := inactiveDenominator_le_exp (principalProfileSize_pos hR _) hv hγv
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTa := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg T) hT ht (layerTailDegree m + 1) le_rfl
  have hTi := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg T) hT ht (j.val + 1) le_rfl
  have hpow2 : (2 : ℝ) ^ (j.val + 1) ≤ Real.exp (j.val + 1 : ℕ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) (j.val + 1) le_rfl
  have hmid : (denom : ℝ) * 2 ^ (j.val + 1) * (T : ℝ) ^ (j.val + 1) ≤
      Real.exp (v + 1 + (j.val + 1 : ℕ) * (t + 1)) := by
    have hb := mul_le_mul (mul_le_mul hden hpow2 (by positivity) (Real.exp_nonneg _))
      hTi (by positivity) (by positivity)
    simp only [← Real.exp_add] at hb
    exact hb.trans_eq (by congr 1; ring)
  have hlast : (2 : ℝ) * denom ≤ Real.exp (v + 2) := by
    have hb := mul_le_mul htwo hden (Nat.cast_nonneg _) (Real.exp_nonneg _)
    exact hb.trans_eq (by rw [← Real.exp_add]; congr 1; ring)
  have hsum := add_le_exp_add_one (by positivity) (by positivity) hTa hmid
  have hsum' := add_le_exp_add_one (by positivity) (by positivity) hsum hlast
  simp only [allocatedSlicedGridHeightCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact hsum'.trans_eq (by congr 1; push_cast; ring)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_slicedGridParameters (dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {F Q δ : ℝ} {q step : ℕ},
      0 ≤ F → 0 ≤ Q → 0 < δ → δ⁻¹ ≤ Real.exp F → 0 < q →
      (q : ℝ) ≤ Real.exp Q → (step : ℝ) ≤ 4 * Real.exp F →
      ∃ T : ℕ, (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        1 ≤ Pg ∧ scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  let fixed := scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 +
    scalarCubePrimitiveEnvelope (Fin dim) A 1 0 1 + 2
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge fixed
  let C := max 2 C₀
  have hC : fixed ≤ (C : ℝ) := hC₀.trans (Nat.cast_le.mpr (le_max_right _ _))
  have hc0 := scalarCubePrimitiveEnvelope_nonneg Empty A 16 (128 * probabilityProfileLipschitz) 1
  have hs0 := scalarCubePrimitiveEnvelope_nonneg (Fin dim) A 1 0 1
  have hc : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ C := by
    dsimp only [fixed] at hC
    linarith
  have hs : scalarCubePrimitiveEnvelope (Fin dim) A 1 0 1 ≤ C := by
    dsimp only [fixed] at hC
    linarith
  refine ⟨C, le_max_left _ _, ?_⟩
  intro F Q δ q step hF hQ hδ hδF hq hqQ hstep
  obtain ⟨T, hT, hTb⟩ := exists_denseSliceThreshold dim q hδ (Nat.cast_nonneg dim)
    hQ hF le_rfl hqQ hδF
  refine ⟨T, hT, hTb, ?_⟩
  let logPg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + F + 4
  have hlog : 0 ≤ logPg := by dsimp only [logPg]; positivity
  have hCexp : (C : ℝ) ≤ Real.exp C := by linarith [Real.add_one_le_exp (C : ℝ)]
  have hCLog : (C : ℝ) ≤ logPg := by
    dsimp only [logPg]
    linarith [mul_nonneg (Nat.cast_nonneg (dim + 1) : (0 : ℝ) ≤ ((dim + 1 : ℕ) : ℝ)) hQ]
  refine ⟨Real.one_le_exp hlog, hc.trans (hCexp.trans (Real.exp_le_exp.mpr hCLog)), ?_, ?_⟩
  · have hpow : (q : ℝ) ^ (dim + 1) ≤ Real.exp (((dim + 1 : ℕ) : ℝ) * Q) := by
      calc
        _ ≤ (Real.exp Q) ^ (dim + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hqQ _
        _ = _ := (Real.exp_nat_mul _ _).symm
    have hscalar := scalarCubePrimitiveEnvelope_le_scaled (Fin dim) A 1 0 hq
    simp only [Fintype.card_fin] at hscalar
    apply hscalar.trans
    calc
      _ ≤ Real.exp C * Real.exp (((dim + 1 : ℕ) : ℝ) * Q) :=
        mul_le_mul (hs.trans hCexp) hpow (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
      _ = Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    rw [Nat.cast_mul]
    calc
      _ ≤ (Real.exp 4 * Real.exp F) * Real.exp Q :=
        mul_le_mul (hstep.trans (mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)))
          hqQ (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (4 + F + Q) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        push_cast
        nlinarith only [hQ, mul_nonneg (Nat.cast_nonneg dim : (0 : ℝ) ≤ dim) hQ,
          Nat.cast_nonneg (α := ℝ) C])

theorem exists_uniform_slicedGridParameters (dim : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {F Q : ℝ}, 0 ≤ F → 0 ≤ Q →
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
      ∀ {δ : ℝ} {q step : ℕ}, 0 < δ → δ⁻¹ ≤ Real.exp F → 0 < q →
        (q : ℝ) ≤ Real.exp Q → (step : ℝ) ≤ 4 * Real.exp F →
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        1 ≤ Pg ∧ scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro F Q hF hQ
  let T : ℕ := ⌈Real.exp (dim + Q + F)⌉₊
  refine ⟨T, natCeil_le_exp_succ (Real.exp_nonneg _) (by positivity) le_rfl, ?_⟩
  intro δ q step hδ hδF hq hqQ hstep
  obtain ⟨_, _, _, hprimitive⟩ := hparameters hF hQ hδ hδF hq hqQ hstep
  refine ⟨?_, hprimitive⟩
  have hdim : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp dim := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.add_one_le_exp (dim : ℝ)
  have hbound : (((dim + 1) * q : ℕ) : ℝ) / δ ≤ Real.exp (dim + Q + F) := by
    rw [Nat.cast_mul, div_eq_mul_inv]
    exact (mul_le_mul (mul_le_mul hdim hqQ (Nat.cast_nonneg _) (Real.exp_nonneg _))
      hδF (inv_nonneg.mpr hδ.le) (by positivity)).trans_eq
      (by rw [← Real.exp_add, ← Real.exp_add])
  exact hbound.trans (Nat.le_ceil _)

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem exists_canonicalSlicedGridParameters (m dim nX : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Pk Qstride F : ℝ}, 0 ≤ Pk → 0 ≤ Qstride → 0 ≤ F →
      let Q := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp (dim + Q + F + 1) ∧
      ∀ {G : Type*} [Fintype G] {M length : ℕ} (selection : Fin dim ↪ G)
        (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → (∀ i, 0 < stride i) →
        (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        ∀ (x : G → IntegerScalarCubeBox (Fin dim) length) {δ : ℝ} {step : ℕ},
        0 < δ → δ⁻¹ ≤ Real.exp F → (step : ℝ) ≤ 4 * Real.exp F →
        let q := canonicalSlicedModulus (M := M) selection stride m x
        let Pg := Real.exp (C + ((dim + 1 : ℕ) : ℝ) * Q + F + 4)
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧ 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Pg ∧ ((step * q : ℕ) : ℝ) ≤ Pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_uniform_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro Pk Qstride F hPk hQstride hF Q
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  obtain ⟨T, hT, hparams⟩ := hparameters hF hQ
  refine ⟨T, hT, ?_⟩
  intro G _ M length selection stride hM hstride hstrideBound x δ step hδ hδF hstep q Pg
  have hq : 0 < q := canonicalSlicedModulus_pos selection stride m hstride x
  have hqQ : (q : ℝ) ≤ Real.exp Q := by
    simpa only [Q, Fintype.card_fin] using
      canonicalSlicedModulus_le_exp selection stride m hPk hQstride hM hstrideBound x
  exact hparams hδ hδF hq hqQ hstep

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_detectedCanonicalGridParameters (m dim nX : ℕ) (A : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {Pk Qstride p : ℝ},
      0 ≤ Pk → 0 ≤ Qstride → 0 ≤ p →
      let Q := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let tg := (dim : ℝ) + Q + (p + 1) + 1
      let pg := (C : ℝ) + ((dim + 1 : ℕ) : ℝ) * Q + (p + 1) + 4
      let δ := Real.exp (-(p + 1))
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp (p + 1) ∧ 0 ≤ tg ∧ 0 ≤ pg ∧
      ∃ T : ℕ, (T : ℝ) ≤ Real.exp tg ∧
      ∀ {M period : ℕ} (stride : Fin nX → ℕ),
        (M : ℝ) ≤ Real.exp Pk → 0 < period → period ≤ M ^ (m + 1) →
        (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp Qstride) →
        let q := residueRefinedPeriod period stride
        (((dim + 1) * q : ℕ) : ℝ) / δ ≤ T ∧
        1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ Real.exp pg ∧
        scalarCubePrimitiveEnvelope (Fin dim) A 1 0 q ≤ Real.exp pg ∧
        ∀ {Y : Type*} (step : Y → ℕ),
          (∀ y, (step y : ℝ) ≤ 4 * Real.exp (p + 1)) →
          ∀ y, ((step y * q : ℕ) : ℝ) ≤ Real.exp pg := by
  obtain ⟨C, hC, hparameters⟩ := exists_uniform_slicedGridParameters dim A
  refine ⟨C, hC, ?_⟩
  intro Pk Qstride p hPk hQstride hp Q tg pg δ
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hF : 0 ≤ p + 1 := by positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδF : δ⁻¹ ≤ Real.exp (p + 1) := by
    simp only [δ, Real.exp_neg, inv_inv, le_refl]
  obtain ⟨T, hT, hgrid⟩ := hparameters hF hQ
  refine ⟨hδ, Real.exp_le_one_iff.mpr (by linarith), hδF,
    by dsimp only [tg]; positivity, by dsimp only [pg]; positivity, T, hT, ?_⟩
  intro M period stride hM hperiod hperiodBound hstride hstrideBound q
  have hperiodLog : (period : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiodBound
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hq : 0 < q := residueRefinedPeriod_pos hperiod stride hstride
  have hqQ : (q : ℝ) ≤ Real.exp Q := by
    simpa only [Fintype.card_fin] using residueRefinedPeriod_exp_bound period stride hperiodLog hstrideBound
  have hstepZero : ((0 : ℕ) : ℝ) ≤ 4 * Real.exp (p + 1) := by
    simpa only [Nat.cast_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_nonneg (p + 1))
  obtain ⟨hQT, hPg, hcP, hsP, _⟩ := hgrid (step := 0) hδ hδF hq hqQ hstepZero
  refine ⟨hQT, hPg, hcP, hsP, ?_⟩
  intro Y step hstep y
  exact (hgrid hδ hδF hq hqQ (hstep y)).2.2.2.2

theorem detectedSlice_support_density {Y : Type*} (c : Y → ℤ)
    (step H L : Y → ℕ) {p : ℝ} (hstep : ∀ y, 0 < step y)
    (hdense : ∀ y, Real.exp (-(p + 1)) * L y ≤ (H y : ℝ)) :
    ∀ y, Real.exp (-(p + 1)) * L y ≤
      ((integerProgressionSupport (c y) (step y : ℤ) (H y)).card : ℝ) := by
  intro y
  simpa only [card_integerProgressionSupport _ _ _ (hstep y)] using hdense y

end Erdos3

end

section

namespace Erdos3

theorem blockTorusFactor_exp_bound (q h b : ℕ) {A D v : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hA : 0 ≤ A)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hb : (b : ℝ) ≤ D)
    (hAv : A ≤ Real.exp v) :
    (blockTorusFactor q h b A : ℝ) ≤ Real.exp (D ^ 2 + 2 * D + v + 4) := by
  have hbexp : (b : ℝ) ≤ Real.exp D := hb.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : ((q + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ h ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) h hh
  have hpowq := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (q + 1)) hqexp hD h hh
  have hblock : blockJetScaleBound q h b A ≤ Real.exp (D ^ 2 + 2 * D + v) := by
    unfold blockJetScaleBound
    calc
      _ ≤ Real.exp D * Real.exp D * Real.exp (D * D) * Real.exp v := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact (blockTorusFactor_upper q h b hA).trans
    (two_mul_add_three_exp_bound (by positivity) hblock)

theorem div_density_pow_exp_bound {X δ t w : ℝ} (n : ℕ)
    (_hX : 0 ≤ X) (hδ : 0 < δ) (hXt : X ≤ Real.exp t) (hδw : δ⁻¹ ≤ Real.exp w) :
    X / δ ^ n ≤ Real.exp (t + n * w) := by
  rw [div_eq_mul_inv, ← inv_pow]
  have hp : (δ⁻¹) ^ n ≤ Real.exp (n * w) := by
    calc
      _ ≤ (Real.exp w) ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδw n
      _ = _ := by rw [← Real.exp_nat_mul]
  exact (mul_le_mul hXt hp (by positivity) (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm

theorem slicedGrid_fourier_geometry_exp_bounds {Ta Ti γ C δ t v c w : ℝ}
    (hTa : 0 ≤ Ta) (hTi : 0 ≤ Ti) (hγ : 0 < γ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hTat : Ta ≤ Real.exp t) (hTit : Ti ≤ Real.exp t)
    (hγv : γ⁻¹ ≤ Real.exp v) (hCc : C ≤ Real.exp c) (hδw : δ⁻¹ ≤ Real.exp w)
    (degree d ta ti : ℕ) :
    (Ta / (2 * γ)) / δ ^ degree ≤ Real.exp (t + v + degree * w) ∧
    (Ti * C) / δ ^ degree ≤ Real.exp (t + c + degree * w) ∧
    Ta ^ d / δ ^ ta ≤ Real.exp (d * t + ta * w) ∧
    (Ti * C) ^ d / δ ^ ti ≤ Real.exp (d * (t + c) + ti * w) := by
  have hactive : Ta / (2 * γ) ≤ Real.exp (t + v) := by
    calc
      _ ≤ Ta / γ := div_le_div_of_nonneg_left hTa hγ (by linarith)
      _ = Ta * γ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp t * Real.exp v := mul_le_mul hTat hγv (inv_nonneg.mpr hγ.le) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hinactive : Ti * C ≤ Real.exp (t + c) :=
    (mul_le_mul hTit hCc hC (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm
  refine ⟨div_density_pow_exp_bound degree (by positivity) hδ hactive hδw,
    div_density_pow_exp_bound degree (by positivity) hδ hinactive hδw, ?_, ?_⟩
  · apply div_density_pow_exp_bound ta (by positivity) hδ _ hδw
    calc
      _ ≤ (Real.exp t) ^ d := pow_le_pow_left₀ hTa hTat d
      _ = _ := by rw [← Real.exp_nat_mul]
  · apply div_density_pow_exp_bound ti (by positivity) hδ _ hδw
    calc
      _ ≤ (Real.exp (t + c)) ^ d := pow_le_pow_left₀ (mul_nonneg hTi hC) hinactive d
      _ = _ := by rw [← Real.exp_nat_mul]

theorem slicedGrid_support_exp_bound (q h d : ℕ) {C R D v : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hCv : C ≤ Real.exp v) (hRv : R ≤ Real.exp v) :
    (d : ℝ) * (C * (2 ^ q * ((q : ℝ) + 1) ^ h) * R) + 1 / 4 ≤
      Real.exp (D ^ 2 + 2 * D + 2 * v + 1) := by
  have hdexp : (d : ℝ) ≤ Real.exp D := hd.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : (q : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp2 : (2 : ℝ) ^ q ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) q hq
  have hpq := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ (q : ℝ) + 1) hqexp hD h hh
  have hbound : (d : ℝ) * (C * (2 ^ q * ((q : ℝ) + 1) ^ h) * R) ≤
      Real.exp (D ^ 2 + 2 * D + 2 * v) := by
    calc
      _ ≤ Real.exp D * (Real.exp v * (Real.exp D * Real.exp (D * D)) * Real.exp v) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hsum := add_le_exp_add_one (by positivity : 0 ≤ D ^ 2 + 2 * D + 2 * v)
    (by norm_num : (0 : ℝ) ≤ 0) hbound (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  simpa only [add_zero] using hsum

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

def slicedGridGeometryLog {A : Type*} [Semiring A] (D v w t : A) : A :=
  (D + 1) * (D ^ 2 + 2 * D + v + 8 + (D + v + 8 + D + 1) + D * w) +
    (2 * D * t + D + 2 * (D + v + 8) + 5) + (D ^ 2 + 2 * D + 2 * v + 1)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) (q d T : ℕ)
local notation "degree" => j.val + 1
local notation "b" => Fintype.card (B (Sigma.mk j (Sum.inr i)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "cost" => (inactiveDenominator gamma : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor q degree b (4 * gamma)
local notation "torusI" => blockTorusFactor q degree b 1

theorem allocatedSlicedGrid_geometry_bounds {δ D v w t : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hδ : 0 < δ) (hR : 0 < R j)
    (hq : (q : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D) (hb : (b : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v) :
    let p := slicedGridGeometryLog D v w t
    ((torusA : ℝ) / (2 * gamma)) / δ ^ degree ≤ Real.exp p ∧
    (torusI : ℝ) * cost / δ ^ degree ≤ Real.exp p ∧
    (torusA : ℝ) ^ d / δ ^ ((layerTailDegree m + 1) * d) ≤ Real.exp p ∧
    ((torusI : ℝ) * cost) ^ d / δ ^ (degree * d) ≤ Real.exp p ∧
    (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ≤ Real.exp p ∧
    (d : ℝ) * ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
      ((2 : ℝ) ^ q * ((q : ℝ) + 1) ^ degree) * R j) + 1 / 4 ≤ Real.exp p := by
  intro p
  let g := D + v + 8
  let tau := D ^ 2 + 2 * D + v + 8
  let c := g + D + 1
  let Z := tau + c + D * w
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hγ : 0 < gamma := principalProfileSize_pos hR _
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  obtain ⟨hγupper, hγinv⟩ := principalProfileSize_exp_bounds _ hR hslots hRv hRi
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hA : 4 * gamma ≤ Real.exp (v + 4) := by
    exact (mul_le_mul h4 hγupper hγ.le (Real.exp_nonneg _)).trans_eq (by rw [← Real.exp_add, add_comm])
  have hTa : (torusA : ℝ) ≤ Real.exp tau := by
    have h := blockTorusFactor_exp_bound q degree b hD (by positivity) (by positivity) hq hdegree hb hA
    convert h using 1
    dsimp [tau]
    ring_nf
  have hTi : (torusI : ℝ) ≤ Real.exp tau := by
    have h := blockTorusFactor_exp_bound q degree b hD (by positivity : 0 ≤ v + 4)
      (by norm_num : (0 : ℝ) ≤ 1) hq hdegree hb (Real.one_le_exp_iff.mpr (by positivity))
    convert h using 1
    dsimp [tau]
    ring_nf
  have hden := inactiveDenominator_le_exp hγ hg hγinv
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp2 : (2 : ℝ) ^ degree ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) degree hdegree
  have hcost : cost ≤ Real.exp c := by
    exact (mul_le_mul hden hp2 (by positivity) (Real.exp_nonneg _)).trans_eq (by
      rw [← Real.exp_add]; dsimp [c]; congr 1; ring)
  obtain ⟨hVa, hVi, hWa, hWi⟩ := slicedGrid_fourier_geometry_exp_bounds
    (Nat.cast_nonneg torusA) (Nat.cast_nonneg torusI) hγ (by positivity) hδ hTa hTi hγinv hcost hδw
    degree d ((layerTailDegree m + 1) * d) (degree * d)
  have hbase0 : 0 ≤ (D + 1) * Z := by positivity
  have hcut0 : 0 ≤ 2 * D * t + D + 2 * g + 5 := by positivity
  have hsup0 : 0 ≤ D ^ 2 + 2 * D + 2 * v + 1 := by positivity
  have hbase : (D + 1) * Z ≤ p := by
    change (D + 1) * Z ≤ (D + 1) * Z + (2 * D * t + D + 2 * g + 5) + (D ^ 2 + 2 * D + 2 * v + 1)
    linarith only [hcut0, hsup0]
  have hsingle : Z ≤ p := (by nlinarith only [mul_nonneg hD hZ] : Z ≤ (D + 1) * Z).trans hbase
  have hprod : D * Z ≤ p := (by nlinarith only [hZ] : D * Z ≤ (D + 1) * Z).trans hbase
  have hcut : 2 * D * t + D + 2 * g + 5 ≤ p := by
    change _ ≤ (D + 1) * Z + (2 * D * t + D + 2 * g + 5) + (D ^ 2 + 2 * D + 2 * v + 1)
    linarith only [hbase0, hsup0]
  have hsup : D ^ 2 + 2 * D + 2 * v + 1 ≤ p := by
    change _ ≤ (D + 1) * Z + (2 * D * t + D + 2 * g + 5) + (D ^ 2 + 2 * D + 2 * v + 1)
    linarith only [hbase0, hcut0]
  refine ⟨hVa.trans (Real.exp_le_exp.mpr ?_), hVi.trans (Real.exp_le_exp.mpr ?_),
    hWa.trans (Real.exp_le_exp.mpr ?_), hWi.trans (Real.exp_le_exp.mpr ?_), ?_, ?_⟩
  · apply le_trans _ hsingle
    change tau + g + _ ≤ tau + (g + D + 1) + D * w
    linarith only [hD, mul_le_mul_of_nonneg_right hdegree hw]
  · apply le_trans _ hsingle
    dsimp [Z]
    linarith only [mul_le_mul_of_nonneg_right hdegree hw]
  · apply le_trans _ hprod
    simp only [Nat.cast_mul]
    calc
      _ ≤ D * tau + (D * D) * w := by gcongr
      _ ≤ D * Z := by dsimp [Z]; nlinarith only [mul_nonneg hD hc]
  · apply le_trans _ hprod
    simp only [Nat.cast_mul]
    calc
      _ ≤ D * (tau + c) + (D * D) * w := by gcongr
      _ = D * Z := by dsimp [Z]; ring
  · apply (allocatedSlicedGridHeightCutoff_exp_bound B R j i hR T hg ht hγinv hT).trans
    apply Real.exp_le_exp.mpr
    apply le_trans _ hcut
    calc
      _ ≤ D * t + D * (t + 1) + 2 * g + 5 := by gcongr
      _ = _ := by ring
  · exact (slicedGrid_support_exp_bound q degree d hD hv (by positivity) hR.le hq hdegree hd hcoeff hRv).trans
      (Real.exp_le_exp.mpr hsup)

end Erdos3.VectorPolynomial

end

end OAI

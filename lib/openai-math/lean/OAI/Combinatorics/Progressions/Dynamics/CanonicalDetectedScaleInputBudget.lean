import OAI.Combinatorics.Progressions.Estimates.DetectedCanonicalEarlyRadiusModelBounds
import OAI.Combinatorics.Progressions.Estimates.JointTupleTolerance

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem natCeil_le_exp_succ_of_le {x p : ℝ} (hp : 0 ≤ p) (hx : x ≤ Real.exp p) :
    (⌈x⌉₊ : ℝ) ≤ Real.exp (p+1) := by
  calc
    _ ≤ (⌈Real.exp p⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hx
    _ ≤ Real.exp p+1 := (Nat.ceil_lt_add_one (Real.exp_pos p).le).le
    _ = 1+Real.exp p := add_comm _ _
    _ ≤ _ := one_add_le_exp_succ hp le_rfl

def scalarCubeGridRatioLog (a : ℕ) : ℝ := ((a : ℝ)+1)^2+4*a+3

theorem scalarCubeGridRatioLog_nonneg (a : ℕ) : 0 ≤ scalarCubeGridRatioLog a := by
  unfold scalarCubeGridRatioLog
  positivity

theorem scalarCubeGridRatio_le_exp (α : Type*) [Fintype α] [DecidableEq α] :
    2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α) ≤
      Real.exp (scalarCubeGridRatioLog (Fintype.card α)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ)^3 := by norm_num
      _ ≤ (Real.exp 1)^3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hv := scalarCubeDomainDensity_le_exp α
  have hv0 := (scalarCubeDomainDensity_pos α).le
  have ha := Real.add_one_le_exp (Fintype.card α : ℝ)
  have heq : 2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α) =
      8*(2 : ℝ)^Fintype.card α*4^Fintype.card α*((Fintype.card α : ℝ)+1)*scalarCubeDomainDensity α := by
    unfold scalarCubeGridBoundaryConstant scalarCubeDomainDensity
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_finset]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ Real.exp 3*(Real.exp 1)^Fintype.card α*(Real.exp 2)^Fintype.card α*
        Real.exp (Fintype.card α : ℝ)*Real.exp (((Fintype.card α : ℝ)+1)^2) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold scalarCubeGridRatioLog
      ring

def scalarTupleToleranceLog (a n : ℕ) (v k e : ℝ) : ℝ :=
  scalarCubeGridRatioLog a+a+n+v+k+e+1

theorem scalarTupleToleranceLog_nonneg (a n : ℕ) {v k e : ℝ}
    (hv : 0 ≤ v) (hk : 0 ≤ k) (he : 0 ≤ e) : 0 ≤ scalarTupleToleranceLog a n v k e := by
  have hr := scalarCubeGridRatioLog_nonneg a
  unfold scalarTupleToleranceLog
  positivity

theorem scalarTupleToleranceCutoff_le_exp (α T : Type*)
    [Fintype α] [DecidableEq α] [Fintype T] {m : ℕ} {K ε v k e : ℝ}
    (hv : 0 ≤ v) (hk : 0 ≤ k) (he : 0 ≤ e) (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hm : (m : ℝ) ≤ Real.exp v) (hK : K ≤ Real.exp k) (hi : ε⁻¹ ≤ Real.exp e) :
    (scalarTupleToleranceCutoff α T m K ε : ℝ) ≤
      Real.exp (scalarTupleToleranceLog (Fintype.card α) (Fintype.card T) v k e) := by
  let U := scalarCubeGridRatioLog (Fintype.card α)+Fintype.card α+Fintype.card T+v+k+e
  have hr := scalarCubeGridRatioLog_nonneg (Fintype.card α)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hsize : (((Fintype.card α+1)*m : ℕ) : ℝ) ≤ Real.exp U := by
    calc
      _ = ((Fintype.card α : ℝ)+1)*m := by push_cast; rfl
      _ ≤ Real.exp (Fintype.card α : ℝ)*Real.exp v :=
        mul_le_mul (Real.add_one_le_exp _) hm (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (Fintype.card α+v) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [U]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card T)])
  have hb : 2*scalarCubeGridBoundaryConstant α*m/volume.real (scalarCubeDomain α) ≤ Real.exp U := by
    calc
      _ = (2*scalarCubeGridBoundaryConstant α/volume.real (scalarCubeDomain α))*m := by ring
      _ ≤ Real.exp (scalarCubeGridRatioLog (Fintype.card α))*Real.exp v :=
        mul_le_mul (scalarCubeGridRatio_le_exp α) hm (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (scalarCubeGridRatioLog (Fintype.card α)+v) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        dsimp only [U]
        linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α), Nat.cast_nonneg (α := ℝ) (Fintype.card T)])
  have ht : (Fintype.card T+1 : ℝ)*m*K/ε ≤ Real.exp U := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp (Fintype.card T : ℝ)*Real.exp v*Real.exp k*Real.exp e := by
        gcongr
        exact Real.add_one_le_exp _
      _ = Real.exp (Fintype.card T+v+k+e) := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [U]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)])
  change _ ≤ Real.exp (U+1)
  unfold scalarTupleToleranceCutoff
  simp only [Nat.cast_max, Nat.cast_one]
  exact max_le (Real.one_le_exp_iff.mpr (by linarith))
    (max_le (hsize.trans (Real.exp_le_exp.mpr (by linarith)))
      (max_le (natCeil_le_exp_succ_of_le hU hb) (natCeil_le_exp_succ_of_le hU ht)))

end Erdos3

end

section

namespace Erdos3

noncomputable def slicedDetectionGainLog (s C count : ℕ) (p q a : ℝ) : ℝ :=
  (5 * p + 20) * count + p + 2 + a + 1 + (2 ^ (s + 1) : ℕ) * (q + C) ^ C

theorem slicedDetectionGainLog_nonneg (s C count : ℕ) {p q a : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) :
    0 ≤ slicedDetectionGainLog s C count p q a := by
  unfold slicedDetectionGainLog
  positivity

theorem slicedDetectionGain_lower (s C count : ℕ) {p q a α : ℝ}
    (hα : Real.exp (-a) ≤ α) :
    Real.exp (-slicedDetectionGainLog s C count p q a) ≤
      (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
        Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
  have hhalf : Real.exp (-(a + 1)) ≤ α / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh : 2 * Real.exp (-(a + 1)) ≤ Real.exp (-a) := by
      calc
        _ ≤ Real.exp 1 * Real.exp (-(a + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    linarith
  calc
    _ = (Real.exp (-((5 * p + 20) * count + p + 2)) * Real.exp (-(a + 1))) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold slicedDetectionGainLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)) (by positivity)

theorem slicedDetection_kernel_cutoff_bound (s C count : ℕ) (G : Type*) [Fintype G]
    {p q a α : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hα : Real.exp (-a) ≤ α) :
    let gain := (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
      Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1))
    let gainLog := slicedDetectionGainLog s C count p q a
    let R := gainLog + p + 4
    (scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2) : ℝ) ≤
      Real.exp (scalarKernelLogarithmicBudget (Fin (s + 1)) G R) := by
  intro gain gainLog R
  have hgain := slicedDetectionGain_lower s C count (p := p) (q := q) hα
  have hg : 0 < gain := (Real.exp_pos _).trans_le hgain
  have hlog : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s C count hp hq ha
  have hR : 0 ≤ R := by dsimp only [R]; linarith
  have hD : (⌈Real.exp (p + 1)⌉₊ : ℝ) ≤ Real.exp (p + 2) := by
    simpa only [add_assoc, one_add_one_eq_two] using
      natCeil_le_exp_succ_of_le (show 0 ≤ p + 1 by linarith) (le_refl (Real.exp (p + 1)))
  have hη : (gain / 2)⁻¹ ≤ Real.exp R := by
    have hgi : gain⁻¹ ≤ Real.exp gainLog := by
      simpa only [← Real.exp_neg, neg_neg] using (inv_le_inv₀ hg (Real.exp_pos _)).mpr hgain
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * gain⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1 * Real.exp gainLog := mul_le_mul htwo hgi (inv_nonneg.mpr hg.le) (Real.exp_nonneg _)
      _ = Real.exp (1 + gainLog) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp only [R]; linarith)
  exact scalarKernelCutoff_le_exp (Fin (s + 1)) G (by decide)
    (Nat.ceil_pos.mpr (Real.exp_pos _)) (half_pos hg) hR
    (by simpa only [Nat.cast_one] using Real.one_le_exp hR)
    (hD.trans (Real.exp_le_exp.mpr (by dsimp only [R]; linarith))) hη

theorem exists_slicedDetection_uniform_budget (s C : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p q a : ℝ} {count : ℕ} (G : Type*) [Fintype G],
      0 ≤ D → 0 ≤ p → 0 ≤ q → 0 ≤ a →
      (count : ℝ) ≤ D → (Fintype.card G : ℝ) ≤ D →
      slicedDetectionGainLog s C count p q a ≤ (D + p + q + a + A) ^ A ∧
      scalarKernelLogarithmicBudget (Fin (s + 1)) G
        (slicedDetectionGainLog s C count p q a + p + 4) ≤ (D + p + q + a + A) ^ A := by
  let X : Polynomial ℕ := Polynomial.X
  let g : Polynomial ℕ := (5 * X + 20) * X + X + 2 + X + 1 +
    Polynomial.C (2 ^ (s + 1)) * (X + Polynomial.C C) ^ C
  let dim : Polynomial ℕ := Polynomial.C (s + 1)
  let k : Polynomial ℕ := 2 * ((4 + 3 * (X * (dim + 1) * dim)) *
    (16 * (10 + dim + X + X * (dim + 1) + (g + X + 4)) ^ 3 + 2)) + 8
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget (g + k)
  refine ⟨A, hA, ?_⟩
  intro D p q a count G _ hD hp hq ha hcount hG
  let R := D + p + q + a
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hDR : D ≤ R := by dsimp only [R]; linarith
  have hpR : p ≤ R := by dsimp only [R]; linarith
  have hqR : q ≤ R := by dsimp only [R]; linarith
  have haR : a ≤ R := by dsimp only [R]; linarith
  have hcR := hcount.trans hDR
  have hGR := hG.trans hDR
  let gainR := (5 * R + 20) * R + R + 2 + R + 1 + (2 ^ (s + 1) : ℕ) * (R + C) ^ C
  let kernelR := 2 * ((4 + 3 * (R * ((s + 1 : ℕ) + 1) * (s + 1 : ℕ))) *
    (16 * (10 + (s + 1 : ℕ) + R + R * ((s + 1 : ℕ) + 1) + (gainR + R + 4)) ^ 3 + 2)) + 8
  have hgainR : slicedDetectionGainLog s C count p q a ≤ gainR := by
    dsimp only [slicedDetectionGainLog, gainR]
    gcongr
  have hgain0 : 0 ≤ gainR := by dsimp only [gainR]; positivity
  have hk0 : 0 ≤ kernelR := by dsimp only [kernelR]; positivity
  have hgainActual := slicedDetectionGainLog_nonneg s C count hp hq ha
  have hkernelR : scalarKernelLogarithmicBudget (Fin (s + 1)) G
      (slicedDetectionGainLog s C count p q a + p + 4) ≤ kernelR := by
    rw [scalarKernelLogarithmicBudget_eq]
    simp only [Fintype.card_fin]
    dsimp only [kernelR]
    push_cast
    gcongr
  have hbound : gainR + kernelR ≤ (R + A) ^ A := by
    simpa [X, g, k, dim, gainR, kernelR, Polynomial.eval₂_pow] using hb R hR
  exact ⟨hgainR.trans ((le_add_of_nonneg_right hk0).trans hbound),
    hkernelR.trans ((le_add_of_nonneg_left hgain0).trans hbound)⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_canonicalDetectedScaleInput_budget (s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P pSlice u : ℝ} {count : ℕ},
      0 ≤ P → pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → (count : ℝ) ≤ P →
      let pModel := allocatedEarlyModelLog P pSlice count
      let pDetect := allocatedModelTestLog u pModel
      let aDetect := 2 * u + 4 * pModel + 7
      let gainLog := slicedDetectionGainLog s Cdetect count pDetect pDetect aDetect
      let target := gainLog + 32
      let budget := (P + C) ^ C
      P ≤ budget ∧ pModel ∈ Set.Icc 0 budget ∧ pDetect ∈ Set.Icc 0 budget ∧
        aDetect ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ target ∈ Set.Icc 0 budget := by
  obtain ⟨Adet, _, hdet⟩ := exists_allocatedEarlyDetector_budget
  let X : Polynomial ℕ := Polynomial.X
  let detectorPoly := (X + Polynomial.C Adet) ^ Adet
  let gainPoly := (5 * detectorPoly + 20) * X + detectorPoly + 2 + detectorPoly + 1 +
    Polynomial.C (2 ^ (s + 1)) * (detectorPoly + Polynomial.C Cdetect) ^ Cdetect
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (X + detectorPoly + gainPoly + 32)
  refine ⟨C, hC, ?_⟩
  intro P pSlice u count hP hpSlice hu hc pModel pDetect aDetect gainLog target budget
  obtain ⟨hM, hD, hA⟩ := hdet hP hpSlice hu hc
  let detectorBound := (P + Adet) ^ Adet
  let gainBound := (5 * detectorBound + 20) * P + detectorBound + 2 + detectorBound + 1 +
    (2 ^ (s + 1) : ℕ) * (detectorBound + Cdetect) ^ Cdetect
  have hdet0 : 0 ≤ detectorBound := by dsimp only [detectorBound]; positivity
  have hgainBound0 : 0 ≤ gainBound := by dsimp only [gainBound]; positivity
  have hgain0 : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect count hD.1 hD.1 hA.1
  have hgain : gainLog ≤ gainBound := by
    dsimp only [gainLog, slicedDetectionGainLog, gainBound]
    have hD0 := hD.1
    gcongr <;> first | exact hD.2 | exact hA.2
  have hsum : P + detectorBound + gainBound + 32 ≤ budget := by
    simpa [X, detectorPoly, gainPoly, detectorBound, gainBound, Polynomial.eval₂_pow] using hbound P hP
  refine ⟨?_, ⟨hM.1, ?_⟩, ⟨hD.1, ?_⟩, ⟨hA.1, ?_⟩, ⟨hgain0, ?_⟩,
    ⟨by dsimp only [target]; positivity, ?_⟩⟩
  all_goals try dsimp only [target]
  all_goals linarith only [hP, hdet0, hgainBound0, hsum, hM.2, hD.2, hA.2, hgain]

end Erdos3

end

end OAI

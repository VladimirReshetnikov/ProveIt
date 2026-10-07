import OAI.Combinatorics.Progressions.Estimates.NormalizedFiberRescaling
import OAI.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coordinateRescaledDensity {I : Type*} (a : I → ℝ)
    (f : (I → ℝ) → ℝ) (x : I → ℝ) : ℝ := f (fun i => a i * x i)

theorem coordinateRescaledDensity_bound {I : Type*} (a : I → ℝ)
    (f : (I → ℝ) → ℝ) {C : ℝ} (hf : ∀ x, |f x| ≤ C) :
    ∀ x, |coordinateRescaledDensity a f x| ≤ C := fun x => hf (fun i => a i * x i)

theorem coordinateScale_lipschitz {I : Type*} [Fintype I]
    (a : I → ℝ) {C : ℝ≥0} (ha : ∀ i, |a i| ≤ C) :
    LipschitzWith C (fun x : I → ℝ => fun i => a i * x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg C.coe_nonneg (norm_nonneg _))).2
  intro i
  change ‖a i * x i - a i * y i‖ ≤ _
  rw [← mul_sub, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul (ha i) (norm_le_pi_norm (x - y) i) (norm_nonneg _) C.coe_nonneg

theorem coordinateRescaledDensity_lipschitz {I : Type*} [Fintype I]
    (a : I → ℝ) (f : (I → ℝ) → ℝ) {K C : ℝ≥0}
    (hf : LipschitzWith K f) (ha : ∀ i, |a i| ≤ C) :
    LipschitzWith (K * C) (coordinateRescaledDensity a f) :=
  hf.comp (coordinateScale_lipschitz a ha)

theorem maskedIntegerImageDensity_rescale {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℤ) (B : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ)
    {H : ℝ} (hH : H ≠ 0) (hP : ∀ i, P i ≠ 0) :
    maskedIntegerImageDensity A B P f =
      maskedIntegerImageDensity A B (fun _ => H) (coordinateRescaledDensity (fun i => H / P i) f) := by
  funext v
  have he : (fun i => H / P i * ((v i : ℝ) / H)) = fun i => (v i : ℝ) / P i := by
    funext i
    field_simp [hH, hP i]
  simp only [maskedIntegerImageDensity, coordinateRescaledDensity, he]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

theorem diagonalDensityTransport_bound (f : (ι → ℝ) → ℝ) {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    |diagonalDensityTransport a ha f x| ≤ |(∏ i, a i)⁻¹| * C := by
  rw [diagonalDensityTransport_eq, abs_mul, abs_inv, abs_abs]
  simpa only [abs_inv] using mul_le_mul_of_nonneg_left
    (hf (fun i => x i / a i)) (abs_nonneg ((∏ i, a i)⁻¹))

theorem diagonalDensityTransport_lipschitz (f : (ι → ℝ) → ℝ) {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hInv : ∀ i, |(a i)⁻¹| ≤ M) :
    LipschitzWith (‖(∏ i, a i)⁻¹‖₊ * (L * M)) (diagonalDensityTransport a ha f) := by
  have hs : LipschitzWith M (fun x : ι → ℝ => fun i => x i / a i) := by
    simpa only [div_eq_mul_inv, mul_comm] using coordinateScale_lipschitz (fun i => (a i)⁻¹) hInv
  have hi := hf.comp hs
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, diagonalDensityTransport_eq, ← mul_sub, abs_mul, abs_inv, abs_abs]
  simpa only [Function.comp_def, Real.dist_eq, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_inv, mul_assoc] using mul_le_mul_of_nonneg_left (hi.dist_le_mul x y) (abs_nonneg ((∏ i, a i)⁻¹))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

variable {I : Type*} [Fintype I]

theorem diagonalImageDensity_bound (d : I → ℝ) (f : (I → ℝ) → ℝ)
    {C : ℝ} (hf : ∀ x, |f x| ≤ C) (x : I → ℝ) :
    |diagonalImageDensity d f x| ≤ (∏ i, |d i|)⁻¹ * C := by
  have h : 0 ≤ (∏ i, |d i|)⁻¹ := inv_nonneg.mpr (Finset.prod_nonneg fun i _ => abs_nonneg _)
  simpa only [diagonalImageDensity, abs_mul, abs_of_nonneg h] using
    mul_le_mul_of_nonneg_left (hf (fun i => x i / d i)) h

theorem diagonalImageDensity_lipschitz (d : I → ℝ) (f : (I → ℝ) → ℝ)
    {K C : ℝ≥0} (hf : LipschitzWith K f) (hd : ∀ i, |(d i)⁻¹| ≤ C) :
    LipschitzWith (‖(∏ i, |d i|)⁻¹‖₊ * (K * C)) (diagonalImageDensity d f) := by
  have hs : LipschitzWith C (fun x : I → ℝ => fun i => x i / d i) := by
    simpa only [div_eq_mul_inv, mul_comm] using coordinateScale_lipschitz (fun i => (d i)⁻¹) hd
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, diagonalImageDensity, ← mul_sub, abs_mul]
  simpa only [Function.comp_def, Real.dist_eq, NNReal.coe_mul, coe_nnnorm,
    Real.norm_eq_abs, mul_assoc] using
      mul_le_mul_of_nonneg_left ((hf.comp hs).dist_le_mul x y)
        (abs_nonneg ((∏ i, |d i|)⁻¹))

theorem diagonalImageDensity_zero_outside (d : I → ℝ) (hd : ∀ i, d i ≠ 0)
    (f : (I → ℝ) → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hdC : ∀ i, |d i| ≤ C)
    (hf : ∀ x, R < ‖x‖ → f x = 0) (x : I → ℝ) (hx : C * R < ‖x‖) :
    diagonalImageDensity d f x = 0 := by
  have hn : ‖x‖ ≤ C * ‖fun i => x i / d i‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
    intro i
    have he : x i = d i * (x i / d i) := by field_simp [hd i]
    calc
      ‖x i‖ = |d i| * ‖x i / d i‖ := by
        simpa only [norm_mul, Real.norm_eq_abs] using congrArg norm he
      _ ≤ C * ‖fun i => x i / d i‖ :=
        mul_le_mul (hdC i) (norm_le_pi_norm (fun i => x i / d i) i) (norm_nonneg _) hC
  have hR : R < ‖fun i => x i / d i‖ := by
    by_contra h
    exact (not_lt_of_ge (hn.trans (mul_le_mul_of_nonneg_left (le_of_not_gt h) hC))) hx
  simp only [diagonalImageDensity, hf _ hR, mul_zero]

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def canonicalSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (W L : ℝ) (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  anisotropicSpatialKernelDensity s root D hp (1 + W) 1 L (by linarith) zero_lt_one hL

noncomputable def canonicalSpatialSiteDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (W L : ℝ) (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  coordinateRescaledDensity (fun i => (1 + W) / physicalSpatialOutputScale I (1 + W) 1 L i)
    (canonicalSpatialKernelDensity s root D hp W L hW hL)

theorem anisotropicSpatialKernelDensity_canonical {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {H T W L : ℝ} (hH : 0 < H) (hT : 0 < T) (hW : 0 ≤ W) (hL : 0 < L)
    (hscale : H = (1 + W) * T) :
    anisotropicSpatialKernelDensity s root D hp H T L hH hT hL =
      canonicalSpatialKernelDensity s root D hp W L hW hL := by
  unfold canonicalSpatialKernelDensity anisotropicSpatialKernelDensity
  apply normalizedFiberDensity_common_scale (c := T)
  · exact hT.ne'
  · rintro (i | i)
    · change H = T * (1 + W)
      nlinarith [hscale]
    · change T = T * 1
      ring
  · rintro (i | i)
    · change H = T * (1 + W)
      nlinarith [hscale]
    · change L * T = T * (L * 1)
      ring
  · intro j
    ring

theorem canonicalSpatialSiteDensity_bounds {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L κ : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    (∀ z, |canonicalSpatialSiteDensity s root D hp W L hW hL z| ≤ anisotropicSpatialDensityCap s κ) ∧
      LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ) * Real.toNNReal (1 + W))
        (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have h := anisotropicSpatialKernelDensity_bounds root D s ha zero_lt_one hL hκ
    (fun j => by simpa only [mul_one] using hr j) hD hminor
  have hcap : ∀ z, |canonicalSpatialKernelDensity s root D hp W L hW hL z| ≤
      anisotropicSpatialDensityCap s κ := h.1
  have hlip : LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ))
      (canonicalSpatialKernelDensity s root D hp W L hW hL) := h.2
  constructor
  · exact coordinateRescaledDensity_bound _ _ hcap
  · apply coordinateRescaledDensity_lipschitz _ _ hlip
    intro i
    rw [Real.coe_toNNReal _ ha.le]
    cases i with
    | inl i =>
      change |(1 + W) / (1 + W)| ≤ 1 + W
      rw [div_self ha.ne', abs_one]
      linarith
    | inr i =>
      change |(1 + W) / (L * 1)| ≤ 1 + W
      rw [mul_one, abs_div, abs_of_pos ha, abs_of_pos hL]
      exact div_le_self ha.le hL1

theorem anisotropicSpatial_mask_canonical {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0) (B : Matrix (Unit ⊕ I) N ℤ)
    {H T W L : ℝ} (hH : 0 < H) (hT : 0 < T) (hW : 0 ≤ W) (hL : 0 < L)
    (hscale : H = (1 + W) * T) :
    maskedIntegerImageDensity (selectedSpatialPivot root D s) B (physicalSpatialOutputScale I H T L)
      (anisotropicSpatialKernelDensity s root D hp H T L hH hT hL) =
    maskedIntegerImageDensity (selectedSpatialPivot root D s) B (fun _ => H)
      (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have hratio : (fun i => H / physicalSpatialOutputScale I H T L i) =
      (fun i => (1 + W) / physicalSpatialOutputScale I (1 + W) 1 L i) := by
    funext i
    cases i with
    | inl i => exact (div_self hH.ne').trans (div_self ha.ne').symm
    | inr i =>
      change H / (L * T) = (1 + W) / (L * 1)
      rw [hscale]
      field_simp
  rw [maskedIntegerImageDensity_rescale _ _ _ _ hH.ne'
    (fun i => (physicalSpatialOutputScale_pos I hH hT hL i).ne'),
    anisotropicSpatialKernelDensity_canonical s root D hp hH hT hW hL hscale, hratio]
  rfl

end Erdos3

end

end OAI

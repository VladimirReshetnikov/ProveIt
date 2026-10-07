import OAI.Combinatorics.Progressions.Dynamics.ScalarCubePrimitiveBudget
import OAI.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
import OAI.Combinatorics.Progressions.Probability.PrincipalCoefficientLaw

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def principalIntervalLength (K T γ : ℝ) : ℕ :=
  Nat.ceil (2 * γ * (K / T))

noncomputable def principalIntervalWeight (K T γ : ℝ) (x : Option Empty → ℝ) : ℝ :=
  (principalIntervalLength K T γ : ℝ) / (K / T) *
    normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2)
      ((principalIntervalLength K T γ : ℝ) / (K / T) * x none)

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

include hK hT hγ in
theorem principalIntervalLength_pos : 0 < principalIntervalLength K T γ := by
  apply Nat.ceil_pos.mpr
  positivity

include hK hT hγ hlarge in
theorem principalIntervalLength_bounds :
    2 * γ * (K / T) ≤ (principalIntervalLength K T γ : ℝ) ∧
      (principalIntervalLength K T γ : ℝ) ≤ 4 * γ * (K / T) := by
  have hP : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hwidth : 16 ≤ γ * (K / T) := by nlinarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * γ * (K / T) by positivity)
  constructor
  · exact Nat.le_ceil _
  · change (Nat.ceil (2 * γ * (K / T)) : ℝ) ≤ _
    nlinarith

theorem principalIntervalLength_support {k : ℤ}
    (hk : k ∈ (principalIntegerPMF K T γ hK hT hγ hlarge).support) :
    k ∈ Finset.Ico 0 (principalIntervalLength K T γ : ℤ) := by
  have hb := principalIntegerPMF_support hK hT hγ hlarge hk
  have he : T * (k : ℝ) / K = (k : ℝ) / (K / T) := by field_simp
  rw [he] at hb
  have hlo := (lt_div_iff₀ (div_pos hK hT)).mp hb.1
  have hhi := (div_lt_iff₀ (div_pos hK hT)).mp hb.2
  have hk0 : (0 : ℝ) ≤ k := (mul_pos hγ (div_pos hK hT)).le.trans hlo.le
  have hkL : (k : ℝ) < principalIntervalLength K T γ :=
    hhi.trans_le (Nat.le_ceil _)
  exact Finset.mem_Ico.mpr ⟨by exact_mod_cast hk0, by exact_mod_cast hkL⟩

theorem principalIntervalWeight_grid (k : ℤ) :
    principalIntervalWeight K T γ (fun _ => (k : ℝ) / principalIntervalLength K T γ) =
      (principalIntervalLength K T γ : ℝ) *
        (principalIntegerPMF K T γ hK hT hγ hlarge k).toReal := by
  have hL : (principalIntervalLength K T γ : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.ne_of_gt (principalIntervalLength_pos hK hT hγ))
  have hQ := (div_pos hK hT).ne'
  unfold principalIntervalWeight
  rw [show (principalIntervalLength K T γ : ℝ) / (K / T) *
      ((k : ℝ) / principalIntervalLength K T γ) = (k : ℝ) / (K / T) by field_simp]
  rw [normalizedIntegerInterpolation_grid (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge k]
  change _ = (principalIntervalLength K T γ : ℝ) *
    (normalizedIntegerPMF (K / T) (3 * γ / 2) (γ / 2) _ _ _ k).toReal
  field_simp

include hK hT hγ hlarge in
theorem principalIntervalWeight_range (x : Option Empty → ℝ) :
    0 ≤ principalIntervalWeight K T γ x ∧ principalIntervalWeight K T γ x ≤ 16 := by
  have hL := principalIntervalLength_pos hK hT hγ
  have ha0 : 0 ≤ (principalIntervalLength K T γ : ℝ) / (K / T) := by positivity
  have ha : (principalIntervalLength K T γ : ℝ) / (K / T) ≤ 4 * γ :=
    (div_le_iff₀ (div_pos hK hT)).mpr (principalIntervalLength_bounds hK hT hγ hlarge).2
  have hb := normalizedIntegerInterpolation_range (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge
      ((principalIntervalLength K T γ : ℝ) / (K / T) * x none)
  constructor
  · exact mul_nonneg ha0 hb.1
  · calc
      principalIntervalWeight K T γ x ≤
          ((principalIntervalLength K T γ : ℝ) / (K / T)) * (2 / (γ / 2)) :=
        mul_le_mul_of_nonneg_left hb.2 ha0
      _ ≤ (4 * γ) * (2 / (γ / 2)) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = 16 := by field_simp; ring

include hK hT hγ hlarge in
theorem principalIntervalWeight_lipschitz :
    LipschitzWith (128 * probabilityProfileLipschitz) (principalIntervalWeight K T γ) := by
  let a : ℝ := (principalIntervalLength K T γ : ℝ) / (K / T)
  have hL := principalIntervalLength_pos hK hT hγ
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ 4 * γ :=
    (div_le_iff₀ (div_pos hK hT)).mpr (principalIntervalLength_bounds hK hT hγ hlarge).2
  have hcoef : a ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) ≤
      128 * (probabilityProfileLipschitz : ℝ) := by
    calc
      _ ≤ (4 * γ) ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 ha 2) (by positivity)
      _ = _ := by field_simp; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy : |x none - y none| ≤ dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y none
  have hb := normalizedIntegerInterpolation_lipschitz_bound (K / T) (3 * γ / 2) (γ / 2)
    (div_pos hK hT) (by positivity) hlarge (a * x none) (a * y none)
  rw [Real.dist_eq]
  change |a * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (a * x none) -
    a * normalizedIntegerInterpolation (K / T) (3 * γ / 2) (γ / 2) (a * y none)| ≤
      (128 * (probabilityProfileLipschitz : ℝ)) * dist x y
  rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
  calc
    _ ≤ a * ((2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2) *
        |a * x none - a * y none|) := mul_le_mul_of_nonneg_left hb ha0
    _ = (a ^ 2 * (2 * (probabilityProfileLipschitz : ℝ) / (γ / 2) ^ 2)) *
        |x none - y none| := by rw [← mul_sub, abs_mul, abs_of_nonneg ha0]; ring
    _ ≤ (128 * (probabilityProfileLipschitz : ℝ)) * dist x y :=
      mul_le_mul hcoef hxy (abs_nonneg _) (by positivity)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem paddedResidueDensityCap_mono (I : Type*) [Fintype I] {M N : ℕ} (hMN : M ≤ N) :
    paddedResidueDensityCap I M ≤ paddedResidueDensityCap I N := by
  unfold paddedResidueDensityCap scalarCubeResidueDensityCap
  gcongr

theorem ScalarCubePrimitiveBudget.mono {I : Type*} [Fintype I] [DecidableEq I]
    {s : NormalizedScalarCubeSource I} {A : ℝ≥0} {U V : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hUV : U ≤ V) : ScalarCubePrimitiveBudget s A V :=
  ⟨h.one_le.trans hUV, h.dimension_le.trans hUV, h.modulus_le.trans hUV,
    h.weight_le.trans hUV, h.weightLipschitz_le.trans hUV, h.boundary_le.trans hUV,
    h.grid_le.trans hUV, h.derivative_le.trans hUV, h.density_le.trans hUV⟩

noncomputable def scalarCubePrimitiveEnvelope (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) : ℝ :=
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  1 + q + M + B + T + 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2 +
    2 * scalarCubeGridBoundaryConstant I * V + scalarCubeCutoffDerivativeNumerator I A +
      paddedResidueDensityCap I M

theorem scalarCubePrimitiveBudget_of_raw_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A B T : ℝ≥0) (M : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (scalarCubePrimitiveEnvelope I A B T M) := by
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  let X := 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2
  let Y := 2 * scalarCubeGridBoundaryConstant I * V
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hX : 0 ≤ X := by dsimp only [X, V]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y, V, scalarCubeGridBoundaryConstant]; positivity
  have hZ : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator; positivity
  have hP : 0 ≤ paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap; positivity
  have hparts :
      1 ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      q ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (M : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (B : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (T : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      X ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      Y ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      paddedResidueDensityCap I M ≤ scalarCubePrimitiveEnvelope I A B T M := by
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧ _
    dsimp only [scalarCubePrimitiveEnvelope]
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      q ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (M : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (B : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (T : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      X ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      Y ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      paddedResidueDensityCap I M ≤ 1 + q + M + B + T + X + Y + _ + _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hq, hX, hY, hZ, hP, Nat.cast_nonneg (α := ℝ) M, B.coe_nonneg, T.coe_nonneg]
  obtain ⟨h1, hq', hM', hB', hT', hX', hY', hZ', hP'⟩ := hparts
  have hvol : scalarCubeDomainDensity I ≤ V := scalarCubeDomainDensity_le_power I
  have hboundary : scalarCubeBoundaryConstant I ≤ X := by
    unfold scalarCubeBoundaryConstant
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by norm_num)) (by positivity)
  have hgrid : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hvol
      (show 0 ≤ 2 * scalarCubeGridBoundaryConstant I by unfold scalarCubeGridBoundaryConstant; positivity)
    simpa only [scalarCubeDomainDensity, div_eq_mul_inv, Y] using hh
  refine ⟨h1, hq', ?_, ?_, ?_, hboundary.trans hX', hgrid.trans hY', hZ', ?_⟩
  · exact (by exact_mod_cast hM : (s.modulusBound : ℝ) ≤ M).trans hM'
  · exact (by exact_mod_cast hB : (s.weightBound : ℝ) ≤ B).trans hB'
  · exact (by exact_mod_cast hT : (s.weightLipschitz : ℝ) ≤ T).trans hT'
  · exact (paddedResidueDensityCap_mono I hM).trans hP'

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem scalarCubePrimitiveEnvelope_nonneg (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) : 0 ≤ scalarCubePrimitiveEnvelope I A B T M := by
  unfold scalarCubePrimitiveEnvelope scalarCubeGridBoundaryConstant
    scalarCubeCutoffDerivativeNumerator paddedResidueDensityCap scalarCubeResidueDensityCap
  positivity

theorem scalarCubePrimitiveEnvelope_mono (I : Type*) [Fintype I] (A : ℝ≥0)
    {B B' T T' : ℝ≥0} {M N : ℕ} (hB : B ≤ B') (hT : T ≤ T') (hM : M ≤ N) :
    scalarCubePrimitiveEnvelope I A B T M ≤ scalarCubePrimitiveEnvelope I A B' T' N := by
  have hB' : (B : ℝ) ≤ B' := hB
  have hT' : (T : ℝ) ≤ T' := hT
  have hM' : (M : ℝ) ≤ N := Nat.cast_le.mpr hM
  have hc := paddedResidueDensityCap_mono I hM
  dsimp only [scalarCubePrimitiveEnvelope]
  linarith only [hB', hT', hM', hc]

theorem paddedResidueDensityCap_scale (I : Type*) [Fintype I] (M : ℕ) :
    paddedResidueDensityCap I M =
      paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
  simp only [paddedResidueDensityCap, scalarCubeResidueDensityCap, Nat.cast_one, mul_one, mul_pow]
  ring

theorem scalarCubePrimitiveEnvelope_split (I : Type*) [Fintype I]
    (A B T : ℝ≥0) (M : ℕ) :
    scalarCubePrimitiveEnvelope I A B T M =
      scalarCubePrimitiveEnvelope I A B T 0 + M + paddedResidueDensityCap I M := by
  simp only [scalarCubePrimitiveEnvelope, paddedResidueDensityCap, scalarCubeResidueDensityCap,
    Nat.cast_zero, mul_zero, zero_pow (Nat.succ_ne_zero _), add_zero]
  ring

theorem scalarCubePrimitiveEnvelope_le_scaled (I : Type*) [Fintype I]
    (A B T : ℝ≥0) {M : ℕ} (hM : 1 ≤ M) :
    scalarCubePrimitiveEnvelope I A B T M ≤
      scalarCubePrimitiveEnvelope I A B T 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : (1 : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) := one_le_pow₀ hM'
  have hMp : (M : ℝ) ≤ (M : ℝ) ^ (Fintype.card I + 1) := by
    calc
      _ = 1 * (M : ℝ) := (one_mul _).symm
      _ ≤ (M : ℝ) ^ Fintype.card I * M :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hM') (Nat.cast_nonneg _)
      _ = _ := (pow_succ _ _).symm
  have hzero := scalarCubePrimitiveEnvelope_nonneg I A B T 0
  have hc : scalarCubePrimitiveEnvelope I A B T 0 ≤
      scalarCubePrimitiveEnvelope I A B T 0 * (M : ℝ) ^ (Fintype.card I + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hzero
  calc
    _ = scalarCubePrimitiveEnvelope I A B T 0 + M +
        paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
      rw [scalarCubePrimitiveEnvelope_split I A B T M, paddedResidueDensityCap_scale]
    _ ≤ scalarCubePrimitiveEnvelope I A B T 0 * (M : ℝ) ^ (Fintype.card I + 1) +
        (M : ℝ) ^ (Fintype.card I + 1) +
        paddedResidueDensityCap I 1 * (M : ℝ) ^ (Fintype.card I + 1) := by
      gcongr
    _ = _ := by rw [scalarCubePrimitiveEnvelope_split I A B T 1]; push_cast; ring

theorem scalarCubePrimitiveEnvelope_eq_of_card
    (I J : Type*) [Fintype I] [Fintype J] (h : Fintype.card I = Fintype.card J)
    (A B T : ℝ≥0) (M : ℕ) :
    scalarCubePrimitiveEnvelope I A B T M = scalarCubePrimitiveEnvelope J A B T M := by
  simp only [scalarCubePrimitiveEnvelope, scalarCubeGridBoundaryConstant,
    scalarCubeCutoffDerivativeNumerator, paddedResidueDensityCap, scalarCubeResidueDensityCap,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_finset, h]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def normalizedUniformCubeSource (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) :
    NormalizedScalarCubeSource I where
  length := L
  modulusBound := M
  length_pos := hL
  modulus := m
  residue := r
  modulus_pos := hm
  modulus_le := hmM
  size := hsize
  weight := fun _ => 1
  weightBound := 1
  weightLipschitz := 0
  weightBound_pos := by norm_num
  weight_range := fun _ => by norm_num
  weight_lipschitz := LipschitzWith.const 1
  normalized := (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean_const 1

theorem normalizedUniformCubeSource_mean (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (f : IntegerScalarCubeBox I L → ℝ) :
    (normalizedUniformCubeSource I L M hL m r hm hmM hsize).source.mean f =
      (scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean f := by
  simp only [NormalizedScalarCubeSource.source, NormalizedScalarCubeSource.baseLaw,
    normalizedUniformCubeSource, FiniteProbabilityWeights.reweight, FiniteProbabilityWeights.mean, mul_one]
  rfl

theorem normalizedUniformCubeSource_primitive (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (normalizedUniformCubeSource I L M hL m r hm hmM hsize) A
      (scalarCubePrimitiveEnvelope I A 1 0 M) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 M le_rfl le_rfl le_rfl

theorem normalizedUniformCubeSource_translated_mean (q L M : ℕ) (c : ℤ) (hL : 0 < L)
    (m : Option (Fin q) → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card (Fin q) + 1) * M ≤ L)
    (f : (Option (Fin q) → ℤ) → ℝ) :
    (normalizedUniformCubeSource (Fin q) L M hL m (shiftScalarCubeResidues c m r) hm hmM hsize).source.mean
      (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
        𝔼 p : TranslatedResidueSupportedCube q L c m r, f (supportedCubeCoordinates p.val.val) := by
  apply (normalizedUniformCubeSource_mean (Fin q) L M hL m (shiftScalarCubeResidues c m r) hm hmM hsize
    (fun x => f (shiftScalarCube c (fun i => (x i : ℤ))))).trans
  rw [scalarCubeResidueWeights_mean]
  apply Fintype.expect_equiv (shiftedScalarCubeResidueEquiv q L c m r)
  intro x
  rw [shiftedScalarCubeResidueEquiv_coordinates]

noncomputable def normalizedProgressionCubeSource (q m H : ℕ) (c : ℤ)
    (hL : 0 < m * H) (hm : 0 < m) (hsize : (q + 1) * m ≤ m * H) : NormalizedScalarCubeSource (Fin q) :=
  normalizedUniformCubeSource (Fin q) (m * H) m hL (fun _ => m)
    (shiftScalarCubeResidues c (fun _ => m) (progressionCubeResidues q m c))
    (fun _ => hm) (fun _ => le_rfl) (by simpa only [Fintype.card_fin] using hsize)

theorem normalizedProgressionCubeSource_mean (q m H : ℕ) (c : ℤ)
    (hL : 0 < m * H) (hm : 0 < m) (hsize : (q + 1) * m ≤ m * H)
    (f : (Option (Fin q) → ℤ) → ℝ) :
    (normalizedProgressionCubeSource q m H c hL hm hsize).source.mean
      (fun x => f (shiftScalarCube c (fun i => (x i : ℤ)))) =
        𝔼 p : SupportedCube q (integerProgressionSupport c (m : ℤ) H : Set ℤ), f (supportedCubeCoordinates p.val) := by
  unfold normalizedProgressionCubeSource
  rw [normalizedUniformCubeSource_translated_mean]
  exact (Fintype.expect_equiv (progressionResidueSupportedCubeEquiv q m H c hm) _ _ (fun _ => rfl)).symm

theorem normalizedProgressionCubeSource_primitive (q m H : ℕ) (c : ℤ)
    (hL : 0 < m * H) (hm : 0 < m) (hsize : (q + 1) * m ≤ m * H) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (normalizedProgressionCubeSource q m H c hL hm hsize) A
      (scalarCubePrimitiveEnvelope (Fin q) A 1 0 m) :=
  normalizedUniformCubeSource_primitive _ _ _ _ _ _ _ _ _ A

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def principalNormalizedSource {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    NormalizedScalarCubeSource Empty :=
  normalizedScalarCubeSourceOfIntegerPMF
    (principalIntervalLength K T γ) (principalIntervalLength_pos hK hT hγ)
    (principalIntegerPMF K T γ hK hT hγ hlarge)
    (fun k hk => principalIntervalLength_support hK hT hγ hlarge hk)
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalIntervalWeight_grid hK hT hγ hlarge)

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

theorem principalNormalizedSource_parameters :
    (principalNormalizedSource hK hT hγ hlarge).length = principalIntervalLength K T γ ∧
    (principalNormalizedSource hK hT hγ hlarge).modulusBound = 1 ∧
    (principalNormalizedSource hK hT hγ hlarge).weightBound = 16 ∧
    (principalNormalizedSource hK hT hγ hlarge).weightLipschitz =
      128 * probabilityProfileLipschitz := ⟨rfl, rfl, rfl, rfl⟩

theorem principalNormalizedSource_law :
    (principalNormalizedSource hK hT hγ hlarge).source.toPMF.map (fun x => (x none : ℤ)) =
      principalIntegerPMF K T γ hK hT hγ hlarge :=
  normalizedScalarCubeSourceOfIntegerPMF_law
    (principalIntervalLength K T γ) (principalIntervalLength_pos hK hT hγ)
    (principalIntegerPMF K T γ hK hT hγ hlarge)
    (fun k hk => principalIntervalLength_support hK hT hγ hlarge hk)
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalIntervalWeight_grid hK hT hγ hlarge)

theorem principalNormalizedSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (principalNormalizedSource hK hT hγ hlarge) A
      (scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 16 (128 * probabilityProfileLipschitz) 1
    le_rfl le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def scalarSourceTransitionBound : ℝ≥0 :=
  Classical.choose exists_smoothTransition_lipschitz

theorem scalarSourceTransitionBound_spec :
    1 ≤ scalarSourceTransitionBound ∧
      LipschitzWith scalarSourceTransitionBound Real.smoothTransition :=
  Classical.choose_spec exists_smoothTransition_lipschitz

def canonicalScalarSourceDegree (m : ℕ) : ℕ := (m + 1) * (m + 2)

noncomputable def canonicalScalarSourceConstant (m : ℕ) : ℕ :=
  1 + ⌈∑ d : Fin (m + 2), scalarCubePrimitiveEnvelope (Fin d.val)
    scalarSourceTransitionBound 16 (128 * probabilityProfileLipschitz) 1⌉₊

theorem canonicalScalarSourceConstant_bounds (m : ℕ) :
    1 ≤ canonicalScalarSourceConstant m ∧
      ∀ dim : ℕ, dim ≤ m + 1 →
        scalarCubePrimitiveEnvelope (Fin dim) scalarSourceTransitionBound
          16 (128 * probabilityProfileLipschitz) 1 ≤ canonicalScalarSourceConstant m := by
  refine ⟨by unfold canonicalScalarSourceConstant; omega, ?_⟩
  intro dim hdim
  let total := ∑ d : Fin (m + 2), scalarCubePrimitiveEnvelope (Fin d.val)
    scalarSourceTransitionBound 16 (128 * probabilityProfileLipschitz) 1
  have hsum : scalarCubePrimitiveEnvelope (Fin dim) scalarSourceTransitionBound
      16 (128 * probabilityProfileLipschitz) 1 ≤ total :=
    Finset.single_le_sum (fun d _ => scalarCubePrimitiveEnvelope_nonneg (Fin d.val)
      scalarSourceTransitionBound 16 (128 * probabilityProfileLipschitz) 1)
      (Finset.mem_univ (⟨dim, by omega⟩ : Fin (m + 2)))
  have hceil : total ≤ (⌈total⌉₊ : ℝ) := Nat.le_ceil _
  have hlast : (⌈total⌉₊ : ℝ) ≤ canonicalScalarSourceConstant m := by
    change (⌈total⌉₊ : ℝ) ≤ ((1 + ⌈total⌉₊ : ℕ) : ℝ)
    exact_mod_cast (show ⌈total⌉₊ ≤ 1 + ⌈total⌉₊ by omega)
  exact hsum.trans (hceil.trans hlast)

noncomputable def canonicalScalarSourceEnvelope (m M : ℕ) : ℝ :=
  canonicalScalarSourceConstant m * ((max 1 M : ℕ) : ℝ) ^ canonicalScalarSourceDegree m

noncomputable def canonicalScalarSourceLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (canonicalScalarSourceConstant m : A) + (canonicalScalarSourceDegree m + 1 : ℕ) * p

theorem canonicalScalarSourceConstant_le_envelope (m M : ℕ) :
    (canonicalScalarSourceConstant m : ℝ) ≤ canonicalScalarSourceEnvelope m M := by
  have hbase : (1 : ℝ) ≤ ((max 1 M : ℕ) : ℝ) := by exact_mod_cast le_max_left 1 M
  have hp : (1 : ℝ) ≤ ((max 1 M : ℕ) : ℝ) ^ canonicalScalarSourceDegree m := one_le_pow₀ hbase
  simpa only [canonicalScalarSourceEnvelope, mul_one] using
    mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (canonicalScalarSourceConstant m))

theorem canonicalScalarSourceEnvelope_bounds (m M : ℕ) :
    1 ≤ canonicalScalarSourceEnvelope m M ∧
      scalarCubePrimitiveEnvelope Empty scalarSourceTransitionBound
        16 (128 * probabilityProfileLipschitz) 1 ≤ canonicalScalarSourceEnvelope m M ∧
      ∀ dim : ℕ, dim ≤ m + 1 →
        scalarCubePrimitiveEnvelope (Fin dim) scalarSourceTransitionBound
          1 0 (M ^ (m + 1)) ≤ canonicalScalarSourceEnvelope m M := by
  have hc := canonicalScalarSourceConstant_bounds m
  have hCP := canonicalScalarSourceConstant_le_envelope m M
  have hone : (1 : ℝ) ≤ canonicalScalarSourceConstant m := by exact_mod_cast hc.1
  refine ⟨hone.trans hCP, ?_, ?_⟩
  · rw [scalarCubePrimitiveEnvelope_eq_of_card Empty (Fin 0) (by simp)]
    exact (hc.2 0 (by omega)).trans hCP
  · intro dim hdim
    let N := max 1 M
    have hN : 1 ≤ N := le_max_left _ _
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpow : 1 ≤ N ^ (m + 1) := Nat.succ_le_of_lt (pow_pos (by omega : 0 < N) _)
    have hMN : M ^ (m + 1) ≤ N ^ (m + 1) := Nat.pow_le_pow_left (le_max_right _ _) _
    have hweights := scalarCubePrimitiveEnvelope_mono (Fin dim) scalarSourceTransitionBound
      (by norm_num : (1 : ℝ≥0) ≤ 16) (by positivity : (0 : ℝ≥0) ≤ 128 * probabilityProfileLipschitz) hMN
    have hscaled := scalarCubePrimitiveEnvelope_le_scaled (Fin dim)
      scalarSourceTransitionBound 16 (128 * probabilityProfileLipschitz) hNpow
    have hpowers : ((N ^ (m + 1) : ℕ) : ℝ) ^ (Fintype.card (Fin dim) + 1) ≤
        (N : ℝ) ^ canonicalScalarSourceDegree m := by
      rw [Fintype.card_fin, Nat.cast_pow, ← pow_mul]
      exact pow_le_pow_right₀ hN' (Nat.mul_le_mul_left (m + 1) (by omega))
    exact (hweights.trans hscaled).trans
      (mul_le_mul (hc.2 dim hdim) hpowers (by positivity) (Nat.cast_nonneg _))

theorem canonicalScalarSourceLog_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ canonicalScalarSourceLog m p ∧ p ≤ canonicalScalarSourceLog m p := by
  unfold canonicalScalarSourceLog
  push_cast
  have hc := Nat.cast_nonneg (α := ℝ) (canonicalScalarSourceConstant m)
  have hd := mul_nonneg (Nat.cast_nonneg (α := ℝ) (canonicalScalarSourceDegree m)) hp
  constructor <;> nlinarith

theorem canonicalScalarSourceEnvelope_le_exp (m : ℕ) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    canonicalScalarSourceEnvelope m M ≤ Real.exp (canonicalScalarSourceLog m p) := by
  have hbase : ((max 1 M : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (Real.one_le_exp_iff.mpr hp) hM
  have hpow := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (max 1 M)) hbase hp
    (canonicalScalarSourceDegree m) le_rfl
  have hc : (canonicalScalarSourceConstant m : ℝ) ≤ Real.exp (canonicalScalarSourceConstant m : ℝ) := by
    linarith [Real.add_one_le_exp (canonicalScalarSourceConstant m : ℝ)]
  have hprod := (mul_le_mul hc hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  apply hprod.trans (Real.exp_le_exp.mpr ?_)
  unfold canonicalScalarSourceLog
  push_cast
  nlinarith

end Erdos3

end

end OAI

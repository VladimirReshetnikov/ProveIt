import OAI.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
import OAI.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGridBoundaryConstant_pos (I : Type*) [Fintype I] :
    0 < scalarCubeGridBoundaryConstant I := by
  unfold scalarCubeGridBoundaryConstant
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_finset]
  positivity

noncomputable def scalarCubeRiemannAllowance (I : Type*) [Fintype I] [DecidableEq I]
    (B K : ℝ) : ℝ := 2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K

theorem scalarCubeRiemannAllowance_nonneg (I : Type*) [Fintype I] [DecidableEq I]
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) : 0 ≤ scalarCubeRiemannAllowance I B K := by
  have hC := (scalarCubeGridBoundaryConstant_pos I).le
  have hV := (scalarCubeDomain_volumeReal_pos I).le
  unfold scalarCubeRiemannAllowance
  positivity

theorem scalarCubeGrid_small_error_of_length (I : Type*) [Fintype I] [DecidableEq I]
    {L M : ℕ} (hL : 0 < L)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L) :
    scalarCubeGridBoundaryConstant I * ((M : ℝ)/L) < volume.real (scalarCubeDomain I) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hV := scalarCubeDomain_volumeReal_pos I
  have h := (div_le_iff₀ hV).mp hlarge
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hLp).mpr
  nlinarith [mul_pos hLp hV]

theorem scalarCubeResidueWeights_riemann_of_length (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1)*M ≤ L)
    (φ : (Option I → ℝ) → ℝ) {K : ℝ≥0} {B ε : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) (hε : 0 < ε)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L)
    (htest : M * scalarCubeRiemannAllowance I B K / ε ≤ L) :
    |(scalarCubeResidueWeights I L M hL m r hm hmM hsize).mean
        (fun z => φ (fun i => (z i : ℝ) / L)) - ∫ x, φ x ∂scalarCubeMeasure I| ≤ ε := by
  have h := scalarCubeResidueWeights_riemann I L M hL m r hm hmM hsize
    (scalarCubeGrid_small_error_of_length I hL hlarge) φ hφ hB hb
  apply h.trans
  change scalarCubeRiemannAllowance I B K * ((M : ℝ)/L) ≤ ε
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have he := (div_le_iff₀ hε).mp htest
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hLp).mpr
  nlinarith

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

def scalarCubeRiemannLog {A : Type*} [Semiring A] (D : A) : A :=
  (D + 1) ^ 2 + 4 * D + 2

theorem scalarCubeRiemannBoundary_le_exp (α : Type*) [Fintype α] [DecidableEq α]
    {D : ℝ} (_hD : 0 ≤ D) (hcard : (Fintype.card α : ℝ) ≤ D) :
    scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤
      Real.exp (scalarCubeRiemannLog D) := by
  let q := Fintype.card α
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h2q : (2 : ℝ) ^ q ≤ Real.exp q := by
    simpa only [← Real.exp_nat_mul, mul_one] using pow_le_pow_left₀ (by norm_num) h2 q
  have h4q : (4 : ℝ) ^ q ≤ Real.exp (2 * q) := by
    simpa only [← Real.exp_nat_mul, mul_comm] using pow_le_pow_left₀ (by norm_num) h4 q
  have hb : scalarCubeGridBoundaryConstant α ≤ Real.exp (4 * q + 2) := by
    simp only [scalarCubeGridBoundaryConstant, Fintype.card_prod, Fintype.card_bool,
      Fintype.card_finset, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (Real.exp 1 * Real.exp q) * Real.exp (2 * q) * Real.exp 1 * Real.exp q := by
        gcongr
        exact Real.add_one_le_exp _
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  calc
    _ = scalarCubeGridBoundaryConstant α * scalarCubeDomainDensity α := by
      rw [div_eq_mul_inv]; rfl
    _ ≤ Real.exp (4 * q + 2) * Real.exp (((q : ℝ) + 1) ^ 2) :=
      mul_le_mul hb (scalarCubeDomainDensity_le_exp α)
        (scalarCubeDomainDensity_pos α).le (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [scalarCubeRiemannLog]
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
      change (q : ℝ) ≤ D at hcard
      nlinarith [sq_nonneg (D - q)]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

def progressionSliceLengthLog {A : Type*} [Semiring A] (D E F T : A) : A :=
  E + F + T + D + scalarCubeRiemannLog D + 5

theorem progressionSlice_scale_bounds
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    {D E F T δ : ℝ} {S modulus : ℕ} (H step : ι → ℕ) (c : ι → ℤ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (_hF : 0 ≤ F) (hT : 0 ≤ T)
    (hcard : (Fintype.card ι : ℝ) ≤ D) (hq : (Fintype.card α : ℝ) ≤ D)
    (hδ : 0 < δ) (hδF : δ⁻¹ ≤ Real.exp F)
    (hm : 0 < modulus) (hmT : (modulus : ℝ) ≤ Real.exp T)
    (hS : Real.exp (progressionSliceLengthLog D E F T) ≤ S)
    (hstep : ∀ j, 0 < step j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : ∀ j, δ * S ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    (∀ j, 2 ≤ H j) ∧
    (∀ j, (Fintype.card α + 1) * modulus ≤ H j) ∧
    (∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α)) ∧
    (∑ j, (modulus : ℝ) / H j) ≤ Real.exp (-E) ∧
    (∀ j, (step j : ℝ) / S ≤ Real.exp (-E)) := by
  let B := scalarCubeRiemannLog D
  have hB : 0 ≤ B := by dsimp [B, scalarCubeRiemannLog]; positivity
  have hS0 : (0 : ℝ) < S := (Real.exp_pos _).trans_le hS
  have hSpos : 0 < S := by exact_mod_cast hS0
  have hδlow : Real.exp (-F) ≤ δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos F) hδ).mpr hδF
  have hHlow (j : ι) : Real.exp (E + T + D + B + 5) ≤ (H j : ℝ) := by
    calc
      _ = Real.exp (-F) * Real.exp (progressionSliceLengthLog D E F T) := by
        rw [← Real.exp_add]; dsimp [progressionSliceLengthLog, B]; congr 1; ring
      _ ≤ δ * S := mul_le_mul hδlow hS (Real.exp_nonneg _) hδ.le
      _ ≤ _ := by simpa only [card_integerProgressionSupport _ _ _ (hstep j)] using hdense j
  have hH2 (j : ι) : 2 ≤ H j := by
    have he : (2 : ℝ) ≤ Real.exp (E + T + D + B + 5) := by
      linarith [Real.add_one_le_exp (E + T + D + B + 5)]
    exact_mod_cast he.trans (hHlow j)
  have hHp (j : ι) : (0 : ℝ) < H j := (Real.exp_pos _).trans_le (hHlow j)
  have hr (j : ι) : (modulus : ℝ) / H j ≤ Real.exp (-(E + D + B + 5)) := by
    calc
      _ ≤ Real.exp T / Real.exp (E + T + D + B + 5) :=
        div_le_div₀ (Real.exp_nonneg _) hmT (Real.exp_pos _) (hHlow j)
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hcancel (a : ℝ) : Real.exp a * Real.exp (-(E + D + B + 5)) =
      Real.exp (a - (E + D + B + 5)) := by rw [← Real.exp_add]; rfl
  refine ⟨hH2, ?_, ?_, ?_, ?_⟩
  · intro j
    have hc : (Fintype.card α : ℝ) + 1 ≤ Real.exp D :=
      by linarith [Real.add_one_le_exp D]
    have hratio : ((Fintype.card α : ℝ) + 1) * ((modulus : ℝ) / H j) ≤ 1 := by
      calc
        _ ≤ Real.exp D * Real.exp (-(E + D + B + 5)) :=
          mul_le_mul hc (hr j) (div_nonneg (Nat.cast_nonneg _) (hHp j).le) (Real.exp_nonneg _)
        _ ≤ 1 := by rw [hcancel]; apply Real.exp_le_one_iff.mpr; linarith
    rw [← mul_div_assoc] at hratio
    have hn := (div_le_one (hHp j)).mp hratio
    exact_mod_cast hn
  · intro j
    have hb := scalarCubeRiemannBoundary_le_exp α hD hq
    have hx : (scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α)) *
        ((modulus : ℝ) / H j) < 1 := by
      calc
        _ ≤ Real.exp B * Real.exp (-(E + D + B + 5)) :=
          mul_le_mul hb (hr j) (div_nonneg (Nat.cast_nonneg _) (hHp j).le) (Real.exp_nonneg _)
        _ < 1 := by rw [hcancel]; apply Real.exp_lt_one_iff.mpr; linarith
    apply (div_lt_one (scalarCubeDomain_volumeReal_pos α)).mp
    simpa only [div_mul_eq_mul_div] using hx
  · calc
      _ ≤ ∑ _j : ι, Real.exp (-(E + D + B + 5)) := Finset.sum_le_sum (fun j _ => hr j)
      _ = (Fintype.card ι : ℝ) * Real.exp (-(E + D + B + 5)) := by simp
      _ ≤ Real.exp D * Real.exp (-(E + D + B + 5)) := by
        gcongr
        exact hcard.trans (by linarith [Real.add_one_le_exp D])
      _ ≤ _ := by rw [hcancel]; apply Real.exp_le_exp.mpr; linarith
  · intro j
    have hg := progression_slice_endpoint_geometry (c j) hSpos (hstep j) (hH2 j) hδ
      (hsubset j) (hdense j)
    have hHreal : (2 : ℝ) ≤ H j := by exact_mod_cast hH2 j
    have hmesh : (step j : ℝ) / S ≤ 4 * ((modulus : ℝ) / H j) := by
      apply hg.2.2.2.trans
      apply (div_le_iff₀ (by linarith : 0 < (H j : ℝ) - 1)).mpr
      rw [show 4 * ((modulus : ℝ) / H j) * ((H j : ℝ) - 1) =
        (4 * modulus * ((H j : ℝ) - 1)) / H j by ring]
      apply (le_div_iff₀ (hHp j)).mpr
      have hm1 : (1 : ℝ) ≤ modulus := by exact_mod_cast hm
      have hprod := mul_le_mul_of_nonneg_right hm1 (by linarith : 0 ≤ (H j : ℝ) - 1)
      nlinarith
    calc
      _ ≤ 4 * ((modulus : ℝ) / H j) := hmesh
      _ ≤ Real.exp 3 * Real.exp (-(E + D + B + 5)) := by
        gcongr
        · linarith [Real.add_one_le_exp (3 : ℝ)]
        · exact hr j
      _ ≤ _ := by rw [hcancel]; apply Real.exp_le_exp.mpr; linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeRiemannAllowance_mul_mesh_le (I : Type*) [Fintype I] [DecidableEq I]
    {L M : ℕ} (hL : 0 < L) (B K : ℝ) {ε : ℝ} (hε : 0 < ε)
    (htest : M * scalarCubeRiemannAllowance I B K / ε ≤ L) :
    scalarCubeRiemannAllowance I B K * ((M : ℝ)/L) ≤ ε := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have he := (div_le_iff₀ hε).mp htest
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hLp).mpr
  nlinarith

theorem scalarCubeResidueWeights_pi_riemann_of_lengths {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B)
    (ε : J → ℝ) (hε : ∀ j, 0 < ε j)
    (hlarge : ∀ j, 2 * scalarCubeGridBoundaryConstant I * M j / volume.real (scalarCubeDomain I) ≤ L j)
    (htest : ∀ j, M j * scalarCubeRiemannAllowance I B K / ε j ≤ L j) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i => (z j i : ℝ) / L j)) -
      ∫ x, φ x ∂scalarCubeProductMeasure J I| ≤ ∑ j, ε j := by
  apply (scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize
    (fun j => scalarCubeGrid_small_error_of_length I (hL j) (hlarge j)) φ hφ hB hb).trans
  change scalarCubeRiemannAllowance I B K * (∑ j, (M j : ℝ)/L j) ≤ _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => scalarCubeRiemannAllowance_mul_mesh_le I (hL j) B K (hε j) (htest j))

theorem scalarCubeResidueWeights_pi_riemann_uniform_tolerance {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {B ε : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) (hε : 0 < ε)
    (hlarge : ∀ j, 2 * scalarCubeGridBoundaryConstant I * M j / volume.real (scalarCubeDomain I) ≤ L j)
    (htest : ∀ j, (Fintype.card J + 1 : ℝ) * M j * scalarCubeRiemannAllowance I B K / ε ≤ L j) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i => (z j i : ℝ) / L j)) -
      ∫ x, φ x ∂scalarCubeProductMeasure J I| ≤ ε := by
  have hn : (0 : ℝ) < Fintype.card J + 1 := by positivity
  have he (j) : M j * scalarCubeRiemannAllowance I B K / (ε / (Fintype.card J + 1)) ≤ L j := by
    rw [div_div_eq_mul_div]
    convert htest j using 1
    ring
  apply (scalarCubeResidueWeights_pi_riemann_of_lengths L M hL m r hm hmM hsize
    φ hφ hB hb (fun _ => ε/(Fintype.card J+1)) (fun _ => div_pos hε hn) hlarge he).trans
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hn).mpr
  nlinarith

end Erdos3

end

end OAI

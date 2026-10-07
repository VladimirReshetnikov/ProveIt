import OAI.Combinatorics.Progressions.Estimates.FiniteApproximationComparison
import OAI.Combinatorics.Progressions.Estimates.FiniteShellSum
import OAI.Combinatorics.Progressions.Estimates.LocalizedAverageScaleOrder
import OAI.Combinatorics.Progressions.Estimates.MonotoneRegularPoint
import OAI.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
import OAI.Combinatorics.Progressions.Geometry.ChordBoxCutoff
import OAI.Combinatorics.Progressions.Probability.MassConvolution

namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def ndilate (B : Set N) (t : ℝ≥0) : Set N := B.dilate t

@[simp] theorem radius_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).radius = t * B.radius := by simp [ndilate]

@[simp] theorem rank_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).rank = B.rank := rfl

@[simp] theorem ndilate_one (B : Set N) : B.ndilate 1 = B := by simp [ndilate]

@[simp] theorem ndilate_ndilate (B : Set N) (s t : ℝ≥0) :
    (B.ndilate s).ndilate t = B.ndilate (t * s) := by simp [ndilate]

theorem carrier_ndilate_mono {B : Set N} {s t : ℝ≥0} (hst : s ≤ t) :
    (B.ndilate s).carrier ⊆ (B.ndilate t).carrier :=
  B.dilate_mono s.coe_nonneg (by exact_mod_cast hst)

def IsRankRegular (B : Set N) : Prop :=
  let d : ℕ := 2 * max B.rank 1
  ∀ kappa : ℝ≥0,
    kappa ≤ 1 / (100 * (d : ℝ≥0)) →
      (1 - 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ) ≤
          ((B.ndilate (1 - kappa)).carrier.card : ℝ) ∧
      ((B.ndilate (1 + kappa)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ)

theorem isRankRegular_ndilate_iff (B : Set N) (rho : ℝ≥0) :
    (B.ndilate rho).IsRankRegular ↔
      let d : ℕ := 2 * max B.rank 1
      ∀ kappa : ℝ≥0,
        kappa ≤ 1 / (100 * (d : ℝ≥0)) →
          (1 - 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) ≤
              ((B.ndilate ((1 - kappa) * rho)).carrier.card : ℝ) ∧
          ((B.ndilate ((1 + kappa) * rho)).carrier.card : ℝ) ≤
              (1 + 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) := by
  simp [IsRankRegular, mul_comm]

theorem log_card_growth_lt_five_mul_rank (B : Set N) (hB : 0 < B.radius) :
    Real.log ((B.ndilate (5 / 4)).carrier.card : ℝ) -
        Real.log ((B.ndilate (1 / 4)).carrier.card : ℝ) <
      5 * (2 * max B.rank 1 : ℕ) := by
  classical
  let d : ℕ := 2 * max B.rank 1
  have hcard : (B.ndilate (5 / 4)).carrier.card ≤
      9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card := by
    calc
      (B.ndilate (5 / 4)).carrier.card ≤ (B.ndilate 2).carrier.card :=
        Finset.card_le_card (carrier_ndilate_mono
          (show (5 / 4 : NNReal) ≤ 2 by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
            norm_num))
      _ ≤ 9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card :=
        by simpa [ndilate] using card_two_le_nine_pow_three_rank_mul_card_quarter B hB
  have hsmall_pos : (0 : ℝ) < (B.ndilate (1 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (1 / 4)).carrier_nonempty.card_pos
  have hlarge_pos : (0 : ℝ) < (B.ndilate (5 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (5 / 4)).carrier_nonempty.card_pos
  have hlog := Real.log_le_log hlarge_pos (show
      ((B.ndilate (5 / 4)).carrier.card : ℝ) ≤
        ((9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card : ℕ) : ℝ) by
      exact_mod_cast hcard)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) hsmall_pos.ne',
    Real.log_pow] at hlog
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by simp [d])
  have hlog9 : Real.log (9 : ℝ) < 10 / 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by norm_num : (9 : ℝ) ≤ 2 ^ 4)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have hmain : (3 * B.rank : ℕ) * Real.log (9 : ℝ) < 5 * d := by
    have hpos : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
    have hrank : (B.rank : ℝ) ≤ (max B.rank 1 : ℕ) := by exact_mod_cast le_max_left B.rank 1
    push_cast
    calc
      3 * (B.rank : ℝ) * Real.log 9 ≤ 3 * (max B.rank 1 : ℕ) * Real.log 9 := by gcongr
      _ < 3 * (max B.rank 1 : ℕ) * (10 / 3) := by gcongr
      _ = 5 * d := by dsimp [d]; push_cast; ring
  dsimp [d] at hmain ⊢
  linarith

noncomputable def normalizedLogCard (B : Set N) (s : ℝ) : ℝ :=
  Real.log ((B.ndilate s.toNNReal).carrier.card : ℝ) /
    (2 * max B.rank 1 : ℕ)

theorem normalizedLogCard_monotone (B : Set N) :
    Monotone B.normalizedLogCard := by
  intro s t hst
  dsimp [normalizedLogCard]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.log_le_log
  · exact_mod_cast (B.ndilate s.toNNReal).carrier_nonempty.card_pos
  · exact_mod_cast Finset.card_le_card
      (carrier_ndilate_mono (B := B) (Real.toNNReal_mono hst))

theorem normalizedLogCard_buffer_growth (B : Set N) (hB : 0 < B.radius) :
    B.normalizedLogCard (5 / 4) - B.normalizedLogCard (1 / 4) < 5 := by
  classical
  have h := log_card_growth_lt_five_mul_rank B hB
  have hd : (0 : ℝ) < (2 * max B.rank 1 : ℕ) := by positivity
  have h54 : Real.toNNReal (5 / 4 : ℝ) = (5 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have h14 : Real.toNNReal (1 / 4 : ℝ) = (1 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  dsimp [normalizedLogCard]
  rw [h54, h14]
  rw [div_sub_div_same]
  exact (div_lt_iff₀ hd).2 (by simpa [mul_comm] using h)

theorem exists_rankRegular_ndilate (B : Set N) (hB : 0 < B.radius) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      (B.ndilate rho).IsRankRegular := by
  classical
  let d : ℕ := 2 * max B.rank 1
  obtain ⟨r, hr, hlip⟩ := exists_regular_point_of_monotone
    B.normalizedLogCard (normalizedLogCard_monotone B)
      (normalizedLogCard_buffer_growth B hB)
  let rho : NNReal := r.toNNReal
  have hrho : (rho : ℝ) = r := Real.coe_toNNReal r (by linarith [hr.1])
  have hrho_half : (1 / 2 : NNReal) ≤ rho := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.1
  have hrho_one : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.2
  refine ⟨rho, hrho_half, hrho_one, ?_⟩
  rw [isRankRegular_ndilate_iff]
  dsimp only [rank_ndilate]
  intro kappa hkappa
  have hdposN : 0 < d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hkappa_real : (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
    exact_mod_cast hkappa
  let sminus : NNReal := (1 - kappa) * rho
  let splus : NNReal := (1 + kappa) * rho
  have hkreal : (kappa : ℝ) ≤ 1 / 100 := by
    calc
      (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := hkappa_real
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hd_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by dsimp [d]; omega)
        nlinarith
  have hrho_real : (1 / 2 : ℝ) ≤ rho ∧ (rho : ℝ) ≤ 1 := by
    exact ⟨by exact_mod_cast hrho_half, by exact_mod_cast hrho_one⟩
  have hsminus_buf : (sminus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hk_lower : (99 / 100 : ℝ) ≤ 1 - (kappa : ℝ) := by
      nlinarith
    constructor
    · calc
        (1 / 4 : ℝ) ≤ (99 / 100) * (1 / 2) := by norm_num
        _ ≤ (1 - (kappa : ℝ)) * (rho : ℝ) := by
          exact mul_le_mul hk_lower hrho_real.1 (by norm_num)
            (sub_nonneg.mpr (by exact_mod_cast hkappa_one))
    · calc
        (1 - (kappa : ℝ)) * (rho : ℝ) ≤ 1 * rho :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 (by positivity)) (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrho_real.2 (by norm_num)
        _ ≤ 5 / 4 := by norm_num
  have hsplus_buf : (splus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [splus]
    constructor <;> nlinarith
  have hdistminus : |(sminus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 - (kappa : ℝ)) * (rho : ℝ) - rho = -(kappa * rho) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hdistplus : |(splus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [splus]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 + (kappa : ℝ)) * (rho : ℝ) - rho = kappa * rho by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hlipminus := hlip (sminus : ℝ) hsminus_buf
  have hlipplus := hlip (splus : ℝ) hsplus_buf
  simp only [normalizedLogCard, Real.toNNReal_coe,
    show r.toNNReal = rho by rfl] at hlipminus hlipplus
  change
    |Real.log ((B.ndilate sminus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(sminus : ℝ) - r| at hlipminus
  change
    |Real.log ((B.ndilate splus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(splus : ℝ) - r| at hlipplus
  rw [div_sub_div_same, abs_div, abs_of_pos hdpos] at hlipminus hlipplus
  have hlogminus :
      Real.log ((B.ndilate rho).carrier.card : ℝ) -
          Real.log ((B.ndilate sminus).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipminus
    calc
      _ ≤ |Real.log ((B.ndilate sminus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 60 * |(sminus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  have hlogplus :
      Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipplus
    calc
      _ ≤ |Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := le_abs_self _
      _ ≤ 60 * |(splus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  let u : ℝ := 100 * d * (kappa : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      100 * (d : ℝ) * (kappa : ℝ) ≤
          100 * d * (1 / (100 * d)) := by gcongr
      _ = 1 := by field_simp
  have hslope : 60 * d * (kappa : ℝ) = (3 / 5 : ℝ) * u := by
    dsimp [u]
    ring
  constructor
  · change (1 - u) * ((B.ndilate rho).carrier.card : ℝ) ≤
      ((B.ndilate sminus).carrier.card : ℝ)
    by_cases hu : u = 1
    · rw [hu]
      norm_num
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu
      have honeu : 0 < 1 - u := sub_pos.mpr hu_lt
      have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
        exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
      have hinner : (0 : ℝ) < (B.ndilate sminus).carrier.card := by
        exact_mod_cast (B.ndilate sminus).carrier_nonempty.card_pos
      rw [← Real.log_le_log_iff (mul_pos honeu hcenter) hinner]
      rw [Real.log_mul (sub_ne_zero.mpr (Ne.symm hu)) hcenter.ne']
      have hlogone := Real.log_le_sub_one_of_pos honeu
      rw [hslope] at hlogminus
      nlinarith
  · change ((B.ndilate splus).carrier.card : ℝ) ≤
      (1 + u) * ((B.ndilate rho).carrier.card : ℝ)
    have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
      exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
    have houter : (0 : ℝ) < (B.ndilate splus).carrier.card := by
      exact_mod_cast (B.ndilate splus).carrier_nonempty.card_pos
    rw [← Real.log_le_log_iff houter (mul_pos (by linarith) hcenter)]
    rw [Real.log_mul (by linarith) hcenter.ne']
    have hlogone := Real.le_log_one_add_of_nonneg hu0
    have hfrac : (3 / 5 : ℝ) * u ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    rw [hslope] at hlogplus
    linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def torusChordCutoff (a : ℝ) (h : ℝ≥0) (v : ι → CircleFourier.Circle) : ℝ :=
  chordBoxCutoff a h (fun i => CircleFourier.character (v i))

theorem torusChordCutoff_range (a : ℝ) (h : ℝ≥0) (v : ι → CircleFourier.Circle) :
    0 ≤ torusChordCutoff a h v ∧ torusChordCutoff a h v ≤ 1 := chordBoxCutoff_range _ _ _

theorem torus_character_map_lipschitz :
    LipschitzWith CircleFourier.characterLipConstant
      (fun v : ι → CircleFourier.Circle => fun i => CircleFourier.character (v i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [dist_eq_norm]
  change ‖(fun i => CircleFourier.character (v i)) - (fun i => CircleFourier.character (w i))‖ ≤
    (2 * Real.pi) * dist v w
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖CircleFourier.character (v i) - CircleFourier.character (w i)‖ ≤ _
  have h : ‖CircleFourier.character (v i) - CircleFourier.character (w i)‖ ≤
      (2 * Real.pi) * dist (v i) (w i) := by
    simpa only [dist_eq_norm, CircleFourier.coe_characterLipConstant] using
      CircleFourier.character_lipschitz.dist_le_mul (v i) (w i)
  exact h.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist v w i)
    (show 0 ≤ 2 * Real.pi by positivity))

theorem torusChordCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith (((Fintype.card ι : ℝ≥0) * h⁻¹) * CircleFourier.characterLipConstant)
      (torusChordCutoff (ι := ι) a h) :=
  (chordBoxCutoff_lipschitz a h hh).comp torus_character_map_lipschitz

end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationWidth (B : Set N) (rho : ℝ≥0) : ℝ≥0 :=
  rho * ⟨B.radius, B.radius_nonneg⟩

theorem approximationWidth_pos (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho) :
    0 < B.approximationWidth rho := mul_pos hrho hB

noncomputable def upperApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) : ℝ :=
  chordBoxCutoff B.radius (B.approximationWidth rho) (fun r : B.frequencies => character r x)

noncomputable def lowerApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) : ℝ :=
  chordBoxCutoff (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)
    (fun r : B.frequencies => character r x)

theorem upperApprox_range (B : Set N) (rho : ℝ≥0) (x : ZMod N) :
    0 ≤ B.upperApprox rho x ∧ B.upperApprox rho x ≤ 1 := chordBoxCutoff_range _ _ _

theorem lowerApprox_range (B : Set N) (rho : ℝ≥0) (x : ZMod N) :
    0 ≤ B.lowerApprox rho x ∧ B.lowerApprox rho x ≤ 1 := chordBoxCutoff_range _ _ _

theorem lowerApprox_le_upperApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) :
    B.lowerApprox rho x ≤ B.upperApprox rho x := by
  exact chordBoxCutoff_mono_center (by nlinarith [rho.coe_nonneg, B.radius_nonneg]) _ _

theorem upperApprox_eq_one (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho)
    {x : ZMod N} (hx : x ∈ B.carrier) : B.upperApprox rho x = 1 := by
  apply chordBoxCutoff_eq_one _ _ (B.approximationWidth_pos hB rho hrho)
  intro r
  exact (mem_carrier.mp hx) r r.property

theorem lowerApprox_eq_zero (B : Set N) (rho : ℝ≥0) {x : ZMod N} (hx : x ∉ B.carrier) :
    B.lowerApprox rho x = 0 := by
  rw [mem_carrier] at hx
  push Not at hx
  obtain ⟨r, hr, hbad⟩ := hx
  apply chordBoxCutoff_eq_zero
  refine ⟨⟨r, hr⟩, ?_⟩
  change B.radius - (rho : ℝ) * B.radius + (rho : ℝ) * B.radius ≤ ‖1 - character r x‖
  linarith

theorem lowerApprox_eq_one_inner (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) {x : ZMod N} (hx : x ∈ (B.ndilate (1 - rho)).carrier) :
    B.lowerApprox rho x = 1 := by
  apply chordBoxCutoff_eq_one _ _ (B.approximationWidth_pos hB rho hrho)
  intro r
  have h := (mem_carrier.mp hx) r r.property
  rw [radius_ndilate, NNReal.coe_sub hrho1, NNReal.coe_one] at h
  change ‖1 - character r x‖ ≤ B.radius - (rho : ℝ) * B.radius
  nlinarith

theorem upperApprox_eq_zero_outer (B : Set N) (rho : ℝ≥0) {x : ZMod N}
    (hx : x ∉ (B.ndilate (1 + rho)).carrier) : B.upperApprox rho x = 0 := by
  rw [mem_carrier] at hx
  push Not at hx
  obtain ⟨r, hr, hbad⟩ := hx
  apply chordBoxCutoff_eq_zero
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [radius_ndilate, NNReal.coe_add, NNReal.coe_one] at hbad
  change B.radius + (rho : ℝ) * B.radius ≤ ‖1 - character r x‖
  nlinarith

theorem approximation_sandwich (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho)
    (x : ZMod N) :
    B.lowerApprox rho x ≤ (if x ∈ B.carrier then (1 : ℝ) else 0) ∧
      (if x ∈ B.carrier then (1 : ℝ) else 0) ≤ B.upperApprox rho x := by
  by_cases hx : x ∈ B.carrier
  · simp only [hx, ite_true]
    exact ⟨(B.lowerApprox_range rho x).2, (B.upperApprox_eq_one hB rho hrho hx).ge⟩
  · simp only [hx, ite_false]
    exact ⟨(B.lowerApprox_eq_zero rho hx).le, (B.upperApprox_range rho x).1⟩

theorem approximation_gap_le_shell (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (x : ZMod N) :
    B.upperApprox rho x - B.lowerApprox rho x ≤
      (if x ∈ (B.ndilate (1 + rho)).carrier then (1 : ℝ) else 0) -
        (if x ∈ (B.ndilate (1 - rho)).carrier then (1 : ℝ) else 0) := by
  by_cases hi : x ∈ (B.ndilate (1 - rho)).carrier
  · have ho : x ∈ (B.ndilate (1 + rho)).carrier :=
      carrier_ndilate_mono ((tsub_le_self : 1 - rho ≤ (1 : ℝ≥0)).trans le_self_add) hi
    simp only [hi, ho, ite_true]
    rw [B.lowerApprox_eq_one_inner hB rho hrho hrho1 hi]
    linarith [(B.upperApprox_range rho x).2]
  · simp only [hi, ite_false, sub_zero]
    by_cases ho : x ∈ (B.ndilate (1 + rho)).carrier
    · simp only [ho, ite_true]
      linarith [(B.upperApprox_range rho x).2, (B.lowerApprox_range rho x).1]
    · simp only [ho, ite_false]
      rw [B.upperApprox_eq_zero_outer rho ho]
      linarith [(B.lowerApprox_range rho x).1]

theorem approximation_observables_lipschitz (B : Set N) (hB : 0 < B.radius)
    (rho : ℝ≥0) (hrho : 0 < rho) :
    LipschitzWith (B.rank * (B.approximationWidth rho)⁻¹)
      (chordBoxCutoff (ι := B.frequencies) B.radius (B.approximationWidth rho)) ∧
    LipschitzWith (B.rank * (B.approximationWidth rho)⁻¹)
      (chordBoxCutoff (ι := B.frequencies) (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)) := by
  constructor <;> simpa only [rank, Fintype.card_coe] using
    chordBoxCutoff_lipschitz (ι := B.frequencies) _ _ (B.approximationWidth_pos hB rho hrho)

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem add_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x + y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using add_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem sub_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x - y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using sub_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem uniformMass_translation_le_shell (B : Set N) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1) {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      (((B.ndilate (1 + kappa)).carrier.card : ℝ) - (B.ndilate (1 - kappa)).carrier.card) /
        B.carrier.card := by
  apply Erdos3.uniformMass_translation_le_shell
  · intro x hx
    constructor
    · have h := carrier_ndilate_mono (B := B) (show 1 - kappa ≤ 1 from tsub_le_self) hx
      simpa only [ndilate_one] using h
    · have h := sub_mem_ndilate (B := B) hx ht
      simpa only [tsub_add_cancel_of_le hkappa, ndilate_one, mem_iff, mem_carrier] using h
  · intro x hx
    rcases hx with hx | hx
    · have h := carrier_ndilate_mono (B := B) (show (1 : ℝ≥0) ≤ 1 + kappa from le_self_add)
      apply h
      simpa only [ndilate_one] using hx
    · have h := add_mem_ndilate (B := B) (r := 1) (s := kappa)
        (x := x - t) (y := t) (by simpa only [ndilate_one, mem_iff, mem_carrier] using hx) ht
      simpa only [sub_add_cancel, mem_iff, mem_carrier] using h

theorem uniformMass_translation_le_of_rankRegular {B : Set N} (hreg : B.IsRankRegular)
    {kappa : ℝ≥0} (hkappa : kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      400 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
    · positivity
  have hcards := hreg kappa hkappa
  have hcenter : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  apply (uniformMass_translation_le_shell B hkappa_one ht).trans
  rw [div_le_iff₀ hcenter]
  push_cast at hcards ⊢
  nlinarith [hcards.1, hcards.2]

theorem exists_regular_dilate_with_translation_bound (B : Set N) (hB : 0 < B.radius) :
    ∃ rho : ℝ≥0, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧ (B.ndilate rho).IsRankRegular ∧
      ∀ kappa : ℝ≥0, kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) →
        ∀ t ∈ (B.ndilate rho).ndilate kappa,
          ∑ x : ZMod N,
            |realUniformMass (B.ndilate rho).carrier (x - t) - realUniformMass (B.ndilate rho).carrier x| ≤
              400 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  obtain ⟨rho, hrho0, hrho1, hreg⟩ := exists_rankRegular_ndilate B hB
  refine ⟨rho, hrho0, hrho1, hreg, ?_⟩
  intro kappa hkappa t ht
  simpa only [rank_ndilate] using uniformMass_translation_le_of_rankRegular hreg hkappa ht

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem sum_approximation_gap_le (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (∑ x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * B.carrier.card := by
  have hrho1 : rho ≤ 1 := by
    apply hsmall.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have hsum : (∑ x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      ((B.ndilate (1 + rho)).carrier.card : ℝ) - (B.ndilate (1 - rho)).carrier.card := by
    calc
      _ ≤ ∑ x, ((if x ∈ (B.ndilate (1 + rho)).carrier then (1 : ℝ) else 0) -
          (if x ∈ (B.ndilate (1 - rho)).carrier then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun x _ => B.approximation_gap_le_shell hBpos rho hrho hrho1 x)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcards := hB rho hsmall
  push_cast at hcards ⊢
  nlinarith [hcards.1, hcards.2]

theorem mean_approximation_gap_le (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (𝔼 x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * ((B.carrier.card : ℝ) / N) := by
  rw [Fintype.expect_eq_sum_div_card]
  have h := div_le_div_of_nonneg_right (B.sum_approximation_gap_le hBpos hB rho hrho hsmall)
    (Nat.cast_nonneg (Fintype.card (ZMod N)) : (0 : ℝ) ≤ Fintype.card (ZMod N))
  simpa only [ZMod.card, mul_div_assoc] using h

theorem mean_shifted_approximation_gap_le
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) (z : ZMod N) :
    (𝔼 x, (B.upperApprox rho (x - z) - B.lowerApprox rho (x - z))) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * ((B.carrier.card : ℝ) / N) := by
  have heq : (𝔼 x, (B.upperApprox rho x - B.lowerApprox rho x)) =
      𝔼 x, (B.upperApprox rho (x - z) - B.lowerApprox rho (x - z)) := by
    apply Fintype.expect_equiv (Equiv.addRight z)
    intro x
    simp
  rw [← heq]
  exact B.mean_approximation_gap_le hBpos hB rho hrho hsmall

theorem mean_indicator_approximation_error_le
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (𝔼 x, |(if x ∈ B.carrier then (1 : ℝ) else 0) - B.upperApprox rho x|) ≤
        (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * ((B.carrier.card : ℝ) / N) ∧
    (𝔼 x, |(if x ∈ B.carrier then (1 : ℝ) else 0) - B.lowerApprox rho x|) ≤
        (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * ((B.carrier.card : ℝ) / N) := by
  have hgap := B.mean_approximation_gap_le hBpos hB rho hrho hsmall
  constructor
  · apply le_trans _ hgap
    apply Finset.expect_le_expect
    intro x _
    obtain ⟨hlo, hhi⟩ := B.approximation_sandwich hBpos rho hrho x
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hhi)]
    linarith
  · apply le_trans _ hgap
    apply Finset.expect_le_expect
    intro x _
    obtain ⟨hlo, hhi⟩ := B.approximation_sandwich hBpos rho hrho x
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem square_mean_le_local_add_boundary
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (C : Finset (ZMod N)) (hC : C.Nonempty) {kappa : ℝ≥0}
    (hCL : C ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.carrier.card ≤
      (𝔼 x ∈ L.carrier, (𝔼 c ∈ C, f (x + c)) ^ 2) +
        200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 := by
  let g : ZMod N → ℝ := fun x => 𝔼 c ∈ C, f (x + c)
  let U := (L.ndilate (1 + kappa)).carrier
  have hLc : (0 : ℝ) < L.carrier.card := by exact_mod_cast L.card_pos
  have hg (x : ZMod N) : 0 ≤ g x ∧ g x ≤ M := by
    constructor
    · exact Finset.expect_nonneg (fun c _ => (hf (x + c)).1)
    · exact (Finset.expect_le_expect (fun c (_ : c ∈ C) => (hf (x + c)).2)).trans_eq
        (Finset.expect_const hC M)
  have hgU : ∀ x, x ∉ U → g x = 0 := by
    intro x hx
    apply Finset.expect_eq_zero
    intro c hc
    apply hsupport
    intro hxc
    have h₁ : x + c ∈ L.ndilate (1 : ℝ≥0) := by
      simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using hxc
    have h₂ := CyclicBohr.Set.sub_mem_ndilate h₁ (hCL hc)
    exact hx (by simpa only [U, add_sub_cancel_right, CyclicBohr.Set.mem_iff,
      CyclicBohr.Set.mem_carrier] using h₂)
  have hLU : L.carrier ⊆ U := by
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := L) (show (1 : ℝ≥0) ≤ 1 + kappa from le_self_add)
  have hshell : (U.card : ℝ) - L.carrier.card ≤
      (200 * (max L.rank 1 : ℕ) * (kappa : ℝ)) * L.carrier.card := by
    have h := (hL kappa hkappa).2
    change ((L.ndilate (1 + kappa)).carrier.card : ℝ) - L.carrier.card ≤ _
    push_cast at h ⊢
    nlinarith
  have hsum := sum_le_local_sum_add_shell L.carrier U hLU (fun x => g x ^ 2)
    (fun x hx => by rw [hgU x hx]; norm_num)
    (fun x => pow_le_pow_left₀ (hg x).1 (hg x).2 2)
  have herror : M ^ 2 * (((U.card : ℝ) - L.carrier.card) / L.carrier.card) ≤
      200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hLc).mpr hshell) (sq_nonneg M)
    nlinarith
  change (∑ x, g x ^ 2) / L.carrier.card ≤
    (𝔼 x ∈ L.carrier, g x ^ 2) + 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2
  calc
    _ ≤ ((∑ x ∈ L.carrier, g x ^ 2) + M ^ 2 * ((U.card : ℝ) - L.carrier.card)) /
        L.carrier.card := div_le_div_of_nonneg_right hsum hLc.le
    _ = (𝔼 x ∈ L.carrier, g x ^ 2) +
        M ^ 2 * (((U.card : ℝ) - L.carrier.card) / L.carrier.card) := by
      rw [Finset.expect_eq_sum_div_card, add_div]
      ring
    _ ≤ _ := add_le_add le_rfl herror

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

def whole : Set N := ofFrequencies {0} 1 (by norm_num)

@[simp] theorem rank_whole : (whole : Set N).rank = 1 := by simp [whole]

@[simp] theorem radius_whole : (whole : Set N).radius = 1 := rfl

@[simp] theorem carrier_whole : (whole : Set N).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [whole, mem_carrier, ofFrequencies]

theorem exists_controlled_regular_subdilate (B : Set N) (hB : 0 < B.radius)
    (r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ C : Set N, C.frequencies = B.frequencies ∧ C.IsRankRegular ∧
      (r : ℝ) * B.radius / 2 ≤ C.radius ∧ C.radius ≤ r * B.radius ∧
      C.carrier ⊆ (B.ndilate r).carrier ∧
      ((r : ℝ) / 4) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ C.carrier.card := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hB0 : 0 < (B.ndilate r).radius := by
    rw [radius_ndilate]
    exact mul_pos hrR hB
  obtain ⟨rho, hrho0, hrho1, hreg⟩ := exists_rankRegular_ndilate (B.ndilate r) hB0
  let C := (B.ndilate r).ndilate rho
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have hC : C.radius = (rho : ℝ) * ((r : ℝ) * B.radius) := by simp only [C, radius_ndilate]
  refine ⟨C, rfl, hreg, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · have h := carrier_ndilate_mono (B := B.ndilate r) hrho1
    simpa only [ndilate_one] using h
  · have hprod : 0 < (rho : ℝ) * r := mul_pos (by linarith) hrR
    have hprod1 : (rho : ℝ) * r ≤ 1 := by nlinarith
    have hvol := relative_card_lower_bound B hB hprod hprod1
    have hlower : (r : ℝ) / 4 ≤ ((rho : ℝ) * r) / 2 := by nlinarith
    have hcost := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ r / 4 by positivity) hlower (4 * B.rank))
      (Nat.cast_nonneg B.carrier.card : (0 : ℝ) ≤ B.carrier.card)
    have hfull := hcost.trans hvol
    simpa only [C, ndilate, dilate_dilate] using hfull

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem average_sub_le_of_upperApprox
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) {W epsilon : ℝ} (hW : 0 ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W) (z : ZMod N)
    (hcompare : (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon) :
    (𝔼 x ∈ B.carrier, (f (z + x) - g (z + x))) ≤
      (N : ℝ) / B.carrier.card * epsilon + W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) := by
  have hmean : (𝔼 x, B.upperApprox rho x * (f (z + x) - g (z + x))) ≤ epsilon := by
    calc
      _ = 𝔼 x, B.upperApprox rho (x - z) * (f x - g x) := by
        apply Fintype.expect_equiv (Equiv.addLeft z)
        intro x
        simp
      _ ≤ epsilon := hcompare
  have hgap : (𝔼 x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) *
        ((B.carrier.card : ℝ) / Fintype.card (ZMod N)) := by
    simpa only [ZMod.card] using B.mean_approximation_gap_le hBpos hB rho hrho hsmall
  have h := local_average_le_of_approximation B.carrier B.carrier_nonempty
    (fun x => f (z + x)) (fun x => g (z + x)) (B.lowerApprox rho) (B.upperApprox rho)
    hW (fun x => hf (z + x)) (fun x => hg (z + x))
    (B.approximation_sandwich hBpos rho hrho) hmean hgap
  simpa only [ZMod.card] using h

theorem sum_average_sub_le_of_upperApprox
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) {W epsilon : ℝ} (hW : 0 ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hcompare : ∀ z, (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon)
    (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤
      (N : ℝ) / B.carrier.card * epsilon + W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) := by
  have h := Finset.expect_le_expect (fun s (_ : s ∈ B.carrier) =>
    B.average_sub_le_of_upperApprox hBpos hB rho hrho hsmall f g hW hf hg (z + s) (hcompare (z + s)))
  simpa only [Finset.expect_const B.carrier_nonempty] using h

theorem small_sum_average_of_upperApprox
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (f g : ZMod N → ℝ) {W eta epsilon : ℝ} (hW : 0 ≤ W) (heta : 0 < eta)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hepsilon : epsilon ≤ (eta / 2) * ((B.carrier.card : ℝ) / N)) :
    let rho := localizedAverageScale B.rank W (eta / 2)
    (∀ z, (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon) →
      ∀ z, (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ eta := by
  intro rho hcompare z
  obtain ⟨hrho, hsmall, herror⟩ := localizedAverageScale_spec B.rank hW
    (show 0 < eta / 2 by positivity)
  change 0 < rho at hrho
  change rho ≤ _ at hsmall
  change W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) ≤ eta / 2 at herror
  have h := B.sum_average_sub_le_of_upperApprox hBpos hB rho hrho hsmall f g hW hf hg hcompare z
  have hcard : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have heps : (N : ℝ) / B.carrier.card * epsilon ≤ eta / 2 := by
    calc
      _ ≤ (N : ℝ) / B.carrier.card * ((eta / 2) * ((B.carrier.card : ℝ) / N)) :=
        mul_le_mul_of_nonneg_left hepsilon (by positivity)
      _ = eta / 2 := by field_simp
  linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem carrier_eq_univ_of_rank_zero (B : Set N) (hB : B.rank = 0) :
    B.carrier = Finset.univ := by
  have hfreq : B.frequencies = ∅ := Finset.card_eq_zero.mp hB
  apply Finset.eq_univ_of_forall
  intro x
  simp [mem_carrier, hfreq]

@[simp] theorem carrier_ndilate_whole (t : ℝ≥0) :
    ((whole : Set N).ndilate t).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [mem_carrier, whole, ndilate, ofFrequencies, dilate]

theorem isRankRegular_whole : (whole : Set N).IsRankRegular := by
  intro kappa _
  simp only [rank_whole, max_self, Nat.mul_one, Nat.cast_ofNat, carrier_whole,
    carrier_ndilate_whole]
  have hcard : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod N)).card := Nat.cast_nonneg _
  constructor <;> nlinarith [mul_nonneg kappa.coe_nonneg hcard]

theorem exists_bounded_presentation (B : Set N) (hB : B.IsRankRegular)
    (hBpos : 0 < B.radius) {d : ℕ} (hd : 1 ≤ d) (hrank : B.rank ≤ d)
    {w : ℝ} (hw : w ≤ 1) (hwidth : w ≤ B.radius) :
    ∃ C : Set N, C.carrier = B.carrier ∧ C.IsRankRegular ∧
      0 < C.radius ∧ 1 ≤ C.rank ∧ C.rank ≤ d ∧ w ≤ C.radius ∧ C.radius ≤ 2 := by
  by_cases hwhole : B.rank = 0 ∨ 2 ≤ B.radius
  · have hcarrier : B.carrier = Finset.univ := hwhole.elim
      (carrier_eq_univ_of_rank_zero B) (carrier_eq_univ_of_two_le_radius B)
    refine ⟨whole, ?_, isRankRegular_whole, ?_, ?_, ?_, ?_, ?_⟩
    · rw [carrier_whole, hcarrier]
    · norm_num
    · norm_num
    · simpa only [rank_whole] using hd
    · simpa only [radius_whole] using hw
    · norm_num
  · push Not at hwhole
    exact ⟨B, rfl, hB, hBpos, by omega, hrank, hwidth, hwhole.2.le⟩

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def torusUpperApprox (B : Set N) (rho : ℝ≥0) :
    (B.frequencies → CircleFourier.Circle) → ℝ :=
  torusChordCutoff B.radius (B.approximationWidth rho)

noncomputable def torusLowerApprox (B : Set N) (rho : ℝ≥0) :
    (B.frequencies → CircleFourier.Circle) → ℝ :=
  torusChordCutoff (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)

theorem torus_approximation_ranges (B : Set N) (rho : ℝ≥0) (v : B.frequencies → CircleFourier.Circle) :
    (0 ≤ B.torusUpperApprox rho v ∧ B.torusUpperApprox rho v ≤ 1) ∧
      (0 ≤ B.torusLowerApprox rho v ∧ B.torusLowerApprox rho v ≤ 1) :=
  ⟨torusChordCutoff_range _ _ _, torusChordCutoff_range _ _ _⟩

theorem torus_approximations_lipschitz (B : Set N) (hB : 0 < B.radius)
    (rho : ℝ≥0) (hrho : 0 < rho) :
    LipschitzWith (((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant)
      (B.torusUpperApprox rho) ∧
    LipschitzWith (((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant)
      (B.torusLowerApprox rho) := by
  constructor <;> simpa only [rank, Fintype.card_coe, torusUpperApprox, torusLowerApprox] using
    torusChordCutoff_lipschitz (ι := B.frequencies) _ _ (B.approximationWidth_pos hB rho hrho)

theorem exists_torus_approximation_orbit (B : Set N) (rho : ℝ≥0) :
    ∃ theta : B.frequencies → ℝ, ∀ x z : ZMod N,
      B.torusUpperApprox rho
          (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) =
        B.upperApprox rho (x - z) ∧
      B.torusLowerApprox rho
          (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) =
        B.lowerApprox rho (x - z) := by
  obtain ⟨theta, htheta⟩ := exists_real_frequency_phases B
  refine ⟨theta, ?_⟩
  intro x z
  have hcoords :
      (fun r : B.frequencies => CircleFourier.character
        ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) =
      (fun r : B.frequencies => character r (x - z)) := funext (htheta x z)
  constructor <;> simp only [torusUpperApprox, torusLowerApprox, torusChordCutoff,
    upperApprox, lowerApprox, hcoords]

end Erdos3.CyclicBohr.Set

end

end OAI

import IntegerPoints.GKSec33SqrtPhase
import IntegerPoints.GKSec33SqrtBProcess
import IntegerPoints.GKSec33DualRange
import IntegerPoints.KuzminLandau

/-!
# Graham--Kolesnik section 3.3: a resonant square-root dual sum

For `H = Q^2`, take `R` to be a positive multiple of `H!`, put
`N = R^2`, and set `t = H R`.  At the stationary point
`x_ν = (t / ν)^2`, every phase in the Lemma 3.6 dual sum differs from
`-1/8` by an integer.  Its terms therefore point in the same complex
direction.  Their amplitudes and the size of the dual interval then give a
lower bound of `R Q / 4`.

The exact dual sum itself is `sqrtBDualMain`, defined by the square-root
B-process specialization.  This module only supplies the resonant parameter
choice and its elementary lower bound.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-! ### Resonant integral scales -/

/-- The square parameter controlling the dual frequency interval. -/
def sqrtDualH (Q : ℕ) : ℕ := Q ^ 2

/-- A resonating scale divisible by every positive integer up to `H`. -/
def sqrtDualR (Q M : ℕ) : ℕ := M * (sqrtDualH Q).factorial

/-- The primal dyadic scale `N = R^2`. -/
def sqrtDualN (Q M : ℕ) : ℕ := (sqrtDualR Q M) ^ 2

/-- The square-root phase parameter `t = H R`. -/
def sqrtDualT (Q M : ℕ) : ℕ := sqrtDualH Q * sqrtDualR Q M

/-- The exact stationary point solving `(2 t sqrt x)' = ν`. -/
noncomputable def sqrtDualX (Q M : ℕ) (ν : ℤ) : ℝ :=
  (((sqrtDualT Q M : ℕ) : ℝ) / (ν : ℝ)) ^ 2

/-- The integer frequencies produced by the square-root B-process. -/
noncomputable def sqrtDualRange (Q : ℕ) : Finset ℤ :=
  Finset.Icc ⌈sqrtBH Q / Real.sqrt 2⌉ (Q ^ 2 : ℤ)

/-- The real amplitude of the simplified square-root dual summand. -/
noncomputable def sqrtDualAmplitude (Q M : ℕ) (ν : ℤ) : ℝ :=
  1 / Real.sqrt
    ((ν : ℝ) ^ 3 /
      (2 * sqrtBT Q (sqrtDualR Q M) ^ 2))

@[simp]
theorem sqrtDualH_cast (Q : ℕ) : (sqrtDualH Q : ℝ) = sqrtBH Q := by
  simp [sqrtDualH, sqrtBH]

@[simp]
theorem sqrtDualN_cast (Q M : ℕ) :
    (sqrtDualN Q M : ℝ) = sqrtBN (sqrtDualR Q M) := by
  simp [sqrtDualN, sqrtBN]

@[simp]
theorem sqrtDualT_cast (Q M : ℕ) :
    (sqrtDualT Q M : ℝ) = sqrtBT Q (sqrtDualR Q M) := by
  simp [sqrtDualT, sqrtDualH, sqrtBT, sqrtBH]

@[simp]
theorem sqrtDualX_eq_sqrtCritical (Q M : ℕ) (ν : ℤ) :
    sqrtDualX Q M ν =
      sqrtCritical (sqrtBT Q (sqrtDualR Q M)) ν := by
  simp [sqrtDualX, sqrtCritical]

theorem sqrtDualH_pos (Q : ℕ) (hQ : 0 < Q) : 0 < sqrtDualH Q := by
  simp only [sqrtDualH]
  positivity

theorem sqrtDualR_pos (Q M : ℕ) (hM : 0 < M) : 0 < sqrtDualR Q M := by
  simp only [sqrtDualR]
  positivity

theorem sqrtDualN_pos (Q M : ℕ) (hM : 0 < M) : 0 < sqrtDualN Q M := by
  simp only [sqrtDualN]
  exact pow_pos (sqrtDualR_pos Q M hM) _

theorem sqrtDualT_pos (Q M : ℕ) (hQ : 0 < Q) (hM : 0 < M) :
    0 < sqrtDualT Q M := by
  simp only [sqrtDualT]
  exact mul_pos (sqrtDualH_pos Q hQ) (sqrtDualR_pos Q M hM)

/-! ### The stationary points and factorial resonance -/

/-- Every dual frequency is positive and at most `H`. -/
theorem sqrtDual_mem_bounds {Q : ℕ} (hQ : 0 < Q) {ν : ℤ}
    (hν : ν ∈ sqrtDualRange Q) :
    0 < (ν : ℝ) ∧ (ν : ℝ) ≤ sqrtBH Q := by
  have hH : 0 < sqrtBH Q := by
    simp only [sqrtBH]
    positivity
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hbase : 0 < sqrtBH Q / Real.sqrt 2 := div_pos hH hsqrt
  have hmem := Finset.mem_Icc.mp hν
  have hceil : (0 : ℤ) < ⌈sqrtBH Q / Real.sqrt 2⌉ :=
    Int.ceil_pos.2 hbase
  constructor
  · exact_mod_cast hceil.trans_le hmem.1
  · calc
      (ν : ℝ) ≤ ((Q ^ 2 : ℤ) : ℝ) := by exact_mod_cast hmem.2
      _ = sqrtBH Q := by simp [sqrtBH]

/-- On the dual range, the positive ratio `t / ν` is at least `R`. -/
theorem sqrtDualR_le_t_div {Q M : ℕ} (hQ : 0 < Q) {ν : ℤ}
    (hν : ν ∈ sqrtDualRange Q) :
    (sqrtDualR Q M : ℝ) ≤
      (sqrtDualT Q M : ℝ) / (ν : ℝ) := by
  obtain ⟨hν0, hνH⟩ := sqrtDual_mem_bounds hQ hν
  apply (le_div_iff₀ hν0).2
  rw [sqrtDualT]
  push_cast
  calc
    (sqrtDualR Q M : ℝ) * (ν : ℝ) ≤
        (sqrtDualR Q M : ℝ) * sqrtBH Q :=
      mul_le_mul_of_nonneg_left hνH (Nat.cast_nonneg _)
    _ = (sqrtDualH Q : ℝ) * (sqrtDualR Q M : ℝ) := by
      rw [sqrtDualH_cast]
      ring

/-- Every stationary point lies to the right of `1/2`, where the smooth
extension is the ordinary square-root phase. -/
theorem half_lt_sqrtDualX {Q M : ℕ} (hQ : 0 < Q) (hM : 0 < M) {ν : ℤ}
    (hν : ν ∈ sqrtDualRange Q) : 1 / 2 < sqrtDualX Q M ν := by
  have hR1 : (1 : ℝ) ≤ (sqrtDualR Q M : ℝ) := by
    have hRpos := sqrtDualR_pos Q M hM
    have hR1Nat : 1 ≤ sqrtDualR Q M := by omega
    exact_mod_cast hR1Nat
  have hratio1 :
      (1 : ℝ) ≤ (sqrtDualT Q M : ℝ) / (ν : ℝ) :=
    hR1.trans (sqrtDualR_le_t_div hQ hν)
  have hx1 : (1 : ℝ) ≤ sqrtDualX Q M ν := by
    rw [sqrtDualX]
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hratio1 2
  linarith

/-- Factorial divisibility makes every phase in `sqrtBDualMain` equal to
`e(-1/8)`. -/
theorem sqrtDual_phase_eq {Q M : ℕ} (hQ : 0 < Q) {ν : ℤ}
    (hν : ν ∈ sqrtDualRange Q) :
    e (sqrtBT Q (sqrtDualR Q M) ^ 2 / (ν : ℝ) - 1 / 8) =
      e (-1 / 8) := by
  obtain ⟨hν0, _hνH⟩ := sqrtDual_mem_bounds hQ hν
  have hνZ : (0 : ℤ) < ν := by exact_mod_cast hν0
  have hνNat : ((ν.toNat : ℕ) : ℤ) = ν := Int.toNat_of_nonneg hνZ.le
  have hνNatPos : 0 < ν.toNat := by omega
  have hmem := Finset.mem_Icc.mp hν
  have hνNatH : ν.toNat ≤ sqrtDualH Q := by
    exact_mod_cast (show ((ν.toNat : ℕ) : ℤ) ≤ (sqrtDualH Q : ℤ) by
      rw [hνNat, sqrtDualH]
      exact hmem.2)
  have hνFac : ν.toNat ∣ (sqrtDualH Q).factorial :=
    Nat.dvd_factorial hνNatPos hνNatH
  have hνR : ν.toNat ∣ sqrtDualR Q M := by
    exact dvd_mul_of_dvd_right hνFac M
  have hνT : ν.toNat ∣ sqrtDualT Q M := by
    exact dvd_mul_of_dvd_right hνR (sqrtDualH Q)
  have hνTT : ν.toNat ∣ sqrtDualT Q M * sqrtDualT Q M :=
    dvd_mul_of_dvd_left hνT (sqrtDualT Q M)
  have hνNatReal : (ν.toNat : ℝ) = (ν : ℝ) := by
    exact_mod_cast hνNat
  have hratioInt :
      sqrtBT Q (sqrtDualR Q M) ^ 2 / (ν : ℝ) =
        (((sqrtDualT Q M * sqrtDualT Q M) / ν.toNat : ℕ) : ℝ) := by
    rw [← sqrtDualT_cast, ← hνNatReal]
    calc
      (sqrtDualT Q M : ℝ) ^ 2 / (ν.toNat : ℝ) =
          ((sqrtDualT Q M * sqrtDualT Q M : ℕ) : ℝ) /
            (ν.toNat : ℝ) := by
        push_cast
        ring
      _ = (((sqrtDualT Q M * sqrtDualT Q M) / ν.toNat : ℕ) : ℝ) :=
        (Nat.cast_div_charZero hνTT).symm
  rw [hratioInt]
  let q : ℕ := (sqrtDualT Q M * sqrtDualT Q M) / ν.toNat
  calc
    e ((q : ℝ) - 1 / 8) = e (-1 / 8 + (q : ℝ)) := by
      congr 1
      ring
    _ = e (-1 / 8) * e (q : ℝ) := KL.e_add _ _
    _ = e (-1 / 8) := by
      rw [show e (q : ℝ) = 1 by simpa using KL.e_int (q : ℤ), mul_one]

/-! ### The amplitude and norm lower bounds -/

/-- Each reciprocal square-root-curvature amplitude is at least `R / Q`. -/
theorem sqrtDual_amplitude_ge {Q M : ℕ} (hQ : 0 < Q) (hM : 0 < M)
    {ν : ℤ} (hν : ν ∈ sqrtDualRange Q) :
    (sqrtDualR Q M : ℝ) / (Q : ℝ) ≤ sqrtDualAmplitude Q M ν := by
  obtain ⟨hν0, hνH⟩ := sqrtDual_mem_bounds hQ hν
  have hR : 0 < (sqrtDualR Q M : ℝ) :=
    Nat.cast_pos.2 (sqrtDualR_pos Q M hM)
  have hQ' : 0 < (Q : ℝ) := Nat.cast_pos.2 hQ
  have ht : 0 < sqrtBT Q (sqrtDualR Q M) := by
    simp only [sqrtBT, sqrtBH]
    positivity
  have hνcube : (ν : ℝ) ^ 3 ≤ sqrtBH Q ^ 3 :=
    pow_le_pow_left₀ hν0.le hνH 3
  have hcurvUpper :
      (ν : ℝ) ^ 3 / (2 * sqrtBT Q (sqrtDualR Q M) ^ 2) ≤
        ((Q : ℝ) / (sqrtDualR Q M : ℝ)) ^ 2 := by
    calc
      (ν : ℝ) ^ 3 / (2 * sqrtBT Q (sqrtDualR Q M) ^ 2) ≤
          sqrtBH Q ^ 3 / (2 * sqrtBT Q (sqrtDualR Q M) ^ 2) :=
        div_le_div_of_nonneg_right hνcube (by positivity)
      _ = (Q : ℝ) ^ 2 / (2 * (sqrtDualR Q M : ℝ) ^ 2) := by
        simp only [sqrtBT, sqrtBH]
        field_simp [hQ'.ne', hR.ne']
      _ ≤ ((Q : ℝ) / (sqrtDualR Q M : ℝ)) ^ 2 := by
        calc
          (Q : ℝ) ^ 2 / (2 * (sqrtDualR Q M : ℝ) ^ 2) =
              ((Q : ℝ) ^ 2 / 2) / (sqrtDualR Q M : ℝ) ^ 2 := by
            ring
          _ ≤ (Q : ℝ) ^ 2 / (sqrtDualR Q M : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right
              (by nlinarith [sq_nonneg (Q : ℝ)]) (sq_nonneg _)
          _ = ((Q : ℝ) / (sqrtDualR Q M : ℝ)) ^ 2 := by
            rw [div_pow]
  have hcurv0 :
      0 < (ν : ℝ) ^ 3 /
        (2 * sqrtBT Q (sqrtDualR Q M) ^ 2) := by
    positivity
  have hsqrtUpper :
      Real.sqrt
          ((ν : ℝ) ^ 3 /
            (2 * sqrtBT Q (sqrtDualR Q M) ^ 2)) ≤
        (Q : ℝ) / (sqrtDualR Q M : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨div_nonneg hQ'.le hR.le, hcurvUpper⟩
  have hsqrt0 :
      0 < Real.sqrt
        ((ν : ℝ) ^ 3 /
          (2 * sqrtBT Q (sqrtDualR Q M) ^ 2)) :=
    Real.sqrt_pos.2 hcurv0
  unfold sqrtDualAmplitude
  calc
    (sqrtDualR Q M : ℝ) / (Q : ℝ) =
        1 / ((Q : ℝ) / (sqrtDualR Q M : ℝ)) := by
      field_simp [hQ'.ne', hR.ne']
    _ ≤ 1 / Real.sqrt
        ((ν : ℝ) ^ 3 /
          (2 * sqrtBT Q (sqrtDualR Q M) ^ 2)) :=
      one_div_le_one_div_of_le hsqrt0 hsqrtUpper

/-- The coherently phased exact B-process dual main sum has size at least
`R Q / 4`. -/
theorem sqrtBDualMain_norm_ge (Q M : ℕ) (hQ : 0 < Q) (hM : 0 < M) :
    (sqrtDualR Q M : ℝ) * (Q : ℝ) / 4 ≤
      ‖sqrtBDualMain Q (sqrtDualR Q M)‖ := by
  have hmain :
      sqrtBDualMain Q (sqrtDualR Q M) =
        e (-1 / 8) *
          ((∑ ν ∈ sqrtDualRange Q, sqrtDualAmplitude Q M ν : ℝ) : ℂ) := by
    calc
      sqrtBDualMain Q (sqrtDualR Q M) =
          ∑ ν ∈ sqrtDualRange Q,
            e (-1 / 8) * ((sqrtDualAmplitude Q M ν : ℝ) : ℂ) := by
        unfold sqrtBDualMain sqrtDualRange
        apply Finset.sum_congr rfl
        intro ν hν
        rw [sqrtDual_phase_eq hQ (by simpa [sqrtDualRange] using hν)]
        simp only [sqrtDualAmplitude, div_eq_mul_inv, one_mul,
          Complex.ofReal_inv]
      _ = e (-1 / 8) *
          ∑ ν ∈ sqrtDualRange Q, ((sqrtDualAmplitude Q M ν : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
      _ = e (-1 / 8) *
          ((∑ ν ∈ sqrtDualRange Q, sqrtDualAmplitude Q M ν : ℝ) : ℂ) := by
        push_cast
        rfl
  have hamp0 : ∀ ν : ℤ, 0 ≤ sqrtDualAmplitude Q M ν := by
    intro ν
    simp only [sqrtDualAmplitude]
    positivity
  have hsum0 :
      0 ≤ ∑ ν ∈ sqrtDualRange Q, sqrtDualAmplitude Q M ν :=
    Finset.sum_nonneg fun ν _ => hamp0 ν
  have hnorm :
      ‖sqrtBDualMain Q (sqrtDualR Q M)‖ =
        ∑ ν ∈ sqrtDualRange Q, sqrtDualAmplitude Q M ν := by
    rw [hmain, norm_mul, norm_e, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hsum0]
  have hH : 0 < sqrtDualH Q := sqrtDualH_pos Q hQ
  have hcard := dualRange_card_ge_quarter (sqrtDualH Q) hH
  have hcard' :
      sqrtBH Q / 4 ≤ ((sqrtDualRange Q).card : ℝ) := by
    simpa [sqrtDualRange, sqrtDualH, sqrtBH] using hcard
  have hR : 0 < (sqrtDualR Q M : ℝ) :=
    Nat.cast_pos.2 (sqrtDualR_pos Q M hM)
  have hQ' : 0 < (Q : ℝ) := Nat.cast_pos.2 hQ
  calc
    (sqrtDualR Q M : ℝ) * (Q : ℝ) / 4 =
        sqrtBH Q / 4 *
          ((sqrtDualR Q M : ℝ) / (Q : ℝ)) := by
      simp only [sqrtBH]
      field_simp [hQ'.ne']
    _ ≤ ((sqrtDualRange Q).card : ℝ) *
        ((sqrtDualR Q M : ℝ) / (Q : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard' (div_nonneg hR.le hQ'.le)
    _ = ∑ _ν ∈ sqrtDualRange Q,
        (sqrtDualR Q M : ℝ) / (Q : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ ν ∈ sqrtDualRange Q, sqrtDualAmplitude Q M ν := by
      exact Finset.sum_le_sum fun ν hν => sqrtDual_amplitude_ge hQ hM hν
    _ = ‖sqrtBDualMain Q (sqrtDualR Q M)‖ := hnorm.symm

end GKSec33

end LeanProofs.IntegerPoints

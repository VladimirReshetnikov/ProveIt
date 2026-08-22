import ExponentialIdentities.TwoBaseIntegerExponent.DilationDifferenceQuotient
import Mathlib.RingTheory.Polynomial.Basic

namespace LeanProofs.TwoBaseIntegerExponent

open Polynomial

/-! A coefficientwise cancellation hinge for the paired boundary residuals. -/

theorem C_prime_pow_dvd_right_of_dvd_mul {p : ℤ} (hp : Prime p) :
    ∀ (e : ℕ) (J G : ℤ[X]), ¬ C p ∣ J → C (p ^ e) ∣ J * G → C (p ^ e) ∣ G := by
  intro e
  induction e with
  | zero =>
      intro J G _ _
      simp
  | succ e ih =>
      intro J G hJ hprod
      rw [pow_succ, map_mul] at hprod
      have hpC : Prime (C p : ℤ[X]) := (prime_C_iff.mpr hp)
      have hpdiv : C p ∣ J * G :=
        (dvd_mul_left (C p) (C (p ^ e))).trans hprod
      have hpG : C p ∣ G := (hpC.dvd_mul.mp hpdiv).resolve_left hJ
      obtain ⟨G₁, hG₁⟩ := hpG
      have hprod' : C p * C (p ^ e) ∣ C p * (J * G₁) := by
        rw [hG₁] at hprod
        simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
      have hcancel : C (p ^ e) ∣ J * G₁ := by
        exact (mul_dvd_mul_iff_left hpC.ne_zero).mp hprod'
      have hind : C (p ^ e) ∣ G₁ := ih J G₁ hJ hcancel
      rw [hG₁]
      have hmul := mul_dvd_mul_left (C p) hind
      simpa [pow_succ, map_mul, mul_comm] using hmul

theorem not_C_two_dvd_of_odd_constantCoeff {J : ℤ[X]}
    (hodd : Odd J.constantCoeff) : ¬ C (2 : ℤ) ∣ J := by
  intro h
  have hcoeff : (2 : ℤ) ∣ J.constantCoeff :=
    (C_dvd_iff_dvd_coeff (2 : ℤ) J).mp h 0
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨q, hq⟩ := hcoeff
  omega

/-- A constant polynomial cannot divide a polynomial whose constant coefficient
is not divisible by the same integer. -/
theorem not_C_dvd_of_not_dvd_constantCoeff {p : ℤ} {J : ℤ[X]}
    (hunit : ¬ p ∣ J.constantCoeff) : ¬ C p ∣ J := by
  intro h
  exact hunit ((C_dvd_iff_dvd_coeff p J).mp h 0)

/-- Prime-power coefficientwise cancellation.  This is the structural-prime
version of `crossResidualScaling_of_odd_factor`; it applies equally at `2` and
at `3`. -/
theorem crossResidualScaling_of_prime_factor
    {p : ℤ} (hp : Prime p) (b e : ℕ) (J G R : ℤ[X])
    (hunit : ¬ p ∣ J.constantCoeff)
    (hidentity : C (p ^ (b + e)) * R = C (p ^ b) * J * G) :
    C (p ^ e) ∣ G := by
  rw [pow_add, map_mul, mul_assoc] at hidentity
  have hbase : C (p ^ b) ≠ 0 := by
    exact C_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  have hcancel : C (p ^ e) * R = J * G := by
    apply mul_left_cancel₀ hbase
    simpa only [mul_assoc] using hidentity
  exact C_prime_pow_dvd_right_of_dvd_mul hp e J G
    (not_C_dvd_of_not_dvd_constantCoeff hunit) ⟨R, hcancel.symm⟩

/-- If a scaled commutator side has an extra `2^e` beyond a factor with odd constant
coefficient, then the opposite residual itself has that full coefficientwise factor. -/
theorem crossResidualScaling_of_odd_factor
    (b e : ℕ) (J G R : ℤ[X]) (hodd : Odd J.constantCoeff)
    (hidentity : C ((2 : ℤ) ^ (b + e)) * R = C ((2 : ℤ) ^ b) * J * G) :
    C ((2 : ℤ) ^ e) ∣ G := by
  exact crossResidualScaling_of_prime_factor
    (show Prime (2 : ℤ) by norm_num) b e J G R
    (by
      simpa only [even_iff_two_dvd] using
        (Int.not_even_iff_odd.mpr hodd)) hidentity

/-- Abstract paired-residual transfer at an arbitrary structural prime. -/
theorem crossResidualScaling_of_prime_scaled_defect
    {p : ℤ} (hp : Prime p) (b e : ℕ) (s c m : ℤ)
    (P H D J G : ℤ[X])
    (hP : P.comp (C s * X) = C (p ^ (b + e)) * H)
    (hD : D.comp (C s * X) = C (p ^ b) * J)
    (hunit : ¬ p ∣ J.constantCoeff)
    (hdefect : P.comp (C c * X) - C m * P = D * G) :
    C (p ^ e) ∣ G.comp (C s * X) := by
  have hPcs : P.comp (C (c * s) * X) =
      C (p ^ (b + e)) * H.comp (C c * X) := by
    have h := congrArg (fun Q : ℤ[X] ↦ Q.comp (C c * X)) hP
    simpa [comp_assoc, mul_comp, C_comp, X_comp, mul_assoc, mul_comm,
      mul_left_comm] using h
  have hscaledDefect :
      P.comp (C (c * s) * X) - C m * P.comp (C s * X) =
        D.comp (C s * X) * G.comp (C s * X) := by
    have h := congrArg (fun Q : ℤ[X] ↦ Q.comp (C s * X)) hdefect
    simpa [sub_comp, mul_comp, C_comp, X_comp, comp_assoc, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hid :
      C (p ^ (b + e)) *
          (H.comp (C c * X) - C m * H) =
        C (p ^ b) * J * G.comp (C s * X) := by
    rw [hPcs, hP, hD] at hscaledDefect
    simpa [mul_sub, mul_assoc, mul_comm, mul_left_comm] using hscaledDefect
  exact crossResidualScaling_of_prime_factor hp b e J (G.comp (C s * X))
    (H.comp (C c * X) - C m * H) hunit hid

/-- Abstract paired-residual transfer.  If `P(sX)` carries `2^(b+e)`, the node divisor
`D(sX)` carries only `2^b` and its normalized factor has odd constant coefficient, then
the residual in `P(cX)-mP(X)=D(X)G(X)` carries the remaining `2^e` after the same scaling. -/
theorem crossResidualScaling_of_scaled_defect
    (b e : ℕ) (s c m : ℤ) (P H D J G : ℤ[X])
    (hP : P.comp (C s * X) = C ((2 : ℤ) ^ (b + e)) * H)
    (hD : D.comp (C s * X) = C ((2 : ℤ) ^ b) * J)
    (hodd : Odd J.constantCoeff)
    (hdefect : P.comp (C c * X) - C m * P = D * G) :
    C ((2 : ℤ) ^ e) ∣ G.comp (C s * X) := by
  exact crossResidualScaling_of_prime_scaled_defect
    (show Prime (2 : ℤ) by norm_num) b e s c m P H D J G hP hD
      (by
        simpa only [even_iff_two_dvd] using
          (Int.not_even_iff_odd.mpr hodd)) hdefect

/-- After exact division by a transferred prime power, the normalized identity
has no remaining scalar factors. -/
theorem crossNormalization_eq_of_prime_scaled_identity
    {p : ℤ} (hp : Prime p) (b e : ℕ) (J G G₀ R : ℤ[X])
    (hidentity : C (p ^ (b + e)) * R = C (p ^ b) * J * G)
    (hGnorm : G = C (p ^ e) * G₀) :
    R = J * G₀ := by
  have hb : C (p ^ b) ≠ 0 := C_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  have he : C (p ^ e) ≠ 0 := C_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  have hbase :
      C (p ^ b) * (C (p ^ e) * R) =
        C (p ^ b) * (C (p ^ e) * (J * G₀)) := by
    rw [hGnorm] at hidentity
    simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hidentity
  have h₁ := mul_left_cancel₀ hb hbase
  exact mul_left_cancel₀ he h₁

/-- Prime-generic reduction of a cross normalization. -/
theorem map_cross_normalization_eq_C_of_prime_scaled_identity
    {p : ℤ} (hp : Prime p) {k : Type*} [Field k]
    (b e : ℕ) (J G G₀ R : ℤ[X]) (φ : ℤ →+* k) (u : k)
    (hidentity : C (p ^ (b + e)) * R = C (p ^ b) * J * G)
    (hGnorm : G = C (p ^ e) * G₀)
    (hJmap : J.map φ ≠ 0)
    (hRmap : R.map φ = J.map φ * C u) :
    G₀.map φ = C u := by
  have hnorm := crossNormalization_eq_of_prime_scaled_identity
    hp b e J G G₀ R hidentity hGnorm
  have hmap := congrArg (fun P : ℤ[X] ↦ P.map φ) hnorm
  rw [Polynomial.map_mul, hRmap] at hmap
  exact mul_left_cancel₀ hJmap hmap.symm

/-- A report-14 style scaled defect supplies both the transferred content and,
when its normalized commutator quotient is known modulo a residue field, the
constant reduction of the normalized cross residual. -/
theorem exists_crossResidualNormalization_of_prime_scaled_defect
    {p : ℤ} (hp : Prime p) {k : Type*} [Field k]
    (b e : ℕ) (s c m : ℤ) (P H D J G : ℤ[X])
    (φ : ℤ →+* k) (u : k)
    (hP : P.comp (C s * X) = C (p ^ (b + e)) * H)
    (hD : D.comp (C s * X) = C (p ^ b) * J)
    (hunit : ¬ p ∣ J.constantCoeff)
    (hdefect : P.comp (C c * X) - C m * P = D * G)
    (hJmap : J.map φ ≠ 0)
    (hRmap : (H.comp (C c * X) - C m * H).map φ =
      J.map φ * C u) :
    ∃ G₀ : ℤ[X],
      G.comp (C s * X) = C (p ^ e) * G₀ ∧ G₀.map φ = C u := by
  have hdiv := crossResidualScaling_of_prime_scaled_defect
    hp b e s c m P H D J G hP hD hunit hdefect
  obtain ⟨G₀, hG₀⟩ := hdiv
  have hPcs : P.comp (C (c * s) * X) =
      C (p ^ (b + e)) * H.comp (C c * X) := by
    have h := congrArg (fun Q : ℤ[X] ↦ Q.comp (C c * X)) hP
    simpa [comp_assoc, mul_comp, C_comp, X_comp, mul_assoc, mul_comm,
      mul_left_comm] using h
  have hscaledDefect :
      P.comp (C (c * s) * X) - C m * P.comp (C s * X) =
        D.comp (C s * X) * G.comp (C s * X) := by
    have h := congrArg (fun Q : ℤ[X] ↦ Q.comp (C s * X)) hdefect
    simpa [sub_comp, mul_comp, C_comp, X_comp, comp_assoc, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hid :
      C (p ^ (b + e)) * (H.comp (C c * X) - C m * H) =
        C (p ^ b) * J * G.comp (C s * X) := by
    rw [hPcs, hP, hD] at hscaledDefect
    simpa [mul_sub, mul_assoc, mul_comm, mul_left_comm] using hscaledDefect
  refine ⟨G₀, hG₀, ?_⟩
  exact map_cross_normalization_eq_C_of_prime_scaled_identity
    hp b e J (G.comp (C s * X)) G₀
      (H.comp (C c * X) - C m * H) φ u hid hG₀ hJmap hRmap

/-- Once the secondary residual has been divided by the transferred power, its
reduction is determined by the normalized commutator quotient.  This is the
algebraic cancellation step used to prove that the cross resultant is nonzero. -/
theorem map_cross_normalization_eq_C_of_scaled_identity
    {k : Type*} [Field k]
    (b e : ℕ) (J G G₀ R : ℤ[X]) (φ : ℤ →+* k) (u : k)
    (hidentity : C ((2 : ℤ) ^ (b + e)) * R =
      C ((2 : ℤ) ^ b) * J * G)
    (hGnorm : G = C ((2 : ℤ) ^ e) * G₀)
    (hJmap : J.map φ ≠ 0)
    (hRmap : R.map φ = J.map φ * C u) :
    G₀.map φ = C u := by
  exact map_cross_normalization_eq_C_of_prime_scaled_identity
    (show Prime (2 : ℤ) by norm_num) b e J G G₀ R φ u
      hidentity hGnorm hJmap hRmap

end LeanProofs.TwoBaseIntegerExponent

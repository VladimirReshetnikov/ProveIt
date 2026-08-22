import ExponentialIdentities.TwoBaseIntegerExponent.CrossResidualScaling
import ExponentialIdentities.TwoBaseIntegerExponent.ResultantScaling
import ExponentialIdentities.TwoBaseIntegerExponent.NodeDivisorScaling
import Mathlib.Data.ZMod.Basic

/-!
# Cross-resultant bridge for the simultaneous favorable branch of structural-residual analysis

This module deliberately does not identify the cross resultant below
with either of structural-residual analysis's self-dilation resultants.  It packages the genuinely
new object `Res(F, G)` arising when both favorable structural-prime scalings are
available for the two boundary residuals.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Polynomial

noncomputable section

/-- Closed form of the exponent occurring after the report-14 substitution
`e = n(n-1)/2`. -/
theorem report14CrossResultantExponent_eq (n : ℕ) :
    n * (n * (n - 1) / 2) = n * n * (n - 1) / 2 := by
  rw [← Nat.mul_div_assoc n
    (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))]
  simp only [mul_assoc]

/-- A unit constant coefficient guarantees that reduction modulo `p` is a
nonzero polynomial. -/
theorem map_zmod_ne_zero_of_not_dvd_constantCoeff
    (p : ℕ) (J : ℤ[X]) (hunit : ¬ (p : ℤ) ∣ J.constantCoeff) :
    J.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun Q : (ZMod p)[X] ↦ Q.coeff 0) hzero
  rw [coeff_map, coeff_zero] at hcoeff
  exact hunit
    ((ZMod.intCast_zmod_eq_zero_iff_dvd J.constantCoeff p).mp hcoeff)

/-- The two normalized defect identities transfer the missing structural-prime
content to the opposite boundary residual.  The final two hypotheses at each
prime are exactly the residue calculation needed to show that the cross
normalization is a nonzero constant modulo that prime. -/
theorem report14_simultaneous_cross_normalizations
    (n b e : ℕ) (M A : ℤ)
    (P H₂ H₃ D₂ D₃ J₂ J₃ F G : ℤ[X])
    (u₂ : ZMod 2) (u₃ : ZMod 3)
    (hP₂ : P.comp (C ((2 : ℤ) ^ n) * X) = C ((2 : ℤ) ^ (b + e)) * H₂)
    (hD₃₂ : D₃.comp (C ((2 : ℤ) ^ n) * X) = C ((2 : ℤ) ^ b) * J₂)
    (hJ₂unit : ¬ (2 : ℤ) ∣ J₂.constantCoeff)
    (hGdefect : P.comp (C 3 * X) - C A * P = D₃ * G)
    (hR₂map : (H₂.comp (C 3 * X) - C A * H₂).map
        (Int.castRingHom (ZMod 2)) =
      J₂.map (Int.castRingHom (ZMod 2)) * C u₂)
    (hP₃ : P.comp (C ((3 : ℤ) ^ n) * X) = C ((3 : ℤ) ^ (b + e)) * H₃)
    (hD₂₃ : D₂.comp (C ((3 : ℤ) ^ n) * X) = C ((3 : ℤ) ^ b) * J₃)
    (hJ₃unit : ¬ (3 : ℤ) ∣ J₃.constantCoeff)
    (hFdefect : P.comp (C 2 * X) - C M * P = D₂ * F)
    (hR₃map : (H₃.comp (C 2 * X) - C M * H₃).map
        (Int.castRingHom (ZMod 3)) =
      J₃.map (Int.castRingHom (ZMod 3)) * C u₃) :
    (∃ G₂ : ℤ[X],
      G.comp (C ((2 : ℤ) ^ n) * X) = C ((2 : ℤ) ^ e) * G₂ ∧
        G₂.map (Int.castRingHom (ZMod 2)) = C u₂) ∧
    (∃ F₃ : ℤ[X],
      F.comp (C ((3 : ℤ) ^ n) * X) = C ((3 : ℤ) ^ e) * F₃ ∧
        F₃.map (Int.castRingHom (ZMod 3)) = C u₃) := by
  constructor
  · exact exists_crossResidualNormalization_of_prime_scaled_defect
      (show Prime (2 : ℤ) by norm_num) b e ((2 : ℤ) ^ n) 3 A
        P H₂ D₃ J₂ G (Int.castRingHom (ZMod 2)) u₂
        hP₂ hD₃₂ hJ₂unit hGdefect
        (map_zmod_ne_zero_of_not_dvd_constantCoeff 2 J₂ hJ₂unit) hR₂map
  · exact exists_crossResidualNormalization_of_prime_scaled_defect
      (show Prime (3 : ℤ) by norm_num) b e ((3 : ℤ) ^ n) 2 M
        P H₃ D₂ J₃ F (Int.castRingHom (ZMod 3)) u₃
        hP₃ hD₂₃ hJ₃unit hFdefect
        (map_zmod_ne_zero_of_not_dvd_constantCoeff 3 J₃ hJ₃unit) hR₃map

/-- The same transfer with structural-residual analysis's actual node divisors substituted.  The
exact node-divisor scalings and their unit constant coefficients are discharged
by `NodeDivisorScaling`; only the interpolant scalings and residue
identities remain as hypotheses. -/
theorem report14_actual_divisors_cross_normalizations
    (n e : ℕ) (M A : ℤ) (P H₂ H₃ F G : ℤ[X])
    (u₂ : ZMod 2) (u₃ : ZMod 3)
    (hP₂ : P.comp (C ((2 : ℤ) ^ n) * X) =
      C ((2 : ℤ) ^ (report14BoundaryDivisorExponent n + e)) * H₂)
    (hGdefect : P.comp (C 3 * X) - C A * P =
      report14TriadicDefectDivisor n * G)
    (hR₂map : (H₂.comp (C 3 * X) - C A * H₂).map
        (Int.castRingHom (ZMod 2)) =
      (report14TriadicDivisorDyadicNormalization n).map
        (Int.castRingHom (ZMod 2)) * C u₂)
    (hP₃ : P.comp (C ((3 : ℤ) ^ n) * X) =
      C ((3 : ℤ) ^ (report14BoundaryDivisorExponent n + e)) * H₃)
    (hFdefect : P.comp (C 2 * X) - C M * P =
      report14DyadicDefectDivisor n * F)
    (hR₃map : (H₃.comp (C 2 * X) - C M * H₃).map
        (Int.castRingHom (ZMod 3)) =
      (report14DyadicDivisorTriadicNormalization n).map
        (Int.castRingHom (ZMod 3)) * C u₃) :
    (∃ G₂ : ℤ[X],
      G.comp (C ((2 : ℤ) ^ n) * X) = C ((2 : ℤ) ^ e) * G₂ ∧
        G₂.map (Int.castRingHom (ZMod 2)) = C u₂) ∧
    (∃ F₃ : ℤ[X],
      F.comp (C ((3 : ℤ) ^ n) * X) = C ((3 : ℤ) ^ e) * F₃ ∧
        F₃.map (Int.castRingHom (ZMod 3)) = C u₃) := by
  apply report14_simultaneous_cross_normalizations n
    (report14BoundaryDivisorExponent n) e M A P H₂ H₃
    (report14DyadicDefectDivisor n) (report14TriadicDefectDivisor n)
    (report14TriadicDivisorDyadicNormalization n)
    (report14DyadicDivisorTriadicNormalization n) F G u₂ u₃
  · exact hP₂
  · exact report14TriadicDefectDivisor_comp_two_pow n
  · simpa only [even_iff_two_dvd] using
      (Int.not_even_iff_odd.mpr
        (report14TriadicDivisorDyadicNormalization_constantCoeff_odd n))
  · exact hGdefect
  · exact hR₂map
  · exact hP₃
  · exact report14DyadicDefectDivisor_comp_three_pow n
  · exact report14DyadicDivisorTriadicNormalization_constantCoeff_not_three_dvd n
  · exact hFdefect
  · exact hR₃map

/-- In the simultaneous favorable branch, exact primary normalizations together
with the transferred cross normalizations make `Res(F,G)` nonzero.  Its forced
`2`- and `3`-power factors are exact: after each is removed, the corresponding
quotient has nonzero reduction. -/
theorem report14_simultaneous_favorable_cross_resultant
    (n b e : ℕ) (M A : ℤ)
    (P H₂ H₃ D₂ D₃ J₂ J₃ F G F₂ G₃ : ℤ[X])
    (u₂ : ZMod 2) (u₃ : ZMod 3)
    (hFdeg : F.natDegree = n) (hGdeg : G.natDegree = n)
    (hF₂scale : F.comp (C ((2 : ℤ) ^ n) * X) =
      C ((2 : ℤ) ^ (n * n)) * F₂)
    (hG₃scale : G.comp (C ((3 : ℤ) ^ n) * X) =
      C ((3 : ℤ) ^ (n * n)) * G₃)
    (hF₂coeff : (F₂.map (Int.castRingHom (ZMod 2))).coeff n ≠ 0)
    (hG₃coeff : (G₃.map (Int.castRingHom (ZMod 3))).coeff n ≠ 0)
    (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (hP₂ : P.comp (C ((2 : ℤ) ^ n) * X) = C ((2 : ℤ) ^ (b + e)) * H₂)
    (hD₃₂ : D₃.comp (C ((2 : ℤ) ^ n) * X) = C ((2 : ℤ) ^ b) * J₂)
    (hJ₂unit : ¬ (2 : ℤ) ∣ J₂.constantCoeff)
    (hGdefect : P.comp (C 3 * X) - C A * P = D₃ * G)
    (hR₂map : (H₂.comp (C 3 * X) - C A * H₂).map
        (Int.castRingHom (ZMod 2)) =
      J₂.map (Int.castRingHom (ZMod 2)) * C u₂)
    (hP₃ : P.comp (C ((3 : ℤ) ^ n) * X) = C ((3 : ℤ) ^ (b + e)) * H₃)
    (hD₂₃ : D₂.comp (C ((3 : ℤ) ^ n) * X) = C ((3 : ℤ) ^ b) * J₃)
    (hJ₃unit : ¬ (3 : ℤ) ∣ J₃.constantCoeff)
    (hFdefect : P.comp (C 2 * X) - C M * P = D₂ * F)
    (hR₃map : (H₃.comp (C 2 * X) - C M * H₃).map
        (Int.castRingHom (ZMod 3)) =
      J₃.map (Int.castRingHom (ZMod 3)) * C u₃) :
    F.resultant G ≠ 0 ∧
      (2 : ℤ) ^ (n * e) * 3 ^ (n * e) ∣ F.resultant G ∧
      ∃ r₂ r₃ : ℤ,
        F.resultant G = (2 : ℤ) ^ (n * e) * r₂ ∧
        (Int.castRingHom (ZMod 2)) r₂ ≠ 0 ∧
        F.resultant G = (3 : ℤ) ^ (n * e) * r₃ ∧
        (Int.castRingHom (ZMod 3)) r₃ ≠ 0 := by
  obtain ⟨⟨G₂, hG₂scale, hG₂map⟩, ⟨F₃, hF₃scale, hF₃map⟩⟩ :=
    report14_simultaneous_cross_normalizations n b e M A
      P H₂ H₃ D₂ D₃ J₂ J₃ F G u₂ u₃
      hP₂ hD₃₂ hJ₂unit hGdefect hR₂map
      hP₃ hD₂₃ hJ₃unit hFdefect hR₃map
  have hF₂deg : F₂.natDegree = n :=
    Polynomial.natDegree_of_comp_eq_C_mul F F₂ ((2 : ℤ) ^ n) 2
      (n * n) n (pow_ne_zero _ (by norm_num)) (by norm_num)
      hFdeg hF₂scale
  have hG₂deg : G₂.natDegree = n :=
    Polynomial.natDegree_of_comp_eq_C_mul G G₂ ((2 : ℤ) ^ n) 2
      e n (pow_ne_zero _ (by norm_num)) (by norm_num)
      hGdeg hG₂scale
  have hF₃deg : F₃.natDegree = n :=
    Polynomial.natDegree_of_comp_eq_C_mul F F₃ ((3 : ℤ) ^ n) 3
      e n (pow_ne_zero _ (by norm_num)) (by norm_num)
      hFdeg hF₃scale
  have hG₃deg : G₃.natDegree = n :=
    Polynomial.natDegree_of_comp_eq_C_mul G G₃ ((3 : ℤ) ^ n) 3
      (n * n) n (pow_ne_zero _ (by norm_num)) (by norm_num)
      hGdeg hG₃scale
  obtain ⟨r₂, hr₂, -, hr₂unit⟩ :=
    Polynomial.exists_residue_unit_quotient_of_cross_normalization
      F G F₂ G₂ 2 n e (by norm_num)
      (Int.castRingHom (ZMod 2)) u₂
      hFdeg hGdeg hF₂deg hG₂deg hF₂scale hG₂scale
      hF₂coeff hu₂ hG₂map
  obtain ⟨r₃, hr₃, -, hr₃unit⟩ :=
    Polynomial.exists_residue_unit_quotient_of_cross_normalization_right
      F G F₃ G₃ 3 n e (by norm_num)
      (Int.castRingHom (ZMod 3)) u₃
      hFdeg hGdeg hF₃deg hG₃deg hF₃scale hG₃scale
      hG₃coeff hu₃ hF₃map
  have hne : F.resultant G ≠ 0 := by
    intro hzero
    have hprod : (2 : ℤ) ^ (n * e) * r₂ = 0 := hr₂.symm.trans hzero
    have hrzero : r₂ = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (by norm_num))
    exact hr₂unit (by simp [hrzero])
  have htwo : (2 : ℤ) ^ (n * e) ∣ F.resultant G := ⟨r₂, hr₂⟩
  have hthree : (3 : ℤ) ^ (n * e) ∣ F.resultant G := ⟨r₃, hr₃⟩
  have hcop : IsCoprime ((2 : ℤ) ^ (n * e)) ((3 : ℤ) ^ (n * e)) :=
    (show IsCoprime (2 : ℤ) 3 from
      Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).pow
  exact ⟨hne, hcop.mul_dvd htwo hthree,
    r₂, r₃, hr₂, hr₂unit, hr₃, hr₃unit⟩

/-- Production endpoint with the actual report-14 node divisors.  At the
report's value `e = n(n-1)/2`, the conclusion says that the nonzero cross
resultant has exact `2`- and `3`-adic orders `n²(n-1)/2`, encoded without any
valuation API by the two nonzero residue quotients. -/
theorem actual_divisors_favorable_cross_resultant
    (n e : ℕ) (M A : ℤ) (P H₂ H₃ F G F₂ G₃ : ℤ[X])
    (u₂ : ZMod 2) (u₃ : ZMod 3)
    (hFdeg : F.natDegree = n) (hGdeg : G.natDegree = n)
    (hF₂scale : F.comp (C ((2 : ℤ) ^ n) * X) =
      C ((2 : ℤ) ^ (n * n)) * F₂)
    (hG₃scale : G.comp (C ((3 : ℤ) ^ n) * X) =
      C ((3 : ℤ) ^ (n * n)) * G₃)
    (hF₂coeff : (F₂.map (Int.castRingHom (ZMod 2))).coeff n ≠ 0)
    (hG₃coeff : (G₃.map (Int.castRingHom (ZMod 3))).coeff n ≠ 0)
    (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (hP₂ : P.comp (C ((2 : ℤ) ^ n) * X) =
      C ((2 : ℤ) ^ (report14BoundaryDivisorExponent n + e)) * H₂)
    (hGdefect : P.comp (C 3 * X) - C A * P =
      report14TriadicDefectDivisor n * G)
    (hR₂map : (H₂.comp (C 3 * X) - C A * H₂).map
        (Int.castRingHom (ZMod 2)) =
      (report14TriadicDivisorDyadicNormalization n).map
        (Int.castRingHom (ZMod 2)) * C u₂)
    (hP₃ : P.comp (C ((3 : ℤ) ^ n) * X) =
      C ((3 : ℤ) ^ (report14BoundaryDivisorExponent n + e)) * H₃)
    (hFdefect : P.comp (C 2 * X) - C M * P =
      report14DyadicDefectDivisor n * F)
    (hR₃map : (H₃.comp (C 2 * X) - C M * H₃).map
        (Int.castRingHom (ZMod 3)) =
      (report14DyadicDivisorTriadicNormalization n).map
        (Int.castRingHom (ZMod 3)) * C u₃) :
    F.resultant G ≠ 0 ∧
      (2 : ℤ) ^ (n * e) * 3 ^ (n * e) ∣ F.resultant G ∧
      ∃ r₂ r₃ : ℤ,
        F.resultant G = (2 : ℤ) ^ (n * e) * r₂ ∧
        (Int.castRingHom (ZMod 2)) r₂ ≠ 0 ∧
        F.resultant G = (3 : ℤ) ^ (n * e) * r₃ ∧
        (Int.castRingHom (ZMod 3)) r₃ ≠ 0 := by
  apply report14_simultaneous_favorable_cross_resultant n
    (report14BoundaryDivisorExponent n) e M A P H₂ H₃
    (report14DyadicDefectDivisor n) (report14TriadicDefectDivisor n)
    (report14TriadicDivisorDyadicNormalization n)
    (report14DyadicDivisorTriadicNormalization n) F G F₂ G₃ u₂ u₃
    hFdeg hGdeg hF₂scale hG₃scale hF₂coeff hG₃coeff hu₂ hu₃
  · exact hP₂
  · exact report14TriadicDefectDivisor_comp_two_pow n
  · simpa only [even_iff_two_dvd] using
      (Int.not_even_iff_odd.mpr
        (report14TriadicDivisorDyadicNormalization_constantCoeff_odd n))
  · exact hGdefect
  · exact hR₂map
  · exact hP₃
  · exact report14DyadicDefectDivisor_comp_three_pow n
  · exact report14DyadicDivisorTriadicNormalization_constantCoeff_not_three_dvd n
  · exact hFdefect
  · exact hR₃map

end

end LeanProofs.TwoBaseIntegerExponent

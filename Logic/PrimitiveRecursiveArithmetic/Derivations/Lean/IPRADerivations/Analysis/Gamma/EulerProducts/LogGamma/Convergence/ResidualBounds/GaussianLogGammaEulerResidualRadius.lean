import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.ResidualBounds.GaussianLogGammaEulerResidualDomain

/-!
# A computed radius for every right-half-plane Euler input

The actual signed native numerator has squared norm A²+B². The
numerical radius A+B is positive and bounds the represented argument.
Its product with the original positive denominator supplies the
source condition for the quadratic Euler logarithm remainder.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualRadius

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq normSq_code)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianRationalHorner (ofGaussian_represents)
open GaussianRationalMetric (bounded_of_cleared)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open RationalArithmetic (select select_zero select_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (A B : PTm n) : PTm n := A + B

ipra_subst radius

theorem native_norm (A B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] normSq (native A B neg) ≐ A * A + B * B := by
  refine .orE h ?_ ?_
  · let Δ := (neg ≐ zero) :: Γ
    have u := natEq (select_zero (Γ := Δ) neg B zero Prf.hyp0)
    have v := natEq (select_zero (Γ := Δ) neg zero B Prf.hyp0)
    apply deriveNat
    rw [native, normSq_code, ZT.toZ_ofNat]
    simp only [signedImag, ZT.toZ]
    rw [u, v]
    ipra_simps
    ring
  · let Δ := (neg ≐ one) :: Γ
    have u := natEq (select_one (Γ := Δ) neg B zero Prf.hyp0)
    have v := natEq (select_one (Γ := Δ) neg zero B Prf.hyp0)
    apply deriveNat
    rw [native, normSq_code, ZT.toZ_ofNat]
    simp only [signedImag, ZT.toZ]
    rw [u, v]
    ipra_simps
    ring

theorem radius_positive (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] le one (radius A B) :=
  le_trans h.andE₁.andE₁ (le_add_right A B)

/-- The original input supplies the radius required by the Euler residual. -/
theorem source_of_right_half_plane (A B D neg : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] source A B D neg (radius A B) := by
  let R := radius A B
  have hb : Γ ⊢[PRAAx] le (A * A + B * B) (R * R) := by
    refine le_of_eq_add (d := A * B + A * B) ?_
    unfold R radius
    ipra_ring
  have hD : Γ ⊢[PRAAx] le R (R * D) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl R) h.andE₂)
  exact .andI h (le_trans (le_congr (native_norm A B neg h.andE₁.andE₂).eqSymm (.eqRefl _) hb)
    (le_mul_mono hD hD))

/-- The same bound applies to the original Gaussian-rational argument. -/
theorem argument_bound (A B D neg : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (argument A B D neg) (radius A B) one := by
  have raw := (source_of_right_half_plane A B D neg h).andE₂
  exact bounded_of_cleared _ (native A B neg) D (radius A B) one h.andE₂ (le_refl one)
    (ofGaussian_represents (native A B neg) D h.andE₂)
    (le_congr (by ipra_ring) (by ipra_ring) raw)

theorem right_half_plane_Euler_residual_radius_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶
        (source (var 0) (var 1) (var 2) (var 3) (radius (var 0) (var 1)) ⋏
          (le one (radius (var 0) (var 1)) ⋏
            GaussianRationalMetric.bounded (argument (var 0) (var 1) (var 2) (var 3))
              (radius (var 0) (var 1)) one))) :=
  closeUniv 4 (.impI (.andI (source_of_right_half_plane _ _ _ _ Prf.hyp0)
    (.andI (radius_positive _ _ _ _ Prf.hyp0) (argument_bound _ _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerResidualRadius

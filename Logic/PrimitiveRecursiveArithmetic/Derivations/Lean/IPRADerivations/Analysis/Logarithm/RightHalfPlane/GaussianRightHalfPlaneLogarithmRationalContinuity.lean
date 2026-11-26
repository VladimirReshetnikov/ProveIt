import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmIncrement
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmIncrementMargin
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Local continuity of the actual rational right-half-plane logarithm

The relative linear increment is bounded by twice the native
displacement divided by the real numerator. The local admission
condition pays for the quadratic remainder, giving a linear bound at
the original logarithm's independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRationalContinuity

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalDenominator diagonalEnvelope diagonalNumerator)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianReconstructionRoots (norm_from_distance)
open GaussianRightHalfPlaneLogarithmIncrementBound (input subst_input)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep)
open GaussianRightHalfPlaneLogarithmRelativeStep (denominator numerator mercator_source paid_radius relative radius)
open RationalValueBounds (positive_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "data" => GaussianRightHalfPlaneLogarithm.data
local notation "F" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data

private theorem smallness (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) : Γ ⊢[PRAAx] le (num 4*H) A :=
  le_trans (le_trans (le_of_eq_add (d := num 124*H) (by ipra_ring)) h.andE₂.andE₂.andE₂.andE₂.andE₁)
    h.andE₂.andE₂.andE₁

private theorem relative_bound (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] bounded (relative (native A B neg) (native a b sign)) (two*H) A := by
  let u := native A B neg
  let v := native a b sign
  let N := denominator u
  have hA := h.andE₁.andE₁.andE₁
  have admitted := mercator_source A B neg v H hA h.andE₁.andE₂.andE₂.andE₁
    (smallness A B neg a b sign D H J M h)
  have pay := paid_radius A B neg H hA
  have nativeBound := le_mul_mono (le_refl (A*A)) admitted.andE₂.andE₁
  have cleared : Γ ⊢[PRAAx] le ((A*A)*ComplexLogarithmRemainder.normSq (numerator u v))
      ((two*H)*(two*H)*(N*N)) :=
    le_trans nativeBound (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono pay pay))
  exact bounded_of_cleared (relative u v) (numerator u v) N (two*H) A admitted.andE₁ hA.andE₁
    (ofGaussian_represents _ _ admitted.andE₁) cleared

theorem diagonal_at (p A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 G p (data a b D sign)) (ap2 G p (data A B D neg))
      (diagonalNumerator (num 3*H) A (num 9) p) (diagonalDenominator A p) := by
  let x := data a b D sign
  let y := data A B D neg
  let w := relative (native A B neg) (native a b sign)
  let raw := qsub (ap2 G p x) (ap2 G p y)
  let estimate := ap2 (F G G) p (diffData x y)
  let U := unit p
  let Q := A*A*U
  let P := num 6*(A*A) + (num 4*H*H*U+num 3*(A*A))
  have hA := h.andE₁.andE₁.andE₁.andE₁
  have hu := unit_positive (Γ := Γ) p
  have hQ := positive_product _ _ (positive_product A A hA hA) hu
  have hAU := positive_product A U hA hu
  have hx := GaussianRightHalfPlaneLogarithm.regular a b D sign h.andE₁.andE₂.andE₁
  have hy := GaussianRightHalfPlaneLogarithm.regular A B D neg h.andE₁.andE₁
  have sampling := distance_symmetric _ _ _ _ hu (GaussianNamedDifference.sample_error G G x y p hx hy)
  have read : Γ ⊢[PRAAx] distanceBounded raw estimate (num 6*(A*A)) Q :=
    distance_radius_mono _ _ _ _ _ _ hu hQ (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring)) sampling
  have toRelative : Γ ⊢[PRAAx] distanceBounded raw w P Q :=
    distance_triangle_same raw estimate w _ _ Q hQ read
      (GaussianRightHalfPlaneLogarithmIncrement.sample_error p A B neg a b sign D H J M h)
  have norm := norm_from_distance raw w P Q (two*H) A hQ hA toRelative (relative_bound A B neg a b sign D H J M h)
  have hSmall := smallness A B neg a b sign D H J M h
  exact bounded_radius_mono raw (P*A+two*H*Q) (Q*A)
    (diagonalNumerator (num 3*H) A (num 9) p) (diagonalDenominator A p)
    (positive_product Q A hQ hA) hAU
    (by
      dsimp only [P, Q, U, diagonalNumerator, diagonalDenominator]
      ipra_le 𝔞(H)*𝔞(A)^2*𝔞(unit p)^2*sl hSmall) norm

theorem independent_rate (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] independentRate G G (data a b D sign) (data A B D neg) (num 3*H) A := by
  apply GaussianNamedLipschitzRate.independent_rate G G _ _ _ _ (num 9) h.andE₁.andE₁.andE₁.andE₁
    (GaussianRightHalfPlaneLogarithm.regular a b D sign h.andE₁.andE₂.andE₁)
    (GaussianRightHalfPlaneLogarithm.regular A B D neg h.andE₁.andE₁)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s J) (s M) := by
    simpa only [Fm.shift, Syn.shift, s, subst_input] using h.shift
  simpa only [diagonalEnvelope, Syn.shift, s, PTm.subst_mul, PTm.subst_num, GaussianRightHalfPlaneLogarithm.subst_data]
    using diagonal_at (var 0) (s A) (s B) (s neg) (s a) (s b) (s sign) (s D) (s H) (s J) (s M) hs

/-- The gain pays for the local admission after rounding a native displacement. -/
def gain (K C : PTm n) : PTm n := num 6*K + num 256*(C+one)*(K*K)

ipra_subst gain

theorem local_guard (H E K C d D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] le (H*D) (two*E*d)) (hClose : Γ ⊢[PRAAx] le (gain K C*E) D) :
    Γ ⊢[PRAAx] smallStep H K C d := by
  apply positive_cancel (c := D) hD
  unfold gain at hClose
  ipra_le 128*(𝔞(C)+1)*𝔞(K)^2*sl hStep + 𝔞(d)*sl hClose + 6*𝔞(K)*𝔞(E)*𝔞(d)

theorem widened_rate (A B neg a b sign d H J M K C E D : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign d H J M) (hm : Γ ⊢[PRAAx] le d (K*A))
    (hD : Γ ⊢[PRAAx] le one D) (hStep : Γ ⊢[PRAAx] le (H*D) (two*E*d)) :
    Γ ⊢[PRAAx] independentRate G G (data a b d sign) (data A B d neg) (gain K C*E) D := by
  apply GaussianNamedRateRadius.weaken G G _ _ (num 3*H) A _ D h.andE₁.andE₁.andE₁.andE₁ hD _
    (independent_rate A B neg a b sign d H J M h)
  unfold gain
  ipra_le 3*sl hStep+6*𝔞(E)*sl hm+256*(𝔞(C)+1)*𝔞(K)^2*𝔞(E)*𝔞(A)

theorem actual_canonical_right_half_plane_logarithm_continuity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        independentRate G G (data (var 3) (var 4) (var 6) (var 5)) (data (var 0) (var 1) (var 6) (var 2))
          (num 3*var 7) (var 0)) :=
  closeUniv 10 (.impI (independent_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmRationalContinuity

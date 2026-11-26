import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalWeightedTaylorBallCover
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily

/-!
# Finite Barnes Taylor-ball cover with a common coefficient precision

The computed grid entry selects one local chart. Its single scheduled
polynomial certifies the value at the queried point and all retained
factorial Taylor coefficients at the center.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCoverCertificate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalWeightedTaylorBallCover (center centers center_listed center_source chartDen index step)
open GaussianBarnesCanonicalWeightedTaylorBallDyadic (denominator numerator)
open GaussianCoefficientNameBounds (unit)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "D" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "dd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "W" => GaussianBarnesCanonicalWeightedTaylorBall.nameF
local notation "wa" => GaussianBarnesCanonicalWeightedTaylorBall.approxData
local notation "cd" => GaussianBarnesCanonicalWeightedTaylorBallCoefficient.data

def clock (P q R M : PTm n) : PTm n :=
  GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily.clock P (center q R) (two*R+one) (chartDen q R) M

def bounds (P q R M e : PTm n) : Fm PTm n :=
  let z := center q R
  let B := chartDen q R
  let S := two*R+one
  let H := rawDen q
  let p := clock P q R M
  (lt (index q R) (length (centers R)) ⋏ (ofGaussian z B ≐ entry (centers R) (index q R))) ⋏
    (independentRate V W (vd (rawGaussian q) R H) (wa p z (step q R) S B H M)
      (numerator p z S B M) (denominator p M) ⋏
      (le e (previous M) ⟶ independentRate D W (dd z S B M e) (cd p z S B H M e) one (unit P)))

theorem certified (P q R M e : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] bounds P q R M e :=
  .andI (center_listed q R hq) (.andI (GaussianBarnesCanonicalWeightedTaylorBallCover.rate (clock P q R M) q R M hq)
    (.impI (GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily.rate P (center q R) (two*R)
      (chartDen q R) (rawDen q) M e (center_source q R hq.wk) Prf.hyp0)))

theorem actual_Barnes_Taylor_ball_cover_value_and_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (bounded (var 1) (var 2) one ⟶ bounds (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (certified _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCoverCertificate

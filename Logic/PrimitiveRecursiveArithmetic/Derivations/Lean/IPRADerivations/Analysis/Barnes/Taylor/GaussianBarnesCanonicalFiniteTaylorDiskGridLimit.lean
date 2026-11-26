import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorGridUniformObservations
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling

/-!
# A disk-only step threshold for the literal finite Barnes grid

Static head and scalar caps replace the arithmetic costs of the
particular center encoding. The step threshold is consequently
independent of both the center and its native denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorDiskGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded bounded_scale normSq normSq_one oneCode scale)
open GaussianBarnesCanonicalFiniteCentralDiskBound (cap)
open GaussianBarnesCanonicalFiniteTaylorGridComparison (value)
open GaussianBarnesCanonicalFiniteTaylorGridBudget (analyticGainWithCaps clockGainWithCaps numeratorWithCaps)
open GaussianBarnesCanonicalFiniteTaylorGridLimit
  (gridCost observationClockWithGain polynomialClockWithGain row_weaken stepClockWithGain)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid polynomialGrid observationCap)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (rowNumeratorWithGains rowDenominator)
open GaussianBarnesCanonicalHeadUniformMass (headCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianL1 (norm1 norm1_one normSq_le_norm1_square)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (ofGaussian positive_product)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def analyticGain (R M : PTm n) : PTm n :=
  analyticGainWithCaps (R+one) M (headCap (R+one)) (cap (R+one))

def clockGain (R : PTm n) : PTm n := clockGainWithCaps (R+one) (cap (R+one))

def stepClock (p R M : PTm n) : PTm n := stepClockWithGain p R M (analyticGain R M)

def observationClock (p z h R B r M : PTm n) : PTm n :=
  observationClockWithGain p z h R B r M (clockGain R)

def refinement (p R M d : PTm n) : PTm n := unit (stepClock p R M)*d

theorem admitted_refinement (p z R B M d : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hd : Γ ⊢[PRAAx] le one d) :
    let E := refinement p R M d
    Γ ⊢[PRAAx] source (scale E z) R (E*B) ⋏
      ((ofGaussian (scale E z) (E*B) ≐ ofGaussian z B) ⋏
        (le one (normSq oneCode) ⋏ le (norm1 oneCode*unit (stepClock p R M)) (E*B))) := by
  let U := unit (stepClock p R M)
  let E := refinement p R M d
  have hu := unit_positive (Γ := Γ) (stepClock p R M)
  have he : Γ ⊢[PRAAx] le one E := positive_product U d hu hd
  have positive := positive_product E B he hz.andE₁
  have disk : Γ ⊢[PRAAx] bounded (scale E z) (R*(E*B)) :=
    le_congr (.eqRefl _) (by ipra_ring) (bounded_scale E hz.andE₂)
  have center := GaussianGammaEncodingRescaling.fraction_rescale z B E hz.andE₁ he
  have nonzero : Γ ⊢[PRAAx] le one (normSq oneCode) :=
    le_congr (.eqRefl _) normSq_one.eqSymm (le_refl one)
  have first : Γ ⊢[PRAAx] le U E :=
    le_congr (one_mul U) (mul_comm _ _) (mul_le_mul_right U hd)
  have next : Γ ⊢[PRAAx] le E (E*B) :=
    le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E hz.andE₁)
  have small : Γ ⊢[PRAAx] le (norm1 oneCode*U) (E*B) :=
    le_congr ((congrMul norm1_one (.eqRefl U)).eqTrans (one_mul U)).eqSymm (.eqRefl _) (le_trans first next)
  exact .andI (.andI positive disk) (.andI center (.andI nonzero small))

private theorem normalized_rows (t q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le ((previous M*stepDivisor R)*H) B) :
    Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r (previous M)) (polynomialGrid t q z h R B H r M (previous M))
      (succ (previous M)) (rowNumeratorWithGains q t B H M (gridCost q z h R B H r M) (analyticGain R M) (clockGain R))
      (rowDenominator q t B M) := by
  let U := unit t
  let e := previous M
  let S := R+one
  let P := headCap S
  let K := cap S
  let A := GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.numerator q S B (e*H) M
  let D := GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q S B M
  let A' := numeratorWithCaps q S B H M P K
  let D' := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M
  let C := observationCap q z h R B H r M e
  have cmp : Γ ⊢[PRAAx] le (A*D') (A'*D) :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.radius_comparison_with_caps q S B H M P K
  have hf : Γ ⊢[PRAAx] le ((A*U*U+D*(U+(one+C)*U))*(D'*U))
      ((A'*U+D'*(two+C))*(D*U*U)) := by
    ipra_le 𝔞(U)*𝔞(U)*𝔞(U)*sl cmp
  exact row_weaken _ _ _ _ _ _ _
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.denominator_positive t t q R B M hz.andE₁)
    (GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.row_denominator_positive q t B M hz.andE₁)
    hf (GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.row_bound t t q z h R B H r M e hz hh hs)

theorem rate (p z h R B r M t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hh : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R M)) B)
    (ht : Γ ⊢[PRAAx] le (observationClock p z h R B r M) t) :
    Γ ⊢[PRAAx] distanceBounded (value t z h R B r M) (ap2 F u (fd z (R+one) B r M (previous M)))
      (unit p+unit u) (unit p*unit u) :=
  GaussianBarnesCanonicalFiniteTaylorGridLimit.rate_with_gains (analyticGain R M) (clockGain R) p z h R B r M t u hz hn hh ht
    (normalized_rows t (polynomialClockWithGain p z R B M (clockGain R)) z h R B (norm1 h) r M hz
      (normSq_le_norm1_square h))

theorem actual_Barnes_finite_disk_normalized_grid_limit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     let t := var 7
     let u := var 8
     (source z R B ⋏ le one (normSq h)) ⟶
       (le (norm1 h*unit (stepClock p R M)) B ⋏ le (observationClock p z h R B r M) t) ⟶
       distanceBounded (value t z h R B r M) (ap2 F u (fd z (R+one) B r M (previous M)))
         (unit p+unit u) (unit p*unit u)) :=
  closeUniv 9 (.impI (.impI (rate _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

theorem actual_Barnes_disk_step_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let p := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let d := var 5
     let E := refinement p R M d
     source z R B ⟶ le one d ⟶ source (scale E z) R (E*B) ⋏
      ((ofGaussian (scale E z) (E*B) ≐ ofGaussian z B) ⋏
        (le one (normSq oneCode) ⋏ le (norm1 oneCode*unit (stepClock p R M)) (E*B)))) :=
  closeUniv 6 (.impI (.impI (admitted_refinement _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorDiskGridLimit

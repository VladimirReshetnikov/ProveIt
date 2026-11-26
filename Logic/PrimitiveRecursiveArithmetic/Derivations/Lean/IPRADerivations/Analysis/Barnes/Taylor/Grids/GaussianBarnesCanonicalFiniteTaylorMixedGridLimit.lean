import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorMixedGridLimit

/-!
# Linear rate to the next fixed Barnes factorial name

Every row and the factorial name use the given finite cutoff.
The coefficient is observed at an independent clock, and the
literal grid clock pays the remaining normalization errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded_mono normSq)
open GaussianBarnesCanonicalCofinalTaylorMixedGridLimit (baseClock polynomialClock)
open GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial (mixedGrid grid_rate)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial (analyticCoefficient combinedClockGain combinedGridCost value)
open GaussianBarnesCanonicalFiniteTaylorGridLeading (observationCost prefactorClock rational_readback)
open GaussianBarnesCanonicalFiniteTaylorGridLimit (coefficientClock)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (amplification)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (readbackGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_as_product naturalPoint)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def observationClock (z h R B r M : PTm n) : PTm n :=
  let q := polynomialClock z R B M
  exponent (amplification B M*combinedGridCost q z h R B r M+(one+observationCost q z R B (two*norm1 h) r M)) (baseClock B)

def gain (R M : PTm n) : PTm n := analyticCoefficient R M+num 6

private theorem double_bound (x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y A D) :
    Γ ⊢[PRAAx] distanceBounded (natScale two x) (natScale two y) (two*A) D :=
  distance_congr (natScale_as_product two x).eqSymm (natScale_as_product two y).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifferenceQuotient.scale_distance (naturalPoint two) x y two A D hD
      (GaussianNamedNaturalScale.natural_point_bound two) h)

theorem rate (z h R B r M e t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*norm1 h))) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (ht : Γ ⊢[PRAAx] le (observationClock z h R B r M) t) :
    Γ ⊢[PRAAx] distanceBounded (mixedGrid t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r M (succ e))))
      (gain R M*norm1 h*unit u+two*B) (B*unit u) := by
  let S := R+one
  let k := baseClock B
  let q := polynomialClock z R B M
  let c := coefficientClock k z R B M
  let N := previous M
  let H := norm1 h
  let T := unit t
  let Q := unit q
  let U := unit u
  let K := unit k
  let C := unit c
  let a := analyticCoefficient R M
  let b := amplification B M*combinedClockGain R
  let d := amplification B M*combinedGridCost q z h R B r M
  let f := observationCost q z R B (two*H) r M
  let g := readbackGain z S B N
  let x := mixedGrid t z h R B r e
  let y := value t q z h R B r M
  let v := ap2 F u (fd z S B r M N)
  have hB := hz.andE₁
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hE := positive_product _ _ hB (unit_positive u)
  have wide : Γ ⊢[PRAAx] source z S B :=
    .andI hB (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by dsimp only [S]; ipra_ring)))
  have payK : Γ ⊢[PRAAx] le B K :=
    le_congr ((congrMul (.eqRefl B) (pw_zero two)).eqTrans (by ipra_ring)) (.eqRefl K) (query_budget B zero)
  have payB : Γ ⊢[PRAAx] le (b*B) Q :=
    le_trans (Common.mul_le_mul (le_refl b) payK) (le_trans (query_budget b k) (unit_monotone (le_add_left _ _)))
  have payT : Γ ⊢[PRAAx] le ((d+(one+f))*B) T :=
    le_trans (Common.mul_le_mul (le_refl _) payK)
      (le_trans (query_budget _ _) (unit_monotone ht))
  have payD : Γ ⊢[PRAAx] le (d*B) T :=
    le_trans (mul_le_mul_right B (le_add_right d (one+f))) payT
  have payF : Γ ⊢[PRAAx] le ((one+f)*B) T :=
    le_trans (mul_le_mul_right B (le_add_left (one+f) d)) payT
  have payG : Γ ⊢[PRAAx] le (g*B) C := by
    have leading := Common.mul_le_mul (le_refl g) payK
    have fuller : Γ ⊢[PRAAx] le (g*K) ((num 4*g)*K) := le_of_eq_add (d := num 3*g*K) (by ipra_ring)
    exact le_trans leading (le_trans fuller (query_budget _ _))
  have raw := grid_rate t q z h R B r M e hz hn hsmall hdeg
  have grid : Γ ⊢[PRAAx] distanceBounded x y (a*H+two) B :=
    distance_radius_mono _ _ _ _ _ _
      (GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.denominator_positive q t B hB) hB
      (show Γ ⊢[PRAAx] le (((a*H*Q*T+b*B*T+d*B*Q))*B) ((a*H+two)*(B*Q*T)) from
        by ipra_le 𝔞(B)*𝔞(T)*sl payB+𝔞(B)*𝔞(Q)*sl payD) raw
  have rawCoeff := rational_readback u t c q z R B (two*H) r M wide (le_add_right _ _)
  have coeff : Γ ⊢[PRAAx] distanceBounded v
      (GaussianRationalHorner.qmul (ap2 finiteNameF t (finiteData z S B r))
        (GaussianBarnesCanonicalFiniteTaylorGridLeading.coefficient q z R B (two*H) r M))
      (two*U+B) (B*U) :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive c)) hE
      (by
        change Γ ⊢[PRAAx] le (((g*U*T+C*(U+T))+f*C*U)*(B*U)) ((two*U+B)*(C*U*T))
        ipra_le 𝔞(U)*𝔞(U)*𝔞(T)*sl payG+𝔞(C)*𝔞(U)*𝔞(U)*sl payF) rawCoeff
  have first := distance_radius_mono x y (a*H+two) B ((a*H+two)*U) (B*U) hB hE
    (le_of_eq_add (d := zero) (by ipra_ring)) grid
  have last := distance_symmetric _ _ _ _ hE (double_bound _ _ _ _ hE coeff)
  have total := distance_triangle_same _ _ _ _ _ _ hE first last
  have target : Γ ⊢[PRAAx] natScale two v ≐ natScale two (ap2 F u (fd z S B r M (succ e))) := by
    let y₀ := finiteData z S B r
    let L := GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientF
    have d₀ : Γ ⊢[PRAAx] GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData z S B r M N ≐
        GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData z S B r M (succ e) := by
      ipra_congr (GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData
        (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
        with [.eqRefl z, .eqRefl S, .eqRefl B, .eqRefl r, .eqRefl M, hdeg]
        using [GaussianBarnesCanonicalFixedTaylorDerivativeName.coefficientData,LeanProofs.IPRA.Analysis.Products.fact,one]
    have ds : Γ ⊢[PRAAx] fd z S B r M N ≐ fd z S B r M (succ e) := by
      ipra_congr (GaussianNameArithmetic.multiplyData finiteNameF L (var 0) (var 1) : PTm 2)
        with [.eqRefl y₀, d₀] using [GaussianBarnesCanonicalFixedTaylorDerivativeName.data,y₀,L]
    exact GaussianRationalNaturalScale.natScale_congr (.eqRefl two) (congrAp2 F (.eqRefl u) ds)
  have fit : Γ ⊢[PRAAx] le (((a*H+two)*U)+two*(two*U+B)) (gain R M*H*U+two*B) := by
    change Γ ⊢[PRAAx] le (((a*H+two)*U)+two*(two*U+B)) ((a+num 6)*H*U+two*B)
    ipra_le 6*𝔞(U)*sl hH
  exact distance_congr (.eqRefl x) target (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hE hE (mul_le_mul_right (B*U) fit) total)

theorem actual_Barnes_finite_mixed_grid_next_factorial_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let e := var 6
     let t := var 7
     let u := var 8
     (source z R B ⋏ le one (normSq h) ⋏ previous M ≐ succ e) ⟶
       (le (stepDivisor R*(previous M*(two*norm1 h))) B ⋏ le (observationClock z h R B r M) t) ⟶
       distanceBounded (mixedGrid t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r M (succ e))))
         (gain R M*norm1 h*unit u+two*B) (B*unit u)) :=
  closeUniv 9 (.impI (.impI (rate _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp0.andE₁
    Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorMixedGridLimit

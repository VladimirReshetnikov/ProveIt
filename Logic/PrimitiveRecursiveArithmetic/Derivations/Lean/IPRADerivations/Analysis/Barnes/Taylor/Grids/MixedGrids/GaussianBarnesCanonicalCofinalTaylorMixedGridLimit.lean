import IPRADerivations.Analysis.Barnes.Taylor.Grids.MixedGrids.GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence

/-!
# Linear rate from the mixed Barnes grid to the next factorial name

A single Taylor polynomial controls both original cofinal grids. The
observation clocks pay the arithmetic error after normalization, while
the leading analytic error is linear in the native Gaussian step.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorMixedGridLimit

open_ipra
open ComplexLogarithmRemainder (bounded_mono normSq)
open GaussianBarnesCanonicalCofinalTaylorGridIncrementRate (mixedGrid)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (tailCutoff)
open GaussianBarnesCanonicalCofinalTaylorMixedGridPolynomial (analyticCoefficient combinedClockGain combinedGridCost grid_rate value)
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
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_as_product naturalPoint)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "gd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def baseClock (B : PTm n) : PTm n := exponent B zero

def polynomialClock (z R B M : PTm n) : PTm n :=
  let p := baseClock B
  prefactorClock (coefficientClock p z R B M) z R B M+
    exponent (amplification B M*combinedClockGain R) p

def cutoff (z R B M : PTm n) : PTm n :=
  tailCutoff (polynomialClock z R B M) R+
    GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff (baseClock B) (R+one) M (previous M)

def observationClock (z h R B M : PTm n) : PTm n :=
  let k := baseClock B
  let q := polynomialClock z R B M
  let r := cutoff z R B M
  k+exponent (amplification B M*combinedGridCost q z h R B r M+(two+observationCost q z R B (two*norm1 h) r M)) k

def gain (R M : PTm n) : PTm n := analyticCoefficient R M+num 10

private theorem double_bound (x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y A D) :
    Γ ⊢[PRAAx] distanceBounded (natScale two x) (natScale two y) (two*A) D :=
  distance_congr (natScale_as_product two x).eqSymm (natScale_as_product two y).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifferenceQuotient.scale_distance (naturalPoint two) x y two A D hD
      (GaussianNamedNaturalScale.natural_point_bound two) h)

theorem rate (z h R B M e t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*(two*norm1 h))) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (ht : Γ ⊢[PRAAx] le (observationClock z h R B M) t) :
    Γ ⊢[PRAAx] distanceBounded (mixedGrid t z h R B e) (natScale two (ap2 G u (gd z (R+one) B M (succ e))))
      (gain R M*norm1 h*unit u+two*B) (B*unit u) := by
  let S := R+one
  let k := baseClock B
  let q := polynomialClock z R B M
  let c := coefficientClock k z R B M
  let r := cutoff z R B M
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
  let x := mixedGrid t z h R B e
  let y := value t q z h R B r M
  let v := ap2 F t (fd z S B r M N)
  let w := ap2 G u (gd z S B M N)
  have hB := hz.andE₁
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hE := positive_product _ _ hB (unit_positive u)
  have wide : Γ ⊢[PRAAx] source z S B :=
    .andI hB (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by dsimp only [S]; ipra_ring)))
  have payK : Γ ⊢[PRAAx] le B K :=
    le_congr ((congrMul (.eqRefl B) (pw_zero two)).eqTrans (by ipra_ring)) (.eqRefl K) (query_budget B zero)
  have payB : Γ ⊢[PRAAx] le (b*B) Q :=
    le_trans (Common.mul_le_mul (le_refl b) payK) (le_trans (query_budget b k) (unit_monotone (le_add_left _ _)))
  have payT : Γ ⊢[PRAAx] le ((d+(two+f))*B) T :=
    le_trans (Common.mul_le_mul (le_refl _) payK)
      (le_trans (query_budget _ _) (unit_monotone (le_trans (le_add_left _ k) ht)))
  have payD : Γ ⊢[PRAAx] le (d*B) T :=
    le_trans (mul_le_mul_right B (le_add_right d (two+f))) payT
  have payF : Γ ⊢[PRAAx] le ((two+f)*B) T :=
    le_trans (mul_le_mul_right B (le_add_left (two+f) d)) payT
  have payG : Γ ⊢[PRAAx] le (g*B) C := by
    have leading := Common.mul_le_mul (le_refl g) payK
    have fuller : Γ ⊢[PRAAx] le (g*K) ((num 4*g)*K) := le_of_eq_add (d := num 3*g*K) (by ipra_ring)
    exact le_trans leading (le_trans fuller (query_budget _ _))
  have payTK : Γ ⊢[PRAAx] le K T := unit_monotone (le_trans (le_add_right k _) ht)
  have raw := grid_rate t q z h R B r M e hz hn hsmall (le_add_right _ _) hdeg
  have grid : Γ ⊢[PRAAx] distanceBounded x y (a*H+two) B :=
    distance_radius_mono _ _ _ _ _ _
      (GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.denominator_positive q t B hB) hB
      (show Γ ⊢[PRAAx] le (((a*H*Q*T+b*B*T+d*B*Q))*B) ((a*H+two)*(B*Q*T)) from
        by ipra_le 𝔞(B)*𝔞(T)*sl payB+𝔞(B)*𝔞(Q)*sl payD) raw
  have rawCoeff := rational_readback t t c q z R B (two*H) r M wide (le_add_right _ _)
  have coeff : Γ ⊢[PRAAx] distanceBounded v
      (GaussianRationalHorner.qmul
        (ap2 GaussianBarnesCanonicalFiniteCentralExponential.finiteNameF t
          (GaussianBarnesCanonicalFiniteCentralExponential.finiteData z S B r))
        (GaussianBarnesCanonicalFiniteTaylorGridLeading.coefficient q z R B (two*H) r M)) two B :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive c)) hB
      (by
        change Γ ⊢[PRAAx] le (((g*T*T+C*(T+T))+f*C*T)*B) (two*(C*T*T))
        ipra_le 𝔞(T)*𝔞(T)*sl payG+𝔞(C)*𝔞(T)*sl payF) rawCoeff
  have first : Γ ⊢[PRAAx] distanceBounded x (natScale two v) (a*H+num 6) B :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same x y (natScale two v) _ _ B hB grid
        (distance_symmetric _ _ _ _ hB (double_bound _ _ _ _ hB coeff)))
  have rawTail := rate_at G F (gd z S B M N) (fd z S B r M N) one K u t
    (GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate k z S B r M N wide (le_refl N) (le_add_left _ _))
  have tail : Γ ⊢[PRAAx] distanceBounded w v (two*U+B) (B*U) :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive k)) hE
      (by
        change Γ ⊢[PRAAx] le ((one*U*T+K*(U+T))*(B*U)) ((two*U+B)*(K*U*T))
        ipra_le 𝔞(U)*𝔞(U)*𝔞(T)*sl payK+𝔞(U)*𝔞(U)*𝔞(K)*sl (le_trans payK payTK)) rawTail
  have first' := distance_radius_mono x (natScale two v) (a*H+num 6) B ((a*H+num 6)*U) (B*U) hB hE
    (le_of_eq_add (d := zero) (by ipra_ring)) first
  have last := distance_symmetric _ _ _ _ hE (double_bound _ _ _ _ hE tail)
  have total := distance_triangle_same _ _ _ _ _ _ hE first' last
  have target : Γ ⊢[PRAAx] natScale two w ≐ natScale two (ap2 G u (gd z S B M (succ e))) := by
    let y₀ := GaussianBarnesCanonicalCenteredExponentialShift.baseData z S B
    let E := GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
    let L := GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientF
    have d₀ : Γ ⊢[PRAAx] GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData z S B M N ≐
        GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData z S B M (succ e) := by
      ipra_congr (GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        with [.eqRefl z, .eqRefl S, .eqRefl B, .eqRefl M, hdeg]
        using [GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData,LeanProofs.IPRA.Analysis.Products.fact,one]
    have ds : Γ ⊢[PRAAx] gd z S B M N ≐ gd z S B M (succ e) := by
      ipra_congr (GaussianNameArithmetic.multiplyData E L (var 0) (var 1) : PTm 2) with [.eqRefl y₀, d₀]
        using [GaussianBarnesCanonicalTaylorProductDerivativeName.data,y₀,E,L]
    exact GaussianRationalNaturalScale.natScale_congr (.eqRefl two) (congrAp2 G (.eqRefl u) ds)
  have fit : Γ ⊢[PRAAx] le (((a*H+num 6)*U)+two*(two*U+B)) (gain R M*H*U+two*B) := by
    change Γ ⊢[PRAAx] le (((a*H+num 6)*U)+two*(two*U+B)) ((a+num 10)*H*U+two*B)
    ipra_le 10*𝔞(U)*sl hH
  exact distance_congr (.eqRefl x) target (.eqRefl _) (.eqRefl _)
    (distance_radius_mono_same hE fit total)

theorem actual_Barnes_mixed_grid_next_factorial_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let e := var 5
     let t := var 6
     let u := var 7
     (source z R B ⋏ le one (normSq h) ⋏ previous M ≐ succ e) ⟶
       (le (stepDivisor R*(previous M*(two*norm1 h))) B ⋏ le (observationClock z h R B M) t) ⟶
       distanceBounded (mixedGrid t z h R B e) (natScale two (ap2 G u (gd z (R+one) B M (succ e))))
         (gain R M*norm1 h*unit u+two*B) (B*unit u)) :=
  closeUniv 8 (.impI (.impI (rate _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp0.andE₁
    Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorMixedGridLimit

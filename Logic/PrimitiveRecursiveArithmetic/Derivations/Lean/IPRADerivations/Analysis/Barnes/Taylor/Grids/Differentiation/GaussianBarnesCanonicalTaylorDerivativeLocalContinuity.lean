import IPRADerivations.Analysis.Barnes.Taylor.Grids.Differentiation.GaussianBarnesCanonicalTaylorAllOrderDerivative
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.FixedCoefficients.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Bounds.GaussianNamedBoundedProductObservation
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct

/-!
# A local modulus for the original cofinal Barnes factorial names

The adjacent derivative estimate at precision zero bounds the actual
quotient uniformly. Multiplication by the exact rational step recovers
the endpoint difference. The diagonal observation allowance is removed
by the finite integer-gap comparison at independent clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeLocalContinuity

open_ipra
open ComplexLogarithmRemainder (add bounded_mono normSq)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData)
open GaussianBarnesCanonicalCentralUniformBound (centralCap central_samples)
open GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence (factorialCap factorial_samples)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaCanonicalExponent (constantF)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNameArithmetic (multiply_canonical)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNamedMultiplyRate (sampleBound sample_bound_at)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianRationalHorner (canonical ofGaussian ofGaussian_represents positive_product qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "K" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientF
local notation "kd" => GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "Q" => GaussianBarnesCanonicalTaylorNamedQuotient.nameF
local notation "qd" => GaussianBarnesCanonicalTaylorNamedQuotient.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def cap (R J e : PTm n) : PTm n := centralCap R*factorialCap R J e
def localCap (R e : PTm n) : PTm n := cap (R+one) (pred e) (succ e)+num 3
def threshold (R e : PTm n) : PTm n := GaussianBarnesCanonicalTaylorAllOrderDerivative.stepClock zero R e

theorem samples (z R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous J)) : Γ ⊢[PRAAx] sampleBound F (fd z R B J e) (cap R J e) :=
  GaussianNamedBoundedProductObservation.sample_bounds E K (baseData z R B) (kd z R B J e)
    (centralCap R) (factorialCap R J e) (central_samples z R B hz) (factorial_samples z R B J e hz he)

private theorem widen (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem retained_next (e : PTm n) : Γ ⊢[PRAAx] le (succ e) (previous (pred e)) := by
  apply Common.succ_le_succ
  refine .orE (lt_or_le zero e) ?_ ?_
  · exact le_congr (.eqRefl e) (Common.pos_of_one_le Prf.hyp0) (le_refl e)
  · exact le_trans Prf.hyp0 (zero_le _)

private theorem norm_near (x y C A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hx : Γ ⊢[PRAAx] canonical x) (hy : Γ ⊢[PRAAx] bounded y C one)
    (hd : Γ ⊢[PRAAx] distanceBounded x y A B) : Γ ⊢[PRAAx] bounded x (C*B+A) B :=
  bound_congr (GaussianRationalLinearProduct.add_sub_right y x hx) (by ipra_ring) (one_mul B)
    (bounded_sum y (qsub x y) C one A B (le_refl one) hB hy hd)

private theorem quotient_bound (f g D : PR 2) (x y h B w C : PTm n)
    (hr : Γ ⊢[PRAAx] independentRate (GaussianNamedDifferenceQuotient.nameF f g) D
      (GaussianNamedDifferenceQuotient.data f g x y h B) w one one)
    (hb : Γ ⊢[PRAAx] sampleBound D w C) :
    Γ ⊢[PRAAx] sampleBound (GaussianNamedDifferenceQuotient.nameF f g)
      (GaussianNamedDifferenceQuotient.data f g x y h B) (C+num 3) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let t : PTm (n+1) := var 0
  let J := GaussianNamedDifferenceQuotient.nameF f g
  let a := GaussianNamedDifferenceQuotient.data f g (sh x) (sh y) (sh h) (sh B)
  have rr : Δ ⊢[PRAAx] independentRate J D a (sh w) one one := by simpa [Δ,a,J,sh,Fm.shift,Syn.shift,one] using hr.shift
  have bb : Δ ⊢[PRAAx] sampleBound D (sh w) (sh C) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hb.shift
  have ht : Δ ⊢[PRAAx] le one (unit t) := unit_positive t
  have hfit : Δ ⊢[PRAAx] le (rateNumerator one one t t*one) (num 3*rateDenominator one t t) := by
    dsimp only [rateNumerator,rateDenominator]
    ipra_le Groth.ι (IPRA.Q.mk Δ (unit t))*sl ht + Groth.ι (IPRA.Q.mk Δ (unit t))*sl ht
  have near : Δ ⊢[PRAAx] distanceBounded (ap2 J t a) (ap2 D t (sh w)) (num 3) one :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ (le_refl one))
      (le_refl one) hfit (rate_at J D a (sh w) one one t t rr)
  have can : Δ ⊢[PRAAx] canonical (ap2 J t a) :=
    multiply_canonical constantF (GaussianNamedDifference.nameF f g) (GaussianNamedDifferenceQuotient.inverse (sh h) (sh B))
      (GaussianNamedDifference.data (sh x) (sh y)) t
  have b := norm_near _ _ (sh C) (num 3) one (le_refl one) can (sample_bound_at D (sh w) (sh C) t bb) near
  have exactBound : Δ ⊢[PRAAx] bounded (ap2 J t a) (sh C+num 3) one :=
    bound_congr (.eqRefl _) (congrAdd ((mul_comm (sh C) one).eqTrans (one_mul (sh C))) (.eqRefl _)) (.eqRefl _) b
  simpa [sampleBound,Δ,a,J,t,sh,Syn.shift,one] using exactBound

theorem quotient_samples (z h R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (he : Γ ⊢[PRAAx] le e (previous J)) (hs : Γ ⊢[PRAAx] le (norm1 h*unit (threshold R e)) B) :
    Γ ⊢[PRAAx] sampleBound Q (qd z h R B J e) (localCap R e) := by
  let d := fd z (R+one) B (pred e) (succ e)
  have hr := GaussianBarnesCanonicalTaylorAllOrderDerivative.rate zero z h R B J e hz hw hn he hs
  have rr := GaussianNamedDifferenceRate.rate_parameters_congr Q F (qd z h R B J e) d one (unit zero) one one
    (.eqRefl one) (pw_zero two) hr
  exact quotient_bound F F F _ _ h B d _ rr
    (samples z (R+one) B (pred e) (succ e) (widen z R B hz) (retained_next e))

private theorem step_bound (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ofGaussian h B) (norm1 h) B := by
  have scaled : Γ ⊢[PRAAx] le (normSq h*(B*B)) ((norm1 h*norm1 h)*(B*B)) :=
    mul_le_mul_right (B*B) (normSq_le_norm1_square h)
  exact bounded_of_cleared (ofGaussian h B) h B (norm1 h) B hB hB (ofGaussian_represents h B hB)
    (le_congr (mul_comm _ _) (.eqRefl _) scaled)

private theorem multiply_back_at (f g : PR 2) (x y h B C t : PTm n)
    (hi : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input f g x y h B)
    (hc : Γ ⊢[PRAAx] sampleBound (GaussianNamedDifferenceQuotient.nameF f g)
      (GaussianNamedDifferenceQuotient.data f g x y h B) C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f t x) (ap2 g t y)
      ((norm1 h*C)*unit t+(norm1 h*(one+two*B))*B) (B*unit t) := by
  let J := GaussianNamedDifferenceQuotient.nameF f g
  let d := GaussianNamedDifferenceQuotient.data f g x y h B
  let u := ap2 J t d
  let v := GaussianNamedDifferenceQuotient.raw f g t t x y h B
  let w := ofGaussian h B
  let y' := qsub (ap2 f t x) (ap2 g t y)
  let I := GaussianNamedDifferenceQuotient.inverse h B
  let A := one+two*B
  let U := unit t
  let H := norm1 h
  let sep := hi.andE₂.andE₂
  have hB := sep.andE₁
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  have den := GaussianNamedDifferenceQuotient.denominator_positive (Γ := Γ) t t t
  have raw := GaussianNamedDifferenceQuotient.independent_readback f g t t t x y h B hi
  have near : Γ ⊢[PRAAx] distanceBounded v u A U :=
    distance_symmetric _ _ _ _ hU (distance_radius_mono _ _ _ _ _ _ den hU
      (le_of_eq_add (d := zero) (by
        dsimp only [A,U,GaussianNamedDifferenceQuotient.numerator,GaussianNamedDifferenceQuotient.denominator]
        ipra_ring)) raw)
  have vb : Γ ⊢[PRAAx] bounded v (C*U+A) U :=
    norm_near v u C A U hU (qmul_canonical I y') (sample_bound_at J d C t hc) near
  have inverse := (GaussianRationalPowerAlgebra.qmul_commutative (Γ := Γ) w I).eqTrans
    (GaussianNamedDifferenceQuotient.actual_inverse h B sep)
  have cancel : Γ ⊢[PRAAx] qmul w v ≐ y' :=
    GaussianRationalInverseQuadraticAlgebra.cancel_nested_product w I y' (qsub_canonical _ _) inverse
  have base : Γ ⊢[PRAAx] distanceBounded (ap2 f t x) (ap2 g t y) (H*(C*U+A)) (B*U) :=
    bound_congr cancel (.eqRefl _) (.eqRefl _)
      (bounded_product w v H B (C*U+A) U hB hU (step_bound h B hB) vb)
  have fit : Γ ⊢[PRAAx] le (H*(C*U+A)) ((H*C)*U+(H*A)*B) := by
    ipra_le 𝔞 H*𝔞 A*sl hB
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hB hU) (positive_product _ _ hB hU)
    (mul_le_mul_right (B*U) fit) base

private theorem multiply_back (f g : PR 2) (x y h B C : PTm n)
    (hi : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input f g x y h B)
    (hc : Γ ⊢[PRAAx] sampleBound (GaussianNamedDifferenceQuotient.nameF f g)
      (GaussianNamedDifferenceQuotient.data f g x y h B) C) :
    Γ ⊢[PRAAx] independentRate f g x y (norm1 h*C) B := by
  apply GaussianNamedLipschitzRate.independent_rate f g x y (norm1 h*C) B (norm1 h*(one+two*B))
    hi.andE₂.andE₂.andE₁ hi.andE₁ hi.andE₂.andE₁
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have inp : Δ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input f g (sh x) (sh y) (sh h) (sh B) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hi.shift
  have cap' : Δ ⊢[PRAAx] sampleBound (GaussianNamedDifferenceQuotient.nameF f g)
      (GaussianNamedDifferenceQuotient.data f g (sh x) (sh y) (sh h) (sh B)) (sh C) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift
  simpa [GaussianNamedLipschitzRate.diagonalNumerator,GaussianNamedLipschitzRate.diagonalDenominator,sh,Syn.shift,one,two] using
    multiply_back_at f g (sh x) (sh y) (sh h) (sh B) (sh C) (var 0) inp cap'

theorem local_rate (z h R B J e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (he : Γ ⊢[PRAAx] le e (previous J)) (hs : Γ ⊢[PRAAx] le (norm1 h*unit (threshold R e)) B) :
    Γ ⊢[PRAAx] independentRate F F (fd (add z h) (R+one) B J e) (fd z (R+one) B J e)
      (norm1 h*localCap R e) B := by
  have plus := GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ (widen (add z h) R B hw) he
  have base := GaussianBarnesCanonicalTaylorProductDerivativeName.regular _ _ _ _ _ (widen z R B hz) he
  exact multiply_back F F _ _ h B (localCap R e) (.andI plus (.andI base (.andI hz.andE₁ hn)))
    (quotient_samples z h R B J e hz hw hn he hs)

theorem actual_Barnes_factorial_Taylor_local_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let J := var 4
     let e := var 5
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h) ⋏ le e (previous J) ⋏
       le (norm1 h*unit (threshold R e)) B) ⟶
       independentRate F F (fd (add z h) (R+one) B J e) (fd z (R+one) B J e) (norm1 h*localCap R e) B) :=
  closeUniv 6 (.impI (local_rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorDerivativeLocalContinuity

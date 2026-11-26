import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorEvenGridUniformComparison
import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFiniteTaylorDiskGridLimit

/-!
# The quadratic displacement term of the finite Barnes even grid

The opposite grids use a polynomial of degree one greater than the
normalization order. Cancel the common step powers in the analytic
error, and keep explicit separate bounds for the two observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ComplexLogarithmRemainder (bounded bounded_neg)
open GaussianBarnesCanonicalCenteredProductRate (headCap)
open GaussianBarnesCanonicalCorrectedMercatorCofinal (analyticDenominator)
open GaussianBarnesCanonicalExponentTaylorWeightedMass (massCap)
open GaussianBarnesCanonicalFiniteTaylorDiskGridLimit (analyticGain clockGain)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (backward_samples observed target)
open GaussianBarnesCanonicalFiniteTaylorGridLimit (row_weaken)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid polynomialGrid scaledPolynomial observationCap)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget (rowNumeratorWithGains rowDenominator row_denominator_positive)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorRecomposition (capGain)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPolynomialForwardDifferenceGrid (samples)
open GaussianPolynomialForwardDifferenceGridError (rowBound subst_rowBound)
open GaussianPolynomialForwardDifferenceGridEvenError (even_coefficient_error)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product qzero)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (distanceBounded qnegative)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "TaylorNumerator" => GaussianBarnesCanonicalFiniteWeightedTaylorUniformValue.numerator
local notation "TaylorDenominator" => GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator

def amplification (B e : PTm n) : PTm n := pw (num 4*B) e

def analyticCoefficient (R M e : PTm n) : PTm n := two*pw (num 4) e*analyticGain R M

def clockCoefficient (R B e : PTm n) : PTm n := amplification B e*(two*clockGain R)

def rowCost (q z h R B H r M e : PTm n) : PTm n :=
  two+observationCap q z h R B H r M e

def observationCoefficient (q z h R B H r M e : PTm n) : PTm n :=
  amplification B e*(rowCost q z h R B H r M e+rowCost q z (ComplexLogarithmRemainder.neg h) R B H r M e)

def numerator (q t z h R B H r M e : PTm n) : PTm n :=
  analyticCoefficient R M e*(H*H)*unit q*unit t+
    clockCoefficient R B e*(B*B)*unit t+
    observationCoefficient q z h R B H r M e*(B*B)*unit q

def denominator (q t B : PTm n) : PTm n := (B*B)*unit q*unit t

theorem denominator_positive (q t B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator q t B) :=
  positive_product _ _ (positive_product _ _ (positive_product B B hb hb) (unit_positive q)) (unit_positive t)

private theorem numerator_monotone (q R B x y M P F : PTm n) (hxy : Γ ⊢[PRAAx] le x y) :
    Γ ⊢[PRAAx] le (GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator_with_caps q R B x M P F)
      (GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator_with_caps q R B y M P F) := by
  let j := succ (previous M)
  let U := unit q
  let d := analyticDenominator (previous M) R B
  let b := pw B j
  let K := headCap R
  let c : PTm n := capGain two
  let L := massCap R
  let E := pw (num 3) L
  have h₂ := pw_le_pw j (Common.mul_le_mul (le_refl two) hxy)
  have h₄ := pw_le_pw j (Common.mul_le_mul (le_refl (num 4)) hxy)
  change Γ ⊢[PRAAx] le
    (K*(F*((c*(two*pw (two*x) j*U+d))*b+((two*pw L j+E)*pw (num 4*x) j)*(d*U)))+
      (d*U)*(F*((P*E)*pw (num 4*x) j)))
    (K*(F*((c*(two*pw (two*y) j*U+d))*b+((two*pw L j+E)*pw (num 4*y) j)*(d*U)))+
      (d*U)*(F*((P*E)*pw (num 4*y) j)))
  ipra_le (2*𝔞(K)*𝔞(F)*𝔞(c)*𝔞(U)*𝔞(b))*sl h₂+
    ((𝔞(K)*𝔞(F)*(2*𝔞(pw L j)+𝔞(E))+𝔞(F)*𝔞(P)*𝔞(E))*𝔞(d)*𝔞(U))*sl h₄

private theorem rows (t q z h R B H r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r e) (polynomialGrid t q z h R B H r M e) (succ e)
      (rowNumeratorWithGains q t B H M (rowCost q z h R B H r M e) (analyticGain R M) (clockGain R))
      (rowDenominator q t B M) := by
  let U := unit t
  let S := R+one
  let P := GaussianBarnesCanonicalHeadUniformMass.headCap S
  let F := GaussianBarnesCanonicalFiniteCentralDiskBound.cap S
  let A := TaylorNumerator q S B (e*H) M
  let D := TaylorDenominator q S B M
  let A' := GaussianBarnesCanonicalFiniteTaylorGridBudget.numeratorWithCaps q S B H M P F
  let D' := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M
  let C := observationCap q z h R B H r M e
  have grow : Γ ⊢[PRAAx] le A (TaylorNumerator q S B (previous M*H) M) :=
    numerator_monotone q S B (e*H) (previous M*H) M P F (mul_le_mul_right H he)
  have cmp : Γ ⊢[PRAAx] le (A*D') (A'*D) :=
    le_trans (mul_le_mul_right D' grow)
      (GaussianBarnesCanonicalFiniteTaylorGridBudget.radius_comparison_with_caps q S B H M P F)
  have fit : Γ ⊢[PRAAx] le ((A*U*U+D*(U+(one+C)*U))*(D'*U))
      ((A'*U+D'*(two+C))*(D*U*U)) := by
    ipra_le 𝔞(U)*𝔞(U)*𝔞(U)*sl cmp
  exact row_weaken _ _ _ _ _ _ _
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.denominator_positive t t q R B M hz.andE₁)
    (row_denominator_positive q t B M hz.andE₁) fit
    (GaussianBarnesCanonicalFiniteTaylorGridUniformObservations.row_bound t t q z h R B H r M e hz hh hsmall)

private theorem row_target_congr {V P Q N A B : PTm n} (he : Γ ⊢[PRAAx] P ≐ Q)
    (hrow : Γ ⊢[PRAAx] rowBound V P N A B) : Γ ⊢[PRAAx] rowBound V Q N A B := by
  have moved := Prf.eqSubst1 (Γ := Γ) (rowBound (Syn.shift V) (var 0) (Syn.shift N) (Syn.shift A) (Syn.shift B)) he
    (by simpa only [subst_rowBound,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using hrow)
  simpa only [subst_rowBound,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using moved

private theorem power_two_steps (B M e : PTm n) (he : Γ ⊢[PRAAx] previous M ≐ succ e) :
    Γ ⊢[PRAAx] pw B (succ (previous M)) ≐ pw B e*(B*B) :=
  (congrAp2 powF (congrSucc he) (.eqRefl B)).eqTrans
    ((pw_succ B (succ e)).eqTrans
      ((congrMul (pw_succ B e) (.eqRefl B)).eqTrans (by ipra_ring)))

private theorem radius_comparison (q t z h R B H r M e : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (he : Γ ⊢[PRAAx] previous M ≐ succ e) :
    let K₁ := rowCost q z h R B H r M e
    let K₂ := rowCost q z (ComplexLogarithmRemainder.neg h) R B H r M e
    let A := analyticGain R M
    let C := clockGain R
    let X := rowNumeratorWithGains q t B H M K₁ A C
    let Y := rowNumeratorWithGains q t B H M K₂ A C
    Γ ⊢[PRAAx] le
      ((pw (two*B) e*(pw two e*(X+Y)))*denominator q t B)
      (numerator q t z h R B H r M e*(pw H e*rowDenominator q t B M)) := by
  let j := succ (previous M)
  let U := unit q
  let T := unit t
  let K₁ := rowCost q z h R B H r M e
  let K₂ := rowCost q z (ComplexLogarithmRemainder.neg h) R B H r M e
  let A := analyticGain R M
  let C := clockGain R
  let X := rowNumeratorWithGains q t B H M K₁ A C
  let Y := rowNumeratorWithGains q t B H M K₂ A C
  let W := amplification B e
  let D := denominator q t B
  let hpow := pw H e
  let bpow := pw B e
  have fit : Γ ⊢[PRAAx] le one hpow := GaussianFactorBudget.power_positive H e hH
  have amp : Γ ⊢[PRAAx] pw (two*B) e*pw two e ≐ W :=
    (AnalyticNumberTheory.LocalFactor.pw_mul_base (two*B) two e).eqSymm.eqTrans
      (congrAp2 powF (.eqRefl e) (by ipra_ring))
  have rearrange : Γ ⊢[PRAAx] (pw (two*B) e*(pw two e*(X+Y)))*D ≐ W*(X+Y)*D :=
    (show Γ ⊢[PRAAx] (pw (two*B) e*(pw two e*(X+Y)))*D ≐ (pw (two*B) e*pw two e)*(X+Y)*D by ipra_ring).eqTrans
      (congrMul (congrMul amp (.eqRefl _)) (.eqRefl _))
  have hEq := natEq (power_two_steps (Γ := Γ) H M e he)
  have bEq := natEq (power_two_steps (Γ := Γ) B M e he)
  have ampExpanded : Γ ⊢[PRAAx] W ≐ pw (num 4) e*bpow :=
    AnalyticNumberTheory.LocalFactor.pw_mul_base (num 4) B e
  have aEq := natEq ampExpanded
  refine le_congr rearrange.eqSymm (.eqRefl _) ?_
  change Γ ⊢[PRAAx] le
    ((W*(((A*pw H j*U+C*pw B j)*T+(pw B j*U)*K₁)+
      ((A*pw H j*U+C*pw B j)*T+(pw B j*U)*K₂)))*((B*B)*U*T))
    ((two*pw (num 4) e*A*(H*H)*U*T+W*(two*C)*(B*B)*T+W*(K₁+K₂)*(B*B)*U)*
      (hpow*((pw B j*U)*T)))
  ipra_le (𝔞(W)*𝔞(pw B j)*𝔞(B)*𝔞(B)*𝔞(U)*𝔞(T)*(2*𝔞(C)*𝔞(T)+(𝔞(K₁)+𝔞(K₂))*𝔞(U)))*sl fit using
    rw [hEq,bEq,aEq]
    dsimp only [hpow,bpow]
    ring

theorem coefficient_error (q t z h R B H r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B)
    (hH : Γ ⊢[PRAAx] le one H) (he : Γ ⊢[PRAAx] previous M ≐ succ e)
    (hstep : Γ ⊢[PRAAx] lower (ofGaussian h B) H (two*B)) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (target t q z R B H r M e)
      (numerator q t z h R B H r M e) (denominator q t B) := by
  let P := scaledPolynomial t q z R B H r M e
  let V := literalGrid t z h R B r e
  let W := literalGrid t z (ComplexLogarithmRemainder.neg h) R B r e
  let u := ofGaussian h B
  let N := rowDenominator q t B M
  let A := analyticGain R M
  let C := clockGain R
  let K₁ := rowCost q z h R B H r M e
  let K₂ := rowCost q z (ComplexLogarithmRemainder.neg h) R B H r M e
  let X := rowNumeratorWithGains q t B H M K₁ A C
  let Y := rowNumeratorWithGains q t B H M K₂ A C
  have hb := hz.andE₁
  have order : Γ ⊢[PRAAx] le e (previous M) := le_congr (.eqRefl e) he.eqSymm (le_succ_self e)
  have shape : Γ ⊢[PRAAx] length P ≐ succ (succ e) :=
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.scaled_polynomial_length t q z R B H r M e).eqTrans (congrSucc he)
  have hd : Γ ⊢[PRAAx] le one (two*B) := positive_product _ _ (le_succ_self one) hb
  have hN := row_denominator_positive q t B M hb
  have plus : Γ ⊢[PRAAx] rowBound V (samples P (succ e) qzero u) (succ e) X N :=
    rows t q z h R B H r M e hz hh hsmall order
  have minus : Γ ⊢[PRAAx] rowBound W (samples P (succ e) qzero (qnegative u)) (succ e) Y N :=
    row_target_congr (backward_samples t q z h R B H r M e hb)
      (rows t q z (ComplexLogarithmRemainder.neg h) R B H r M e hz (bounded_neg hh) hsmall order)
  have raw := even_coefficient_error V W P e u H (two*B) X Y N shape hH hd hstep hN plus minus
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (GaussianFactorBudget.power_positive H e hH) hN)
    (denominator_positive q t B hb) (radius_comparison q t z h R B H r M e hH he) raw

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridBudget

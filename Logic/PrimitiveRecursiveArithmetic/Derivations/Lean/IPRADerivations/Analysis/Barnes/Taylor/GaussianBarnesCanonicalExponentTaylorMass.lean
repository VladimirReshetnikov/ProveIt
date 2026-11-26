import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalExponentTaylorBuffer
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalHeadCorrectionExponentialDerivative
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalPrefactorLipschitz
import IPRADerivations.Analysis.Polynomials.GaussianCoefficientUniformNorm

/-!
# The frozen Barnes exponent coefficients have a uniform mass cap

The two fixed named constants have numerical bounds independent of
their observation clocks. The inverse-square tail estimates bound
the stored finite logarithmic coefficients independently of the
retained product cutoff. Together these supply a uniform finite
coefficient mass at each requested order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorMass

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalExponentTaylorBuffer
  (buffer buffer_length descending_at coefficient coefficient_zero coefficient_one coefficient_two coefficient_high
    prefactorLinear prefactorQuadratic linearCoefficient quadraticCoefficient highCoefficient)
open GaussianBarnesCanonicalHigherRows (previous degree coefficientGain)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogCofinalRate (initial_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalPrefactor
  (negativeHalf quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (fraction)
open GaussianNameBounds (sample_bound U)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticBounds (natCode)
open RationalArgmin (rationalLE)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianStirlingConstant.nameF
local notation "sd" => GaussianStirlingConstant.nameData
local notation "Q" => quadraticCoefficientF
local notation "qd" => quadraticCoefficientData
local notation "Const" => GaussianGammaCanonicalExponent.constantF
local notation "D₁" => GaussianBarnesCanonicalDerivativeRow.boundNumerator
local notation "D₂" => GaussianBarnesCanonicalSecondDerivativeRow.boundNumerator

def stirlingCap : PTm n := U S (sd zero)
def quadraticCap : PTm n := U Q qd
def halfCap : PTm n := U Const negativeHalf

def linearCap (R : PTm n) : PTm n :=
  stirlingCap+halfCap*(one+(R+R)*quadraticCap)+initial R*(R+one)+D₁ R

def squareCap (R : PTm n) : PTm n := halfCap*quadraticCap+initial R+D₂ R

def coefficientCap (R M : PTm n) : PTm n := linearCap R+squareCap R+pw two (previous M)

def massCap (R M : PTm n) : PTm n := succ (previous M)*(two*coefficientCap R M)

private theorem product_one (x y A E : PTm n) (hx : Γ ⊢[PRAAx] bounded x A one)
    (hy : Γ ⊢[PRAAx] bounded y E one) : Γ ⊢[PRAAx] bounded (qmul x y) (A*E) one :=
  bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product x y A one E one (le_refl one) (le_refl one) hx hy)

private theorem add_one (x y A E : PTm n) (hx : Γ ⊢[PRAAx] bounded x A one)
    (hy : Γ ⊢[PRAAx] bounded y E one) : Γ ⊢[PRAAx] bounded (qadd x y) (A+E) one :=
  GaussianRationalPowerDifference.bounded_sum_same x y A E one (le_refl one) hx hy

private theorem weaken_one (x A B E : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le A E) (hx : Γ ⊢[PRAAx] bounded x A B) : Γ ⊢[PRAAx] bounded x E one := by
  have more : Γ ⊢[PRAAx] le (E*one) (E*B) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E hb)
  exact bounded_radius_mono _ _ _ _ _ hb (le_refl one) (le_trans (mul_le_mul_right one ha) more) hx

private theorem half_bound : Γ ⊢[PRAAx] bounded (negativeHalf : PTm n) (halfCap : PTm n) one :=
  bound_congr (GaussianGammaCanonicalExponent.constant_at zero negativeHalf) (.eqRefl _) (.eqRefl _)
    (sample_bound Const negativeHalf zero (GaussianGammaCanonicalExponent.constant_regular negativeHalf))

private theorem prefactor_first_bound (q z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (prefactorLinear q z B) (stirlingCap+halfCap*(one+(R+R)*quadraticCap)) one := by
  have wz := GaussianGammaEulerHead.fraction_disk z R B h.andE₁ h.andE₂
  have hs := sample_bound (Γ := Γ) S (sd zero) q (GaussianStirlingConstant.name_regular zero)
  have hc := sample_bound (Γ := Γ) Q qd q quadratic_coefficient_regular
  have a := add_one _ _ _ _ wz wz
  have b := product_one _ _ _ _ a hc
  have c := add_one _ _ _ _ GaussianRationalReciprocal.qone_bounded b
  exact add_one _ _ _ _ hs (product_one _ _ _ _ half_bound c)

theorem linear_bound (q z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (linearCoefficient q z R B r) (linearCap R) one := by
  let N := initial R
  have slope := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.slope_bound z B N R h.andE₁ h.andE₂
  have tail := GaussianBarnesCanonicalDerivativeTail.tail_bound z R B N r (initial_source z R B h)
  exact add_one _ _ _ _ (add_one _ _ _ _ (prefactor_first_bound q z R B h) slope)
    (weaken_one _ _ _ _ (initial_positive R) (le_refl _) tail)

theorem quadratic_bound (q z R B r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (quadraticCoefficient q z R B r) (squareCap R) one := by
  let N := initial R
  have sliced := GaussianBarnesCanonicalSecondDerivativeTail.tail_bound z R B N r (initial_source z R B h)
  have tail := weaken_one _ _ _ _ (initial_positive R) (le_refl _) sliced
  have hp := product_one (Γ := Γ) _ _ _ _ half_bound (sample_bound Q qd q quadratic_coefficient_regular)
  have half := weaken_one (Γ := Γ) _ _ _ _ (le_succ_self one) (le_refl one) (radius_bounded one two (le_succ_self one))
  have harmonic := GaussianGammaCanonicalExponentBound.harmonic_point_bound (Γ := Γ) N
  have a := bound_congr (.eqRefl _) (one_mul N) (.eqRefl _) (product_one _ _ _ _ half harmonic)
  have b := bound_congr (.eqRefl _) (one_mul (D₂ R)) (.eqRefl _) (product_one _ _ _ _ half tail)
  exact add_one _ _ _ _ (add_one _ _ _ _ hp a) b

theorem higher_bound (z R B r j : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] bounded (highCoefficient z R B r j) (coefficientGain j) one :=
  weaken_one _ _ _ _ (initial_positive R) (le_refl _)
    (GaussianBarnesCanonicalHigherTail.tail_bound z R B (initial R) j r (initial_source z R B h))

private theorem coefficient_congr (q z R B r : PTm n) {e f : PTm n} (he : Γ ⊢[PRAAx] e ≐ f) :
    Γ ⊢[PRAAx] coefficient q z R B r e ≐ coefficient q z R B r f := by
  ipra_congr (coefficient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl q,.eqRefl z,.eqRefl R,.eqRefl B,.eqRefl r,he]

theorem coefficient_bound (q z R B r M e : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] bounded (coefficient q z R B r e) (coefficientCap R M) one := by
  let E := pw two (previous M)
  let T := coefficientCap R M
  have hlin : Γ ⊢[PRAAx] le (linearCap R) T :=
    le_trans (le_add_right _ _) (le_add_right _ _)
  have hquad : Γ ⊢[PRAAx] le (squareCap R) T :=
    le_trans (le_add_left _ _) (le_add_right _ _)
  have hhigh : Γ ⊢[PRAAx] le E T := le_add_left _ _
  refine (lt_or_le e one).orE ?_ ?_
  · let Δ := lt e one :: Γ
    have ez : Δ ⊢[PRAAx] e ≐ zero :=
      le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) (zero_le e)
    have read := (coefficient_congr q z R B r ez).eqTrans (coefficient_zero q z R B r)
    exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded T one (le_refl one))
  · refine (lt_or_le e two).orE ?_ ?_
    · let Δ := lt e two :: le one e :: Γ
      have eq : Δ ⊢[PRAAx] e ≐ one :=
        le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) Prf.hyp1
      have read := (coefficient_congr q z R B r eq).eqTrans (coefficient_one q z R B r)
      exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
        (weaken_one _ _ _ _ (le_refl one) hlin.wk.wk (linear_bound q z R B r h.wk.wk))
    · refine (lt_or_le e (num 3)).orE ?_ ?_
      · let Δ := lt e (num 3) :: le two e :: le one e :: Γ
        have eq : Δ ⊢[PRAAx] e ≐ two :=
          le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) Prf.hyp1
        have read := (coefficient_congr q z R B r eq).eqTrans (coefficient_two q z R B r)
        exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
          (weaken_one _ _ _ _ (le_refl one) hquad.wk.wk.wk (quadratic_bound q z R B r h.wk.wk.wk))
      · let j := monus e (num 3)
        have eq : (le (num 3) e :: le two e :: le one e :: Γ) ⊢[PRAAx] e ≐ degree j :=
          (eq_add_of_le Prf.hyp0).eqTrans (by unfold degree previous; ipra_ring)
        have leDegree := le_congr eq (.eqRefl _) he.wk.wk.wk
        have powLe := GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) leDegree
        have read := (coefficient_congr q z R B r eq).eqTrans (coefficient_high q z R B r j)
        exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
          (weaken_one _ _ _ _ (le_refl one) (le_trans powLe hhigh.wk.wk.wk) (higher_bound z R B r j h.wk.wk.wk))

theorem mass (q z R B r M : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] rationalLE (coefficientNorm (buffer q z R B r M)) (fraction (massCap R M) one) := by
  let C := buffer q z R B r M
  let N := succ (previous M)
  let E := two*coefficientCap R M
  have entries : Γ ⊢[PRAAx] GaussianCoefficientUniformNorm.entryBounds C N (natCode E) := by
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh N) :: Γ.map Fm.shift
    have source_shift : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
      simpa only [Δ, Fm.shift, Syn.shift, sh, GaussianBarnesCanonicalLogCofinal.subst_source] using h.shift.wk
    have idx : Δ ⊢[PRAAx] le i (previous (sh M)) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    let e := monus (previous (sh M)) i
    have em : Δ ⊢[PRAAx] le e (previous (sh M)) := GaussianRationalMonicReconstruction.monus_le_left _ _
    have read := descending_at (sh q) (sh z) (sh R) (sh B) (sh r) (sh M) i idx
    have bound := coefficient_bound (sh q) (sh z) (sh R) (sh B) (sh r) (sh M) e source_shift em
    have l1 := GaussianRationalL1Algebra.qL1_of_bounded _ _ _ (le_refl one)
      (bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) bound)
    simpa [GaussianCoefficientUniformNorm.entryBounds, Syn.shift, sh, i, Δ, C, N, E, coefficientCap,
      linearCap, squareCap, stirlingCap, halfCap, quadraticCap, natCode, fraction, one, two, pw,
      GaussianBarnesCanonicalPrefactor.negativeHalf, GaussianBarnesCanonicalPrefactor.quadraticCoefficientData] using l1
  have g := GaussianCoefficientUniformNorm.coefficient_uniform C N (natCode E) (buffer_length q z R B r M) entries
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (GaussianRationalSyntheticBounds.natCode_multiply N E) g

theorem actual_Barnes_exponent_Taylor_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let q := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     source z R B ⟶ rationalLE (coefficientNorm (buffer q z R B r M)) (fraction (massCap R M) one)) :=
  closeUniv 6 (.impI (mass _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorMass

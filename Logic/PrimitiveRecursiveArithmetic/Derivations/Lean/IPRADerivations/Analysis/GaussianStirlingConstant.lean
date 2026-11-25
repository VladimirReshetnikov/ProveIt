import IPRADerivations.Analysis.GaussianStirlingNames
import IPRADerivations.Analysis.GaussianGaussTriplicationPi
import IPRADerivations.Analysis.GaussianArctangentPiMargins

/-!
# The literal Stirling constant

The positive logarithm reads the original doubled arctangent π name.
A finite rational comparison makes every doubled-π observation at
least one. The result is multiplied by the exact scalar (1/2).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingConstant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGaussTriplicationPi (doubledPiF doubledPiData doubled_pi_regular)
open GaussianStirlingNames (constant_real fraction_axis multiply_real positive_log_real)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaHalfPiName (meshAt clearing)
open GaussianGammaHalfRisingFactorial (factorial_positive)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at multiply_fast)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul qmul_canonical canonical canonical_congr ofGaussian_canonical
  ofGaussian_represents positive_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianEuclideanDistanceName (pointCN)
open RationalValueBounds (upper upper_congr upper_of_order positive_cancel)
open RationalArgmin (rationalLE)
open RationalGaussianEmbedding (axis axis_congr)
open ComplexLogarithmRemainder (re oneCode)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "P" => GaussianGammaHalfPiName.nameF
local notation "C" => constantF
local notation "L" => GaussianArctangentPiMargins.lowerDen
local notation "K" => GaussianArctangentPiMargins.lowerNum

def piNumerator (p : PTm n) : PTm n := num 4*BaselQuadrature.Q (meshAt p) (clearing p)
def piDenominator (p : PTm n) : PTm n := fact (clearing p)

private theorem pi_read (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 P p x ≐ fraction (piNumerator p) (piDenominator p) :=
  GaussianGammaHalfPiName.sample_at p x

private theorem pi_denominator_positive (p : PTm n) : Γ ⊢[PRAAx] le one (piDenominator p) :=
  factorial_positive _

private theorem margin_denominator_positive : Γ ⊢[PRAAx] le one (L : PTm n) := by
  unfold GaussianArctangentPiMargins.lowerDen
  ipra_le 499

private theorem pi_fraction_lower (p x : PTm n) :
    Γ ⊢[PRAAx] le (piDenominator p) (piNumerator p) := by
  let A := piNumerator p
  let B := piDenominator p
  let U := unit p
  let D : PTm n := L
  let N : PTm n := K
  let a := fstT (fraction N D)
  let b := fstT (fraction A B)
  have hD : Γ ⊢[PRAAx] le one D := margin_denominator_positive
  have hB : Γ ⊢[PRAAx] le one B := pi_denominator_positive p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have raw : Γ ⊢[PRAAx] upper a b one U := upper_congr (.eqRefl _) (congrFst (pi_read p x)) (.eqRefl _) (.eqRefl _)
    (GaussianArctangentPiMargins.named_margins p x).andE₁
  let lhs := ZT.ofNat (U*B)*ZT.ofNat N
  let rhs := ZT.ofNat (U*D)*ZT.ofNat A+ZT.ofNat (one*D*B)
  have e : Γ ⊢[PRAAx] zle lhs rhs :=
    RationalUpperRepresentation.upper_from_representations _ _ D B one U (ZT.ofNat N) (ZT.ofNat A)
      (fraction_first_represents N D hD) (fraction_first_represents A B hB) raw
  have finite : Γ ⊢[PRAAx] le (U*B*N) (U*D*A+D*B) := by
    apply le_of_eq_add (d := PolynomialBisection.slack lhs rhs)
    have signed := zle_toZ e
    apply deriveNat
    unfold PolynomialBisection.slack
    dsimp only [lhs,rhs] at signed
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at signed
    ipra_simps
    linear_combination -signed
  apply positive_cancel (c := U*D) (positive_product _ _ hU hD)
  dsimp only [N] at finite
  unfold GaussianArctangentPiMargins.lowerNum at finite
  change Γ ⊢[PRAAx] le (U*D*B) (U*D*A)
  ipra_le sl finite + 2*𝔞 D*𝔞 B*sl hU + 𝔞 D*𝔞 B + 𝔞 U*𝔞 B

def inputClock (p x : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus P C x (naturalPoint two)) p

theorem doubled_read (p x : PTm n) :
    Γ ⊢[PRAAx] ap2 doubledPiF p (doubledPiData x) ≐
      fraction (piNumerator (inputClock p x)*two) (piDenominator (inputClock p x)*one) := by
  let t := inputClock p x
  let a := ap2 P t x
  let b := ap2 C t (naturalPoint two)
  have e := (multiply_at (Γ := Γ) P C x (naturalPoint two) p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul a b) (qmul_canonical a b))
  exact e.eqTrans ((GaussianRationalSyntheticDivision.qmul_congr (pi_read t x) (constant_at t (naturalPoint two))).eqTrans
    (GaussianEulerDampedTimeRate.fraction_product (piNumerator t) (piDenominator t) two one
      (pi_denominator_positive t) (le_refl one)))

private theorem doubled_fraction_denominator (p x : PTm n) :
    Γ ⊢[PRAAx] le one (piDenominator (inputClock p x)*one) :=
  positive_product _ _ (pi_denominator_positive _) (le_refl one)

theorem doubled_lower (p x : PTm n) :
    Γ ⊢[PRAAx] rationalLE (fstT (marginPoint one)) (fstT (ap2 doubledPiF p (doubledPiData x))) := by
  let t := inputClock p x
  let A := piNumerator t
  let B := piDenominator t
  let q := ap2 doubledPiF p (doubledPiData x)
  have hp := doubled_fraction_denominator (Γ := Γ) p x
  have order : Γ ⊢[PRAAx] le (B*one) (A*two) := by ipra_le sl (pi_fraction_lower t x) + 𝔞 A
  have hq := GaussianRationalHorner.scalar_congr (congrFst (doubled_read p x)).eqSymm (.eqRefl _) (.eqRefl _)
    (fraction_first_represents (A*two) (B*one) hp)
  apply RationalArithmetic.order_of_representations _ _ (re oneCode) (ZT.ofNat (A*two)) one (B*one)
    (ofGaussian_represents oneCode one (le_refl one)).andE₁ hq (le_refl one) hp
  apply zle_of_toZ (monus (A*two) (B*one))
  have e := natEq (eq_add_of_le order)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]
  ipra_simps
  linear_combination -e

private theorem shift_doubled (x : PTm n) : Syn.shift (doubledPiData x) = doubledPiData (Syn.shift x) := by
  simp [doubledPiData,Syn.shift,two,one]

theorem doubled_pi_real (x : PTm n) : Γ ⊢[PRAAx] realSamples doubledPiF (doubledPiData x) := by
  refine .allI ?_
  rw [shift_doubled]
  let p : PTm (n+1) := var 0
  let X := Syn.shift x
  let Δ := Γ.map Fm.shift
  let t := inputClock p X
  have hD := doubled_fraction_denominator (Γ := Δ) p X
  have read := doubled_read (Γ := Δ) p X
  exact .andI (canonical_congr read (ofGaussian_canonical _ _ hD))
    (axis_congr read.eqSymm (fraction_axis (piNumerator t*two) (piDenominator t*one) hD))

theorem doubled_pi_source (x : PTm n) : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source doubledPiF (doubledPiData x) one := by
  refine .andI (doubled_pi_regular x) (.andI (le_refl one) ?_)
  refine .allI (.allI ?_)
  let X := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have e := upper_of_order _ _ (unit p+unit q) (unit p*unit q) (doubled_lower (Γ := Δ) q X)
  have align := upper_congr (congrFst (constant_at (Γ := Δ) p (marginPoint one))).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) e
  simpa [GaussianNamedRightHalfPlane.certificate,GaussianNamedPositiveExponentialOrder.realOrder,
    GaussianNamedRightHalfPlane.marginPoint,doubledPiData,one,two,ComplexLogarithmRemainder.oneCode,
    ComplexLogarithmRemainder.code,ZT.ofNat,Syn.shift,Δ,X,p,q] using align

def logDoubledPiF : PR 2 := GaussianNamedPositiveLogarithm.nameF (retimedF doubledPiF)
def logDoubledPiData (x : PTm n) : PTm n :=
  GaussianNamedPositiveLogarithm.data (retimedData (doubledPiData x) one) (two*one)
def nameF : PR 2 := multiplyF C logDoubledPiF
def nameData (x : PTm n) : PTm n := multiplyData C logDoubledPiF (fraction one two) (logDoubledPiData x)

@[simp] theorem subst_logDoubledPiData {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (logDoubledPiData x) = logDoubledPiData (Syn.subst σ x) := by
  simp [logDoubledPiData,doubledPiData,two,one]
@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) :
    Syn.subst σ (nameData x) = nameData (Syn.subst σ x) := by simp [nameData,one,two]

theorem log_source (x : PTm n) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source (retimedF doubledPiF)
      (retimedData (doubledPiData x) one) (two*one) (GaussianNameBounds.U doubledPiF (doubledPiData x)) :=
  GaussianNamedPositiveLateLogSource.positive_source doubledPiF (doubledPiData x) one
    (doubled_pi_source x) (doubled_pi_real x)

theorem log_doubled_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN logDoubledPiF (logDoubledPiData x) :=
  GaussianNamedPositiveLogarithm.name_regular _ _ _ _ (log_source x)

theorem name_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN nameF (nameData x) :=
  multiply_fast C logDoubledPiF _ _ (constant_regular _) (log_doubled_regular x)

theorem name_real (x : PTm n) : Γ ⊢[PRAAx] realSamples nameF (nameData x) :=
  multiply_real C logDoubledPiF _ _
    (constant_real _ (ofGaussian_canonical _ _ (le_succ_self one)) (fraction_axis one two (le_succ_self one)))
    (positive_log_real _ _ _)

theorem actual_Stirling_constant_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN nameF (nameData (var 0)) ⋏ realSamples nameF (nameData (var 0))) :=
  closeUniv 1 (.andI (name_regular _) (name_real _))

end LeanProofs.IPRA.Analysis.GaussianStirlingConstant

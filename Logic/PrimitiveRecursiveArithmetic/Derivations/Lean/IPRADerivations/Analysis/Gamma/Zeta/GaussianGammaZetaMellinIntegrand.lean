import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName
import IPRADerivations.Analysis.Exponential.GaussianExponentialAffineLower
import IPRADerivations.Analysis.Names.GaussianNamedDifference
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductApartness

/-!
# The original Gamma–zeta Mellin integrand at positive rational times

Use the same power of the positive time as in the Euler Gamma
integrand. Its other factor is the actual reciprocal of the unscaled
exponential minus one. All observations of that denominator have a
certified gap of at least the original time.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianDominantPairAlgebra (radiusPoint subst_radiusPoint)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiplyModulus multiplyRaw)
open GaussianNameRingLaws (negativeF negativeData negative_at oneF one_at one_fast)
open GaussianRationalHorner (qmul qmul_canonical ofGaussian_canonical)
open GaussianRationalLowerBounds (lower lower_congr name_lower inverse_bound)
open GaussianRationalMetric (bounded qnegative qnegative_canonical qsub qsub_canonical)
open GaussianRationalPolynomialExponential (scalarBody)
open GaussianRationalReciprocal (bound_congr reciprocal reciprocal_canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr qzero_add)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Power" => GaussianEulerIntegrandName.powerF
local notation "powerData" => GaussianEulerIntegrandName.powerData

def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def exponentialData (a b : PTm n) : PTm n :=
  GaussianGammaFiniteApproximantName.exponentialInputData constantF (radiusPoint a b)
def denominatorF : PR 2 := GaussianNamedDifference.nameF exponentialF oneF
def denominatorData (a b : PTm n) : PTm n := GaussianNamedDifference.data (exponentialData a b) zero
def denominatorClock (p : PTm n) : PTm n := exponent two p
def reciprocalF : PR 2 := GaussianNameReciprocal.nameF denominatorF
def reciprocalData (a b : PTm n) : PTm n := GaussianNameReciprocal.nameData b (denominatorData a b)
def reciprocalClock (p b : PTm n) : PTm n :=
  exponent (GaussianNameReciprocal.modulus b) p+GaussianNameReciprocal.anchor b
def nameF : PR 2 := multiplyF Power reciprocalF
def data (z D a b : PTm n) : PTm n := multiplyData Power reciprocalF (powerData z D a b) (reciprocalData a b)
def factorClock (p z D a b : PTm n) : PTm n :=
  exponent (multiplyModulus Power reciprocalF (powerData z D a b) (reciprocalData a b)) p

@[simp] theorem subst_exponentialData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (exponentialData a b) = exponentialData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [exponentialData,GaussianGammaFiniteApproximantName.exponentialInputData]

@[simp] theorem subst_denominatorData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (denominatorData a b) = denominatorData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [denominatorData]

@[simp] theorem subst_reciprocalData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (reciprocalData a b) = reciprocalData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [reciprocalData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z D a b : PTm n) :
    Syn.subst σ (data z D a b) = data (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [data]

theorem denominator_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN denominatorF (denominatorData a b) := by
  let t := radiusPoint a b
  let R := GaussianNameBounds.U constantF t
  exact GaussianNamedDifference.name_regular _ _ _ _
    (GaussianRadiusExponentialName.name_regular constantF R t
      (GaussianGammaFiniteApproximantName.exponential_input constantF t (constant_regular t))) (one_fast zero)

private theorem negative_one_at (p : PTm n) :
    Γ ⊢[PRAAx] ap2 (negativeF oneF) p (negativeData zero) ≐ qnegative qone := by
  have raw := (negative_at (Γ := Γ) oneF zero p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qsub_canonical _ _))
  exact raw.eqTrans ((qsub_congr (.eqRefl _) (one_at _ _)).eqTrans
    (qzero_add _ (qnegative_canonical _)))

theorem denominator_at (p a b : PTm n) : Γ ⊢[PRAAx]
    ap2 denominatorF p (denominatorData a b) ≐
      qsub (ap2 exponentialF (denominatorClock p) (exponentialData a b)) qone :=
  (GaussianExponentialReference.add_sample exponentialF (negativeF oneF) (exponentialData a b)
    (negativeData zero) p).eqTrans (qadd_congr (.eqRefl _) (negative_one_at (denominatorClock p)))

theorem denominator_lower (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] lower (ap2 denominatorF p (denominatorData a b)) a b := by
  let x := radiusPoint a b
  let R := GaussianNameBounds.U constantF x
  let r := denominatorClock p
  let k := GaussianRadiusExponentialName.index R r
  let t := GaussianRadiusExponentialName.inputPrecision R r
  have read := (GaussianRadiusExponentialName.sample_at (Γ := Γ) constantF R r x).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _) (constant_at t x))
  have gap := GaussianExponentialAffineLower.finite_gap_lower x k a b
    (GaussianPositiveExponentialTermBound.actual_positive_fraction a b hb)
    (ofGaussian_canonical _ _ hb)
    (GaussianPositiveExponentialSeparation.original_cutoff_positive R r) hb
    (RationalArgmin.reflexive (fstT x))
  exact lower_congr ((denominator_at p a b).eqTrans (qsub_congr read (.eqRefl qone))).eqSymm
    (.eqRefl a) (.eqRefl b) gap

theorem denominator_apart (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart denominatorF b (denominatorData a b) := by
  let p := GaussianNameReciprocal.anchor b
  let x := ap2 denominatorF p (denominatorData a b)
  have h := name_lower x a b ha hb (denominator_lower p a b hb)
  have grow : Γ ⊢[PRAAx] le b (unit b) := le_trans (le_succ_self b) (RationalClosure.succ_le_two_pow b)
  exact GaussianNamedFiniteProductApartness.weaken_margin x b (unit b) hb grow h

theorem reciprocal_bound (p a b : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (ap2 reciprocalF p (reciprocalData a b)) b a := by
  let r := reciprocalClock p b
  let x := ap2 denominatorF r (denominatorData a b)
  have read : Γ ⊢[PRAAx] ap2 reciprocalF p (reciprocalData a b) ≐ reciprocal x :=
    (GaussianNameReciprocal.name_at denominatorF b (denominatorData a b) p).eqTrans
      (GaussianExponentialReference.recode_fixed _ (reciprocal_canonical x))
  exact bound_congr read.eqSymm (.eqRefl b) (.eqRefl a)
    (inverse_bound x a b ha hb (denominator_lower r a b hb))

theorem reciprocal_at (p a b : PTm n) : Γ ⊢[PRAAx]
    ap2 reciprocalF p (reciprocalData a b) ≐
      reciprocal (qsub (ap2 exponentialF (denominatorClock (reciprocalClock p b)) (exponentialData a b)) qone) := by
  let r := reciprocalClock p b
  let x := ap2 denominatorF r (denominatorData a b)
  have read := (GaussianNameReciprocal.name_at (Γ := Γ) denominatorF b (denominatorData a b) p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (reciprocal_canonical x))
  exact read.eqTrans (GaussianNameReciprocal.reciprocal_congr (denominator_at r a b))

theorem regular (z D a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z D a b) :
    Γ ⊢[PRAAx] pointCN nameF (data z D a b) :=
  multiply_fast _ _ _ _ (GaussianEulerIntegrandName.power_regular z D a b h)
    (GaussianNameReciprocal.name_fast denominatorF b (denominatorData a b) (denominator_regular a b)
      (denominator_apart a b h.andE₂.andE₁ h.andE₂.andE₂))

theorem sample_at (p z D a b : PTm n) :
    let k := factorClock p z D a b
    Γ ⊢[PRAAx] ap2 nameF p (data z D a b) ≐
      qmul (ap2 Power k (powerData z D a b)) (ap2 reciprocalF k (reciprocalData a b)) := by
  let x := powerData z D a b
  let y := reciprocalData a b
  let k := factorClock p z D a b
  exact (GaussianNameArithmetic.multiply_at Power reciprocalF x y p).eqTrans
    (GaussianExponentialReference.recode_fixed (multiplyRaw Power reciprocalF k x y) (qmul_canonical _ _))

theorem actual_gamma_zeta_mellin_integrand_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianEulerIntegrandName.source (var 0) (var 1) (var 2) (var 3) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinIntegrand

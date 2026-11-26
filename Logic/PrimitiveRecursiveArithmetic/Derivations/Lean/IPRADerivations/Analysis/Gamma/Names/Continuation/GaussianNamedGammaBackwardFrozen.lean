import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaBackwardShift
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Rounds for the backward Gamma construction at exact native inputs

The denominator of a sampled positive argument also encodes its difference
from one. The same frozen sample supplies the reciprocal factor and the
positive Gamma factor. All sufficiently late sample indices give an
independent-observation error bound for their actual original product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaBackwardFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedGammaBackwardShift (source minusOneF minusOneData negativeOne reciprocalF reciprocalData
  minus_one_at reciprocal_input nameF data)
open GaussianNamedRightHalfPlane (numerator denominator radius threshold)
open GaussianEulerNamedShiftInput (clock clock_later)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameReciprocal (R anchor lower R_positive)
open GaussianRationalHorner (ofGaussian canonical ofGaussian_represents ofGaussian_canonical
  canonical_unique qzero qadd qadd_represents qadd_canonical represents_congr positive_product)
open GaussianRationalMetric (bounded qsub_represents)
open GaussianRationalReciprocal (qone qone_represents_scaled reciprocal bound_congr)
open ComplexLogarithmRemainder (scale oneCode zeroCode)
open GaussianRootAlgebra (sub)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (cross_refl)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianExponentialReference (unit_monotone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nativeZ (f : PR 2) (k x : PTm n) : PTm n := numerator f (clock k) x
def nativeDen (f : PR 2) (k x : PTm n) : PTm n := denominator f (clock k) x
def nativeW (f : PR 2) (k x : PTm n) : PTm n :=
  sub (nativeZ f k x) (scale (nativeDen f k x) oneCode)

abbrev frozenF : PR 2 := multiplyF constantF gammaF
def frozenReciprocal (f : PR 2) (k x : PTm n) : PTm n :=
  reciprocal (ofGaussian (nativeW f k x) (nativeDen f k x))
def frozenData (f : PR 2) (k x A : PTm n) : PTm n :=
  multiplyData constantF gammaF (frozenReciprocal f k x)
    (GaussianNamedGammaLateInput.encodedData f (clock k) x A)

def accuracy (f : PR 2) (s x A a : PTm n) : PTm n :=
  exponent (U (GaussianNamedGamma.nameF f) (GaussianNamedGamma.data x A)+R a) s
def freezeClock (f : PR 2) (s x A a : PTm n) : PTm n :=
  let t := accuracy f s x A a
  (exponent (GaussianNameReciprocal.modulus a) t+anchor a)+
    (threshold A+succ (GaussianGammaHalfPlaneInputContinuity.modulus t (radius f x) (two*A)))

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x A : PTm n) :
    Syn.subst σ (frozenData f k x A) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ A) := by
  simp [frozenData,frozenReciprocal,nativeW,nativeZ,nativeDen,sub]

@[simp] theorem subst_freezeClock {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (s x A a : PTm n) :
    Syn.subst σ (freezeClock f s x A a) =
      freezeClock f (Syn.subst σ s) (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ a) := by
  simp [freezeClock,accuracy,threshold,GaussianNamedRightHalfPlane.precision]

theorem minus_one_fraction (f : PR 2) (k x : PTm n) : Γ ⊢[PRAAx]
    ap2 (minusOneF f) k (minusOneData x) ≐ ofGaussian (nativeW f k x) (nativeDen f k x) := by
  let z := nativeZ f k x
  let B := nativeDen f k x
  let w := nativeW f k x
  let q := ap2 f (clock k) x
  have hB : Γ ⊢[PRAAx] le one B := GaussianRationalL1.raw_den_positive q
  have ow := qsub_represents qzero qone zeroCode (scale B oneCode) B hB
    (GaussianRationalHorner.zero_represents B) (qone_represents_scaled B)
  have p := qadd_represents q negativeOne z (sub zeroCode (scale B oneCode)) B hB
    (GaussianRationalL1.raw_represents q) ow
  have represented := represents_congr (.eqRefl _) (b := w) ?_ (.eqRefl _) p
  · exact (minus_one_at f k x).eqTrans (canonical_unique _ _ w B (qadd_canonical _ _)
      (ofGaussian_canonical w B hB) hB represented (ofGaussian_represents w B hB))
  · apply GaussianRootAlgebra.equal_of_values <;>
      simp only [w,nativeW,z,B,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
        GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
        GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero] <;> ring

private theorem frozen_reciprocal_at (f : PR 2) (k x : PTm n) : Γ ⊢[PRAAx]
    GaussianNamedReciprocalFrozenRate.frozen (minusOneF f) (minusOneData x) k ≐ frozenReciprocal f k x := by
  let w := ap2 (minusOneF f) k (minusOneData x)
  let v := ofGaussian (nativeW f k x) (nativeDen f k x)
  have re := minus_one_fraction (Γ := Γ) f k x
  have hB : Γ ⊢[PRAAx] le one (nativeDen f k x) := GaussianRationalL1.raw_den_positive _
  have hCan : Γ ⊢[PRAAx] canonical w :=
    GaussianRationalHorner.canonical_congr re (ofGaussian_canonical _ _ hB)
  have e : Γ ⊢[PRAAx] GaussianFastValueCut.recode w ≐ v :=
    (GaussianExponentialReference.recode_fixed w hCan).eqTrans re
  change Γ ⊢[PRAAx] reciprocal (GaussianFastValueCut.recode w) ≐ reciprocal v
  simpa only [GaussianRationalReciprocal.subst_reciprocal,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (reciprocal (var 0) : PTm 1) (σ := ![GaussianFastValueCut.recode w]) (σ' := ![v])
      (fun i => by fin_cases i; exact e)

theorem late_anchor (f : PR 2) (s k x A a : PTm n)
    (hk : Γ ⊢[PRAAx] le (freezeClock f s x A a) k) : Γ ⊢[PRAAx] le (anchor a) k :=
  le_trans (le_add_left _ _) (le_trans (le_add_right _ _) hk)

theorem positive_late_input (f : PR 2) (s k x A a : PTm n) (hs : Γ ⊢[PRAAx] source f x A a)
    (hk : Γ ⊢[PRAAx] le (freezeClock f s x A a) k) :
    Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f (accuracy f s x A a) (clock k) x A := by
  have h := le_trans hk (clock_later k)
  exact .andI hs.andE₁ (.andI (le_trans (le_add_right _ _) (le_trans (le_add_left _ _) h))
    (le_trans (le_add_left _ _) (le_trans (le_add_left _ _) h)))

theorem original_native_lower (f : PR 2) (k x A a : PTm n) (hs : Γ ⊢[PRAAx] source f x A a)
    (hk : Γ ⊢[PRAAx] le (anchor a) k) : Γ ⊢[PRAAx]
    lower (ofGaussian (nativeW f k x) (nativeDen f k x)) (R a) :=
  GaussianNameReciprocal.lower_congr (minus_one_fraction f k x) (.eqRefl _)
    (GaussianNamedReciprocalFrozenRate.late_lower _ _ _ _ (reciprocal_input f x A a hs) hk)

private theorem constant_bound (w M : PTm n) (hw : Γ ⊢[PRAAx] bounded w M one) :
    Γ ⊢[PRAAx] sampleBound constantF w M := by
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift w) (Syn.shift M) one := by
    simpa [Fm.shift,Syn.shift] using hw.shift
  simpa only [sampleBound,Syn.shift] using
    bound_congr (constant_at (var 0) (Syn.shift w)).eqSymm (.eqRefl _) (.eqRefl _) h

theorem original_positive_quotient_rate (f : PR 2) (s k x A a : PTm n)
    (hs : Γ ⊢[PRAAx] source f x A a)
    (hk : Γ ⊢[PRAAx] le (freezeClock f s x A a) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) frozenF (data f x A a) (frozenData f k x A) one (unit s) := by
  let G := GaussianNamedGamma.nameF f
  let g := GaussianNamedGamma.data x A
  let I := reciprocalF f
  let i := reciprocalData x a
  let j := frozenReciprocal f k x
  let v := GaussianNamedGammaLateInput.encodedData f (clock k) x A
  let K := GaussianNameReciprocal.modulus a
  let t := accuracy f s x A a
  have ha := late_anchor f s k x A a hk
  have hQ := reciprocal_input f x A a hs
  have hI := GaussianNameReciprocal.name_fast _ _ _ hQ.andE₁ hQ.andE₂
  have hG := GaussianNamedGamma.name_regular f x A hs.andE₁
  have lift := GaussianNamedReciprocalFrozenRate.frozen_rate _ _ _ _ hQ ha
  have enc := frozen_reciprocal_at (Γ := Γ) f k x
  have fixed := GaussianGammaWeierstrassApproximant.constant_data_cross _ _ enc.eqSymm
  have moved := GaussianNamedRateTransport.transport I constantF I constantF i _ i j K (unit k)
    (unit_positive k) lift (cross_refl _ _ hI) fixed
  have later : Γ ⊢[PRAAx] le (exponent K t) k :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) hk)
  have query := le_trans (query_budget K t) (unit_monotone later)
  have paid := GaussianNamedRateRadius.weaken I constantF i j K (unit k) one (unit t)
    (unit_positive k) (unit_positive t) (le_congr (.eqRefl _) (one_mul _).eqSymm query) moved
  have late := positive_late_input f s k x A a hs hk
  have regular := GaussianNamedGammaLateInput.encoded_regular f t (clock k) x A late
  have positiveRate := GaussianNamedGammaLateInput.original_independent_rate f t (clock k) x A late
  have bound := GaussianNameReciprocal.inverse_bound _ _ (R_positive a) (original_native_lower f k x A a hs ha)
  have hD := unit_positive (Γ := Γ) t
  have product := GaussianNamedMultiplyRate.independent_rate I G constantF gammaF i g j v
    one (unit t) one (unit t) (U G g) (R a) hD hD hI hG (constant_regular _) regular
    (all_samples_bounded G g hG) (constant_bound j (R a) bound) paid positiveRate
  have budget : Γ ⊢[PRAAx] le ((U G g+R a)*unit s) (unit t) := query_budget (U G g+R a) s
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hD hD) (unit_positive s)
    (le_congr (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring) (by ipra_ring)
      (mul_le_mul_right (unit t) budget)) product

end LeanProofs.IPRA.Analysis.GaussianNamedGammaBackwardFrozen

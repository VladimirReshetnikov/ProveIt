import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFactorialTaylorFrozen
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedIncrementEndpoints
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeChart

/-!
# Simultaneous rational readback of the named Barnes factorial Taylor endpoints

The original named base and shifted values can freeze at the same
addition clock. Their exact common rational chart evaluates both
factorial Taylor coefficients with the same retained order and disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorIncrementEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_mono)
open GaussianBarnesCanonicalNamedDemand (source native_source)
open GaussianBarnesCanonicalNamedFactorialTaylor (data frozenData clock regular retains)
open GaussianBarnesCanonicalNamedIncrementEndpoints
  (observation nativeClock native_clock_later shifted_source base_chart_source shifted_chart_source)
open GaussianNamedIncrementChart (denominator baseNumerator stepNumerator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (recode)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalL1 (rawGaussian rawDen)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "VD" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "B" => GaussianBarnesCanonicalNamedFactorialTaylor.nameF
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

private theorem widen_disk (z R D : PTm n) (h : Γ ⊢[PRAAx] disk z R D) :
    Γ ⊢[PRAAx] disk z (R+one) D :=
  .andI h.andE₁ (bounded_mono h.andE₂ (mul_le_mul_right D (le_add_right R one)))

theorem chart_rate (F : PR 2) (p k x S z D e : PTm n)
    (hf : Γ ⊢[PRAAx] source F x S) (hz : Γ ⊢[PRAAx] disk z S D)
    (hk : Γ ⊢[PRAAx] le (clock p S e) k) (he : Γ ⊢[PRAAx] ofGaussian z D ≐ recode (ap2 F k x)) :
    Γ ⊢[PRAAx] independentRate (B F) V (data x S e) (VD z (S+one) D e e) one (unit p) := by
  let q := ap2 F k x
  have same := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross
    z (rawGaussian q) (S+one) D (rawDen q) e e (widen_disk z S D hz)
    (widen_disk (rawGaussian q) S (rawDen q) (native_source F k x S hf)) (retains e) he
  have frozen := GaussianBarnesCanonicalNamedFactorialTaylorFrozen.frozen_rate F p k x S e hf hk
  exact GaussianNamedRateTransport.transport
    (B F) V (B F) V (data x S e) (frozenData F k x S e) (data x S e) (VD z (S+one) D e e)
    one (unit p) (unit_positive p) frozen (cross_refl _ _ (regular F x S e hf)) same

theorem base_rate (F K : PR 2) (p k x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hk : Γ ⊢[PRAAx] le (clock p (R+one) e) k) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] independentRate (B F) V (data x (R+one) e)
      (VD (baseNumerator q r) ((R+one)+one) (denominator q r) e e) one (unit p) :=
  chart_rate F p (nativeClock k) x (R+one) _ _ e
    (GaussianBarnesCanonicalNamedFrozen.source_widen F x R (R+one) hf (le_add_right R one))
    (base_chart_source F K k x y R hf)
    (le_trans hk (native_clock_later k)) (GaussianNamedIncrementChart.base_fraction _ _)

theorem shifted_rate (F K : PR 2) (p k x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hs : Γ ⊢[PRAAx] source K y one)
    (hk : Γ ⊢[PRAAx] le (clock p (R+one) e) k) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] independentRate (B (addF F K)) V (data (addData x y) (R+one) e)
      (VD (add (baseNumerator q r) (stepNumerator q r)) ((R+one)+one) (denominator q r) e e)
      one (unit p) := by
  let W := ap2 (addF F K) k (addData x y)
  have canonical := GaussianNameArithmetic.add_canonical (Γ := Γ) F K x y k
  have read := (GaussianNamedIncrementChart.actual_sum_at (Γ := Γ) F K k x y).eqTrans
    (GaussianExponentialReference.recode_fixed W canonical).eqSymm
  exact chart_rate (addF F K) p k (addData x y) (R+one) _ _ e
    (shifted_source F K x y R hf hs) (shifted_chart_source F K k x y R hf hs) hk read

def endpointRates (F K : PR 2) (p k x y R e : PTm n) : Fm PTm n :=
  let q := observation F k x
  let r := observation K k y
  let D := denominator q r
  let z := baseNumerator q r
  let h := stepNumerator q r
  let S := R+one
  independentRate (B (addF F K)) V (data (addData x y) S e) (VD (add z h) (S+one) D e e) one (unit p) ⋏
    independentRate (B F) V (data x S e) (VD z (S+one) D e e) one (unit p)

@[simp] theorem subst_endpointRates {m : ℕ} (σ : Fin n → PTm m) (F K : PR 2) (p k x y R e : PTm n) :
    (endpointRates F K p k x y R e).subst σ =
      endpointRates F K (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ y)
        (Syn.subst σ R) (Syn.subst σ e) := by
  simp [endpointRates,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
    GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData,LeanProofs.IPRA.Analysis.Products.fact,one]

theorem rates (F K : PR 2) (p k x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hs : Γ ⊢[PRAAx] source K y one)
    (hk : Γ ⊢[PRAAx] le (clock p (R+one) e) k) :
    Γ ⊢[PRAAx] endpointRates F K p k x y R e :=
  .andI (shifted_rate F K p k x y R e hf hs hk) (base_rate F K p k x y R e hf hk)

theorem actual_named_Barnes_factorial_Taylor_increment_endpoint_rates_closed (F K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let p := var 0
       let k := var 1
       let x := var 2
       let y := var 3
       let R := var 4
       let e := var 5
       (source F x R ⋏ (source K y one ⋏ le (clock p (R+one) e) k)) ⟶ endpointRates F K p k x y R e) :=
  closeUniv 6 (.impI (rates F K _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylorIncrementEndpoints

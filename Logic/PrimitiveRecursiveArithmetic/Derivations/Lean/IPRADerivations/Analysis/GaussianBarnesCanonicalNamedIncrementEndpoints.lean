import IPRADerivations.Analysis.GaussianBarnesCanonicalNamedFrozen
import IPRADerivations.Analysis.GaussianNamedIncrementChart
import IPRADerivations.Analysis.GaussianNamedBoundedSumObservation
import IPRADerivations.Analysis.GaussianNamedIncrementQuotientFrozenRate

/-!
# Simultaneous rational readback of the original named Barnes endpoints

The actual addition sampler reads the base and step at one common
clock. Their exact sum and rescaled base give the two rational Barnes
inputs. Bounds for a unit step certify both at the enlarged disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedIncrementEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded_mono)
open GaussianBarnesCanonicalNamedDemand (source data frozenData native_source)
open GaussianNamedIncrementChart (denominator baseNumerator stepNumerator denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent recode)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRootApproximationWitness (point_at)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "VD" => GaussianBarnesCanonicalValue.data
local notation "B" => GaussianBarnesCanonicalNamed.nameF
local notation "clock" => GaussianBarnesCanonicalNamed.clock
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

abbrev nativeClock (k : PTm n) : PTm n := exponent two k

def observation (F : PR 2) (k x : PTm n) : PTm n := ap2 F (nativeClock k) x

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (F : PR 2) (k x : PTm n) :
    Syn.subst σ (observation F k x) = observation F (Syn.subst σ k) (Syn.subst σ x) := by
  simp [observation,two]

theorem native_clock_later (k : PTm n) : Γ ⊢[PRAAx] le k (nativeClock k) := le_add_right _ _

theorem shifted_source (F K : PR 2) (x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hs : Γ ⊢[PRAAx] source K y one) :
    Γ ⊢[PRAAx] source (addF F K) (addData x y) (R+one) :=
  .andI (add_fast F K x y hf.andE₁ hs.andE₁)
    (GaussianNamedBoundedSumObservation.sample_bounds F K x y R one hf.andE₂ hs.andE₂)

theorem base_chart_source (F K : PR 2) (k x y R : PTm n) (hf : Γ ⊢[PRAAx] source F x R) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] disk (baseNumerator q r) (R+one) (denominator q r) := by
  let q := observation F k x
  let r := observation K k y
  let D := denominator q r
  have base := GaussianNamedIncrementChart.base_source F (nativeClock k) x r R hf.andE₂
  exact .andI base.andE₁ (bounded_mono base.andE₂ (mul_le_mul_right D (le_add_right R one)))

theorem shifted_chart_source (F K : PR 2) (k x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hs : Γ ⊢[PRAAx] source K y one) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] disk (add (baseNumerator q r) (stepNumerator q r)) (R+one) (denominator q r) := by
  let q := observation F k x
  let r := observation K k y
  exact .andI (denominator_positive q r) (GaussianNamedIncrementChart.sum_disk q r R one
    (point_at F R x (nativeClock k) hf.andE₂) (point_at K one y (nativeClock k) hs.andE₂))

theorem chart_sources (F K : PR 2) (k x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hs : Γ ⊢[PRAAx] source K y one) :
    let q := observation F k x
    let r := observation K k y
    let D := denominator q r
    Γ ⊢[PRAAx] disk (baseNumerator q r) (R+one) D ⋏
      disk (add (baseNumerator q r) (stepNumerator q r)) (R+one) D :=
  .andI (base_chart_source F K k x y R hf) (shifted_chart_source F K k x y R hf hs)

theorem native_quotient_data_equal (F K L M : PR 2) (k x y u v : PTm n) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] GaussianNamedIncrementQuotientFrozenRate.nativeData L M K u v y (nativeClock k) ≐
      GaussianNamedDifferenceQuotient.data L M u v (stepNumerator q r) (denominator q r) := by
  let q := observation F k x
  let r := observation K k y
  let d := GaussianNamedDifference.data u v
  let constant := GaussianBoundedConstantProductName.constantF
  let diff := GaussianNamedDifference.nameF L M
  have he := GaussianNamedIncrementChart.step_fraction (Γ := Γ) q r
  have read := Prf.eqCongr1
    (GaussianNameArithmetic.multiplyData constant diff (GaussianRationalReciprocal.reciprocal (var 0)) (Syn.shift d)) he.eqSymm
  let raw := GaussianRationalReciprocal.reciprocal (recode r)
  let rescaled := GaussianRationalReciprocal.reciprocal (ofGaussian (stepNumerator q r) (denominator q r))
  change Γ ⊢[PRAAx] GaussianNameArithmetic.multiplyData constant diff raw d ≐
    GaussianNameArithmetic.multiplyData constant diff rescaled d
  simpa only [GaussianNameArithmetic.subst_multiplyData,GaussianRationalReciprocal.subst_reciprocal,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift,raw,rescaled] using read

private theorem endpoint_rate (F : PR 2) (p k x R z S D : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hz : Γ ⊢[PRAAx] disk z S D)
    (hk : Γ ⊢[PRAAx] le (clock p R) k) (he : Γ ⊢[PRAAx] ofGaussian z D ≐ recode (ap2 F k x)) :
    Γ ⊢[PRAAx] independentRate (B F) V (data x R) (VD z S D) one (unit p) := by
  let q := ap2 F k x
  have same := GaussianBarnesCanonicalProperness.proper z (rawGaussian q) S R D (rawDen q) hz (native_source F k x R hf) he
  have frozen := GaussianBarnesCanonicalNamedFrozen.frozen_rate F p k x R hf hk
  exact GaussianNamedRateTransport.transport (B F) V (B F) V (data x R) (frozenData F k x R) (data x R) (VD z S D)
    one (unit p) (unit_positive p) frozen
    (cross_refl _ _ (GaussianBarnesCanonicalNamed.name_regular F x R hf)) same

theorem base_rate (F K : PR 2) (p k x y R S : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hfS : Γ ⊢[PRAAx] source F x S)
    (hk : Γ ⊢[PRAAx] le (clock p S) (nativeClock k)) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] independentRate (B F) V (data x S)
      (VD (baseNumerator q r) (R+one) (denominator q r)) one (unit p) :=
  endpoint_rate F p (nativeClock k) x S _ (R+one) _ hfS (base_chart_source F K k x y R hf) hk
    (GaussianNamedIncrementChart.base_fraction _ _)

theorem shifted_rate (F K : PR 2) (p k x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hs : Γ ⊢[PRAAx] source K y one)
    (hk : Γ ⊢[PRAAx] le (clock p (R+one)) k) :
    let q := observation F k x
    let r := observation K k y
    Γ ⊢[PRAAx] independentRate (B (addF F K)) V (data (addData x y) (R+one))
      (VD (add (baseNumerator q r) (stepNumerator q r)) (R+one) (denominator q r)) one (unit p) := by
  let W := ap2 (addF F K) k (addData x y)
  have canonical := GaussianNameArithmetic.add_canonical (Γ := Γ) F K x y k
  have read := (GaussianNamedIncrementChart.actual_sum_at (Γ := Γ) F K k x y).eqTrans
    (GaussianExponentialReference.recode_fixed W canonical).eqSymm
  exact endpoint_rate (addF F K) p k (addData x y) (R+one) _ (R+one) _
    (shifted_source F K x y R hf hs) (shifted_chart_source F K k x y R hf hs) hk read

def endpointRates (F K : PR 2) (p k x y R S : PTm n) : Fm PTm n :=
  let q := observation F k x
  let r := observation K k y
  let D := denominator q r
  let z := baseNumerator q r
  let h := stepNumerator q r
  independentRate (B (addF F K)) V (data (addData x y) (R+one)) (VD (add z h) (R+one) D) one (unit p) ⋏
    independentRate (B F) V (data x S) (VD z (R+one) D) one (unit p)

@[simp] theorem subst_endpointRates {m : ℕ} (σ : Fin n → PTm m) (F K : PR 2) (p k x y R S : PTm n) :
    (endpointRates F K p k x y R S).subst σ =
      endpointRates F K (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ R) (Syn.subst σ S) := by
  simp [endpointRates,one]

theorem rates (F K : PR 2) (p k x y R S : PTm n)
    (hf : Γ ⊢[PRAAx] source F x R) (hfS : Γ ⊢[PRAAx] source F x S) (hs : Γ ⊢[PRAAx] source K y one)
    (hk : Γ ⊢[PRAAx] le (clock p (R+one)) k) (hj : Γ ⊢[PRAAx] le (clock p S) (nativeClock k)) :
    Γ ⊢[PRAAx] endpointRates F K p k x y R S :=
  .andI (shifted_rate F K p k x y R hf hs hk) (base_rate F K p k x y R S hf hfS hj)

theorem actual_named_Barnes_increment_endpoint_rates_closed (F K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let p := var 0
       let k := var 1
       let x := var 2
       let y := var 3
       let R := var 4
       let S := var 5
       (source F x R ⋏ (source F x S ⋏ (source K y one ⋏
        (le (clock p (R+one)) k ⋏ le (clock p S) (nativeClock k))))) ⟶ endpointRates F K p k x y R S) :=
  closeUniv 6 (.impI (rates F K _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedIncrementEndpoints

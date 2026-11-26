import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalValueDerivativeContinuity
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalDerivativeDiskIndependence
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalNamedDerivative
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalNamedFrozen

/-!
# The original Barnes derivative at regular Gaussian names

Use the explicit disk modulus of the whole rational derivative.
One unit of extra disk radius allows the rational derivative names
from different certified disks to be identified. The same late
observation of the original input is enough to compare the two
actual named samplers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedValueDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA

open GaussianBarnesCanonicalNamedDemand (source native_source)
open GaussianBarnesCanonicalNamedFrozen (source_widen)
open GaussianBarnesCanonicalLogSchedule (initial_positive)
open GaussianBarnesCanonicalValueDerivativeContinuity (inputClockF input_clock_at uniform_input)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValueDerivative.nameF
local notation "vd" => GaussianBarnesCanonicalValueDerivative.data

def modulus : GaussianBarnesCanonicalNamedDerivative.Modulus where
  inputClockF := inputClockF
  uniform_input := by
    intro _ Δ z w R B C p hz hw h
    have eq := input_clock_at (Γ := Δ) R p
    have u : Δ ⊢[PRAAx] unit (ap2 inputClockF R p) ≐ unit (GaussianBarnesCanonicalValueDerivativeContinuity.inputClock R p) := by
      ipra_congr (unit (var 0) : PTm 1) with [eq]
    exact uniform_input z w R B C p hz hw (distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) u h)

abbrev nameF (f : PR 2) : PR 2 := GaussianBarnesCanonicalNamedDerivative.nameF modulus f
def data (x R : PTm n) : PTm n := GaussianBarnesCanonicalNamedDemand.data x (succ R)
def clock (p R : PTm n) : PTm n := GaussianBarnesCanonicalNamedDerivative.clock modulus p (succ R)
def frozenData (f : PR 2) (k x R : PTm n) : PTm n := GaussianBarnesCanonicalNamedDerivative.frozenData f k x (succ R)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x R : PTm n) :
    Syn.subst σ (data x R) = data (Syn.subst σ x) (Syn.subst σ R) := by simp [data]

theorem regular (f : PR 2) (x R : PTm n) (hf : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x R) :=
  GaussianBarnesCanonicalNamedDerivative.name_regular modulus f x (succ R) (source_widen f x R (succ R) hf (le_succ_self R))

theorem frozen_rate (f : PR 2) (p k x R : PTm n) (hf : Γ ⊢[PRAAx] source f x R)
    (hk : Γ ⊢[PRAAx] le (clock p R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) V (data x R) (frozenData f k x R) one (unit p) :=
  GaussianBarnesCanonicalNamedDerivative.frozen_rate modulus f p k x (succ R)
    (source_widen f x R (succ R) hf (le_succ_self R)) hk

private theorem radius_observations (f : PR 2) (p x R S : PTm n) (hr : Γ ⊢[PRAAx] source f x R)
    (hs : Γ ⊢[PRAAx] source f x S) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R)) (ap2 (nameF f) p (data x S)) (num 4) (unit p) := by
  let k := clock p R+clock p S
  let q := ap2 f k x
  let a := data x R
  let b := data x S
  let A := frozenData f k x R
  let B := frozenData f k x S
  let U := unit p
  have hl := frozen_rate f p k x R hr (le_add_right _ _)
  have hp := frozen_rate f p k x S hs (le_add_left _ _)
  have eq : Γ ⊢[PRAAx] crossEquivalent V V A B :=
    GaussianBarnesCanonicalDerivativeDiskIndependence.independent_radii (rawGaussian q) R S (rawDen q)
      (native_source f k x R hr) (native_source f k x S hs)
  have hu := unit_positive (Γ := Γ) p
  have left := GaussianNamedRateTransport.transport (nameF f) V (nameF f) V a A a B one U hu hl
    (cross_refl _ _ (regular f x R hr)) (cross_symm _ _ _ _ eq)
  have joined := GaussianNamedRateComposition.same_denominator (nameF f) V (nameF f) a B b one U one hu left
    (GaussianNamedRateComposition.symmetric (nameF f) V b B one U hu hp)
  have d := diagonal_rate (nameF f) (nameF f) a b (one+one) U p hu joined
  exact distance_radius_mono _ _ _ _ (num 4) U (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) d

theorem independent_radii (f : PR 2) (x R S : PTm n) (hr : Γ ⊢[PRAAx] source f x R)
    (hs : Γ ⊢[PRAAx] source f x S) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data x R) (data x S) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4) (regular f x R hr) (regular f x S hs)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have r : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift
  have s : Δ ⊢[PRAAx] source f (sh x) (sh S) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_data,PTm.subst_num,Syn.shift,sh,Δ] using
    radius_observations f (var 0) (sh x) (sh R) (sh S) r s

theorem proper (f g : PR 2) (x y R S : PTm n) (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y S)
    (eq : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (nameF g) (data x R) (data y S) := by
  let W := R+S
  have hf' := source_widen f x R W hf (le_add_right _ _)
  have hg' := source_widen g y S W hg (le_add_left _ _)
  have mid := GaussianBarnesCanonicalNamedDerivative.proper modulus f g x y (succ W)
    (source_widen f x W (succ W) hf' (le_succ_self W)) (source_widen g y W (succ W) hg' (le_succ_self W)) eq
  exact cross_trans _ _ _ _ _ _ (independent_radii f x R W hf hf')
    (cross_trans _ _ _ _ _ _ mid (independent_radii g y W S hg' hg))

theorem rational_configuration_rate (F H K : PR 2) (u v x a z h R B : PTm n)
    (hv : Γ ⊢[PRAAx] source H v R)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalValueDerivative.input z h (succ R) B)
    (hn : Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedQuotientBinding.input F H K u v x a z h (succ R) (succ R) B) :
    Γ ⊢[PRAAx] independentRate (GaussianBarnesCanonicalNamedQuotientBinding.nameF F H K) (nameF H)
      (GaussianBarnesCanonicalNamedQuotientBinding.quotientData F H K u v x a (succ R) (succ R)) (data v R)
      (GaussianBarnesCanonicalValueDerivative.numerator (succ R) h)
      (GaussianBarnesCanonicalValueDerivative.denominator (succ R) B) := by
  have disk := hn.andE₂.andE₁.andE₂.andE₁
  have eq := GaussianBarnesCanonicalNamedDerivative.bind modulus H v z (succ R) B
    (source_widen H v R (succ R) hv (le_succ_self R)) disk hn.andE₂.andE₂.andE₂.andE₂.andE₁
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _
    (positive_product _ _ disk.andE₁ (initial_positive (succ R))) (GaussianBarnesCanonicalValueDerivative.rate z h (succ R) B hs)
    (GaussianBarnesCanonicalNamedQuotientBinding.binding F H K u v x a z h (succ R) (succ R) B hn) eq

theorem actual_original_Barnes_named_derivative_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (regular f _ _ Prf.hyp0))

theorem actual_original_Barnes_named_derivative_proper_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ (source g (var 1) (var 3) ⋏ crossEquivalent f g (var 0) (var 1))) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3))) :=
  closeUniv 4 (.impI (proper f g _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_Barnes_named_rational_configuration_derivative_closed (F H K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let u := var 0
       let v := var 1
       let x := var 2
       let a := var 3
       let z := var 4
       let h := var 5
       let R := var 6
       let B := var 7
       (source H v R ⋏ GaussianBarnesCanonicalValueDerivative.input z h (succ R) B) ⟶
         GaussianBarnesCanonicalNamedQuotientBinding.input F H K u v x a z h (succ R) (succ R) B ⟶
           independentRate (GaussianBarnesCanonicalNamedQuotientBinding.nameF F H K) (nameF H)
             (GaussianBarnesCanonicalNamedQuotientBinding.quotientData F H K u v x a (succ R) (succ R)) (data v R)
             (GaussianBarnesCanonicalValueDerivative.numerator (succ R) h)
             (GaussianBarnesCanonicalValueDerivative.denominator (succ R) B)) :=
  closeUniv 8 (.impI (.impI (rational_configuration_rate F H K _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedValueDerivative

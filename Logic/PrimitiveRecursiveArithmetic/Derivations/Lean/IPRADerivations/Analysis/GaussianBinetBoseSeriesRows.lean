import IPRADerivations.Analysis.GaussianBinetBoseSeries
import IPRADerivations.Analysis.GaussianBinetBoseIntegerScale
import IPRADerivations.Analysis.GaussianExponentialInverseSamples

/-!
# Match geometric powers to the original damping rows

At each internal row index, compare the exact power of the frozen
positive exponential inverse with the original exponential of the
matching negative, integer-scaled Pi argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseSeriesRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseExponential (scaleF scaleData scaleBudget exp_input exp_regular expRadius expData expF)
open GaussianBinetBoseSeries (ratio denominatorClock)
open GaussianBinetBoseDenominator (sampleClock)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianExponentialInverseSamples (negative negativeRadius height negative_power)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_trans diagonal_at)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedNaturalScale (radius)
open GaussianRationalDistanceOrder (distance_triangle_same)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (power reciprocal)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "SF" => GaussianNamedNaturalScale.nameF scaleF
local notation "sd" => GaussianNamedNaturalScale.data

theorem signed_stage (E i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le i E) :
    Γ ⊢[PRAAx] crossEquivalent
      (GaussianRadiusExponentialName.nameF (negativeF SF)) expF
      (GaussianRadiusExponentialName.data (radius E (expRadius A)) (negativeData (sd E i (scaleData false A B))))
      (expData true (i*A) B) := by
  let x := sd E i (scaleData false A B)
  let y := scaleData false (i*A) B
  let R := radius E (expRadius A)
  have ha := exp_input false A B hB
  have hs := GaussianNamedNaturalScale.exponential_input scaleF E i (expRadius A) (scaleData false A B) ha hi
  have hd := exp_input false (i*A) B hB
  have eq := GaussianBinetBoseIntegerScale.scale_equivalent false E i A B hB hi
  have neg := GaussianNameRingLaws.negative_equivalent SF scaleF x y hs.andE₁ hd.andE₁
    (cross_to_diagonal _ _ _ _ eq)
  have cap : Γ ⊢[PRAAx] le (two*(i*A)) (scaleBudget (i*A)*B) :=
    le_trans (le_add_right (two*(i*A)) one)
      (le_congr (one_mul _) (mul_comm B _) (mul_le_mul_right (scaleBudget (i*A)) hB))
  have actual := GaussianPiRationalScale.negation false (two*(i*A)) B (scaleBudget (i*A)) zero hB cap
  exact GaussianExponentialRadiusIndependence.independent_radii_proper (negativeF SF) scaleF R (expRadius (i*A))
    (negativeData x) (scaleData true (i*A) B)
    (GaussianExponentialInverse.negative_input SF R x hs) (exp_input true (i*A) B hB)
    (cross_trans _ _ _ _ _ _ neg actual)

def rowClock (p B : PTm n) : PTm n := sampleClock (denominatorClock p B)

def rowCost (E i A B : PTm n) : PTm n :=
  two+negativeRadius scaleF E i (expRadius A) (scaleData false A B)+i*(B*B*two)

private theorem inverse_unit_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (reciprocal (ap2 expF p (expData false A B))) one one := by
  have hb := le_trans hB (le_add_right B (num 4*A))
  exact bounded_radius_mono _ _ _ _ _ hb (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (le_add_right B (num 4*A)))
    (GaussianBinetBoseGeometricRatio.inverse_bound p A B hB)

theorem inverse_clock_error (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded
      (negative scaleF (rowClock p B) (expRadius A) (scaleData false A B))
      (ratio p A B) (B*B*two) (unit (rowClock p B)) := by
  let r := rowClock p B
  let x := scaleData false A B
  let R := expRadius A
  let s := r+GaussianNameReciprocal.anchor (height scaleF R x)
  let gx := ap2 expF s (expData false A B)
  let gy := ap2 expF r (expData false A B)
  have reg := exp_regular false A B hB
  have ht := le_trans hB (le_add_right B (num 4*A))
  have lb (k : PTm n) : Γ ⊢[PRAAx] GaussianNameReciprocal.lower (ap2 expF k (expData false A B)) B :=
    GaussianRationalLowerBounds.name_lower _ _ _ ht hB (GaussianBinetBoseGeometricRatio.positive_lower k A B hB)
  have move := GaussianNamedProductObservationBound.late_observation expF (expData false A B) r s reg (le_add_right _ _)
  exact GaussianNameReciprocal.inverse_distance_two gx gy B B two (unit r) hB hB (unit_positive r) (lb s) (lb r) move

theorem row_error (p E i A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] le i E) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 expF (rowClock p B) (expData true (i*A) B))
      (power (ratio p A B) i) (rowCost E i A B) (unit (rowClock p B)) := by
  let r := rowClock p B
  let x := scaleData false A B
  let R := expRadius A
  let s := r+GaussianNameReciprocal.anchor (height scaleF R x)
  let y := negative scaleF r R x
  let z := ratio p A B
  have cross := signed_stage E i A B hB hi
  have left := diagonal_at _ _ _ _ r (cross_to_diagonal _ _ _ _ cross)
  have middle := negative_power scaleF r E i R x (exp_input false A B hB) hi hE
  have tail := GaussianRationalPowerDifference.unit_disk_power_difference y z (B*B*two) (unit r) i
    (unit_positive r) (inverse_unit_bound s A B hB) (inverse_unit_bound r A B hB) (inverse_clock_error p A B hB)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive r)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive r)
      (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ (unit_positive r) left) middle) tail

theorem actual_Bose_geometric_row_from_original_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ (le (var 2) (var 1) ⋏ le one (var 1))) ⟶
      distanceBounded (ap2 expF (rowClock (var 0) (var 4)) (expData true (var 2*var 3) (var 4)))
        (power (ratio (var 0) (var 3) (var 4)) (var 2)) (rowCost (var 1) (var 2) (var 3) (var 4))
        (unit (rowClock (var 0) (var 4)))) :=
  closeUniv 5 (.impI (row_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseSeriesRows

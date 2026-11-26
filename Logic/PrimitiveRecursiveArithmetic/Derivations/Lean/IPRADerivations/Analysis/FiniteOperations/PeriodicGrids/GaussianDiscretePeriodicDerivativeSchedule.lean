import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.GaussianDiscretePeriodicThirdDerivative
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut

/-!
# Noncircular precision selection for actual nested fine-grid rates

Choose the analytic error denominator from the coarse mesh and target
precision. After the fine refinement is known, multiply by 2D+1 to
choose the signed lattice denominator. This absorbs all lattice
rounding costs without tightening the earlier derivative tolerances.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicDerivativeSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDiscretePeriodicGridReadback (factor sample)
open GaussianDiscretePeriodicThirdDerivative (certified rowBudget projected_distance)
open GaussianDiscreteDerivativeRounding (latticeScale)
open SignedDiscreteDerivativeOperators (width divisor)
open GaussianSignedObservationReadback (realProjection)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def padding (D : PTm n) : PTm n := two*D+one

def gain (N : PTm n) : PTm n := num 14+num 16*N+num 32*(N*N)+num 96*factor N

def clock (N p : PTm n) : PTm n := GaussianFastValueCut.exponent (gain N) p

def denominator (x N p : PTm n) : PTm n := unit (clock N p)*padding (divisor x)

theorem padding_positive (D : PTm n) : Γ ⊢[PRAAx] le one (padding D) := le_add_left _ _

theorem denominator_positive (x N p : PTm n) : Γ ⊢[PRAAx] le one (denominator x N p) :=
  positive_product _ _ (unit_positive _) (padding_positive _)

theorem same_radius (q r x N p : PTm n) (hS : Γ ⊢[PRAAx] latticeScale x ≐ denominator x N p)
    (h : Γ ⊢[PRAAx] distanceBounded q r one (unit (clock N p))) :
    Γ ⊢[PRAAx] distanceBounded q r (padding (divisor x)) (latticeScale x) := by
  have hs : Γ ⊢[PRAAx] le one (latticeScale x) :=
    le_congr (.eqRefl _) hS.eqSymm (denominator_positive _ _ _)
  apply distance_radius_mono _ _ _ _ _ _ (unit_positive _) hs _ h
  have eq : Γ ⊢[PRAAx] one*latticeScale x ≐ padding (divisor x)*unit (clock N p) :=
    (congrMul (.eqRefl _) hS).eqTrans (by unfold denominator; ipra_ring)
  exact le_congr eq.eqSymm (.eqRefl _) (le_refl _)

theorem numerator_bound (x N : PTm n) :
    let R := padding (divisor x)
    Γ ⊢[PRAAx] le (num 4*rowBudget x N R R R R R+two) (gain N*R) := by
  let R := padding (divisor x)
  let common := (num 12+num 16*N+num 32*(N*N)+num 32*factor N)*R
  let extra := two+num 64*factor N
  have pair := add_le_add_right common (mul_le_mul_right extra (padding_positive (Γ := Γ) (divisor x)))
  refine le_congr ?_ ?_ pair
  · unfold common extra R rowBudget GaussianDiscreteThirdDerivativeEstimate.comparisonBudget
      SignedDiscreteThirdDerivativeNormalization.budget GaussianDiscreteDerivativeRounding.allowance padding
    ipra_ring
  · unfold common extra gain
    ipra_ring

theorem precision_budget (x N p : PTm n) :
    let R := padding (divisor x)
    Γ ⊢[PRAAx] le ((num 4*rowBudget x N R R R R R+two)*unit p) (denominator x N p) := by
  let R := padding (divisor x)
  have g : Γ ⊢[PRAAx] le (gain N*unit p) (unit (clock N p)) := GaussianFastValueCut.query_budget _ _
  have pay : Γ ⊢[PRAAx] le ((gain N*R)*unit p) (denominator x N p) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right R g)
  exact le_trans (mul_le_mul_right (unit p) (numerator_bound x N)) pay

theorem dyadic_distance (f g h j : PTm 2) (x N i p : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ denominator x N p)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hc : let R := padding (divisor x); Γ ⊢[PRAAx] certified f g h j x N R R R R R) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (sample f x (rem i N)))
      (realProjection (sample f x (rem zero N))) one (unit p) := by
  let R := padding (divisor x)
  have hScale : Γ ⊢[PRAAx] le one (latticeScale x) :=
    le_congr (.eqRefl _) hS.eqSymm (denominator_positive _ _ _)
  have guard : Γ ⊢[PRAAx] le ((num 4*rowBudget x N R R R R R+two)*unit p) (one*latticeScale x) :=
    le_congr (.eqRefl _) (hS.eqSymm.eqTrans (one_mul _).eqSymm) (precision_budget x N p)
  exact distance_radius_mono _ _ _ _ _ _ hScale (unit_positive p) guard
    (projected_distance f g h j x N i R R R R R hM hScale hD hN hi hc)

theorem actual_Gaussian_periodic_refinement_clock_closed (f g h j : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let i := var 2
       let p := var 3
       let R := padding (divisor x)
       le one (width x) ⟶ divisor x ≐ N*width x ⟶ latticeScale x ≐ denominator x N p ⟶
       le one N ⟶ le i N ⟶ certified f g h j x N R R R R R ⟶
         distanceBounded (realProjection (sample f x (rem i N)))
           (realProjection (sample f x (rem zero N))) one (unit p)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (dyadic_distance f g h j _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicDerivativeSchedule

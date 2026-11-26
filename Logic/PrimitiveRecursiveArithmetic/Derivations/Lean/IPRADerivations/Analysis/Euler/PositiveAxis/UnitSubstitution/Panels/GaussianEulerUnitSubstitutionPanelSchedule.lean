import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.Lattices.GaussianEulerUnitSubstitutionLatticeSchedule
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.Densities.GaussianEulerUnitSubstitutionRetimedDensity

/-!
# Computed ordinary unit panels on a fixed original time interval

The original density count is fixed first using its original numerical
program. The decay query is late enough for both that program's error
budget and the floor-cut geometry. The lattice denominator also pays
the original compact unit-kernel modulus. All of these budgets follow
from the original positive-width time-interval source.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionPanelSchedule

open_ipra
open GaussianEulerUnitSubstitutionCompactName (source rowQuery)
open GaussianEulerUnitSubstitutionLatticeGeometry (disk)
open GaussianEulerUnitSubstitutionLatticeRate (meshCoefficient latticeCoefficient queryCoefficient)
open GaussianEulerUnitSubstitutionLatticeSchedule (minimumCount minimumChart minimumLattice)
open GaussianEulerUnitDecayInput (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def densityIndex (s R C E T : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (meshCoefficient R C E T) s
def densityCount (s R C E T : PTm n) : PTm n := GaussianEulerUnitSubstitutionCompactName.count (densityIndex s R C E T) R C E T
def chartIndex (s R C E T : PTm n) : PTm n :=
  minimumChart s (densityCount s R C E T) R E T+rowQuery (densityIndex s R C E T) R C E T
def latticeDenominator (s R C E T : PTm n) : PTm n := minimumLattice s (densityCount s R C E T) R E T
def left (s R a C E T : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionLatticeGeometry.start (chartIndex s R C E T) (densityCount s R C E T) a C E T (latticeDenominator s R C E T)
def width (s R a C E T : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionLatticeGeometry.count (chartIndex s R C E T) (densityCount s R C E T) a C E T (latticeDenominator s R C E T)
def panelData (s z R B a C E T : PTm n) : PTm n :=
  GaussianEulerUnitKernelCompactName.data z R B (left s R a C E T) (width s R a C E T) (latticeDenominator s R C E T) (disk E T)
def lattice (s z R B a C E T : PTm n) : PTm n :=
  GaussianEulerUnitKernelLatticeSum.lattice s (width s R a C E T) z B (left s R a C E T) (latticeDenominator s R C E T)
def density (s z R B a C E T : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionDensity.density (clock (chartIndex s R C E T) E T) (densityCount s R C E T) z B a C E

ipra_subst densityIndex
ipra_subst densityCount
ipra_subst chartIndex [minimumChart]
ipra_subst latticeDenominator [minimumLattice]
ipra_subst left
ipra_subst width
ipra_subst panelData

theorem density_index_later (s R C E T : PTm n) : Γ ⊢[PRAAx] le s (densityIndex s R C E T) :=
  le_add_right _ _
theorem chart_later (s R C E T : PTm n) : Γ ⊢[PRAAx] le s (chartIndex s R C E T) :=
  le_trans (le_add_right _ _) (le_add_right _ _)
theorem decay_query_later (s R C E T : PTm n) : Γ ⊢[PRAAx]
    le (rowQuery (densityIndex s R C E T) R C E T) (clock (chartIndex s R C E T) E T) :=
  le_trans (le_add_left _ _) (GaussianEulerUnitDecayInput.clock_later _ _ _)

theorem floor_budget (s R C E T : PTm n) : Γ ⊢[PRAAx] le (unit s) (latticeDenominator s R C E T) := by
  let K := latticeCoefficient (densityCount s R C E T) R E T
  have factor : Γ ⊢[PRAAx] le one (K+disk E T) :=
    le_trans (GaussianEulerUnitSubstitutionLatticeGeometry.disk_positive E T) (le_add_left _ _)
  exact le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit s) factor)

theorem tilt_budget (s R C E T : PTm n) : Γ ⊢[PRAAx]
    le (two*densityCount s R C E T*unit s) (unit (clock (chartIndex s R C E T) E T)) := by
  let N := densityCount s R C E T
  let K := chartIndex s R C E T
  have hK : Γ ⊢[PRAAx] le (minimumChart s N R E T) K := le_add_right _ _
  have hclock : Γ ⊢[PRAAx] le (unit K) (unit (clock K E T)) :=
    GaussianExponentialReference.unit_monotone (GaussianEulerUnitDecayInput.clock_later K E T)
  have hslack : Γ ⊢[PRAAx] le (two*N*unit s) ((queryCoefficient N R E T+num 4*N)*unit s) :=
    le_of_eq_add (d := (queryCoefficient N R E T+two*N)*unit s) (by ipra_ring)
  exact le_trans hslack (le_trans (GaussianEulerUnitSubstitutionLatticeSchedule.chart_budget s K N R E T hK) hclock)

theorem lattice_budget (s R C E T : PTm n) : Γ ⊢[PRAAx]
    le (GaussianEulerUnitKernelCompactName.lipschitz R (disk E T)*unit s) (latticeDenominator s R C E T) := by
  unfold latticeDenominator minimumLattice latticeCoefficient
  exact le_of_eq_add (d := (two*densityCount s R C E T*GaussianEulerCompactPowerMajorant.majorant R E T+disk E T)*unit s)
    (by unfold GaussianEulerUnitKernelCompactName.lipschitz; ipra_ring)

theorem schedule_source (s z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionLatticeSchedule.source s (chartIndex s R C E T) s (densityCount s R C E T)
      z R B a C E T (latticeDenominator s R C E T) := by
  let t := densityIndex s R C E T
  exact .andI (GaussianEulerUnitSubstitutionCompactName.finite_source t z R B a C E T h)
    (.andI (le_trans (GaussianFastValueCut.query_budget (meshCoefficient R C E T) s) (GaussianEulerUnitSubstitutionRetimedDensity.old_count_unit_lower t R C E T))
      (.andI (le_add_right _ _) (.andI (le_refl _) (le_refl _))))

theorem geometry_source (s z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionLatticeGeometry.source (chartIndex s R C E T) (densityCount s R C E T)
      z R B a C E T (latticeDenominator s R C E T) :=
  GaussianEulerUnitSubstitutionLatticeSchedule.original_source s _ s _ z R B a C E T _ (schedule_source s z R B a C E T h)

theorem panel_source (s z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    GaussianEulerUnitKernelCompactName.source z R B (left s R a C E T) (width s R a C E T) (latticeDenominator s R C E T) (disk E T) :=
  GaussianEulerUnitSubstitutionLatticeGeometry.compact_interval_source _ _ z R B a C E T _ (geometry_source s z R B a C E T h)

theorem original_lattice_density (s z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (lattice s z R B a C E T) (density s z R B a C E T) (num 4) (unit s) :=
  GaussianEulerUnitSubstitutionLatticeSchedule.original_scheduled_bound s _ s _ z R B a C E T _ (schedule_source s z R B a C E T h)

theorem actual_computed_original_unit_panel_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (lattice (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (density (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (num 4) (unit (var 0))) :=
  closeUniv 8 (.impI (original_lattice_density _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionPanelSchedule

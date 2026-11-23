import IPRADerivations.Analysis.GaussianEulerUnitSubstitutionPanelSchedule
import IPRADerivations.Analysis.GaussianEulerUnitKernelNamedLatticeBound

/-!
# Ordinary unit-panel quadrature compared to the original compact Euler name

The observation is an original compact unit-kernel query on the
computed rational panel. Its lattice error, signed-density error,
and original compact Euler comparison share explicit dyadic budgets.
The independent requested Euler observation is retained.
-/

set_option autoImplicit false
namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionPanelComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionCompactName (source)
open GaussianEulerUnitSubstitutionPanelSchedule
  (densityIndex densityCount chartIndex latticeDenominator panelData left width)
open GaussianEulerUnitSubstitutionLatticeGeometry (disk)
open GaussianEulerUnitDecayInput (clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def sample (s z R B a C E T : PTm n) : PTm n :=
  ap2 GaussianEulerUnitKernelCompactName.nameF s (panelData s z R B a C E T)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (s z R B a C E T : PTm n) :
    Syn.subst σ (sample s z R B a C E T) = sample (Syn.subst σ s) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [sample]

theorem original_density_observation (s z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (sample s z R B a C E T) (GaussianEulerUnitSubstitutionPanelSchedule.density s z R B a C E T)
      (num 12) (unit s) := by
  have panel := GaussianEulerUnitKernelNamedLatticeBound.original_dyadic_bound s s z R B (left s R a C E T)
    (width s R a C E T) (latticeDenominator s R C E T) (disk E T)
    (GaussianEulerUnitSubstitutionPanelSchedule.panel_source s z R B a C E T h)
    (GaussianEulerUnitSubstitutionPanelSchedule.lattice_budget s R C E T) (le_refl s)
  have density := GaussianEulerUnitSubstitutionPanelSchedule.original_lattice_density s z R B a C E T h
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive s) panel density)

theorem original_observations (s q z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (sample s z R B a C E T)
      (ap2 GaussianEulerCompactAdditivity.nameF q (GaussianEulerCompactAdditivity.data z R B a C E T))
      (num 13*unit q+unit s) (unit s*unit q) := by
  let t := densityIndex s R C E T
  let r := clock (chartIndex s R C E T) E T
  have hS := unit_positive (Γ := Γ) s
  have hQ := unit_positive (Γ := Γ) q
  have hD := positive_product _ _ hS hQ
  have part := original_density_observation s z R B a C E T h
  have d := distance_radius_mono _ _ _ _ (num 12*unit q) (unit s*unit q) hS hD
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) part
  have grow : Γ ⊢[PRAAx] le (unit s) (unit t) :=
    GaussianExponentialReference.unit_monotone (GaussianEulerUnitSubstitutionPanelSchedule.density_index_later s R C E T)
  have old := GaussianEulerUnitSubstitutionRetimedDensity.original_observations t r q z R B a C E T h
    (GaussianEulerUnitSubstitutionPanelSchedule.decay_query_later s R C E T)
  have e := distance_radius_mono _ _ _ _ (unit s+unit q) (unit s*unit q)
    (positive_product _ _ (unit_positive t) hQ) hD
    (by ipra_le (𝔞(unit q)^2)*sl grow) old
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD d e)

theorem actual_ordinary_unit_panel_and_original_Euler_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (sample (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (ap2 GaussianEulerCompactAdditivity.nameF (var 1)
          (GaussianEulerCompactAdditivity.data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (num 13*unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (original_observations _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionPanelComparison

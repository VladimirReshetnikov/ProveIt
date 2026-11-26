import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionOrdinaryContainment
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitKernelNativePanel
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitKernelNestedPanels
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionCofinalPanelRate

/-!
# Nesting an arbitrary rational panel between ordinary Gamma panels

The inner reference panel is computed from the requested error index.
A proper rational panel containing the corresponding endpoint
neighborhoods encloses that reference panel. For every auxiliary index
there is a later ordinary panel enclosing the given rational panel.
The two containment conclusions are ready for exact denominator
rescaling and nested compact quadrature splitting.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionArbitraryPanels

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionOrdinaryImproper (source resolution)
open GaussianEulerUnitSubstitutionOrdinaryEndpoints
  (leftNumerator widthNumerator denominator canonical_endpoints)
open GaussianEulerUnitSubstitutionOrdinaryContainment
  (contains_of_radii containmentIndex containment_index_budget original_panel_contains)
open GaussianEulerUnitKernelNativePanel (proper)
open GaussianEulerUnitSubstitutionCofinalPanelRate (panel_source)
open GaussianEulerUnitSubstitutionLatticeGeometry (disk)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianEulerUnitSubstitutionCompactName (stage)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qone)
open RationalValueBounds (radius)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def innerIndex (s : PTm n) : PTm n := stage s
def innerStart (s A R : PTm n) : PTm n :=
  leftNumerator (innerIndex s) (resolution (innerIndex s)) A R
def innerWidth (s A R : PTm n) : PTm n :=
  widthNumerator (innerIndex s) (resolution (innerIndex s)) A R
def innerDen (s A R : PTm n) : PTm n :=
  denominator (innerIndex s) (resolution (innerIndex s)) A R
def boundarySource (s A R a C E : PTm n) : Fm PTm n :=
  proper a C E ⋏
    (radius (fraction a E) (fstT qzero) one (innerDen s A R) ⋏
      radius (fraction (a+C) E) (fstT qone) one (innerDen s A R))

theorem reference_is_inside (s z R B A a C E : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hP : Γ ⊢[PRAAx] boundarySource s A R a C E) : Γ ⊢[PRAAx]
    RationalNestedPanelGeometry.source a C E (innerStart s A R) (innerWidth s A R) (innerDen s A R) := by
  have endpoints := canonical_endpoints (innerIndex s) z R B A h
  exact contains_of_radii a (a+C) E (innerStart s A R) (innerWidth s A R) (innerDen s A R) (innerDen s A R)
    hP.andE₁.andE₂ hP.andE₂.andE₁ hP.andE₂.andE₂ endpoints.andE₁.andE₁ endpoints.andE₁.andE₂ (le_refl _)

theorem external_panel_is_inside_later (u z R B A a C E : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hP : Γ ⊢[PRAAx] proper a C E) : Γ ⊢[PRAAx]
    RationalNestedPanelGeometry.source
      (leftNumerator (containmentIndex u E) (resolution (containmentIndex u E)) A R)
      (widthNumerator (containmentIndex u E) (resolution (containmentIndex u E)) A R)
      (denominator (containmentIndex u E) (resolution (containmentIndex u E)) A R) a C E :=
  original_panel_contains (containmentIndex u E) (resolution (containmentIndex u E)) z R B A a C E h
    (le_refl _) hP.andE₁ hP.andE₂ (containment_index_budget u E)

def panelMargin (t A R : PTm n) : PTm n := disk (etaDen (resolution t) A R) (top (resolution t) A R)

def exhaustionSource (s z R B A a C E G : PTm n) : Fm PTm n :=
  source z R B A ⋏ (GaussianEulerUnitKernelCompactName.source z R B a C E G ⋏ boundarySource s A R a C E)

theorem surrounding_sources (s u z R B A a C E G : PTm n)
    (h : Γ ⊢[PRAAx] exhaustionSource s z R B A a C E G) : Γ ⊢[PRAAx]
    GaussianEulerUnitKernelNestedPanels.source z R B a C E G (innerStart s A R) (innerWidth s A R) (innerDen s A R)
        (panelMargin (innerIndex s) A R) ⋏
      GaussianEulerUnitKernelNestedPanels.source z R B
        (leftNumerator (containmentIndex u E) (resolution (containmentIndex u E)) A R)
        (widthNumerator (containmentIndex u E) (resolution (containmentIndex u E)) A R)
        (denominator (containmentIndex u E) (resolution (containmentIndex u E)) A R)
        (panelMargin (containmentIndex u E) A R) a C E G := by
  exact .andI (.andI h.andE₂.andE₁ (.andI (panel_source (innerIndex s) z R B A h.andE₁)
    (reference_is_inside s z R B A a C E h.andE₁ h.andE₂.andE₂)))
    (.andI (panel_source (containmentIndex u E) z R B A h.andE₁) (.andI h.andE₂.andE₁
      (external_panel_is_inside_later u z R B A a C E h.andE₁ h.andE₂.andE₂.andE₁)))

theorem actual_Gamma_reference_inside_arbitrary_boundary_panel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) ⋏ boundarySource (var 0) (var 4) (var 2) (var 5) (var 6) (var 7)) ⟶
      RationalNestedPanelGeometry.source (var 5) (var 6) (var 7)
        (innerStart (var 0) (var 4) (var 2)) (innerWidth (var 0) (var 4) (var 2)) (innerDen (var 0) (var 4) (var 2))) :=
  closeUniv 8 (.impI (reference_is_inside _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionArbitraryPanels

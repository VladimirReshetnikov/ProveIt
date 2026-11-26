import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedExtremum
import IPRADerivations.Analysis.Names.GaussianNamedApartnessTightness

/-!
# Uniqueness of the selected extremal offset for the original Gamma name

Equal Gamma values exclude every finite certificate of offset separation.
Tightness gives equality of the regular offsets on the same interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedExtremumUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerRationalLogOrder (order_refl)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF fraction_location_regular)
open GaussianGammaNegativeIntervalNamedApartness (apart)
open GaussianGammaNegativeIntervalNamedExtremum (strict_extremum)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData actual_regular signedData)
open GaussianGammaNegativeIntervalNamedInput (root_source)
open GaussianGammaNegativeIntervalNamedInputRetiming (orderedWindow retimed_source)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedApartnessTightness (noApart names_equivalent_of_no_difference_apart)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedPositiveLateLogSource (retimedF retimedData original_cross)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "R" => fractionLocationF
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def attains (f : PR 2) (x E N : PTm n) : Fm PTm n :=
  crossEquivalent (actualF R) (actualF f) (actualData R N (mesh N) N) (actualData f x E N)

@[simp] theorem subst_attains {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E N : PTm n) :
    (attains f x E N).subst σ = attains f (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [attains, actualData, signedData, GaussianGammaFiniteApproximantName.exponentialInputData]

theorem attaining_excludes_apart (f : PR 2) (x E N h : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (eq : Γ ⊢[PRAAx] attains f x E N) : Γ ⊢[PRAAx] neg (apart f h N x) := by
  let u := actualData R N (mesh N) N
  let v := actualData f x E N
  let F := actualF R
  let G := actualF f
  have hu := actual_regular (Γ := Γ) R N (mesh N) N (root_source N)
  have hv := actual_regular f x E N hs
  have forward : Γ ⊢[PRAAx] realOrder F G u v :=
    GaussianNamedRealOrderTransport.transport F G G G u v v v eq (cross_refl _ _ hv) (order_refl _ _ hv)
  have reverse : Γ ⊢[PRAAx] realOrder G F v u :=
    GaussianNamedRealOrderTransport.transport G F F F v u u u (cross_symm _ _ _ _ eq) (cross_refl _ _ hu) (order_refl _ _ hu)
  refine .impI ?_
  have strict := strict_extremum f x E N h hs.wk Prf.hyp0
  exact .orE (par_cases N)
    ((strict.andE₂.wk.impE Prf.hyp0).andE₂.impE forward.wk.wk)
    ((strict.andE₁.wk.impE Prf.hyp0).andE₂.impE reverse.wk.wk)

theorem attaining_equivalent (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (eq : Γ ⊢[PRAAx] attains f x E N) : Γ ⊢[PRAAx] crossEquivalent R f N x := by
  apply names_equivalent_of_no_difference_apart R f N x (fraction_location_regular N) hs.andE₁
  have hsrc : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) := by
    simpa [Fm.shift, Syn.shift] using hs.shift
  have heq : Γ.map Fm.shift ⊢[PRAAx] attains f (Syn.shift x) (Syn.shift E) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using eq.shift
  refine .allI ?_
  simpa [noApart, apart, Syn.shift] using
    attaining_excludes_apart f (Syn.shift x) (Syn.shift E) (Syn.shift N) (var 0) hsrc heq

theorem ordered_attaining_equivalent (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E)
    (eq : Γ ⊢[PRAAx] attains (retimedF f) (retimedData x E) (two*E) N) : Γ ⊢[PRAAx] crossEquivalent R f N x :=
  cross_trans _ _ _ _ _ _ (attaining_equivalent _ _ _ _ (retimed_source f x E hs) eq)
    (cross_symm _ _ _ _ (original_cross f x E hs.andE₁))

theorem actual_named_negative_Gamma_extremum_attainment_unique_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((source f (var 0) (var 1) ⋏ attains f (var 0) (var 1) (var 2)) ⟶ crossEquivalent R f (var 2) (var 0)) :=
  closeUniv 3 (.impI (attaining_equivalent f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_named_negative_Gamma_ordered_extremum_attainment_unique_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((orderedWindow f (var 0) (var 1) ⋏ attains (retimedF f) (retimedData (var 0) (var 1)) (two*var 1) (var 2)) ⟶
        crossEquivalent R f (var 2) (var 0)) :=
  closeUniv 3 (.impI (ordered_attaining_equivalent f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedExtremumUniqueness

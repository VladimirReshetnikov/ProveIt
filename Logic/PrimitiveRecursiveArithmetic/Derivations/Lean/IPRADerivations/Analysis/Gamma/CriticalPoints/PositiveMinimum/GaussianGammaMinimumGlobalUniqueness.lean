import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaMinimumGlobal
import IPRADerivations.Analysis.Names.Apartness.GaussianNamedApartnessTightness
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogOrder

/-!
# Uniqueness of the positive global Gamma minimum

Equality of the original Gamma values excludes every finite apartness
certificate by the strict minimum theorem. Tightness identifies the
regular input with the selected dyadic location.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaDyadicLocation (locationF location_regular)
open GaussianGammaDigammaLocationInput (named_source)
open GaussianGammaEulerRationalLogOrder (order_refl)
open GaussianGammaMinimumGlobal (strict_global_minimum)
open GaussianGammaMinimumGlobalApartness (apart)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedApartnessTightness (noApart names_equivalent_of_no_difference_apart)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data

def attains (f : PR 2) (x y A : PTm n) : Fm PTm n :=
  crossEquivalent (G locationF) (G f) (gd x one) (gd y A)

@[simp] theorem subst_attains {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x y A : PTm n) :
    (attains f x y A).subst σ = attains f (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) := by
  simp [attains,one]

theorem attaining_excludes_apart (f : PR 2) (h x y A : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (he : Γ ⊢[PRAAx] attains f x y A) :
    Γ ⊢[PRAAx] neg (apart f h x y) := by
  let u := gd x one
  let v := gd y A
  let F := G locationF
  let H := G f
  have hu := GaussianNamedGamma.name_regular locationF x one (named_source (Γ := Γ) x)
  have reverse : Γ ⊢[PRAAx] realOrder H F v u :=
    GaussianNamedRealOrderTransport.transport H F F F v u u u
      (cross_symm F H u v he) (cross_refl F u hu) (order_refl F u hu)
  refine .impI ?_
  exact (strict_global_minimum f h x y A hs.wk Prf.hyp0).andE₂.impE reverse.wk

theorem attaining_equivalent (f : PR 2) (x y A : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (he : Γ ⊢[PRAAx] attains f x y A) :
    Γ ⊢[PRAAx] crossEquivalent locationF f x y := by
  apply names_equivalent_of_no_difference_apart locationF f x y (location_regular x) hs.andE₁.andE₁
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have hsource : Δ ⊢[PRAAx] source f (sh y) (sh A) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianNamedGammaPositiveLower.subst_source] using hs.shift
  have heq : Δ ⊢[PRAAx] attains f (sh x) (sh y) (sh A) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_attains] using he.shift
  refine .allI ?_
  simpa only [noApart,apart,GaussianNamedDifference.subst_data,Syn.shift,sh] using
    attaining_excludes_apart f (var 0) (sh x) (sh y) (sh A) hsource heq

theorem actual_original_named_Gamma_positive_minimum_attainment_unique_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((source f (var 1) (var 2) ⋏ attains f (var 0) (var 1) (var 2)) ⟶
        crossEquivalent locationF f (var 0) (var 1)) :=
  closeUniv 3 (.impI (attaining_equivalent f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalUniqueness

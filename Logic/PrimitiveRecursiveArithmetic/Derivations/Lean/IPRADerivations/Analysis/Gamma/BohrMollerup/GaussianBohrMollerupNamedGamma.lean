import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupNamedLift
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerNamedExponential

/-!
# Named Gamma from the cofinal Bohr–Mollerup lift

On every certified positive regular real input, the lifted log presentation
agrees with the original positive real logarithm. Exponentiating that same
lift recovers the original named Gamma evaluator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupNamedFrozen (source native_source)
open GaussianBohrMollerupNamedLift (nameF data equivalent name_regular)
open GaussianBohrMollerupPresentation (Presentation laws)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedRadiusExponentialFreeze (radius original_input)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nativeF" => GaussianLogGammaEulerNamed.nameF
local notation "expF" => GaussianRadiusExponentialName.nameF
local notation "expData" => GaussianRadiusExponentialName.data
local notation "expNativeF" => GaussianLogGammaEulerNamedExponential.nameF
local notation "expNativeData" => GaussianLogGammaEulerNamedExponential.data
local notation "positiveLogF" => GaussianGammaMinimumFreeze.nameF
local notation "positiveLogData" => GaussianGammaMinimumFreeze.data
local notation "gammaF" => GaussianNamedGamma.nameF
local notation "gammaData" => GaussianNamedGamma.data

def exponentialF (P : Presentation) (f : PR 2) : PR 2 := expF (nameF P f)

def exponentialData (P : Presentation) (f : PR 2) (x A R : PTm n) : PTm n :=
  expData (radius (nameF P f) (data x A R)) (data x A R)

@[simp] theorem subst_exponentialData {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (f : PR 2)
    (x A R : PTm n) : Syn.subst σ (exponentialData P f x A R) =
      exponentialData P f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [exponentialData]

theorem positive_log_equivalent (P : Presentation) (f : PR 2) (x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF P f) (positiveLogF f) (data x A R) (positiveLogData x A) :=
  cross_trans (nameF P f) (nativeF f) (positiveLogF f) (data x A R) (data x A R) (positiveLogData x A)
    (equivalent P f x A R hp hs)
    (GaussianLogGammaEulerNamedPositiveAxis.equivalent_at_radius f x A R hs.andE₁ hs.andE₂)

theorem gamma_equivalent (P : Presentation) (f : PR 2) (x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] crossEquivalent (exponentialF P f) (gammaF f) (exponentialData P f x A R) (gammaData x A) := by
  let X := data x A R
  have hn := native_source f x A R hs
  have hexp : Γ ⊢[PRAAx] crossEquivalent (exponentialF P f) (expNativeF f)
      (exponentialData P f x A R) (expNativeData f x A R) :=
    GaussianExponentialRadiusIndependence.independent_radii_proper (nameF P f) (nativeF f)
      (radius (nameF P f) X) (radius (nativeF f) X) X X
      (original_input (nameF P f) X (name_regular P f x A R hp hs))
      (original_input (nativeF f) X (GaussianLogGammaEulerNamed.name_regular f x A R hn))
      (equivalent P f x A R hp hs)
  exact cross_trans (exponentialF P f) (expNativeF f) (gammaF f)
    (exponentialData P f x A R) (expNativeData f x A R) (gammaData x A)
    hexp (GaussianLogGammaEulerNamedExponential.gamma_equivalent f x A R hn)

theorem actual_named_positive_Bohr_Mollerup_log_Gamma_closed (P : Presentation) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (laws P ⟶ source f (var 0) (var 1) (var 2) ⟶
        crossEquivalent (nameF P f) (positiveLogF f) (data (var 0) (var 1) (var 2))
          (positiveLogData (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (positive_log_equivalent P f _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_Bohr_Mollerup_Gamma_closed (P : Presentation) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (laws P ⟶ source f (var 0) (var 1) (var 2) ⟶
        crossEquivalent (exponentialF P f) (gammaF f) (exponentialData P f (var 0) (var 1) (var 2))
          (gammaData (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (gamma_equivalent P f _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedGamma

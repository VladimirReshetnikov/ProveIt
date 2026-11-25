import IPRADerivations.Analysis.GaussianGammaNamedHalfPlanePoleFree
import IPRADerivations.Analysis.GaussianNamedGammaEulerFirstDerivative

/-!
# The half-plane derivative rate for the original pole-free Gamma quotient

Both endpoints use their own pole-free certificates. The quotient uses
the same regular named increment and the same certified reciprocal as
the original half-plane quotient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedHalfPlanePoleFreeQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "incrementF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "incrementData" => GaussianNamedGammaSmallIncrementInput.sumData
local notation "H" => GaussianNamedGamma.nameF
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "hd" => GaussianNamedGamma.data
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "poleSource" => GaussianGammaNamedPoleFree.source
local notation "halfSource" => GaussianNamedGammaEulerFirstDerivative.source
local notation "halfF" => GaussianNamedGammaEulerFirstDerivative.quotientF
local notation "halfData" => GaussianNamedGammaEulerFirstDerivative.quotientData
local notation "IF" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "id" => GaussianNamedEulerLogarithmicImproper.data
local notation "QF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data

def nameF (f K : PR 2) : PR 2 := QF (P (incrementF f K)) (P f) K

def data (f K : PR 2) (x y R E S D a : PTm n) : PTm n :=
  qd (P (incrementF f K)) (P f) K (pd (incrementData x y) S D) (pd x R E) y a

def source (f K : PR 2) (p x y A R E S D a : PTm n) : Fm PTm n :=
  halfSource f K p x y A a ⋏
    (poleSource f x R E ⋏ poleSource (incrementF f K) (incrementData x y) S D)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f K : PR 2) (x y R E S D a : PTm n) :
    Syn.subst σ (data f K x y R E S D a) =
      data f K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ R) (Syn.subst σ E)
        (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ a) := by
  simp [data]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f K : PR 2) (p x y A R E S D a : PTm n) :
    (source f K p x y A R E S D a).subst σ =
      source f K (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A)
        (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ S) (Syn.subst σ D) (Syn.subst σ a) := by
  simp [source,GaussianNamedGammaEulerFirstDerivative.source]

theorem name_regular (f K : PR 2) (x y R E S D a : PTm n)
    (hK : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a y)
    (hLower : Γ ⊢[PRAAx] poleSource f x R E)
    (hUpper : Γ ⊢[PRAAx] poleSource (incrementF f K) (incrementData x y) S D) :
    Γ ⊢[PRAAx] pointCN (nameF f K) (data f K x y R E S D a) :=
  GaussianNamedIncrementDifferenceQuotient.name_regular (P (incrementF f K)) (P f) K _ _ y a
    (.andI (GaussianGammaNamedPoleFree.name_regular _ _ _ _ hUpper)
      (.andI (GaussianGammaNamedPoleFree.name_regular f x R E hLower) hK))

theorem original_cross (f K : PR 2) (p x y A R E S D a : PTm n)
    (hs : Γ ⊢[PRAAx] halfSource f K p x y A a)
    (hLower : Γ ⊢[PRAAx] poleSource f x R E)
    (hUpper : Γ ⊢[PRAAx] poleSource (incrementF f K) (incrementData x y) S D) :
    Γ ⊢[PRAAx] crossEquivalent (halfF f K) (nameF f K)
      (halfData f K x y A a) (data f K x y R E S D a) := by
  let g := incrementF f K
  let z := incrementData x y
  have hShift := GaussianNamedEulerLogarithmicNamedDerivative.shifted_name_source f K p zero x y A a hs
  exact GaussianNamedIncrementDifferenceQuotientProperness.proper (H g) (P g) (H f) (P f) K
    (hd z (two*A)) (pd z S D) (hd x A) (pd x R E) y a
    (GaussianNamedGamma.name_regular g z (two*A) hShift)
    (GaussianGammaNamedPoleFree.name_regular g z S D hUpper)
    (GaussianNamedGamma.name_regular f x A hs.andE₁)
    (GaussianGammaNamedPoleFree.name_regular f x R E hLower)
    hs.andE₂.andE₁
    (GaussianGammaNamedHalfPlanePoleFree.original_cross g z (two*A) S D hShift hUpper)
    (GaussianGammaNamedHalfPlanePoleFree.original_cross f x A R E hs.andE₁ hLower)

theorem derivative_rate (f K : PR 2) (p x y A R E S D a : PTm n)
    (hs : Γ ⊢[PRAAx] halfSource f K p x y A a)
    (hLower : Γ ⊢[PRAAx] poleSource f x R E)
    (hUpper : Γ ⊢[PRAAx] poleSource (incrementF f K) (incrementData x y) S D) :
    Γ ⊢[PRAAx] independentRate (nameF f K) (IF f) (data f K x y R E S D a)
      (id one x A) one (unit p) :=
  GaussianNamedRateTransport.transport (halfF f K) (IF f) (nameF f K) (IF f)
    (halfData f K x y A a) (id one x A) (data f K x y R E S D a) (id one x A) one (unit p) (unit_positive p)
    (GaussianNamedGammaEulerFirstDerivative.original_first_derivative_rate f K p x y A a hs)
    (cross_symm _ _ _ _ (original_cross f K p x y A R E S D a hs hLower hUpper))
    (cross_refl _ _ (GaussianNamedEulerLogarithmicImproper.name_regular f one x A hs.andE₁))

theorem actual_named_half_plane_pole_free_Gamma_quotient_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (source f K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        (crossEquivalent (halfF f K) (nameF f K) (halfData f K (var 1) (var 2) (var 3) (var 8))
          (data f K (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8)) ⋏
        independentRate (nameF f K) (IF f) (data f K (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8))
          (id one (var 1) (var 3)) one (unit (var 0)))) :=
  closeUniv 9 (.impI (.andI
    (original_cross f K _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (derivative_rate f K _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedHalfPlanePoleFreeQuotient

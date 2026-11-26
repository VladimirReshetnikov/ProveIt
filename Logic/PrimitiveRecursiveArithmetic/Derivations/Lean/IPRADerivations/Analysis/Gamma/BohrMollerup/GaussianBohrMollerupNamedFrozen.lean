import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupLiteralUniqueness
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerNamedPositiveAxis
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Bohr–Mollerup agreement at actual positive real observations

A sufficiently late rational observation of a certified positive regular
real input lies in the literal bracket chart with the fixed admitted radius.
Literal uniqueness on that observation transfers the actual named Euler
log-Gamma modulus to any presentation satisfying the Bohr–Mollerup laws.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupPresentation (Presentation argument laws native)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nativeF" => GaussianLogGammaEulerNamed.nameF
local notation "nativeData" => GaussianLogGammaEulerNamed.data
local notation "nativeMap" => GaussianLogGammaEulerNamed.rationalMap
local notation "cofinalF" => GaussianLogGammaEulerCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerNamed.rationalData
local notation "nativeClock" => GaussianNamedRightHalfPlaneLift.clock nativeMap

def source (f : PR 2) (x A R : PTm n) : Fm PTm n :=
  GaussianNamedGammaPositiveLower.source f x A ⋏ le (radius f x) R

def rationalData (P : Presentation) (f : PR 2) (k x : PTm n) : PTm n :=
  argument P (numerator f k x) (denominator f k x)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A R : PTm n) :
    (source f x A R).subst σ = source f (Syn.subst σ x) (Syn.subst σ A) (Syn.subst σ R) := by
  simp [source]

@[simp] theorem subst_rationalData {m : ℕ} (σ : Fin n → PTm m) (P : Presentation)
    (f : PR 2) (k x : PTm n) :
    Syn.subst σ (rationalData P f k x) = rationalData P f (Syn.subst σ k) (Syn.subst σ x) := by
  simp [rationalData]

theorem native_source (f : PR 2) (x A R : PTm n) (h : Γ ⊢[PRAAx] source f x A R) :
    Γ ⊢[PRAAx] GaussianLogGammaEulerNamed.source f x A R :=
  .andI h.andE₁.andE₁ h.andE₂

theorem frozen_source (f : PR 2) (k x A R : PTm n) (h : Γ ⊢[PRAAx] source f x A R)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] GaussianBohrMollerupBlockChord.source (numerator f k x) (denominator f k x) R :=
  .andI (frozen_rational_domain f k x A h.andE₁ hk).andE₁
    (.andI (le_trans (GaussianNameBounds.U_positive f x) h.andE₂)
      (le_trans (frozen_rational_domain f k x A h.andE₁ hk).andE₂.andE₂
        (mul_le_mul_right (denominator f k x) h.andE₂)))

theorem frozen_positive_axis (P : Presentation) (f : PR 2) (k x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (h : Γ ⊢[PRAAx] source f x A R)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF logGammaF (rationalData P f k x)
      (logGammaData (numerator f k x) (denominator f k x)) := by
  simpa [rationalData, GaussianBohrMollerupPresentation.native_program] using
    GaussianBohrMollerupLiteralUniqueness.uniqueness P native (numerator f k x) (denominator f k x) R
      hp (GaussianBohrMollerupNativeNormalization.native_laws (Γ := Γ)) (frozen_source f k x A R h hk)

theorem frozen_cross (P : Presentation) (f : PR 2) (k x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (h : Γ ⊢[PRAAx] source f x A R)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF cofinalF (rationalData P f k x) (ap1 cofinalData (ap2 f k x)) := by
  let y := logGammaData (numerator f k x) (denominator f k x)
  let z := ap1 cofinalData (ap2 f k x)
  exact cross_trans P.nameF logGammaF cofinalF (rationalData P f k x) y z
    (frozen_positive_axis P f k x A R hp h hk)
    (cross_symm cofinalF logGammaF z y (GaussianLogGammaEulerNamedPositiveAxis.frozen_cross f k x A h.andE₁ hk))

theorem late_rational_rate (P : Presentation) (f : PR 2) (s k x A R : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (h : Γ ⊢[PRAAx] source f x A R)
    (hk : Γ ⊢[PRAAx] le (nativeClock s A R) k) :
    Γ ⊢[PRAAx] independentRate (nativeF f) P.nameF (nativeData x A R) (rationalData P f k x) one (unit s) := by
  have src := native_source f x A R h
  exact GaussianNamedRateTransport.transport (nativeF f) cofinalF (nativeF f) P.nameF
    (nativeData x A R) (ap1 cofinalData (ap2 f k x)) (nativeData x A R) (rationalData P f k x)
    one (unit s) (unit_positive s)
    (GaussianLogGammaEulerNamed.late_rational_rate f s k x A R src hk)
    (cross_refl (nativeF f) (nativeData x A R) (GaussianLogGammaEulerNamed.name_regular f x A R src))
    (frozen_cross P f k x A R hp h (le_trans (GaussianNamedRightHalfPlaneLift.clock_margin nativeMap s A R) hk))

theorem actual_named_Bohr_Mollerup_late_rational_rate_closed (P : Presentation) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (laws P ⟶ source f (var 2) (var 3) (var 4) ⟶ le (nativeClock (var 0) (var 3) (var 4)) (var 1) ⟶
        independentRate (nativeF f) P.nameF (nativeData (var 2) (var 3) (var 4))
          (rationalData P f (var 1) (var 2)) one (unit (var 0))) :=
  closeUniv 5 (.impI (.impI (.impI (late_rational_rate P f _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupNamedFrozen

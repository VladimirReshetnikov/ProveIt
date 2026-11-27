import IPRADerivations.Analysis.Gamma.Names.PoleFree.RealCharts.GaussianGammaNamedPoleFreeRealAdmission
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalDerivative

/-!
# A common increment demand for the real Gamma derivative charts

The sum contains the pole margin, the original half-plane derivative
demand, and the terminal derivative demand for the computed negative
offset. A single certified size bound supplies each chart's guard.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivativeDemand

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianGammaNamedPoleFreeRealAdmission (offsetF offsetData negativeChart)
open GaussianRationalHorner (positive_product)
open GaussianRealNameExponentialInjectivity (axisSamples)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "halfSource" => GaussianNamedRightHalfPlane.source
local notation "positiveSource" => GaussianNamedGammaEulerFirstDerivative.source
local notation "negativeSource" => GaussianGammaNegativeIntervalNamedTerminalDerivative.source
local notation "termModulus" => GaussianGammaNegativeIntervalNamedTerminalDerivative.modulus

def positiveModulus (f : PR 2) (p x E : PTm n) : PTm n :=
  GaussianNamedEulerLogarithmicNamedDerivative.incrementModulus f p zero x (two*E)

def negativeModulus (f : PR 2) (p x E : PTm n) : PTm n :=
  termModulus (offsetF f) p (offsetData f x E) (two*E)

def modulus (f : PR 2) (p x E : PTm n) : PTm n :=
  (two*E+positiveModulus f p x E)+negativeModulus f p x E

ipra_subst positiveModulus [two]

ipra_subst negativeModulus [two]

ipra_subst modulus [two]

theorem positive_modulus_positive (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] le one (positiveModulus f p x E) :=
  GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _

theorem negative_modulus_positive (f : PR 2) (p x E : PTm n) :
    Γ ⊢[PRAAx] le one (negativeModulus f p x E) :=
  le_trans (GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _) (le_add_left _ _)

theorem modulus_positive (f : PR 2) (p x E : PTm n) : Γ ⊢[PRAAx] le one (modulus f p x E) :=
  le_trans (negative_modulus_positive f p x E) (le_add_left _ _)

private theorem small_weaken (K : PR 2) (z M B : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hMB : Γ ⊢[PRAAx] le M B) (h : Γ ⊢[PRAAx] smallSamples K z one B) :
    Γ ⊢[PRAAx] smallSamples K z one M := by
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] smallSamples K (sh z) one (sh B) := by
    simpa [Δ,Fm.shift,Syn.shift,sh,one] using h.shift
  have hm : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hM.shift
  have hmb : Δ ⊢[PRAAx] le (sh M) (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hMB.shift
  have out := bounded_radius_mono (ap2 K (var 0) (sh z)) one (sh B) one (sh M) (le_trans hm hmb) hm
    (le_congr (by ipra_ring) (by ipra_ring) hmb) (small_samples_at K (sh z) one (sh B) (var 0) hs)
  exact .allI (by simpa only [smallSamples,Syn.shift,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,sh] using out)

theorem margin_small (f K : PR 2) (p x z E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hs : Γ ⊢[PRAAx] smallSamples K z one (modulus f p x E)) :
    Γ ⊢[PRAAx] smallSamples K z one (two*E) :=
  small_weaken K z (two*E) (modulus f p x E) (positive_product _ _ RationalAlgebra.two_positive hE)
    (le_trans (le_add_right _ _) (le_add_right _ _)) hs

theorem positive (f K : PR 2) (p x z E a : PTm n)
    (hf : Γ ⊢[PRAAx] halfSource f x (two*E))
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hs : Γ ⊢[PRAAx] smallSamples K z one (modulus f p x E)) :
    Γ ⊢[PRAAx] positiveSource f K p x z (two*E) a :=
  .andI hf (.andI hk
    (small_weaken K z (positiveModulus f p x E) (modulus f p x E) (positive_modulus_positive f p x E)
      (le_trans (le_add_left _ _) (le_add_right _ _)) hs))

theorem negative (f K : PR 2) (p x z E a : PTm n)
    (hf : Γ ⊢[PRAAx] negativeChart f x E)
    (hAxis : Γ ⊢[PRAAx] axisSamples K z)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hs : Γ ⊢[PRAAx] smallSamples K z one (modulus f p x E)) :
    Γ ⊢[PRAAx] negativeSource (offsetF f) K p (offsetData f x E) z (two*E) a :=
  .andI hf.andE₁ (.andI hAxis (.andI hk
    (small_weaken K z (negativeModulus f p x E) (modulus f p x E) (negative_modulus_positive f p x E)
      (le_add_left _ _) hs)))

theorem actual_Gamma_named_real_common_derivative_demand_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((axisSamples K (var 2) ⋏ (GaussianNameReciprocal.input K (var 4) (var 2) ⋏
        smallSamples K (var 2) one (modulus f (var 0) (var 1) (var 3)))) ⟶
        ((le one (var 3) ⟶ smallSamples K (var 2) one (two*var 3)) ⋏
         ((halfSource f (var 1) (two*var 3) ⟶ positiveSource f K (var 0) (var 1) (var 2) (two*var 3) (var 4)) ⋏
          (negativeChart f (var 1) (var 3) ⟶ negativeSource (offsetF f) K (var 0)
            (offsetData f (var 1) (var 3)) (var 2) (two*var 3) (var 4))))) :=
  closeUniv 5 (.impI (.andI
    (.impI (margin_small f K _ _ _ _ Prf.hyp0 Prf.hyp1.andE₂.andE₂))
    (.andI (.impI (positive f K _ _ _ _ _ Prf.hyp0 Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂))
      (.impI (negative f K _ _ _ _ _ Prf.hyp0 Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂)))))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedRealDerivativeDemand

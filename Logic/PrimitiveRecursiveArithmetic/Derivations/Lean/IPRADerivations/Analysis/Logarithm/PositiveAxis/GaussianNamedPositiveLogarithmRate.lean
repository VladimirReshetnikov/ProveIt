import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithm

/-!
# Quantitative transport through the original named positive logarithm

Two named inputs with the same positive lower margin carry a
quantitative distance into their actual named logarithms. The
margin multiplies the rational part of the bound. The original
logarithm clocks pay for the input observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmRate

open_ipra
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianNamedPositiveLogarithm (source nameF data clock observations_of_query_bound)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem log_rate_at (f g : PR 2) (p q x y E T U A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E U)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E)) (ap2 (nameF g) q (data y E))
      (rateNumerator (E*A) D p q) (rateDenominator D p q) :=
  observations_of_query_bound f g p q x y E T U A D hf hg hD
    (rate_at f g x y A D (clock p E) (clock q E) h)

theorem log_rate (f g : PR 2) (x y E T U A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E U)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] independentRate (nameF f) (nameF g) (data x E) (data y E) (E*A) D := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift.shift
  have gs : Δ ⊢[PRAAx] source g (sh y) (sh E) (sh U) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift.shift
  have ds : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have rs : Δ ⊢[PRAAx] independentRate f g (sh x) (sh y) (sh A) (sh D) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [independentRate,GaussianNamedPositiveLogarithm.subst_data,sh,Syn.shift,PTm.subst_mul] using
    log_rate_at f g (var 1) (var 0) (sh x) (sh y) (sh E) (sh T) (sh U) (sh A) (sh D) hs gs ds rs

theorem actual_named_positive_logarithm_rate_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source f (var 0) (var 2) (var 3) ⋏ source g (var 1) (var 2) (var 6)) ⟶
      (le one (var 5) ⋏ independentRate f g (var 0) (var 1) (var 4) (var 5)) ⟶
      independentRate (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 2))
        (var 2*var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (log_rate f g _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmRate

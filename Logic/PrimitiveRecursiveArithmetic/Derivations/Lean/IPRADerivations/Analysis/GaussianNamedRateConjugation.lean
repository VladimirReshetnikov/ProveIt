import IPRADerivations.Analysis.GaussianNameConjugation
import IPRADerivations.Analysis.GaussianNamedInverseRate

/-!
# Conjugation preserves independent observation rates

The exact Gaussian rational isometry preserves the leading radius and
each of the independent clock errors on both original conjugate samplers.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRateConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalConjugation (point_distance)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Conj" => GaussianNameConjugation.nameF

theorem observation (F G : PR 2) (x y A N p q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y A N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Conj F) p x) (ap2 (Conj G) q y)
      (rateNumerator A N p q) (rateDenominator N p q) :=
  distance_congr (GaussianNameConjugation.sample_at F p x).eqSymm
    (GaussianNameConjugation.sample_at G q y).eqSymm (.eqRefl _) (.eqRefl _)
    (point_distance _ _ _ _ (denominator_positive N p q hN) (rate_at F G x y A N p q h))

theorem transport (F G : PR 2) (x y A N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y A N) :
    Γ ⊢[PRAAx] independentRate (Conj F) (Conj G) x y A N := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have positive : Δ ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hN.shift.shift
  have rate : Δ ⊢[PRAAx] independentRate F G (sh x) (sh y) (sh A) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  simpa only [independentRate,Syn.shift,sh,Δ] using
    observation F G (sh x) (sh y) (sh A) (sh N) (var 1) (var 0) positive rate

theorem actual_named_independent_rate_conjugation_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ independentRate F G (var 0) (var 1) (var 2) (var 3) ⟶
      independentRate (Conj F) (Conj G) (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (transport F G _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedRateConjugation

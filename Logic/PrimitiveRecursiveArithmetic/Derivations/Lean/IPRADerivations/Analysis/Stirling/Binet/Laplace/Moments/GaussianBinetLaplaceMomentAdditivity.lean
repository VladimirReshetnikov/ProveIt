import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.FiniteRows.GaussianBinetLaplaceMomentCompact
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity

/-!
# Same-horizon additivity of the actual weighted Binet quadrature

The full interval and the two subintervals use the same weighted
evaluator and the same time chart. The physical right panel starts at
A+C₁. Its translated grid is aligned before applying the name equality.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentAdditivity

open_ipra
open GaussianBinetLaplaceMomentCompact (data sampled_modulus)
open GaussianBinetLaplaceMomentFloor (nameF evaluatorF fixedData gain)
open GaussianBinetLaplaceStrip (source)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem additivity (j X D R T A C₁ C₂ E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A (C₁+C₂) E)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF nameF nameF)
      (data j X D R T A (C₁+C₂) E)
      (addData (data j X D R T A C₁ E) (data j X D R T (A+C₁) C₂ E)) := by
  let L := gain j R T
  let x := fixedData j X D R T
  have he := h.andE₂.andE₁
  exact GaussianCompactNamedAdditivity.name_additivity_with_offset evaluatorF E A C₁ C₂ E L T x
    he he h₁ h₂ h.andE₂.andE₂ (sampled_modulus j X D R T A (C₁+C₂) E h)

theorem actual_weighted_Binet_compact_additivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) zero (var 2) zero (var 3) (var 4) (var 5) (var 6+var 7) (var 8) ⟶
      le one (var 6) ⟶ le one (var 7) ⟶ crossEquivalent nameF (addF nameF nameF)
        (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6+var 7) (var 8))
        (addData (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8))
          (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5+var 6) (var 7) (var 8)))) :=
  closeUniv 9 (.impI (.impI (.impI (additivity _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentAdditivity

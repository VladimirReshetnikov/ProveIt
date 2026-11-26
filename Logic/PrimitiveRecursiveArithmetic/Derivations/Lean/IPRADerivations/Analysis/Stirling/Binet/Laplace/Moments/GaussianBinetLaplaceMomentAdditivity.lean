import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.FiniteRows.GaussianBinetLaplaceMomentCompact
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment

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
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem additivity (j X D R T A C₁ C₂ E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A (C₁+C₂) E)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF nameF nameF)
      (data j X D R T A (C₁+C₂) E)
      (addData (data j X D R T A C₁ E) (data j X D R T (A+C₁) C₂ E)) := by
  let a := E+A
  let L := gain j R T
  let x := fixedData j X D R T
  let d₁ := data j X D R T A C₁ E
  let d₂ := GaussianCompactRiemannName.data (a+C₁) C₂ E L T x
  let d₂' := data j X D R T (A+C₁) C₂ E
  have hi : Γ ⊢[PRAAx] GaussianCompactNamedAdditivity.input evaluatorF a C₁ C₂ E L T x :=
    .andI (le_trans h.andE₂.andE₁ (le_add_right E A)) (.andI h.andE₂.andE₁
      (.andI h₁ (.andI h₂ (.andI (le_trans (le_add_left (C₁+C₂) A) h.andE₂.andE₂)
        (sampled_modulus j X D R T A (C₁+C₂) E h)))))
  have ea : Γ ⊢[PRAAx] a+C₁ ≐ E+(A+C₁) := by dsimp only [a]; ipra_ring
  have e : Γ ⊢[PRAAx] d₂ ≐ d₂' := by
    simpa only [d₂,d₂',data,GaussianCompactRiemannName.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (GaussianCompactRiemannName.data (var 0) (Syn.shift C₂) (Syn.shift E)
        (Syn.shift L) (Syn.shift T) (Syn.shift x)) ea
  have es : Γ ⊢[PRAAx] addData d₁ d₂ ≐ addData d₁ d₂' := by
    simpa only [GaussianNameArithmetic.subst_addData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (addData (Syn.shift d₁) (var 0)) e
  exact cross_data_congr nameF (addF nameF nameF) _ _ _ _ (.eqRefl _) es
    (GaussianCompactNamedAdditivity.name_additivity evaluatorF a C₁ C₂ E L T x hi)

theorem actual_weighted_Binet_compact_additivity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 1) zero (var 2) zero (var 3) (var 4) (var 5) (var 6+var 7) (var 8) ⟶
      le one (var 6) ⟶ le one (var 7) ⟶ crossEquivalent nameF (addF nameF nameF)
        (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6+var 7) (var 8))
        (addData (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8))
          (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5+var 6) (var 7) (var 8)))) :=
  closeUniv 9 (.impI (.impI (.impI (additivity _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentAdditivity

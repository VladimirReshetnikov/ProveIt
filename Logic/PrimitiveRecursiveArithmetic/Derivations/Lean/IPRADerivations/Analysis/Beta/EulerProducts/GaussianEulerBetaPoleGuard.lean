import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Powers.GaussianEulerLowerPowerCoefficients
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPolynomialPrimitive

/-!
# Positive real-part data supply every finite Beta pole guard

The original native margin B<=A*Re(z) is preserved after translation by
B*j. Its genuine nonnegative signed gap and the original native squared
Euclidean norm imply B^2<=A^2*|z+B*j|^2. Every finite pole guard is thereby
derived directly from the paper's input, with no inverse or polynomial
primitive output hypothesis and no upper-radius premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaPoleGuard

open_ipra
open ComplexLogarithmRemainder (scale normSq re)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianEulerLowerPowerCoefficients (realLower)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z B A : PTm n) : Fm PTm n := le one B ⋏ (le one A ⋏ realLower z A B)
ipra_subst source

theorem translated_real_margin (z B A j : PTm n) (h : Γ ⊢[PRAAx] realLower z A B) : Γ ⊢[PRAAx]
    zle (ZT.ofNat B) (re (scale A (translated z B j))) := by
  let hi := ZT.ofNat A*re z
  let lo := ZT.ofNat B
  let gap := monus (hi.pos+lo.neg) (lo.pos+hi.neg)
  have e : ZT.toZ Γ lo+𝔞(gap) = ZT.toZ Γ hi := zle_toZ h
  apply zle_of_toZ (gap+A*B*j)
  simp only [lo,hi,ZT.toZ_mul,ZT.toZ_ofNat] at e
  simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_one,translated]
  try ipra_simps
  linear_combination e

/-- The original REAL input margin gives the full complex squared
separation, independently of the chosen finite horizon. -/
theorem pole_at_every_index (z B A j : PTm n) (h : Γ ⊢[PRAAx] realLower z A B) : Γ ⊢[PRAAx] poleAt z B one A j := by
  let w := scale A (translated z B j)
  have signed := PolynomialBisection.zle_trans (translated_real_margin z B A j h)
    (GaussianRelativeNormTriangle.signed_le_absolute (re w))
  have lower : Γ ⊢[PRAAx] le B (zabs (re w)) := by
    change Γ ⊢[PRAAx] le (B+zero) (zabs (re w)+zero) at signed
    exact le_congr (add_zero _) (add_zero _) signed
  have square := AnalyticNumberTheory.PhiLower.le_mul_mono lower lower
  have component : Γ ⊢[PRAAx] le (zabs (re w)*zabs (re w)) (normSq w) :=
    le_congr (.eqRefl _) (GaussianEulerUpperPowerCoefficients.native_absolute_norm w).eqSymm
      (le_add_right _ (zabs (ComplexLogarithmRemainder.im w)*zabs (ComplexLogarithmRemainder.im w)))
  exact le_congr (by ipra_ring) (ComplexLogarithmRemainder.normSq_scale A (translated z B j)) (le_trans square component)

theorem all_finite_guards (z B A N : PTm n) (h : Γ ⊢[PRAAx] realLower z A B) : Γ ⊢[PRAAx] poleGuard z B one A N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] realLower (Syn.shift z) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,GaussianGammaEulerHeadLower.subst_poleAt] using
    (pole_at_every_index (Syn.shift z) (Syn.shift B) (Syn.shift A) (var 0) hs.wk)

theorem original_integral_source (z R B A N : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    source z B A ⋏ poleGuard z B one A N :=
  .andI (.andI h.andE₂.andE₁.andE₁ (.andI h.andE₁ h.andE₂.andE₂)) (all_finite_guards z B A N h.andE₂.andE₂)

/-- Original real-part data discharge the primitive's entire native
source condition. No finite pole guard remains as an extra premise. -/
theorem primitive_input (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    GaussianEulerBetaPolynomialPrimitive.source z B A N :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (all_finite_guards z B A N h.andE₂.andE₂))
theorem original_beta_primitive (z R B A N t : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (ht : Γ ⊢[PRAAx] GaussianRationalHorner.canonical t) : Γ ⊢[PRAAx]
    GaussianRationalHorner.evaluate (GaussianEulerBetaPolynomialPrimitive.eulerOperator z B N) t ≐
      GaussianRationalReciprocal.power (GaussianRationalMetric.qsub GaussianRationalReciprocal.qone t) N :=
  GaussianEulerBetaPolynomialPrimitive.operator_evaluation z B A N t
    (primitive_input z B A N (original_integral_source z R B A N h).andE₁) ht

def output (z B A j : PTm n) : PTm n := pairT (translated z B j)
  (pairT (B*B) (A*A*normSq (translated z B j)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z B A j : PTm n) : PTm n := PTm.app outputF ![z,B,A,j]
theorem program_at (z B A j : PTm n) : Γ ⊢[PRAAx] run z B A j ≐ output z B A j := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,B,A,j]

theorem original_positive_real_Beta_pole_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (realLower (var 0) (var 2) (var 1) ⟶ poleAt (var 0) (var 1) one (var 2) (var 3)) :=
  closeUniv 4 (.impI (pole_at_every_index _ _ _ _ Prf.hyp0))
theorem original_positive_real_finite_Beta_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (realLower (var 0) (var 2) (var 1) ⟶ poleGuard (var 0) (var 1) one (var 2) (var 3)) :=
  closeUniv 4 (.impI (all_finite_guards _ _ _ _ Prf.hyp0))
theorem original_Euler_input_supplies_Beta_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianEulerLowerPowerCoefficients.source (var 0) (var 1) (var 2) (var 3) ⟶
      (source (var 0) (var 2) (var 3) ⋏ poleGuard (var 0) (var 2) one (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_integral_source _ _ _ _ _ Prf.hyp0))
theorem original_Euler_input_Beta_primitive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((GaussianEulerLowerPowerCoefficients.source (var 0) (var 1) (var 2) (var 3) ⋏ GaussianRationalHorner.canonical (var 5)) ⟶
      GaussianRationalHorner.evaluate (GaussianEulerBetaPolynomialPrimitive.eulerOperator (var 0) (var 2) (var 4)) (var 5) ≐
        GaussianRationalReciprocal.power (GaussianRationalMetric.qsub GaussianRationalReciprocal.qone (var 5)) (var 4)) :=
  closeUniv 6 (.impI (original_beta_primitive _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_Beta_pole_guard_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerBetaPoleGuard

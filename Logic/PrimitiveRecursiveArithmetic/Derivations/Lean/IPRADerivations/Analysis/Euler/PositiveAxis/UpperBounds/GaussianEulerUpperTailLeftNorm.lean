import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayLeftNorm
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactUpperTail

/-!
# Original Euler upper grids retain D_R times the left decay norm

The pointwise majorant is summed by the existing original-grid theorem.
Only its half-decay bound changes: the actual rational left observation
is retained with coefficient D_R=2^(R+1)R!, together with all explicit
finite mesh and observation errors. At a=N,E=2 it is exactly the original
decay sample exp(-N/4), with no dyadic or integer-time replacement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUpperTailLeftNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerCoefficients (source)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianEulerUpperTailScalar (budget)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (quadrature)
open GaussianEulerDecayMesh (observation)
open GaussianGammaIntegralCutoffs (tailCoefficient)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def errorNumerator (p q M C E R : PTm n) : PTm n :=
  C*budget R*GaussianEulerHalfDecayLeftNorm.errorDenominator p q M E+
    majorant R*GaussianEulerHalfDecayLeftNorm.errorNumerator p q M C E*(E*unit p)
def numerator (p q M C E R A D : PTm n) : PTm n :=
  tailCoefficient R*A*(E*unit p*GaussianEulerHalfDecayLeftNorm.errorDenominator p q M E)+
    D*errorNumerator p q M C E R
def denominator (p q M E D : PTm n) : PTm n :=
  D*(E*unit p*GaussianEulerHalfDecayLeftNorm.errorDenominator p q M E)

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (p q M C E R : PTm n) :
    Syn.subst σ (errorNumerator p q M C E R) = errorNumerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ R) := by simp [errorNumerator]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p q M C E R A D : PTm n) :
    Syn.subst σ (numerator p q M C E R A D) = numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ D) := by simp [numerator,tailCoefficient]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p q M E D : PTm n) :
    Syn.subst σ (denominator p q M E D) = denominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ E) (Syn.subst σ D) := by simp [denominator]

theorem original_coefficient (R : PTm n) : Γ ⊢[PRAAx] tailCoefficient R ≐ two*majorant R :=
  (congrMul (pw_succ two R) (.eqRefl (Products.fact R))).eqTrans (by unfold majorant unit; ipra_ring)

/-- Exact D_R*A/D plus the half-decay mesh/error terms and the original
Euler-to-half-decay scalar comparison error. -/
theorem original_grid_left_norm (p q M a C E z R B A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] le one C)
    (hea : Γ ⊢[PRAAx] le E a) (hD : Γ ⊢[PRAAx] le one D)
    (hstep : Γ ⊢[PRAAx] le C ((two*E)*M))
    (hleft : Γ ⊢[PRAAx] bounded (observation a (two*E) q) A D) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p M a C E (fixedData z B))
      (numerator p q M C E R A D) (denominator p q M E D) := by
  let U := GaussianEulerHalfDecayLeftNorm.numerator p q M C E A D
  let V := GaussianEulerHalfDecayLeftNorm.denominator p q M E D
  have half := GaussianEulerHalfDecayLeftNorm.original_half_decay_left_norm p q M a C E zero A D
    (.andI (le_trans hE hea) (.andI hM (.andI hE (.andI hC (.andI hD hstep))))) hleft
  have hV : Γ ⊢[PRAAx] le one V :=
    positive_product _ _ hD (GaussianEulerHalfDecayLeftNorm.error_denominator_positive p q M E hM hE)
  have actual := GaussianEulerCompactUpperTail.original_grid_bound_from_half p M a C E z R B U V hM hE hea h hV half
  have numEq : Γ ⊢[PRAAx] (C*budget R)*V+(majorant R*U)*(E*unit p) ≐ numerator p q M C E R A D := by
    have coeff := natEq (original_coefficient (Γ := Γ) R)
    apply deriveNat
    dsimp only [U,V,numerator,errorNumerator,GaussianEulerHalfDecayLeftNorm.numerator,GaussianEulerHalfDecayLeftNorm.denominator]
    ipra_simps
    rw [coeff]
    ring
  exact bound_congr (.eqRefl _) numEq (by dsimp only [V,denominator,GaussianEulerHalfDecayLeftNorm.denominator]; ipra_ring) actual

/-- The left endpoint is N/2 and the retained actual observation is
exp(-N/4) at precisely q, for every internal N>=2. -/
theorem original_half_degree_upper_grid (p q M N C z R B A D : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C)
    (hN : Γ ⊢[PRAAx] le two N) (hD : Γ ⊢[PRAAx] le one D)
    (hstep : Γ ⊢[PRAAx] le C ((two*two)*M))
    (hleft : Γ ⊢[PRAAx] bounded (observation N (two*two) q) A D) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p M N C two (fixedData z B))
      (numerator p q M C two R A D) (denominator p q M two D) :=
  original_grid_left_norm p q M N C two z R B A D h hM (le_succ_self one) hC hN hD hstep hleft

theorem original_Euler_rational_time_grid_retains_left_decay_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 6) (var 7) (var 8) ⋏ le one (var 2) ⋏ le one (var 5) ⋏ le one (var 4) ⋏
      le (var 5) (var 3) ⋏ le one (var 10) ⋏ le (var 4) ((two*var 5)*var 2) ⋏
      bounded (observation (var 3) (two*var 5) (var 1)) (var 9) (var 10)) ⟶
      bounded (quadrature evaluatorF (var 0) (var 2) (var 3) (var 4) (var 5) (fixedData (var 6) (var 8)))
        (numerator (var 0) (var 1) (var 2) (var 4) (var 5) (var 7) (var 9) (var 10))
        (denominator (var 0) (var 1) (var 2) (var 5) (var 10))) :=
  closeUniv 11 (.impI (original_grid_left_norm _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUpperTailLeftNorm

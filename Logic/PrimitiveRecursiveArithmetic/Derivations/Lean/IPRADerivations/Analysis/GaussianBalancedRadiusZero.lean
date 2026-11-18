import IPRADerivations.Analysis.GaussianBalancedRadiusSyntax
import IPRADerivations.Analysis.RationalNonnegativePowers

/-!
# Genuine zero-radius branch of the balanced radius certificate

The actual coefficient term is its original squared norm times the actual
nonnegative rational radius power. A zero radius numerator and a positive
coefficient index derive a literal zero term, with no coefficient or
output-correctness premise. Thus every positive-degree radius inequality
holds even when the original constant residual vanishes. All numerical
coefficients, degrees, denominators and indices remain internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusZero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (coefficient numerator denominator)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.RationalNonnegativePowers (power)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product scalar_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def term (C N A B i : PTm n) : PTm n := RationalArithmetic.multiply
  (GaussianRationalMetric.qnormSq (coefficient C N i)) (power A B (two*i))

@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (C N A B i : PTm n) :
    Syn.subst σ (term C N A B i) = term (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ i) := by simp [term]

theorem term_congr (C N i : PTm n) {A A' B B' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    term C N A B i ≐ term C N A' B' i := by
  simpa only [subst_term,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (term (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
      (σ := ![C,N,A,B,i]) (σ' := ![C,N,A',B',i])
      (fun j => by fin_cases j; exact .eqRefl _; exact .eqRefl _; exact hA; exact hB; exact .eqRefl _)

theorem term_denominator_positive (C N B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (denominator C N i*pw B (two*i)) :=
  positive_product _ _ (GaussianBalancedRadiusSyntax.denominator_positive C N i)
    (RationalNonnegativePowers.denominator_positive B (two*i) hB)

theorem term_represents (C N A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (term C N A B i)
      (ZT.ofNat (numerator C N i*pw A (two*i))) (denominator C N i*pw B (two*i)) := by
  have h := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (GaussianBalancedRadiusSyntax.coefficient_norm_represents C N i)
    (RationalNonnegativePowers.power_represents A B (two*i) hB)
  apply scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem term_canonical (C N A B i : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (term C N A B i) :=
  RationalArithmetic.multiply_guard _ _

/-- A positive internal exponent is a genuine successor; the actual
natural power program therefore sends zero to zero at that exponent. -/
theorem natural_zero_power (A k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hA : Γ ⊢[PRAAx] A ≐ zero) : Γ ⊢[PRAAx] pw A k ≐ zero :=
  (congrAp2 powF (.eqRefl _) hA).eqTrans
    ((congrAp2 powF (RationalIntegerNormalization.positive_form hk) (.eqRefl zero)).eqTrans
      ((pw_succ zero (PTm.pred k)).eqTrans (mul_zero _)))

/-- Literal zero of the actual normalized coefficient term. The index
condition excludes exponent zero, where the power program correctly gives 1. -/
theorem zero_term_eq (C N A B i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le one i)
    (hA : Γ ⊢[PRAAx] A ≐ zero) : Γ ⊢[PRAAx] term C N A B i ≐ fraction zero one := by
  have positive : Γ ⊢[PRAAx] le one (two*i) :=
    le_trans hi (le_of_eq_add (d := i) (by ipra_ring))
  have p := natural_zero_power A (two*i) positive hA
  have nzero := natEq ((congrMul (.eqRefl (numerator C N i)) p).eqTrans (mul_zero _))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (term_canonical C N A B i)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (term_represents C N A B i hB) (fraction_represents zero one (le_refl one))
    (term_denominator_positive C N B i hB) (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [nzero]
  ring

/-- Actual squared coefficient norms are nonnegative even for arbitrary
noncanonical Gaussian input codes and a zero constant coefficient. -/
theorem constant_norm_nonnegative (C N : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction zero one) (GaussianRationalMetric.qnormSq (coefficient C N zero)) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl one)
    (GaussianBalancedRadiusSyntax.denominator_positive C N zero)
    (fraction_represents zero one (le_refl one)) (GaussianBalancedRadiusSyntax.coefficient_norm_represents C N zero)
    (le_congr (by ipra_ring) (by ipra_ring) (zero_le (numerator C N zero)))

theorem zero_term_bound (C N A B i : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] le one i)
    (hA : Γ ⊢[PRAAx] A ≐ zero) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (term C N A B i) (GaussianRationalMetric.qnormSq (coefficient C N zero)) :=
  RationalArgmin.rationalLE_congr (zero_term_eq C N A B i hB hi hA).eqSymm (.eqRefl _)
    (constant_norm_nonnegative C N)

/-! Actual uniform PR5 term evaluator and closed zero-branch certificates. -/
def termF : PR 5 := PTm.toPR (term (var 0) (var 1) (var 2) (var 3) (var 4))
theorem term_program (C N A B i : PTm n) : Γ ⊢[PRAAx] PTm.app termF ![C,N,A,B,i] ≐ term C N A B i := by
  simpa [termF] using toPR_eq (Γ := Γ) (term (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,A,B,i]

theorem zero_radius_term_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le one (var 4) ⟶ var 2 ≐ zero ⟶
      term (var 0) (var 1) (var 2) (var 3) (var 4) ≐ fraction zero one) :=
  closeUniv 5 (.impI (.impI (.impI (zero_term_eq _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem zero_radius_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le one (var 4) ⟶ var 2 ≐ zero ⟶
      RationalArgmin.rationalLE (term (var 0) (var 1) (var 2) (var 3) (var 4))
        (GaussianRationalMetric.qnormSq (coefficient (var 0) (var 1) zero))) :=
  closeUniv 5 (.impI (.impI (.impI (zero_term_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem coefficient_radius_term_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app termF ![var 0,var 1,var 2,var 3,var 4] ≐ term (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (term_program _ _ _ _ _)

/-- Positive-denominator normalized zero has its unique canonical code. -/
theorem fraction_zero (B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    fraction zero B ≐ fraction zero one := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hB)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (fraction_represents zero B hB) (fraction_represents zero one (le_refl one)) hB (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem zero_fraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ fraction zero (var 0) ≐ fraction zero one) :=
  closeUniv 1 (.impI (fraction_zero _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusZero

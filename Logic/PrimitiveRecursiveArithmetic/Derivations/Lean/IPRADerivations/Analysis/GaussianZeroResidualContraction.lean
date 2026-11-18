import IPRADerivations.Analysis.GaussianDescentClock
import IPRADerivations.Analysis.GaussianTranslatedBalancedRadius

/-!
# The actual zero-residual branch contracts

The input is the computed natural norm numerator of the actual Horner
value. Its two raw positive denominators and the actual clock fraction
derive the zero contraction comparison by exact integer clearing. No
zero-value, multiplication, or residual-output oracle is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianZeroResidualContraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.GaussianDescentClock
  (residualNumerator residualDenominator contractionSquare value_represents)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (rateDenominator rate_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def comparison (N C z : PTm n) : Fm PTm n := RationalArgmin.rationalLE
  (qnormSq (evaluate C z)) (RationalArithmetic.multiply (contractionSquare N) (qnormSq (evaluate C z)))

@[simp] theorem subst_comparison {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    (comparison N C z).subst σ = comparison (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [comparison]

theorem residual_alias (C z : PTm n) : Γ ⊢[PRAAx]
    residualNumerator C z ≐ GaussianTranslatedBalancedRadius.residual C z := .eqRefl _

theorem contraction_represents (N : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents
    (contractionSquare N) (ZT.ofNat (pred (rateDenominator N)*pred (rateDenominator N)))
    (rateDenominator N*rateDenominator N) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (positive_product _ _ (rate_positive N) (rate_positive N))

theorem zero_contraction (N C z : PTm n) (h0 : Γ ⊢[PRAAx] residualNumerator C z ≐ zero) : Γ ⊢[PRAAx]
    comparison N C z := by
  have d := GaussianDescentClock.residual_denominator_positive (Γ := Γ) C z
  have r := rate_positive (Γ := Γ) N
  have value : Γ ⊢[PRAAx] RationalArithmetic.represents (qnormSq (evaluate C z))
      (ZT.ofNat (residualNumerator C z)) (residualDenominator C z*residualDenominator C z) :=
    GaussianRationalMetric.qnormSq_represents _ _ _ d (value_represents _)
  have product := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _ (contraction_represents N) value
  have product' : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (contractionSquare N) (qnormSq (evaluate C z)))
      (ZT.ofNat ((pred (rateDenominator N)*pred (rateDenominator N))*residualNumerator C z))
      ((rateDenominator N*rateDenominator N)*(residualDenominator C z*residualDenominator C z)) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := product)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
  apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ d d) (positive_product _ _ (positive_product _ _ r r) (positive_product _ _ d d)) value product'
  apply le_of_eq_add (d := zero)
  apply deriveNat
  have e := natEq h0
  ipra_simps
  rw [e]
  ring

def output (N C z : PTm n) : PTm n := pairT (qnormSq (evaluate C z))
  (RationalArithmetic.multiply (contractionSquare N) (qnormSq (evaluate C z)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (N C z : PTm n) : PTm n := ap3 outputF N C z
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (output N C z) = output (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (N C z : PTm n) :
    Syn.subst σ (run N C z) = run (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ z) := by simp [run]

theorem program_at (N C z : PTm n) : Γ ⊢[PRAAx] run N C z ≐ output N C z := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![N,C,z]
theorem returned_left (N C z : PTm n) : Γ ⊢[PRAAx] fstT (run N C z) ≐ qnormSq (evaluate C z) :=
  (congrFst (program_at N C z)).eqTrans (fst_pair _ _)
theorem returned_right (N C z : PTm n) : Γ ⊢[PRAAx] sndT (run N C z) ≐
    RationalArithmetic.multiply (contractionSquare N) (qnormSq (evaluate C z)) :=
  (congrSnd (program_at N C z)).eqTrans (snd_pair _ _)

theorem actual_zero_residual_contraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (residualNumerator (var 1) (var 2) ≐ zero ⟶ comparison (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (zero_contraction _ _ _ Prf.hyp0))
theorem actual_zero_residual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem returned_zero_residual_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (residualNumerator (var 1) (var 2) ≐ zero ⟶ RationalArgmin.rationalLE
      (fstT (run (var 0) (var 1) (var 2))) (sndT (run (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (RationalArgmin.rationalLE_congr (returned_left _ _ _).eqSymm
    (returned_right _ _ _).eqSymm (zero_contraction _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianZeroResidualContraction

import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdLogarithmRows
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.HigherOrders.GaussianBarnesCanonicalHigherDerivative

/-!
# Shifted inverse-square telescope for the original cubic logarithmic rows

For x=A/B≥1, a finite block strictly after the index N of the
zero-based positive rows is bounded by 2B²r/((A+NB)(A+(N+r)B)).
The estimate applies directly to the original factorial-scaled finite sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmTail

open_ipra
open GaussianBarnesCanonicalThirdLogarithmRows (center derivative_at row shiftedNumerator shifted_positive square_bound)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (A B N r : PTm n) : PTm n :=
  GaussianBarnesCanonicalHigherDerivative.value (center A B) B (succ N) zero r

def budget (B : PTm n) : PTm n := two*(B*B)

def denominator (A B N r : PTm n) : PTm n := shiftedNumerator A B N*shiftedNumerator A B (N+r)

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (A B N r : PTm n) :
    Syn.subst σ (value A B N r) = value (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [value]

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (B : PTm n) :
    Syn.subst σ (budget B) = budget (Syn.subst σ B) := by simp [budget,two,one]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (A B N r : PTm n) :
    Syn.subst σ (denominator A B N r) =
      denominator (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [denominator]

theorem denominator_positive (A B N r : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (denominator A B N r) :=
  positive_product _ _ (shifted_positive A B N hA) (shifted_positive A B (N+r) hA)

theorem zero_at (A B N : PTm n) :
    Γ ⊢[PRAAx] value A B N zero ≐ GaussianRationalHorner.qzero :=
  GaussianRationalFiniteSum.sum_zero _ _

theorem succ_at (A B N r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] value A B N (succ r) ≐
      GaussianRationalHorner.qadd (value A B N r) (row A B (N+succ r)) := by
  have e : Γ ⊢[PRAAx] row A B (succ N+r) ≐ row A B (N+succ r) := by
    have move : Γ ⊢[PRAAx] succ N+r ≐ N+succ r := by ipra_ring
    ipra_congr (row (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl _, .eqRefl _, move]
  exact (GaussianRationalFiniteSum.sum_succ _ r _).eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) ((GaussianBarnesCanonicalHigherDerivative.body_at
      (center A B) B (succ N) zero r).eqTrans ((derivative_at A B (succ N+r) hA hB).eqTrans e)))

private theorem interval_zero (A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] bounded (value A B N zero) (budget B*zero) (denominator A B N zero) :=
  bound_congr (zero_at A B N).eqSymm (mul_zero _).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero _ (denominator_positive A B N zero hA))

private theorem interval_step (A B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A)
    (ih : Γ ⊢[PRAAx] bounded (value A B N r) (budget B*r) (denominator A B N r)) :
    Γ ⊢[PRAAx] bounded (value A B N (succ r)) (budget B*succ r) (denominator A B N (succ r)) := by
  let C := budget B
  let a := shiftedNumerator A B N
  let k := shiftedNumerator A B (N+succ r)
  let D := denominator A B N r
  let E := k*k
  let F := denominator A B N (succ r)
  have hA := le_trans hB hBA
  have hk : Γ ⊢[PRAAx] le one k := shifted_positive A B (N+succ r) hA
  have hD := denominator_positive A B N r hA
  have hE := positive_product k k hk hk
  have hF := denominator_positive A B N (succ r) hA
  have single : Γ ⊢[PRAAx] bounded (row A B (N+succ r)) C E :=
    bound_congr (.eqRefl _) (congrMul (.eqRefl _) (LeanProofs.IPRA.Common.pw_two B))
      (LeanProofs.IPRA.Common.pw_two k) (square_bound A B (N+succ r) hB hBA)
  have added := bounded_sum (value A B N r) (row A B (N+succ r)) (C*r) D C E hD hE ih single
  have compare : Γ ⊢[PRAAx] le ((C*r*E+C*D)*F) ((C*succ r)*(D*E)) := by
    apply le_of_eq_add (d := C*a*a*k*B)
    dsimp only [a,D,E,F,k,denominator,shiftedNumerator]
    ipra_ring
  exact bound_congr (succ_at A B N r hA hB).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hE) hF compare added)

theorem interval_bound (A B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (value A B N r) (budget B*r) (denominator A B N r) := by
  let sh (u : PTm n) := Syn.shift u
  have all : Γ ⊢[PRAAx] .all
      (bounded (value (sh A) (sh B) (sh N) (var 0)) (budget (sh B)*var 0)
        (denominator (sh A) (sh B) (sh N) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [GaussianRationalMetric.subst_bounded,subst_value,subst_budget,subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using
          interval_zero A B N (le_trans hB hBA)
    · have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,one] using hB.shift
      have hBA' : Γ.map Fm.shift ⊢[PRAAx] le (sh B) (sh A) := by simpa [Fm.shift,Syn.shift,sh] using hBA.shift
      simpa only [GaussianRationalMetric.subst_bounded,subst_value,subst_budget,subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
          interval_step (sh A) (sh B) (sh N) (var 0) hB'.wk hBA'.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_bounded,subst_value,subst_budget,subst_denominator,
    PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE r

theorem tail_bound (A B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (value A B N r) (two*B) (shiftedNumerator A B N) := by
  have hA := le_trans hB hBA
  have compare : Γ ⊢[PRAAx] le ((budget B*r)*shiftedNumerator A B N) ((two*B)*denominator A B N r) := by
    apply le_of_eq_add (d := two*B*shiftedNumerator A B N*(A+N*B))
    dsimp only [budget,denominator,shiftedNumerator]
    ipra_ring
  exact bounded_radius_mono _ _ _ _ _ (denominator_positive A B N r hA) (shifted_positive A B N hA)
    compare (interval_bound A B N r hB hBA)

theorem actual_Barnes_positive_cubic_logarithm_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let A := var 0
     let B := var 1
     let N := var 2
     let r := var 3
     (le one B ⋏ le B A) ⟶ bounded (value A B N r) (two*B) (shiftedNumerator A B N)) :=
  closeUniv 4 (.impI (tail_bound _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmTail

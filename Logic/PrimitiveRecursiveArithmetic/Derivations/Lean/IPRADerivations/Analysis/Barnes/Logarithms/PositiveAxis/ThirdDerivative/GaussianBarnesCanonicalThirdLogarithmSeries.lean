import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdLogarithmTail
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialProduct
import IPRADerivations.Core.CommonLemmas

/-!
# Positive-axis partial sums of the original Barnes cubic logarithmic rows

Every nonempty partial sum dominates the strictly positive first row
on x>0. On x≥1 the sum is bounded by 2/x²+2/x, uniformly in the
number of rows. This gives the finite positivity and decay estimates
used in the Vignéras argument.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHigherDerivative (body body_at)
open GaussianBarnesCanonicalThirdLogarithmRows (center derivative_at row shiftedNumerator square_bound positive_floor)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianPositiveRealArithmetic (positive positive_congr positiveTerms positive_sum)
open RationalArgmin (rationalLE rationalLE_congr)
open ConciseIPRA.PTm (succ zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (A B r : PTm n) : PTm n :=
  GaussianBarnesCanonicalHigherDerivative.value (center A B) B zero zero r

def decayNumerator (A B : PTm n) : PTm n := two*(B*B)+two*B*A

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (A B r : PTm n) :
    Syn.subst σ (value A B r) = value (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ r) := by simp [value]

@[simp] theorem subst_decayNumerator {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (decayNumerator A B) = decayNumerator (Syn.subst σ A) (Syn.subst σ B) := by
  simp [decayNumerator,two,one]

private theorem tail_readback (A B r : PTm n) :
    Γ ⊢[PRAAx] sum (shiftBody body) r (GaussianBarnesCanonicalHigherTail.data (center A B) B zero zero) ≐
      GaussianBarnesCanonicalThirdLogarithmTail.value A B zero r := by
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  let a := Syn.shift A
  let b := Syn.shift B
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift r) :: Γ.map Fm.shift
  have left := body_at (Γ := Δ) (center a b) b zero zero (succ i)
  have right := body_at (Γ := Δ) (center a b) b one zero i
  have idx : Δ ⊢[PRAAx] succ (zero+succ i) ≐ succ (one+i) := by ipra_ring
  have ident : Δ ⊢[PRAAx] GaussianBarnesCanonicalHigherRows.derivative (center a b) b (succ (zero+succ i)) zero ≐
      GaussianBarnesCanonicalHigherRows.derivative (center a b) b (succ (one+i)) zero := by
    ipra_congr (GaussianBarnesCanonicalHigherRows.derivative (var 0) (var 1) (var 2) (var 3) : PTm 4)
      with [.eqRefl _,.eqRefl _,idx,.eqRefl _]
  simpa only [GaussianRationalFiniteSum.termsEqual,Syn.shift,a,b,i,Δ,
    GaussianBarnesCanonicalThirdLogarithmRows.subst_center,GaussianBarnesCanonicalHigherTail.subst_data,
    inst2_shiftBody,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      left.eqTrans (ident.eqTrans right.eqSymm)

theorem split_first (A B r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] value A B (succ r) ≐ qadd (row A B zero) (GaussianBarnesCanonicalThirdLogarithmTail.value A B zero r) := by
  have first := body_at (Γ := Γ) (center A B) B zero zero zero
  have ident : Γ ⊢[PRAAx] GaussianBarnesCanonicalHigherRows.derivative (center A B) B (succ (zero+zero)) zero ≐
      GaussianBarnesCanonicalHigherRows.derivative (center A B) B (succ zero) zero := by
    ipra_congr (GaussianBarnesCanonicalHigherRows.derivative (var 0) (var 1) (var 2) (var 3) : PTm 4)
      with [.eqRefl _,.eqRefl _,congrSucc (zero_add zero),.eqRefl _]
  exact (GaussianRationalFiniteSum.sum_shift_first body r _).eqTrans
    (qadd_congr (first.eqTrans (ident.eqTrans (derivative_at A B zero hA hB))) (tail_readback A B r))

theorem interval_positive (A B N r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] positive (GaussianBarnesCanonicalHigherDerivative.value (center A B) B N zero r) := by
  let x := GaussianBarnesCanonicalHigherTail.data (center A B) B N zero
  apply positive_sum body r x
  refine .allI (.impI ?_)
  let a := Syn.shift A
  let b := Syn.shift B
  let i : PTm (n+1) := var 0
  let Δ := lt i (Syn.shift r) :: Γ.map Fm.shift
  have aPos : Δ ⊢[PRAAx] le one a := by simpa [Δ,Fm.shift,Syn.shift,a,one] using hA.shift.wk
  have bPos : Δ ⊢[PRAAx] le one b := by simpa [Δ,Fm.shift,Syn.shift,b,one] using hB.shift.wk
  have e := (body_at (Γ := Δ) (center a b) b (Syn.shift N) zero i).eqTrans
    (derivative_at a b (Syn.shift N+i) aPos bPos)
  simpa only [positiveTerms,Syn.shift,a,b,i,Δ,x,GaussianBarnesCanonicalThirdLogarithmRows.subst_center,
    GaussianBarnesCanonicalHigherTail.subst_data,ConciseIPRA.PTm.subst_zero] using
      positive_congr e.eqSymm (positive_floor a b (Syn.shift N+i) aPos bPos).andE₁

/-- The first original row supplies a uniform strictly positive real floor. -/
theorem first_floor (A B r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE (fstT (row A B zero)) (fstT (value A B (succ r))) := by
  let t := GaussianBarnesCanonicalThirdLogarithmTail.value A B zero r
  let f := row A B zero
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical f :=
    GaussianRationalHorner.ofGaussian_canonical _ _
      (GaussianBarnesCanonicalThirdLogarithmRows.denominator_positive A B zero hA)
  have lower := GaussianPositiveExponentialProduct.scalar_le_add (fstT f) (fstT t)
    hc.andE₂.andE₁ (interval_positive A B one r hA hB).andE₂
  have e := (congrFst (split_first A B r hA hB)).eqTrans (RationalGaussianRealPart.real_add f t)
  exact rationalLE_congr (.eqRefl _) e.eqSymm lower

theorem decay_bound (A B r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (value A B (succ r)) (decayNumerator A B) (A*A) := by
  let f := row A B zero
  let t := GaussianBarnesCanonicalThirdLogarithmTail.value A B zero r
  let c := shiftedNumerator A B zero
  have hA := le_trans hB hBA
  have hc : Γ ⊢[PRAAx] c ≐ A := by dsimp only [c,shiftedNumerator]; ipra_ring
  have C : Γ ⊢[PRAAx] bounded f (two*(B*B)) (A*A) :=
    bound_congr (.eqRefl _) (congrMul (.eqRefl _) (LeanProofs.IPRA.Common.pw_two B))
      ((LeanProofs.IPRA.Common.pw_two c).eqTrans (congrMul hc hc)) (square_bound A B zero hB hBA)
  have D : Γ ⊢[PRAAx] bounded t (two*B) A :=
    bound_congr (.eqRefl _) (.eqRefl _) hc (GaussianBarnesCanonicalThirdLogarithmTail.tail_bound A B zero r hB hBA)
  have total := bounded_sum f t (two*(B*B)) (A*A) (two*B) A (positive_product _ _ hA hA) hA C D
  have compare : Γ ⊢[PRAAx] le ((((two*(B*B)))*A+(two*B)*(A*A))*(A*A))
      (decayNumerator A B*((A*A)*A)) :=
    le_congr (.eqRefl _) (by dsimp only [decayNumerator]; ipra_ring) (le_refl _)
  exact bound_congr (split_first A B r hA hB).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hA hA) hA)
      (positive_product _ _ hA hA) compare total)

theorem actual_Barnes_positive_cubic_logarithm_partial_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (let A := var 0
     let B := var 1
     let r := var 2
     (le one B ⋏ le B A) ⟶
       rationalLE (fstT (row A B zero)) (fstT (value A B (succ r))) ⋏
       bounded (value A B (succ r)) (decayNumerator A B) (A*A)) :=
  closeUniv 3 (.impI (.andI (first_floor _ _ _ (le_trans Prf.hyp0.andE₁ Prf.hyp0.andE₂) Prf.hyp0.andE₁)
    (decay_bound _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdLogarithmSeries

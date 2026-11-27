import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderCrossedRectangles
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumSegments

/-!
# Exact subinterval splits for the three reflected-grid sums

In each of the centered Bernoulli, reflected weight, and paired
product sums, splitting uses the original grid with its index
increased by the prefix length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCrossedSegments

open_ipra
open GaussianStirlingAllOrderBoxProductGap (sampleAt weightAt)
open GaussianStirlingAllOrderCrossedCells (segmentData bernoulliBody reflectedBody bernoulli_at reflected_at
  subst_sampleAt subst_weightAt)
open GaussianStirlingAllOrderCrossedRectangles (bernoulliSum reflectedSum pairedSum)
open RationalAlgebra (add_congr multiply_congr)
open RationalArgmin (rationalEq_congr)
open RationalArithmetic (add)
open RationalCrossedProductSums (productBody product_at)
open RationalFiniteSum (term sum termwiseEq sum_ext)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem sample_shift (m : ℕ) (i q A B S t K : PTm n) :
    Γ ⊢[PRAAx] term (bernoulliBody m) (K+i) (segmentData q A B S t) ≐
      term (bernoulliBody m) i (segmentData q A B S (t+K)) := by
  have middle : Γ ⊢[PRAAx] sampleAt m S (t+(K+i)) ≐ sampleAt m S (t+K+i) := by
    simpa only [subst_sampleAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (sampleAt m (var 0) (var 1) : PTm 2)
        (σ := ![S,t+(K+i)]) (σ' := ![S,t+K+i])
        (fun v => by fin_cases v; exact .eqRefl _; exact (LeanProofs.IPRA.add_assoc t K i).eqSymm)
  exact (bernoulli_at m (K+i) q A B S t).eqTrans (middle.eqTrans (bernoulli_at m i q A B S (t+K)).eqSymm)

private theorem weight_shift (i q A B S t K : PTm n) :
    Γ ⊢[PRAAx] term reflectedBody (K+i) (segmentData q A B S t) ≐
      term reflectedBody i (segmentData q A B S (t+K)) := by
  have middle : Γ ⊢[PRAAx] weightAt q A B S (t+(K+i)) ≐ weightAt q A B S (t+K+i) := by
    simpa only [subst_weightAt,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (weightAt (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
        (σ := ![q,A,B,S,t+(K+i)]) (σ' := ![q,A,B,S,t+K+i])
        (fun v => by
          fin_cases v
          · exact .eqRefl q
          · exact .eqRefl A
          · exact .eqRefl B
          · exact .eqRefl S
          · exact (LeanProofs.IPRA.add_assoc t K i).eqSymm)
  exact (reflected_at (K+i) q A B S t).eqTrans (middle.eqTrans (reflected_at i q A B S (t+K)).eqSymm)

private theorem product_shift (m : ℕ) (i q A B S t K : PTm n) :
    Γ ⊢[PRAAx] term (productBody (bernoulliBody m) reflectedBody) (K+i) (segmentData q A B S t) ≐
      term (productBody (bernoulliBody m) reflectedBody) i (segmentData q A B S (t+K)) := by
  rw [product_at (bernoulliBody m) reflectedBody (K+i) (segmentData q A B S t),
    product_at (bernoulliBody m) reflectedBody i (segmentData q A B S (t+K))]
  exact multiply_congr (sample_shift m i q A B S t K) (weight_shift i q A B S t K)

private theorem split_with (body : PTm 2) (q A B S t K L : PTm n)
    (reader : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (i q A B S t K : PTm l),
      Δ ⊢[PRAAx] term body (K+i) (segmentData q A B S t) ≐ term body i (segmentData q A B S (t+K))) :
    Γ ⊢[PRAAx] sum body (K+L) (segmentData q A B S t) ≐
      add (sum body K (segmentData q A B S t)) (sum body L (segmentData q A B S (t+K))) := by
  let x := segmentData q A B S t
  let y := segmentData q A B S (t+K)
  have h : Γ ⊢[PRAAx] termwiseEq (offB body) body L (pairT K x) y := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh L) :: Γ.map Fm.shift
    have e := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) body (sh K) i
      (segmentData (sh q) (sh A) (sh B) (sh S) (sh t))).eqTrans
        (reader (Δ := Δ) i (sh q) (sh A) (sh B) (sh S) (sh t) (sh K))
    simpa only [sh,Syn.shift,x,y,i,Δ,subst_pairT,PTm.subst_add,term,
      GaussianStirlingAllOrderCrossedCells.subst_segmentData] using rationalEq_congr e.eqSymm (.eqRefl _) (.eqRefl _)
  exact (RationalSumSegments.split body K L x).eqTrans (add_congr (.eqRefl _) (sum_ext _ _ _ _ _ h))

theorem bernoulli_split (m : ℕ) (q A B S t K L : PTm n) :
    Γ ⊢[PRAAx] bernoulliSum m q A B S t (K+L) ≐
      add (bernoulliSum m q A B S t K) (bernoulliSum m q A B S (t+K) L) :=
  split_with _ _ _ _ _ _ _ _ (sample_shift m)

theorem reflected_split (q A B S t K L : PTm n) :
    Γ ⊢[PRAAx] reflectedSum q A B S t (K+L) ≐
      add (reflectedSum q A B S t K) (reflectedSum q A B S (t+K) L) :=
  split_with _ _ _ _ _ _ _ _ weight_shift

theorem paired_split (m : ℕ) (q A B S t K L : PTm n) :
    Γ ⊢[PRAAx] pairedSum m q A B S t (K+L) ≐ add (pairedSum m q A B S t K) (pairedSum m q A B S (t+K) L) :=
  split_with _ _ _ _ _ _ _ _ (product_shift m)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCrossedSegments

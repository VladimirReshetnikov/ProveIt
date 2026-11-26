import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderCrossedCells

/-!
# The reflected product reader uses the original periodic panel rows

Each product in a reflected half-grid is exactly the sum of the two
mirror samples of the original periodic panel integrand. The
identification uses the same mesh and the original integer panel
offset, at every internal index and fixed Bernoulli order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedReadback

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (positive_product)
open GaussianStirlingAllOrderBoxProductGap (sampleAt weightAt)
open GaussianStirlingAllOrderCrossedCells (segmentData bernoulliBody reflectedBody bernoulli_at reflected_at)
open GaussianStirlingAllOrderKernel (row offset reflected_rows)
open GaussianStirlingAllOrderPairedRefinement (mesh start)
open GaussianStirlingAllOrderPairedWeight (pairWeight subst_pairWeight)
open RationalAlgebra (multiply_congr)
open RationalArithmetic (add multiply)
open RationalCrossedProductSums (productBody product_at)
open RationalFiniteSum (term)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_paired_term (m : ℕ) (q A B S k t i : PTm n)
    (hS : Γ ⊢[PRAAx] le one S) (hr : Γ ⊢[PRAAx] le (t+i) (S*num 8)) :
    Γ ⊢[PRAAx] term (productBody (bernoulliBody m) reflectedBody) i (segmentData q (A+B*k) B S t) ≐
      add (row m q A B (S*num 8) k (t+i)) (row m q A B (S*num 8) k (monus (S*num 8) (t+i))) := by
  let U := A+B*k
  let M := S*num 8
  let r := t+i
  have positive : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have l : Γ ⊢[PRAAx] mesh B S ≐ B*M := by dsimp [M,mesh]; ipra_ring
  have a : Γ ⊢[PRAAx] start U S ≐ offset A B M k := by dsimp [U,M,start,offset]; ipra_ring
  have w : Γ ⊢[PRAAx] weightAt q U B S r ≐ pairWeight q (B*M) (offset A B M k) (B*r) := by
    simpa only [weightAt,subst_pairWeight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (pairWeight (var 0) (var 1) (var 2) (var 3) : PTm 4)
        (σ := ![q,mesh B S,start U S,B*r]) (σ' := ![q,B*M,offset A B M k,B*r])
        (fun j => by fin_cases j; exact .eqRefl q; exact l; exact a; exact .eqRefl (B*r))
  rw [product_at (bernoulliBody m) reflectedBody i (segmentData q U B S t)]
  exact (multiply_congr (bernoulli_at m i q U B S t) ((reflected_at i q U B S t).eqTrans w)).eqTrans
    (reflected_rows m q A B M k r positive hr).eqSymm

theorem actual_original_reflected_panel_product_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((le one (var 3) ⋏ le (var 5+var 6) (var 3*num 8)) ⟶
        term (productBody (bernoulliBody m) reflectedBody) (var 6)
          (segmentData (var 0) (var 1+var 2*var 4) (var 2) (var 3) (var 5)) ≐
        add (row m (var 0) (var 1) (var 2) (var 3*num 8) (var 4) (var 5+var 6))
          (row m (var 0) (var 1) (var 2) (var 3*num 8) (var 4) (monus (var 3*num 8) (var 5+var 6)))) :=
  closeUniv 7 (.impI (original_paired_term m _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedReadback

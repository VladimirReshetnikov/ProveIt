import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareInterval
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference

/-!
# Exact inverse-square telescope with a fixed additional denominator

The sharp interval estimate and the bound for an arbitrary tail use
the same finite proof as the unscaled inverse-square sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianScaledReciprocalSquareInterval

open_ipra
open GaussianRationalFiniteSum (sum sum_shift_first)
open GaussianRationalMetric (bounded)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rows (t : PTm 2) (N C D x : PTm n) : Fm PTm n := .all
  (bounded (inst2 t (var 0) (Syn.shift x)) (Syn.shift C)
    (Syn.shift D*(succ (Syn.shift N+var 0)*succ (Syn.shift N+var 0))))

@[simp] theorem subst_rows {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (N C D x : PTm n) :
    (rows t N C D x).subst σ = rows t (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by
  simp [rows,Syn.subst_shift,Syn.shift_subst]

theorem row_at (t : PTm 2) (N C D x i : PTm n) (h : Γ ⊢[PRAAx] rows t N C D x) :
    Γ ⊢[PRAAx] bounded (inst2 t i x) C (D*(succ (N+i)*succ (N+i))) :=
  GaussianReciprocalSquareInterval.scaled_row_bound_at t N C D x i h

theorem interval_bound (t : PTm 2) (N r C D x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rows t N C D x) :
    Γ ⊢[PRAAx] bounded (sum t r x) (C*r) (D*GaussianReciprocalSquareInterval.denominator N r) :=
  GaussianReciprocalSquareInterval.scaled_interval_bound t N r C D x hN hD h

theorem tail_bound (t : PTm 2) (N r C D x : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rows t N C D x) :
    Γ ⊢[PRAAx] bounded (sum t r x) C (D*N) :=
  GaussianReciprocalSquareInterval.scaled_tail_bound t N r C D x hN hD h

/-- Include the first row of a reciprocal-square sum with a fixed common denominator. -/
theorem full_prefix_bound (t : PTm 2) (r C D x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] rows t zero C D x) : Γ ⊢[PRAAx] bounded (sum t (succ r) x) (two*C) D := by
  have shifted : Γ ⊢[PRAAx] rows (shiftBody t) one C D x := by
    refine .allI ?_
    let sh (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have hs : Δ ⊢[PRAAx] rows t zero (sh C) (sh D) (sh x) := by
      simpa only [Δ,Fm.shift,subst_rows,Syn.shift,sh,ConciseIPRA.PTm.subst_zero] using h.shift
    have idx : Δ ⊢[PRAAx] succ (zero+succ i) ≐ succ (one+i) := by ipra_ring
    have b := row_at t zero (sh C) (sh D) (sh x) (succ i) hs
    simpa only [rows,inst2_shiftBody,Syn.shift,sh,Δ,i,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
      using bound_congr (.eqRefl _) (.eqRefl _) (congrMul (.eqRefl _) (congrMul idx idx)) b
  have head : Γ ⊢[PRAAx] bounded (inst2 t zero x) C D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (row_at t zero C D x zero h)
  have tail : Γ ⊢[PRAAx] bounded (sum (shiftBody t) r x) C D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (tail_bound (shiftBody t) one r C D x (le_refl one) hD shifted)
  exact bound_congr (sum_shift_first t r x).eqSymm (by ipra_ring) (.eqRefl _)
    (bounded_sum_same _ _ C C D hD head tail)

theorem actual_scaled_reciprocal_square_tail_closed (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let N := var 0
       let r := var 1
       let C := var 2
       let D := var 3
       let x := var 4
       (le one N ⋏ (le one D ⋏ rows t N C D x)) ⟶ bounded (sum t r x) C (D*N)) :=
  closeUniv 5 (.impI (tail_bound t _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianScaledReciprocalSquareInterval

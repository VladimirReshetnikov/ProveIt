import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Gcd

/-!
# Finite reciprocal-square tails with denominators cleared

Packet `analysis/barnes_g_ipra_2026-11-16`, `lem:canonical-tail` and
`eq:qtail`. If `A k² e(k, x) ≤ C` beyond a positive starting index `N`,
finite induction proves
`A N (N+r) ∑_{i<r} e(N+i+1, x) ≤ r C`, hence
`A N ∑_{i<r} e(N+i+1, x) ≤ C`.
The Barnes coefficient is the exact substitution `A = 3`, `C = 2 R³ D`.
Here `D` may be a common denominator selected for the finite query.
The pointwise logarithmic-factor estimate is an explicit hypothesis.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ReciprocalSquareTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Variables `0 = i`, `1 = N`, `2 = x`. -/
def errorBody (e : PR 2) : PTm 3 := ap2 e (succ (var 1 + var 0)) (var 2)

/-- The finite error sum from `N + 1` through `N + r`. -/
def tailSum (e : PR 2) (N r x : PTm n) : PTm n := ap3 (sum2F (errorBody e)) r N x

@[simp] theorem subst_tailSum {m : ℕ} (σ : Fin n → PTm m)
    (e : PR 2) (N r x : PTm n) :
    Syn.subst σ (tailSum e N r x) =
      tailSum e (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ x) := by
  simp [tailSum]

theorem tailSum_zero (e : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] tailSum e N zero x ≐ zero := sum2_zero _ _ _

theorem tailSum_succ (e : PR 2) (N r x : PTm n) :
    Γ ⊢[PRAAx] tailSum e N (succ r) x ≐ tailSum e N r x + ap2 e (succ (N + r)) x := by
  simpa [tailSum, errorBody, inst3] using sum2_succ (Γ := Γ) (errorBody e) r N x

private theorem cancel_positive {c a b : PTm n} (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] le (c * a) (c * b)) : Γ ⊢[PRAAx] le a b := by
  have ce : Γ ⊢[PRAAx] c ≐ succ (monus c one) :=
    (eq_add_of_le hc).eqTrans (by ipra_ring)
  exact mul_le_cancel (le_congr (congrMul ce (.eqRefl _)) (congrMul ce (.eqRefl _)) h)

/-- The polynomial induction step in the reciprocal-square comparison. -/
theorem sharp_step {A N r C S E : PTm n} (hN : Γ ⊢[PRAAx] le one N)
    (ih : Γ ⊢[PRAAx] le (A * N * (N + r) * S) (r * C))
    (point : Γ ⊢[PRAAx] le (A * succ (N + r) * succ (N + r) * E) C) :
    Γ ⊢[PRAAx] le (A * N * succ (N + r) * (S + E)) (succ r * C) := by
  let t := N + r
  have ht : Γ ⊢[PRAAx] le one t := le_trans hN (le_add_right N r)
  have i := natEq (eq_add_of_le ih)
  have p := natEq (eq_add_of_le point)
  have scaled : Γ ⊢[PRAAx]
      le (t * (succ t * (A * N * succ t * (S + E))))
        (t * (succ t * (succ r * C))) := by
    refine le_of_eq_add (d :=
      succ t * succ t * monus (r * C) (A * N * t * S) +
      N * t * monus C (A * succ t * succ t * E) + N * C) ?_
    apply deriveNat
    dsimp only [t] at *
    ipra_simps
    linear_combination (𝔞(N) + 𝔞(r) + 1) ^ 2 * i + 𝔞(N) * (𝔞(N) + 𝔞(r)) * p
  exact mul_le_cancel (cancel_positive ht scaled)

/-- The pointwise estimate beyond the starting index. -/
def majorant (e : PR 2) (A N C x : PTm n) : Fm PTm n :=
  .all (le
    (Syn.shift A * succ (Syn.shift N + var 0) * succ (Syn.shift N + var 0) *
      ap2 e (succ (Syn.shift N + var 0)) (Syn.shift x))
    (Syn.shift C))

@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m)
    (e : PR 2) (A N C x : PTm n) :
    (majorant e A N C x).subst σ =
      majorant e (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ x) := by
  simp only [majorant, Fm.subst_all, subst_le, PTm.subst_mul, PTm.subst_add,
    subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero,
    Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

@[simp] theorem shift_majorant (e : PR 2) (A N C x : PTm n) :
    Fm.shift (majorant e A N C x) =
      majorant e (Syn.shift A) (Syn.shift N) (Syn.shift C) (Syn.shift x) :=
  subst_majorant _ _ _ _ _ _

/-- The sharp finite tail comparison, with all length and query parameters
kept internal to the object theory. -/
theorem sharp (e : PR 2) (A N r C x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hm : Γ ⊢[PRAAx] majorant e A N C x) :
    Γ ⊢[PRAAx] le (A * N * (N + r) * tailSum e N r x) (r * C) := by
  have all : Γ ⊢[PRAAx] .all
      (le (Syn.shift A * Syn.shift N * (Syn.shift N + var 0) *
          tailSum e (Syn.shift N) (var 0) (Syn.shift x))
        (var 0 * Syn.shift C)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, PTm.subst_mul, PTm.subst_add, subst_tailSum,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      have eqL : Γ ⊢[PRAAx] A * N * (N + zero) * tailSum e N zero x ≐ zero :=
        (congrMul (.eqRefl _) (tailSum_zero e N x)).eqTrans (mul_zero _)
      exact le_congr eqL.eqSymm (zero_mul C).eqSymm (le_refl zero)
    · simp only [subst_le, PTm.subst_mul, PTm.subst_add, subst_tailSum,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have shifted : Γ.map Fm.shift ⊢[PRAAx]
          majorant e (Syn.shift A) (Syn.shift N) (Syn.shift C) (Syn.shift x) := by
        simpa only [shift_majorant] using hm.shift
      have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hN.shift
      have point := Prf.allE (var 0) shifted
      have step := sharp_step (A := Syn.shift A) (N := Syn.shift N) (r := var 0)
        (C := Syn.shift C) (S := tailSum e (Syn.shift N) (var 0) (Syn.shift x))
        (E := ap2 e (succ (Syn.shift N + var 0)) (Syn.shift x))
        positive.wk Prf.hyp0 (by simpa [majorant] using point.wk)
      exact le_congr
        ((congrMul (congrMul (.eqRefl _) (add_succ _ _)) (.eqRefl _)).eqTrans
          (congrMul (.eqRefl _) (tailSum_succ e _ _ _))).eqSymm
        (.eqRefl _) step
  simpa only [subst_le, PTm.subst_mul, PTm.subst_add, subst_tailSum,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r all

/-- The uniform cleared bound `A N ∑ e ≤ C`. -/
theorem uniform (e : PR 2) (A N r C x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hm : Γ ⊢[PRAAx] majorant e A N C x) :
    Γ ⊢[PRAAx] le (A * N * tailSum e N r x) C := by
  have s := sharp e A N r C x hN hm
  have hright := mul_le_mul_right (Γ := Γ) C (le_add_left r N)
  have scaled : Γ ⊢[PRAAx] le ((N + r) * (A * N * tailSum e N r x)) ((N + r) * C) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_trans s hright)
  exact cancel_positive (le_trans hN (le_add_right N r)) scaled

/-- The sharp comparison at ordered endpoints, with the canonical finite
sum from `N + 1` through `M`. -/
theorem sharp_between (e : PR 2) (A N M C x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hm : Γ ⊢[PRAAx] majorant e A N C x)
    (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (A * N * M * tailSum e N (monus M N) x) (monus M N * C) := by
  have endpoint := (eq_add_of_le order).eqSymm
  exact le_congr (congrMul (congrMul (.eqRefl _) endpoint) (.eqRefl _)) (.eqRefl _)
    (sharp e A N (monus M N) C x hN hm)

/-- The exact cleared constant in Barnes `eq:qtail`. -/
theorem barnes_qtail (e : PR 2) (N r R D x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N)
    (hm : Γ ⊢[PRAAx] majorant e (num 3) N (two * R * R * R * D) x) :
    Γ ⊢[PRAAx] le (num 3 * N * tailSum e N r x) (two * R * R * R * D) :=
  uniform e _ _ _ _ _ hN hm

/-- Variables `0 = A`, `1 = N`, `2 = r`, `3 = C`, `4 = x`. -/
abbrev sharpFormula (e : PR 2) : Fm PTm 5 :=
  le one (var 1) ⟶ majorant e (var 0) (var 1) (var 3) (var 4) ⟶
    le (var 0 * var 1 * (var 1 + var 2) * tailSum e (var 1) (var 2) (var 4)) (var 2 * var 3)

theorem sharp_closed (e : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (sharpFormula e) :=
  closeUniv 5 (.impI (.impI (sharp e _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

abbrev uniformFormula (e : PR 2) : Fm PTm 5 :=
  le one (var 1) ⟶ majorant e (var 0) (var 1) (var 3) (var 4) ⟶
    le (var 0 * var 1 * tailSum e (var 1) (var 2) (var 4)) (var 3)

theorem uniform_closed (e : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (uniformFormula e) :=
  closeUniv 5 (.impI (.impI (uniform e _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Variables `0 = A`, `1 = N`, `2 = M`, `3 = C`, `4 = x`. -/
abbrev endpointsFormula (e : PR 2) : Fm PTm 5 :=
  le one (var 1) ⟶ majorant e (var 0) (var 1) (var 3) (var 4) ⟶ le (var 1) (var 2) ⟶
    (le (var 0 * var 1 * var 2 * tailSum e (var 1) (monus (var 2) (var 1)) (var 4))
      (monus (var 2) (var 1) * var 3) ⋏
     le (var 0 * var 1 * tailSum e (var 1) (monus (var 2) (var 1)) (var 4)) (var 3))

theorem reciprocal_square_tail (e : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (endpointsFormula e) :=
  closeUniv 5 (.impI (.impI (.impI (.andI
    (sharp_between e _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0)
    (uniform e _ _ _ _ _ Prf.hyp1.wk Prf.hyp1)))))

#print axioms sharp_closed
#print axioms uniform_closed
#print axioms reciprocal_square_tail
#print axioms barnes_qtail

end LeanProofs.IPRA.Analysis.ReciprocalSquareTail

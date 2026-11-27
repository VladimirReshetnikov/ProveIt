import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.Core.CommonLemmas

/-!
# Binomial coefficients in iPRA

`C(n, k) = n! div (k! (n ∸ k)!)`. One induction on `n` proves that the division is
exact for every `k ≤ n`. The bounded sum `∑_{k≤n} (n! mod k!(n−k)!) = 0` plays the
role of `∀ k ≤ n`, and the step proves Pascal's rule along the way:

* `binom_spec`: `k ≤ n → n! = k! (n − k)! C(n, k)`;
* `pascal`: `j < n → C(n + 1, j + 1) = C(n, j) + C(n, j + 1)`;
* `binom_zero`, `binom_self`: `C(n, 0) = C(n, n) = 1`.

These are the binomial coefficients of the packets on the central binomial
coefficient (`pnt_ipra_constructive_2026-11-14`, `von_mangoldt_totient_ipra_2026-11-15`),
Catalan numbers (`lagrange_inversion_ipra`) and Bell numbers (`bell_numbers_ipra`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Binomial

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos eq_succ_pred)

variable {m : ℕ} {Γ : List (Fm PTm m)}

/-! ## Division by positive terms -/

alias pos_mul := Common.pos_mul

theorem rem_zero_of_eq {x D w : PTm m} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (h : Γ ⊢[PRAAx] x ≐ D * w) :
    Γ ⊢[PRAAx] rem x D ≐ zero :=
  (congrAp2 remF (.eqRefl _) hD).eqTrans (dvd_of_eq (h.eqTrans (congrMul hD (.eqRefl _))))

theorem eq_of_rem_zero {x D : PTm m} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (h : Γ ⊢[PRAAx] rem x D ≐ zero) :
    Γ ⊢[PRAAx] x ≐ D * quo x D := by
  have e := eq_of_dvd (d' := pred D) ((congrAp2 remF (.eqRefl _) hD).eqSymm.eqTrans h)
  exact e.eqTrans (congrMul hD.eqSymm (congrAp2 quoF (.eqRefl _) hD.eqSymm))

theorem quo_of_eq {x D w : PTm m} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (h : Γ ⊢[PRAAx] x ≐ D * w) :
    Γ ⊢[PRAAx] quo x D ≐ w :=
  Division.quo_eq_mul hD h

/-! ## The coefficients -/

/-- `k! (n ∸ k)!`. -/
abbrev bden (n k : PTm m) : PTm m := fact k * fact (monus n k)
/-- `C(n, k)`. -/
abbrev binom (n k : PTm m) : PTm m := quo (fact n) (bden n k)

theorem bden_pos (n k : PTm m) : Γ ⊢[PRAAx] bden n k ≐ succ (pred (bden n k)) :=
  pos_mul (fact_pos k) (fact_pos _)

/-- The exactness test `n! mod k! (n ∸ k)!`; variables `0 = k`, `1 = n`. -/
abbrev rBody : PTm 2 := rem (fact (var 1)) (bden (var 1) (var 0))

theorem inst2_r (k n : PTm m) : inst2 rBody k n = rem (fact n) (bden n k) := by simp [inst2]

/-- `T(n) = ∑_{k≤n} (n! mod k!(n ∸ k)!)`. -/
abbrev T (n : PTm m) : PTm m := ap2 (sumF rBody) (succ n) n

/-! ## The Pascal step -/

/-- If `j < n` and both `k!(n − k)!` for `k = j, j + 1` divide `n!`, then
`(n + 1)! = (j + 1)! (n − j)! (C(n, j) + C(n, j + 1))`. -/
theorem pascal_step {n j : PTm m} (hj : Γ ⊢[PRAAx] lt j n)
    (h₁ : Γ ⊢[PRAAx] rem (fact n) (bden n j) ≐ zero)
    (h₂ : Γ ⊢[PRAAx] rem (fact n) (bden n (succ j)) ≐ zero) :
    Γ ⊢[PRAAx] fact (succ n) ≐ bden (succ n) (succ j) * (binom n j + binom n (succ j)) := by
  have e₁ := eq_of_rem_zero (bden_pos n j) h₁
  have e₂ := eq_of_rem_zero (bden_pos n (succ j)) h₂
  -- n = S j + d with d = n ∸ S j, so n ∸ j = S d and (S n) ∸ (S j) = S d.
  have wn := eq_add_of_le hj
  have hnj : Γ ⊢[PRAAx] monus n j ≐ succ (monus n (succ j)) := by
    refine (congrMonus (wn.eqTrans ((succ_add _ _).eqTrans (add_succ _ _).eqSymm)) (.eqRefl _)).eqTrans ?_
    exact add_monus' _ _
  have g₁ : Γ ⊢[PRAAx] fact (monus n j) ≐ fact (succ (monus n (succ j))) := congrAp2 factF hnj (.eqRefl _)
  have g₂ : Γ ⊢[PRAAx] fact (monus (succ n) (succ j)) ≐ fact (succ (monus n (succ j))) :=
    congrAp2 factF ((succ_monus_succ _ _).eqTrans hnj) (.eqRefl _)
  refine withEq (fact_succ n zero) fun f₁ => withEq e₁ fun f₂ => withEq e₂ fun f₃ => ?_
  refine withEq (fact_succ j zero) fun f₄ => withEq (fact_succ (monus n (succ j)) zero) fun f₅ => ?_
  refine withEq g₁ fun f₆ => withEq g₂ fun f₇ => withEq wn fun f₈ => ?_
  apply deriveNat; ipra_simps
  set FSd := Groth.ι (Q.mk Γ (fact (succ (monus n (succ j)))))
  set FSj := Groth.ι (Q.mk Γ (fact (succ j)))
  set Fj := Groth.ι (Q.mk Γ (fact j))
  set Fn := Groth.ι (Q.mk Γ (fact n))
  set c₁ := Groth.ι (Q.mk Γ (binom n j))
  set c₂ := Groth.ι (Q.mk Γ (binom n (succ j)))
  linear_combination f₁ + (Groth.ι (Q.mk Γ j) + 1) * f₂ + (Groth.ι (Q.mk Γ (monus n (succ j))) + 1) * f₃
    - FSd * c₁ * f₄ - FSj * c₂ * f₅ + (Groth.ι (Q.mk Γ j) + 1) * Fj * c₁ * f₆
    - (c₁ + c₂) * FSj * f₇ + Fn * f₈

theorem bden_congr {n k k' : PTm m} (h : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] bden n k ≐ bden n k' :=
  congrMul (congrAp2 factF h (.eqRefl _)) (congrAp2 factF (congrMonus (.eqRefl _) h) (.eqRefl _))

theorem fact_one_eq : Γ ⊢[PRAAx] fact (zero : PTm m) ≐ one := fact_zero _

/-- `k! (n ∸ k)! = n!` when `k = 0` or `k = n`. -/
theorem bden_zero (n : PTm m) : Γ ⊢[PRAAx] fact n ≐ bden n zero * one := by
  refine withEq (fact_zero (Γ := Γ) (zero : PTm m)) fun e₁ => ?_
  refine withEq (congrAp2 (Γ := Γ) factF (monus_zero n) (.eqRefl zero)) fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

theorem bden_self (n : PTm m) : Γ ⊢[PRAAx] fact n ≐ bden n n * one := by
  refine withEq (fact_zero (Γ := Γ) (zero : PTm m)) fun e₁ => ?_
  refine withEq (congrAp2 (Γ := Γ) factF (monus_self n) (.eqRefl zero)) fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [e₂, e₁]; ring

/-- The induction step for `k`, over the variables `0 = k`, `1 = n`. -/
theorem key : ([T (var 1) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx]
    lt (var 0) (succ (succ (var 1))) ⟶ (rem (fact (succ (var 1))) (bden (succ (var 1)) (var 0)) ≐ zero) := by
  refine .impI (.orE (zero_or_succ (var 0)) ?_ ?_)
  · -- k = 0.
    refine (congrAp2 remF (.eqRefl _) (bden_congr Prf.hyp0)).eqTrans ?_
    exact rem_zero_of_eq (bden_pos _ _) (bden_zero _)
  · -- k = S j.
    have hjn : ((var 0 ≐ succ (pred (var 0))) :: lt (var 0) (succ (succ (var 1))) ::
        [T (var 1) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx] le (pred (var 0)) (var 1) := by
      refine (succ_monus_succ _ _).eqSymm.eqTrans ((succ_monus_succ _ _).eqSymm.eqTrans ?_)
      exact (congrMonus (congrSucc Prf.hyp0.eqSymm) (.eqRefl _)).eqTrans Prf.hyp1
    refine (congrAp2 remF (.eqRefl _) (bden_congr Prf.hyp0)).eqTrans ?_
    refine .orE (lt_or_eq_of_le hjn) ?_ ?_
    · -- j < n: Pascal.
      have hT : (lt (pred (var 0)) (var 1) :: (var 0 ≐ succ (pred (var 0))) ::
          lt (var 0) (succ (succ (var 1))) :: [T (var 1) ≐ zero] : List (Fm PTm 2)) ⊢[PRAAx]
          T (var 1) ≐ zero := .hyp (by simp)
      have h₁ := sum_zero_elim rBody hT (lt_succ_of_le' (le_of_lt Prf.hyp0))
      have h₂ := sum_zero_elim rBody hT ((succ_monus_succ _ _).eqTrans Prf.hyp0)
      rw [inst2_r] at h₁ h₂
      exact rem_zero_of_eq (bden_pos _ _) (pascal_step Prf.hyp0 h₁ h₂)
    · -- j = n.
      refine (congrAp2 remF (.eqRefl _) (bden_congr (congrSucc Prf.hyp0))).eqTrans ?_
      exact rem_zero_of_eq (bden_pos _ _) (bden_self _)
where
  lt_succ_of_le' {Δ : List (Fm PTm 2)} {i M : PTm 2} (h : Δ ⊢[PRAAx] le i M) : Δ ⊢[PRAAx] lt i (succ M) :=
    (succ_monus_succ i M).eqTrans h

/-- `T(n) = 0` for every `n`: `k! (n − k)!` divides `n!` for all `k ≤ n`. -/
theorem binom_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] T (var 0) ≐ zero := by
  ipra_ind [subst_ap2]
  · refine (sum_singleton rBody zero).eqTrans ?_
    rw [inst2_r]
    exact rem_zero_of_eq (bden_pos _ _) (bden_zero _)
  · refine sum_zero_of_bounded rBody _ _ (.allI ?_)
    simpa [Fm.shift, Syn.shift, inst2_r] using key

/-! ## Consequences -/

theorem binom_rem_zero {k n : PTm m} (h : Γ ⊢[PRAAx] le k n) :
    Γ ⊢[PRAAx] rem (fact n) (bden n k) ≐ zero := by
  have hT := inst (Γ := Γ) binom_open ![n]
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at hT
  have h₀ := sum_zero_elim rBody hT ((succ_monus_succ _ _).eqTrans h)
  rwa [inst2_r] at h₀

/-- `k ≤ n → n! = k! (n − k)! C(n, k)`; variables `0 = k`, `1 = n`. -/
abbrev specFormula : Fm PTm 2 :=
  le (var 0) (var 1) ⟶ (fact (var 1) ≐ bden (var 1) (var 0) * binom (var 1) (var 0))

theorem binom_spec : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 specFormula :=
  closeUniv 2 (.impI (eq_of_rem_zero (bden_pos _ _) (binom_rem_zero Prf.hyp0)))

/-- Pascal's rule: `j < n → C(n + 1, j + 1) = C(n, j) + C(n, j + 1)`; variables `0 = j`, `1 = n`. -/
abbrev pascalFormula : Fm PTm 2 :=
  lt (var 0) (var 1) ⟶ (binom (succ (var 1)) (succ (var 0)) ≐ binom (var 1) (var 0) + binom (var 1) (succ (var 0)))

theorem pascal : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 pascalFormula := by
  refine closeUniv 2 (.impI ?_)
  refine quo_of_eq (bden_pos _ _) (pascal_step Prf.hyp0 (binom_rem_zero (le_of_lt Prf.hyp0))
    (binom_rem_zero Prf.hyp0))

/-- `C(n, 0) = 1` and `C(n, n) = 1`; variable `0 = n`. -/
abbrev edgeFormula : Fm PTm 1 := (binom (var 0) zero ≐ one) ⋏ (binom (var 0) (var 0) ≐ one)

theorem binom_edges : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 edgeFormula :=
  closeUniv 1 (.andI (quo_of_eq (bden_pos _ _) (bden_zero _)) (quo_of_eq (bden_pos _ _) (bden_self _)))

end LeanProofs.IPRA.Combinatorics.Binomial

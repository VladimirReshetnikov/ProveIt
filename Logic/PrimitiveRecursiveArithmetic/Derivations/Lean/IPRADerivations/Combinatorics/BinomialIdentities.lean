import IPRADerivations.Combinatorics.Binomial
import IPRADerivations.Core.SumLemmas

/-!
# Binomial sums, the central binomial coefficient and Catalan numbers

* The binomial sum `∑_{k≤m} C(m, k) = 2^m`, by induction on `m` with Pascal's rule.
* `pnt_ipra_constructive_2026-11-14` (`tex/selberg.tex`): `C(2n, n) ≤ 2^{2n}`.
* `lagrange_inversion_ipra` (`lagrange_inversion_ipra.tex`), the Catalan numbers
  `B_n = C(2n, n) − C(2n, n + 1)`: for `n ≥ 1`, `n C(2n, n) = (n + 1) C(2n, n + 1)` and
  `(n + 1) B_n = C(2n, n)`, i.e. `B_n = C(2n, n)/(n + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BinomialIdentities

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {m : ℕ} {Γ : List (Fm PTm m)}

theorem binom_zero' (n : PTm m) : Γ ⊢[PRAAx] binom n zero ≐ one := quo_of_eq (bden_pos _ _) (bden_zero _)
theorem binom_self' (n : PTm m) : Γ ⊢[PRAAx] binom n n ≐ one := quo_of_eq (bden_pos _ _) (bden_self _)

theorem pascal_at {j n : PTm m} (h : Γ ⊢[PRAAx] lt j n) :
    Γ ⊢[PRAAx] binom (succ n) (succ j) ≐ binom n j + binom n (succ j) :=
  quo_of_eq (bden_pos _ _) (pascal_step h (binom_rem_zero (le_of_lt h)) (binom_rem_zero h))

/-! ## The binomial sum -/

/-- `C(m, k)`, `C(m + 1, k + 1)` and `C(m, k) + C(m, k + 1)` as bodies; variables `0 = k`, `1 = m`. -/
abbrev bBody : PTm 2 := binom (var 1) (var 0)
abbrev gBody : PTm 2 := binom (succ (var 1)) (succ (var 0))
abbrev hBody : PTm 2 := addBody bBody (shiftBody bBody)

theorem inst2_b (k x : PTm m) : inst2 bBody k x = binom x k := by simp [inst2]
theorem inst2_g (k x : PTm m) : inst2 gBody k x = binom (succ x) (succ k) := by simp [inst2]
theorem inst2_sb (k x : PTm m) : inst2 (shiftBody bBody) k x = binom x (succ k) := by
  rw [inst2_shiftBody, inst2_b]
theorem inst2_h (k x : PTm m) : inst2 hBody k x = binom x k + binom x (succ k) := by
  rw [inst2_addBody, inst2_b, inst2_sb]

/-- `∑_{k≤m} C(m, k) = 2^m`; variable `0 = m`. -/
abbrev binomSumFormula : Fm PTm 1 := ap2 (sumF bBody) (succ (var 0)) (var 0) ≐ pw two (var 0)

theorem binom_sum_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] binomSumFormula := by
  ipra_ind [subst_ap2]
  · refine (sum_singleton bBody zero).eqTrans ?_
    rw [inst2_b]
    exact (binom_self' _).eqTrans (pw_zero _).eqSymm
  · have q₁ := sum_shift (Γ := [binomSumFormula]) bBody (succ (var 0)) (succ (var 0))
    rw [inst2_b] at q₁
    have q₃ : [binomSumFormula] ⊢[PRAAx] ap2 (sumF (shiftBody bBody)) (succ (var 0)) (succ (var 0))
        ≐ ap2 (sumF gBody) (succ (var 0)) (var 0) := by
      refine sum_congr_bounded _ _ _ _ _ (.allI ?_)
      simp only [inst2_sb, inst2_g, Syn.shift, ConciseIPRA.PTm.subst_succ, Syn.subst_var]
      exact .impI (.eqRefl _)
    have q₄ := sum_succ' (Γ := [binomSumFormula]) gBody (var 0) (var 0)
    rw [inst2_g] at q₄
    have q₆ : [binomSumFormula] ⊢[PRAAx] ap2 (sumF gBody) (var 0) (var 0) ≐ ap2 (sumF hBody) (var 0) (var 0) := by
      refine sum_congr_bounded _ _ _ _ _ (.allI ?_)
      simp only [inst2_g, inst2_h]
      exact .impI (pascal_at Prf.hyp0)
    have q₇ := sum_add (Γ := [binomSumFormula]) bBody (shiftBody bBody) (var 0) (var 0)
    have q₈ := sum_succ' (Γ := [binomSumFormula]) bBody (var 0) (var 0)
    have q₁₀ := sum_shift (Γ := [binomSumFormula]) bBody (var 0) (var 0)
    rw [inst2_b] at q₈ q₁₀
    refine withEq q₁ fun f₁ => withEq (binom_zero' (Γ := [binomSumFormula]) (succ (var 0))) fun f₂ => ?_
    refine withEq q₃ fun f₃ => withEq q₄ fun f₄ => withEq (binom_self' (Γ := [binomSumFormula]) (succ (var 0)))
      fun f₅ => withEq q₆ fun f₆ => withEq q₇ fun f₇ => withEq q₈ fun f₈ => ?_
    refine withEq (binom_self' (Γ := [binomSumFormula]) (var 0)) fun f₉ => withEq q₁₀ fun f₁₀ =>
      withEq (binom_zero' (Γ := [binomSumFormula]) (var 0)) fun f₁₁ =>
      withEq (Prf.hyp0 : [binomSumFormula] ⊢[PRAAx] binomSumFormula) fun f₁₂ =>
      withEq (pw_succ (Γ := [binomSumFormula]) two (var 0)) fun f₁₃ => ?_
    apply deriveNat; ipra_simps
    rw [f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₁₃]
    rw [f₉] at f₈; rw [f₁₁] at f₁₀
    linear_combination 2 * f₁₂ - f₈ - f₁₀

theorem binom_sum : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 binomSumFormula := closeUniv 1 binom_sum_open

/-! ## The central binomial coefficient -/

/-- `C(2n, n) ≤ 2^{2n}`; variable `0 = n`. -/
abbrev centralFormula : Fm PTm 1 := le (binom (two * var 0) (var 0)) (pw two (two * var 0))

theorem central_binomial : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 centralFormula := by
  refine closeUniv 1 ?_
  have hs := inst (Γ := ([] : List (Fm PTm 1))) binom_sum_open ![two * var 0]
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hs
  have hn : ([] : List (Fm PTm 1)) ⊢[PRAAx] lt (var 0) (succ (two * var 0)) :=
    (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := var 0) (by ipra_ring))
  have ht := term_le_sum bBody (x := two * var 0) hn
  rw [inst2_b] at ht
  exact le_congr (.eqRefl _) hs ht

/-! ## Catalan numbers -/

theorem mul_cancel {D X Y : PTm m} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (h : Γ ⊢[PRAAx] D * X ≐ D * Y) :
    Γ ⊢[PRAAx] X ≐ Y :=
  mul_eq_cancel_at hD h

/-- With `n = m + 1` and `N = 2n`: `C₁ = C(N, n)`, `C₂ = C(N, n + 1)`; variable `0 = m`. -/
abbrev N : PTm 1 := two * succ (var 0)
abbrev C₁ : PTm 1 := binom N (succ (var 0))
abbrev C₂ : PTm 1 := binom N (succ (succ (var 0)))

/-- `n C(2n, n) = (n + 1) C(2n, n + 1)` for `n = m + 1`. -/
abbrev catalanRatioFormula : Fm PTm 1 := succ (var 0) * C₁ ≐ succ (succ (var 0)) * C₂

theorem binom_eq {k n : PTm m} (h : Γ ⊢[PRAAx] le k n) : Γ ⊢[PRAAx] fact n ≐ bden n k * binom n k :=
  eq_of_rem_zero (bden_pos _ _) (binom_rem_zero h)

theorem catalan_ratio_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] catalanRatioFormula := by
  have hN₁ : ([] : List (Fm PTm 1)) ⊢[PRAAx] N ≐ succ (var 0) + succ (var 0) := by
    ipra_ring
  have hN₂ : ([] : List (Fm PTm 1)) ⊢[PRAAx] N ≐ succ (succ (var 0)) + var 0 := by
    ipra_ring
  have e₁ := binom_eq (k := succ (var 0)) (le_of_eq_add (d := succ (var 0)) hN₁)
  have e₂ := binom_eq (k := succ (succ (var 0))) (le_of_eq_add (d := var 0) hN₂)
  have g₁ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fact (monus N (succ (var 0))) ≐ fact (succ (var 0)) :=
    congrAp2 factF ((congrMonus hN₁ (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  have g₂ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fact (monus N (succ (succ (var 0)))) ≐ fact (var 0) :=
    congrAp2 factF ((congrMonus hN₂ (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  refine mul_cancel (D := fact (var 0) * fact (succ (var 0))) (pos_mul (fact_pos _) (fact_pos _)) ?_
  refine withEq e₁ fun f₁ => withEq e₂ fun f₂ => withEq g₁ fun f₃ => withEq g₂ fun f₄ => ?_
  refine withEq (fact_succ (Γ := ([] : List (Fm PTm 1))) (succ (var 0)) zero) fun f₅ => ?_
  refine withEq (fact_succ (Γ := ([] : List (Fm PTm 1))) (var 0) zero) fun f₆ => ?_
  apply deriveNat; ipra_simps
  set fv := Groth.ι (Q.mk ([] : List (Fm PTm 1)) (fact (var 0)))
  set fSv := Groth.ι (Q.mk ([] : List (Fm PTm 1)) (fact (succ (var 0))))
  set fSSv := Groth.ι (Q.mk ([] : List (Fm PTm 1)) (fact (succ (succ (var 0)))))
  set c₁ := Groth.ι (Q.mk ([] : List (Fm PTm 1)) C₁)
  set c₂ := Groth.ι (Q.mk ([] : List (Fm PTm 1)) C₂)
  linear_combination -f₁ + f₂ - fSv * c₁ * f₃ - fSv * c₁ * f₆ + fSSv * c₂ * f₄ + fv * c₂ * f₅

theorem catalan_ratio : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 catalanRatioFormula :=
  closeUniv 1 catalan_ratio_open

/-- `(n + 1) B_n = C(2n, n)` with `B_n = C(2n, n) − C(2n, n + 1)`, for `n = m + 1`. -/
abbrev catalanFormula : Fm PTm 1 := succ (succ (var 0)) * monus C₁ C₂ ≐ C₁

theorem catalan : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 catalanFormula := by
  refine closeUniv 1 ?_
  have hr := catalan_ratio_open
  have hC : ([] : List (Fm PTm 1)) ⊢[PRAAx] le C₂ C₁ := by
    refine mul_le_cancel (d' := succ (var 0)) (le_congr hr (.eqRefl _) (le_of_eq_add (d := C₁) ?_))
    ipra_ring
  refine withEq hr fun f₁ => withEq (eq_add_of_le hC) fun f₂ => ?_
  ipra_lc f₁ - (Groth.ι (Q.mk ([] : List (Fm PTm 1)) (var 0)) + 2) * f₂

end LeanProofs.IPRA.Combinatorics.BinomialIdentities

import IPRADerivations.Combinatorics.FibonacciGcd
import IPRADerivations.DiophantineNumberTheory.PellModular

/-!
# Periodicity of the Fibonacci and Lucas numbers modulo `d`

Packet: `combinatorics/fibonacci_lucas_ipra` (theorem "Purely finite modular periodicity", (19)): for
every `d ≥ 1` there is an explicit `t` with `1 ≤ t ≤ d²` such that

  `(F_{n+t}, F_{n+t+1}) ≡ (F_n, F_{n+1})` and `L_{n+t} ≡ L_n (mod d)` for every `n`.

The packet's argument: the residue pair `σ(k) = (F_k mod d) + d (F_{k+1} mod d) < d²` collides on
`0, …, d²` (`Core/Pigeonhole`), at `i < j`; then `t = j − i`. Invertibility of the update is used
in the form of d'Ocagne's identity (`Combinatorics/FibonacciGcd`):

* `ret_zero`: `F_{i+t} F_{i+1} + [i odd] F_t = F_{i+t+1} F_i + [i even] F_t` and the congruences
  `F_{i+t} ≡ F_i`, `F_{i+t+1} ≡ F_{i+1}` give `F_t ≡ 0`;
* `ret_one`: the same identity at `t + 1` and Cassini give `F_{t+1} ≡ 1`;
* `fib_period`: then the addition laws `F_{t+n} + F_t F_n = F_t F_{n+1} + F_{t+1} F_n` and
  `F_{t+n+1} = F_{t+1} F_{n+1} + F_t F_n` give the periodicity for every `n`, and `L_m + F_m = 2F_{m+1}`
  carries it to the Lucas numbers.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciPeriod

open_ipra
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.FibonacciGcd (docagne)
open LeanProofs.IPRA.DiophantineNumberTheory.PellModular (digit_lt digit_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_eq_of_eq rem_mul_right_congr rem_mul_congr_both
  eq_add_quo_of_rem_eq rem_of_balanced_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The residue code -/

/-- `σ(k) = (F_k mod d) + d (F_{k+1} mod d)`, over `0 = k`, `1 = d`. -/
abbrev sigB : PTm 2 := rem (fib (var 0)) (var 1) + var 1 * rem (fibS (var 0)) (var 1)

theorem inst2_sig (k d : PTm n) : inst2 sigB k d = rem (fib k) d + d * rem (fibS k) d := by simp [inst2]

theorem sig_range {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) : Γ ⊢[PRAAx] Permutation.rangeAll sigB (d * d) d := by
  refine .allI ?_
  rw [inst2_sig, AnalyticNumberTheory.SumPhi.shift_mul']
  have hd' := AnalyticNumberTheory.GcdFiber.shift_pos hd
  exact digit_lt (rem_lt' hd' _) (rem_lt' hd' _)

/-- `x ≡ y` as a linear equation. -/
theorem cong_lin {x y d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] rem x d ≐ rem y d) :
    Γ ⊢[PRAAx] x + d * quo y d ≐ y + d * quo x d :=
  eq_add_quo_of_rem_eq hd h

private theorem rem_add_congr {a b c e d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (h₁ : Γ ⊢[PRAAx] rem a d ≐ rem b d) (h₂ : Γ ⊢[PRAAx] rem c d ≐ rem e d) :
    Γ ⊢[PRAAx] rem (a + c) d ≐ rem (b + e) d := by
  refine rem_eq_of_eq hd (k₁ := quo b d + quo e d) (k₂ := quo a d + quo c d) ?_
  ipra_lc natEq (cong_lin hd h₁) + natEq (cong_lin hd h₂)

/-! ## The return to `(0, 1)` -/

theorem doc_t {i j t : PTm n} (hj : Γ ⊢[PRAAx] j ≐ i + t) : Γ ⊢[PRAAx] fib j * fibS i + par i * fib t ≐ fibS j * fib i + monus one (par i) * fib t :=
  (congrAdd (congrMul (congrFib hj) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((docagne i t).eqTrans (congrAdd (congrMul (congrFibS hj).eqSymm (.eqRefl _)) (.eqRefl _)))

theorem doc_t1 {i j t : PTm n} (hj : Γ ⊢[PRAAx] j ≐ i + t) : Γ ⊢[PRAAx] fibS j * fibS i + par i * fibS t ≐ (fibS j + fib j) * fib i + monus one (par i) * fibS t := by
  have es : Γ ⊢[PRAAx] i + succ t ≐ succ j :=
    (by ipra_ring : Γ ⊢[PRAAx] i + succ t ≐ succ (i + t)).eqTrans (congrSucc hj.eqSymm)
  ipra_lc natEq (docagne (Γ := Γ) i (succ t)) - 𝔞 (fibS i) * natEq ((congrFib es).eqTrans (fib_succ j)) +
    𝔞 (fib i) * natEq ((congrFibS es).eqTrans (fibS_succ j)) -
    (𝔞 (par i) - 𝔞 (monus one (par i))) * natEq (fib_succ (Γ := Γ) t)

private theorem cross_product_congr {i j d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (e₁ : Γ ⊢[PRAAx] rem (fib j) d ≐ rem (fib i) d) (e₂ : Γ ⊢[PRAAx] rem (fibS j) d ≐ rem (fibS i) d) :
    Γ ⊢[PRAAx] rem (fib j * fibS i) d ≐ rem (fibS j * fib i) d :=
  (rem_mul_right_congr (fibS i) hd e₁).eqTrans
    ((congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans (rem_mul_right_congr (fib i) hd e₂).eqSymm)

private theorem next_products_congr {i j d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (e₁ : Γ ⊢[PRAAx] rem (fib j) d ≐ rem (fib i) d) (e₂ : Γ ⊢[PRAAx] rem (fibS j) d ≐ rem (fibS i) d) :
    Γ ⊢[PRAAx] (rem (fibS j * fibS i) d ≐ rem (fibS i * fibS i) d) ⋏
      (rem ((fibS j + fib j) * fib i) d ≐ rem ((fibS i + fib i) * fib i) d) :=
  .andI (rem_mul_right_congr (fibS i) hd e₂) (rem_mul_right_congr (fib i) hd (rem_add_congr hd e₂ e₁))

section Return

variable {d i j t : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hj : Γ ⊢[PRAAx] j ≐ i + t)
  (e₁ : Γ ⊢[PRAAx] rem (fib j) d ≐ rem (fib i) d) (e₂ : Γ ⊢[PRAAx] rem (fibS j) d ≐ rem (fibS i) d)
include hd hj e₁ e₂

theorem rz_even (hp : Γ ⊢[PRAAx] par i ≐ zero) : Γ ⊢[PRAAx] rem (fib t) d ≐ rem zero d := by
  have hq := (congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_zero one)
  refine rem_of_balanced_add hd (a := fibS j * fib i) (b := fib j * fibS i) ?_
    (zero_add _) (cross_product_congr hd e₁ e₂).eqSymm (.eqRefl _)
  ipra_lc -natEq (doc_t hj) + 𝔞 (fib t) * (natEq hp - natEq hq)

theorem rz_odd (hp : Γ ⊢[PRAAx] par i ≐ one) : Γ ⊢[PRAAx] rem (fib t) d ≐ rem zero d := by
  have hq := (congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_self one)
  refine rem_of_balanced_add hd (a := fib j * fibS i) (b := fibS j * fib i) ?_
    (zero_add _) (cross_product_congr hd e₁ e₂) (.eqRefl _)
  ipra_lc natEq (doc_t hj) + 𝔞 (fib t) * (natEq hq - natEq hp)

theorem ro_even (hp : Γ ⊢[PRAAx] par i ≐ zero) : Γ ⊢[PRAAx] rem (fibS t) d ≐ rem one d := by
  have hq := (congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_zero one)
  have r := next_products_congr hd e₁ e₂
  refine rem_of_balanced_add hd ?_ ?_ r.andE₂ r.andE₁
  · ipra_lc -natEq (doc_t1 hj) + 𝔞 (fibS t) * (natEq hp - natEq hq)
  · ipra_lc natEq (cassini i) - 𝔞 (fib i) * natEq (fibS_succ i) + natEq hp - natEq hq

theorem ro_odd (hp : Γ ⊢[PRAAx] par i ≐ one) : Γ ⊢[PRAAx] rem (fibS t) d ≐ rem one d := by
  have hq := (congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_self one)
  have r := next_products_congr hd e₁ e₂
  refine rem_of_balanced_add hd ?_ ?_ r.andE₁ r.andE₂
  · ipra_lc natEq (doc_t1 hj) + 𝔞 (fibS t) * (natEq hq - natEq hp)
  · ipra_lc -natEq (cassini i) + 𝔞 (fib i) * natEq (fibS_succ i) + natEq hq - natEq hp

/-- `F_t ≡ 0`. -/
theorem ret_zero : Γ ⊢[PRAAx] rem (fib t) d ≐ rem zero d :=
  .orE (par_cases i) (rz_even hd.wk hj.wk e₁.wk e₂.wk Prf.hyp0) (rz_odd hd.wk hj.wk e₁.wk e₂.wk Prf.hyp0)

/-- `F_{t+1} ≡ 1`. -/
theorem ret_one : Γ ⊢[PRAAx] rem (fibS t) d ≐ rem one d :=
  .orE (par_cases i) (ro_even hd.wk hj.wk e₁.wk e₂.wk Prf.hyp0) (ro_odd hd.wk hj.wk e₁.wk e₂.wk Prf.hyp0)

end Return

/-! ## The period -/

/-- The explicit period `t = j₀ − i₀`. -/
abbrev tPer (d : PTm n) : PTm n := monus (Pigeonhole.phpJ sigB (d * d) d) (Pigeonhole.phpI sigB (d * d) d)

theorem period_return {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] le one (tPer d) ⋏ (le (tPer d) (d * d) ⋏
      ((rem (fib (tPer d)) d ≐ rem zero d) ⋏ (rem (fibS (tPer d)) d ≐ rem one d))) := by
  have php := Pigeonhole.pigeonhole (sig_range hd)
  have hlt := Prf.andE₁ php
  have hJK := Prf.andE₁ (Prf.andE₂ php)
  have ec := Prf.andE₂ (Prf.andE₂ php)
  rw [inst2_sig, inst2_sig] at ec
  have dg := digit_eq hd (rem_lt' hd _) (rem_lt' hd _) ec.eqSymm
  have hJ : Γ ⊢[PRAAx] Pigeonhole.phpJ sigB (d * d) d ≐ Pigeonhole.phpI sigB (d * d) d + tPer d :=
    eq_add_of_le (le_of_lt hlt)
  exact .andI (Common.one_le_monus_of_lt _ _ hlt) (.andI (le_trans (Common.monus_le_self _ _) hJK)
    (.andI (ret_zero hd hJ dg.andE₁ dg.andE₂) (ret_one hd hJ dg.andE₁ dg.andE₂)))

/-- (19): `1 ≤ t ≤ d²`, and `F_{n+t} ≡ F_n`, `F_{n+t+1} ≡ F_{n+1}`, `L_{n+t} ≡ L_n (mod d)` for every `n`. -/
theorem fib_period {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (N : PTm n) :
    Γ ⊢[PRAAx] le one (tPer d) ⋏ (le (tPer d) (d * d) ⋏
      ((rem (fib (tPer d + N)) d ≐ rem (fib N) d) ⋏ ((rem (fibS (tPer d + N)) d ≐ rem (fibS N) d) ⋏
        (rem (luc (tPer d + N)) d ≐ rem (luc N) d)))) := by
  let t := tPer d
  have h := period_return hd
  have r := h.andE₂.andE₂
  have atN : Γ ⊢[PRAAx] rem (fib (t + N)) d ≐ rem (fib N) d :=
    rem_of_balanced_add hd (fib_add_sym t N) (by ipra_ring)
      (rem_mul_right_congr (fib N) hd r.andE₁)
      (rem_add_congr hd (rem_mul_right_congr (fibS N) hd r.andE₁) (rem_mul_right_congr (fib N) hd r.andE₂))
  have afterN : Γ ⊢[PRAAx] rem (fibS (t + N)) d ≐ rem (fibS N) d :=
    (congrAp2 remF (fibS_add t N) (.eqRefl _)).eqTrans
      ((rem_add_congr hd (rem_mul_right_congr (fibS N) hd r.andE₂) (rem_mul_right_congr (fib N) hd r.andE₁)).eqTrans
        (congrAp2 remF (by ipra_ring) (.eqRefl _)))
  have lucas := rem_of_balanced_add hd (luc_eq (t + N)) (luc_eq N) atN
    (rem_mul_congr_both hd (.eqRefl _) afterN)
  exact .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI atN (.andI afterN lucas)))

/-- (19), closed: variables `0 = d − 1`, `1 = n`. -/
abbrev fibPeriodFormula : Fm PTm 2 :=
  le one (tPer (succ (var 0))) ⋏ (le (tPer (succ (var 0))) (succ (var 0) * succ (var 0)) ⋏
    ((rem (fib (tPer (succ (var 0)) + var 1)) (succ (var 0)) ≐ rem (fib (var 1)) (succ (var 0))) ⋏
      ((rem (fibS (tPer (succ (var 0)) + var 1)) (succ (var 0)) ≐ rem (fibS (var 1)) (succ (var 0))) ⋏
        (rem (luc (tPer (succ (var 0)) + var 1)) (succ (var 0)) ≐ rem (luc (var 1)) (succ (var 0))))))

theorem fibonacci_period : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 fibPeriodFormula :=
  closeUniv 2 (fib_period (congrSucc (pred_succ _).eqSymm) _)

end LeanProofs.IPRA.Combinatorics.FibonacciPeriod

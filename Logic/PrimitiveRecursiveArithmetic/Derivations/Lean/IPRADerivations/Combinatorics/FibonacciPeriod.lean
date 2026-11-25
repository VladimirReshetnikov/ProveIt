import IPRADerivations.Combinatorics.FibonacciGcd
import IPRADerivations.DiophantineNumberTheory.PellModular
import IPRADerivations.Core.CertificateTactics

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.FibonacciGcd (docagne)
open LeanProofs.IPRA.DiophantineNumberTheory.PellModular (digit_lt digit_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_eq_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

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
    Γ ⊢[PRAAx] x + d * quo y d ≐ y + d * quo x d := by
  ipra_lc natEq (div_eq (j := x) hd) - natEq (div_eq (j := y) hd) + natEq h

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

section Return

variable {d i j t : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hj : Γ ⊢[PRAAx] j ≐ i + t)
  (e₁ : Γ ⊢[PRAAx] rem (fib j) d ≐ rem (fib i) d) (e₂ : Γ ⊢[PRAAx] rem (fibS j) d ≐ rem (fibS i) d)
include hd hj e₁ e₂

theorem rz_even (hp : Γ ⊢[PRAAx] par i ≐ zero) : Γ ⊢[PRAAx] rem (fib t) d ≐ rem zero d := by
  have f₁ := natEq (div_eq (j := fib i) hd); have f₁' := natEq (div_eq (j := fib j) hd)
  have f₂ := natEq (div_eq (j := fibS i) hd); have f₂' := natEq (div_eq (j := fibS j) hd)
  have r₁ := natEq e₁; have r₂ := natEq e₂
  have hp' := natEq hp; have hq := natEq ((congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_zero one))
  refine rem_eq_of_eq hd (k₁ := d * quo (fibS j) d * quo (fib i) d + quo (fibS j) d * rem (fib i) d +
    rem (fibS i) d * quo (fib i) d) (k₂ := d * quo (fib j) d * quo (fibS i) d + quo (fib j) d * rem (fibS i) d +
    rem (fib i) d * quo (fibS i) d) ?_
  ipra_lc -natEq (doc_t hj) - 𝔞 (fib t) * hq + 𝔞 (fib t) * hp' + 𝔞 (fibS i) * f₁' +
    (𝔞 d * 𝔞 (quo (fib j) d) + 𝔞 (rem (fib j) d)) * f₂ + (𝔞 d * 𝔞 (quo (fibS i) d) + 𝔞 (rem (fibS i) d)) * r₁ -
    𝔞 (fib i) * f₂' - (𝔞 d * 𝔞 (quo (fibS j) d) + 𝔞 (rem (fibS j) d)) * f₁ -
    (𝔞 d * 𝔞 (quo (fib i) d) + 𝔞 (rem (fib i) d)) * r₂

theorem rz_odd (hp : Γ ⊢[PRAAx] par i ≐ one) : Γ ⊢[PRAAx] rem (fib t) d ≐ rem zero d := by
  have f₁ := natEq (div_eq (j := fib i) hd); have f₁' := natEq (div_eq (j := fib j) hd)
  have f₂ := natEq (div_eq (j := fibS i) hd); have f₂' := natEq (div_eq (j := fibS j) hd)
  have r₁ := natEq e₁; have r₂ := natEq e₂
  have hp' := natEq hp; have hq := natEq ((congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_self one))
  refine rem_eq_of_eq hd (k₂ := d * quo (fibS j) d * quo (fib i) d + quo (fibS j) d * rem (fib i) d +
    rem (fibS i) d * quo (fib i) d) (k₁ := d * quo (fib j) d * quo (fibS i) d + quo (fib j) d * rem (fibS i) d +
    rem (fib i) d * quo (fibS i) d) ?_
  ipra_lc natEq (doc_t hj) - 𝔞 (fib t) * hp' + 𝔞 (fib t) * hq -
    (𝔞 (fibS i) * f₁' + (𝔞 d * 𝔞 (quo (fib j) d) + 𝔞 (rem (fib j) d)) * f₂ + (𝔞 d * 𝔞 (quo (fibS i) d) + 𝔞 (rem (fibS i) d)) * r₁ - 𝔞 (fib i) * f₂' - (𝔞 d * 𝔞 (quo (fibS j) d) + 𝔞 (rem (fibS j) d)) * f₁ - (𝔞 d * 𝔞 (quo (fib i) d) + 𝔞 (rem (fib i) d)) * r₂)

theorem ro_even (hp : Γ ⊢[PRAAx] par i ≐ zero) : Γ ⊢[PRAAx] rem (fibS t) d ≐ rem one d := by
  have cas := natEq (cassini (Γ := Γ) i); have cs := natEq (fibS_succ (Γ := Γ) i)
  have f₁ := natEq (div_eq (j := fib i) hd); have f₁' := natEq (div_eq (j := fib j) hd)
  have f₂ := natEq (div_eq (j := fibS i) hd); have f₂' := natEq (div_eq (j := fibS j) hd)
  have r₁ := natEq e₁; have r₂ := natEq e₂
  have hp' := natEq hp; have hq := natEq ((congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_zero one))
  refine rem_eq_of_eq hd (k₁ := quo (fibS i) d * fibS i + quo (fibS j) d * fib i + quo (fib j) d * fib i)
    (k₂ := quo (fibS j) d * fibS i + quo (fibS i) d * fib i + quo (fib i) d * fib i) ?_
  ipra_lc -natEq (doc_t1 hj) + 𝔞 (fibS t) * hp' - 𝔞 (fibS t) * hq - cas + 𝔞 (fib i) * cs + hq - hp' +
    (𝔞 (fibS i) - 𝔞 (fib i)) * (f₂' - f₂ + r₂) - 𝔞 (fib i) * (f₁' - f₁ + r₁)

theorem ro_odd (hp : Γ ⊢[PRAAx] par i ≐ one) : Γ ⊢[PRAAx] rem (fibS t) d ≐ rem one d := by
  have cas := natEq (cassini (Γ := Γ) i); have cs := natEq (fibS_succ (Γ := Γ) i)
  have f₁ := natEq (div_eq (j := fib i) hd); have f₁' := natEq (div_eq (j := fib j) hd)
  have f₂ := natEq (div_eq (j := fibS i) hd); have f₂' := natEq (div_eq (j := fibS j) hd)
  have r₁ := natEq e₁; have r₂ := natEq e₂
  have hp' := natEq hp; have hq := natEq ((congrMonus (.eqRefl (one : PTm n)) hp).eqTrans (monus_self one))
  refine rem_eq_of_eq hd (k₁ := quo (fibS i) d * fib i + quo (fib i) d * fib i + quo (fibS j) d * fibS i)
    (k₂ := quo (fibS j) d * fib i + quo (fib j) d * fib i + quo (fibS i) d * fibS i) ?_
  ipra_lc natEq (doc_t1 hj) - 𝔞 (fibS t) * hp' + 𝔞 (fibS t) * hq + cas - 𝔞 (fib i) * cs - hq + hp' +
    (𝔞 (fib i) - 𝔞 (fibS i)) * (f₂' - f₂ + r₂) + 𝔞 (fib i) * (f₁' - f₁ + r₁)

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
  refine .andI ?_ (.andI ?_ (.andI (ret_zero hd hJ (Prf.andE₁ dg) (Prf.andE₂ dg))
    (ret_one hd hJ (Prf.andE₁ dg) (Prf.andE₂ dg))))
  · refine le_of_eq_add (d := monus (Pigeonhole.phpJ sigB (d * d) d) (succ (Pigeonhole.phpI sigB (d * d) d))) ?_
    ipra_lc natEq (eq_add_of_le hlt) - natEq hJ
  · exact le_trans (le_of_eq_add (d := Pigeonhole.phpI sigB (d * d) d) (hJ.eqTrans (add_comm _ _))) hJK

/-- (19): `1 ≤ t ≤ d²`, and `F_{n+t} ≡ F_n`, `F_{n+t+1} ≡ F_{n+1}`, `L_{n+t} ≡ L_n (mod d)` for every `n`. -/
theorem fib_period {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (N : PTm n) :
    Γ ⊢[PRAAx] le one (tPer d) ⋏ (le (tPer d) (d * d) ⋏
      ((rem (fib (tPer d + N)) d ≐ rem (fib N) d) ⋏ ((rem (fibS (tPer d + N)) d ≐ rem (fibS N) d) ⋏
        (rem (luc (tPer d + N)) d ≐ rem (luc N) d)))) := by
  have R := period_return hd
  -- `u = quo F_t`, `u' = quo 0`, `v = quo F_{t+1}`, `v' = quo 1`.
  have P1 : Γ ⊢[PRAAx] fib (tPer d + N) + d * (quo zero d * fibS N + quo one d * fib N + quo (fib (tPer d)) d * fib N) ≐
      fib N + d * (quo (fib (tPer d)) d * fibS N + quo (fibS (tPer d)) d * fib N + quo zero d * fib N) := by
    ipra_lc natEq (fib_add_sym (Γ := Γ) (tPer d) N) +
      (𝔞 (fibS N) - 𝔞 (fib N)) * natEq (cong_lin hd (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ R)))) +
      𝔞 (fib N) * natEq (cong_lin hd (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ R))))
  have P2 : Γ ⊢[PRAAx] fibS (tPer d + N) + d * (quo one d * fibS N + quo zero d * fib N) ≐
      fibS N + d * (quo (fibS (tPer d)) d * fibS N + quo (fib (tPer d)) d * fib N) := by
    ipra_lc natEq (fibS_add (Γ := Γ) (tPer d) N) +
      𝔞 (fibS N) * natEq (cong_lin hd (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ R)))) +
      𝔞 (fib N) * natEq (cong_lin hd (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ R))))
  have p₁ := natEq P1; have p₂ := natEq P2
  have l₁ := natEq (luc_eq (Γ := Γ) (tPer d + N)); have l₂ := natEq (luc_eq (Γ := Γ) N)
  have L : Γ ⊢[PRAAx] rem (luc (tPer d + N)) d ≐ rem (luc N) d := by
    refine rem_eq_of_eq hd (k₁ := two * (quo one d * fibS N + quo zero d * fib N) +
      (quo (fib (tPer d)) d * fibS N + quo (fibS (tPer d)) d * fib N + quo zero d * fib N))
      (k₂ := two * (quo (fibS (tPer d)) d * fibS N + quo (fib (tPer d)) d * fib N) +
        (quo zero d * fibS N + quo one d * fib N + quo (fib (tPer d)) d * fib N)) ?_
    ipra_lc l₁ - l₂ - p₁ + 2 * p₂
  exact .andI (Prf.andE₁ R) (.andI (Prf.andE₁ (Prf.andE₂ R)) (.andI (rem_eq_of_eq hd P1)
    (.andI (rem_eq_of_eq hd P2) L)))

/-- (19), closed: variables `0 = d − 1`, `1 = n`. -/
abbrev fibPeriodFormula : Fm PTm 2 :=
  le one (tPer (succ (var 0))) ⋏ (le (tPer (succ (var 0))) (succ (var 0) * succ (var 0)) ⋏
    ((rem (fib (tPer (succ (var 0)) + var 1)) (succ (var 0)) ≐ rem (fib (var 1)) (succ (var 0))) ⋏
      ((rem (fibS (tPer (succ (var 0)) + var 1)) (succ (var 0)) ≐ rem (fibS (var 1)) (succ (var 0))) ⋏
        (rem (luc (tPer (succ (var 0)) + var 1)) (succ (var 0)) ≐ rem (luc (var 1)) (succ (var 0))))))

theorem fibonacci_period : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 fibPeriodFormula :=
  closeUniv 2 (fib_period (congrSucc (pred_succ _).eqSymm) _)

end LeanProofs.IPRA.Combinatorics.FibonacciPeriod

import IPRADerivations.AnalyticNumberTheory.Primes
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Parity
import IPRADerivations.Core.Gcd

/-!
# The explicit tail of the exponential series

Packet: `analysis/trigonometric_identities_ipra_2026-11-15`, `trigonometric_identities_ipra.tex`, Lemma
`lem:exp-tail` ("Explicit exponential tail", (3.2), (3.3)): for `‖z‖₁ ≤ B` and
`N(B, p) = 2B² + 2B + p + 4`, `∑_{n ≥ N} ‖z‖₁ⁿ/n! < 2^{-p-3}`, in the finite-tail form the paper refers to:
every finite section of the majorant tail is at most `2^{-p-3}`.

The section `S_k = ∑_{j<k} B^{N+j}/(N+j)!` is kept as a numerator over `(N + k)!`:
`tsum 0 = 0`, `tsum (k + 1) = (tsum k + B^{N+k}) (N + k + 1)`, so `S_k = tsum k / (N + k)!`.

* `ratio_inv`: if `2B ≤ N`, then `tsum k · N! + 2 B^{N+k} N! ≤ 2 B^N (N + k)!` for every `k`, i.e.
  `S_k + 2 t_k ≤ 2 t_0` with `t_k = B^{N+k}/(N+k)!`: the tail is at most twice its first term, because
  successive terms have ratio `B/(n + 1) ≤ 1/2`;
* `two_pow_fact`: `2^m B^m (2B)! ≤ (2B + m)!`;
* `pow_bound`: `B^{2B} ≤ 2^{2B²}`, from `B ≤ 2^B`;
* `first_term`: for `N = N(B, p)`, `2^{p+4} B^N ≤ N!`, i.e. `2 B^N/N! ≤ 2^{-p-3}`;
* `exp_tail` ((3.3), finite form): `tsum k · 2^{p+3} ≤ (N + k)!`, i.e. `S_k ≤ 2^{-p-3}`, for every `k`.

The strict inequality for the infinite sum and the complex names of the packet are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ExponentialTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The tail numerators -/

/-- Step of `tsum`; variables `0 = k`, `1 = tsum k`, `2 = ⟨N, B⟩`. -/
abbrev sStep : PTm 3 := (var 1 + pw (sndT (var 2)) (fstT (var 2) + var 0)) * succ (fstT (var 2) + var 0)

/-- `tsum N B k = (N + k)! ∑_{j<k} B^{N+j}/(N+j)!`. -/
abbrev tsum (N B k : PTm n) : PTm n := ap2 (rec2 zero sStep) k (pairT N B)

theorem tsum_zero (N B : PTm n) : Γ ⊢[PRAAx] tsum N B zero ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero sStep (pairT N B)

theorem tsum_succ (N B k : PTm n) :
    Γ ⊢[PRAAx] tsum N B (succ k) ≐ (tsum N B k + pw B (N + k)) * succ (N + k) := by
  have h := rec2_succ (Γ := Γ) zero sStep k (pairT N B)
  have e : Syn.subst ![k, ap2 (rec2 zero sStep) k (pairT N B), pairT N B] sStep =
      (tsum N B k + pw (sndT (pairT N B)) (fstT (pairT N B) + k)) * succ (fstT (pairT N B) + k) := by
    simp
  rw [e] at h
  exact h.eqTrans (congrMul
    (congrAdd (.eqRefl _) (congrAp2 powF (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)))
    (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _))))

/-! ## The ratio invariant -/

/-- `tsum k · N! + 2 B^{N+k} N! ≤ 2 B^N (N + k)!`. -/
abbrev TI (N B k : PTm n) : Fm PTm n :=
  le (tsum N B k * fact N + (pw B (N + k) * fact N + pw B (N + k) * fact N))
    (pw B N * fact (N + k) + pw B N * fact (N + k))

theorem t_base (N B : PTm n) : Γ ⊢[PRAAx] TI N B zero := by
  have z := natEq (tsum_zero (Γ := Γ) N B)
  have c₁ := natEq (congrAp2 powF (add_zero (Γ := Γ) N) (.eqRefl B))
  have c₂ := natEq (congrAp2 factF (add_zero (Γ := Γ) N) (.eqRefl zero))
  ipra_le 0 using rw [z, c₁, c₂]; ring

theorem t_step {N B k : PTm n} (h2 : Γ ⊢[PRAAx] le (B + B) N) (ih : Γ ⊢[PRAAx] TI N B k) :
    Γ ⊢[PRAAx] TI N B (succ k) := by
  have es := natEq (tsum_succ (Γ := Γ) N B k)
  have ep := natEq ((congrAp2 powF (add_succ (Γ := Γ) N k) (.eqRefl B)).eqTrans (pw_succ B (N + k)))
  have ef := natEq ((congrAp2 factF (add_succ (Γ := Γ) N k) (.eqRefl zero)).eqTrans (fact_succ (N + k) zero))
  ipra_le (𝔟 N + 𝔟 k + 1) * sl ih + (sl h2 + 𝔟 k + 1) * 𝔟 (pw B (N + k)) * 𝔟 (fact N) using
    rw [es, ep, ef]; ring

/-- Variables: `0 = k` (induction), `1 = N`, `2 = B`. -/
private theorem tail₀ :
    ([] : List (Fm PTm 3)) ⊢[PRAAx] (le (var 2 + var 2) (var 1) ⟶ TI (var 1) (var 2) (var 0)) := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (t_base _ _)
  · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (t_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- The tail is at most twice its first term: `S_k + 2 t_k ≤ 2 t_0` for `2B ≤ N`. -/
theorem ratio_inv {N B : PTm n} (h2 : Γ ⊢[PRAAx] le (B + B) N) (k : PTm n) : Γ ⊢[PRAAx] TI N B k := by
  have h := inst (Γ := Γ) tail₀ (![k, N, B] : Fin 3 → PTm n)
  simp at h
  exact .impE h h2

/-! ## The first term -/

theorem tpf_base (B : PTm n) :
    Γ ⊢[PRAAx] le (pw two zero * pw B zero * fact (B + B)) (fact (B + B + zero)) := by
  have a := natEq (pw_zero (Γ := Γ) two); have b := natEq (pw_zero (Γ := Γ) B)
  have c := natEq (congrAp2 factF (add_zero (Γ := Γ) (B + B)) (.eqRefl zero))
  ipra_le 0 using rw [a, b, c]; ring

theorem tpf_step {B m : PTm n} (ih : Γ ⊢[PRAAx] le (pw two m * pw B m * fact (B + B)) (fact (B + B + m))) :
    Γ ⊢[PRAAx] le (pw two (succ m) * pw B (succ m) * fact (B + B)) (fact (B + B + succ m)) := by
  have a := natEq (pw_succ (Γ := Γ) two m); have b := natEq (pw_succ (Γ := Γ) B m)
  have ef := natEq ((congrAp2 factF (add_succ (Γ := Γ) (B + B) m) (.eqRefl zero)).eqTrans
    (fact_succ (B + B + m) zero))
  ipra_le (𝔟 B + 𝔟 B) * sl ih + (𝔟 m + 1) * 𝔟 (fact (B + B + m)) using rw [a, b, ef]; ring

/-- Variables: `0 = m` (induction), `1 = B`. -/
private theorem tpf₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx]
    le (pw two (var 0) * pw (var 1) (var 0) * fact (var 1 + var 1)) (fact (var 1 + var 1 + var 0)) := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tpf_base _
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact tpf_step Prf.hyp0

/-- `2^m B^m (2B)! ≤ (2B + m)!`. -/
theorem two_pow_fact (B m : PTm n) :
    Γ ⊢[PRAAx] le (pw two m * pw B m * fact (B + B)) (fact (B + B + m)) := by
  have h := inst (Γ := Γ) tpf₀ (![m, B] : Fin 2 → PTm n)
  simpa using h

/-- `B^{2B} ≤ 2^{2B²}`. -/
theorem pow_bound (B : PTm n) : Γ ⊢[PRAAx] le (pw B (B + B)) (pw two (B * (B + B))) :=
  le_congr (.eqRefl _) (pw_mul two B (B + B))
    (pw_le_pw (B + B) (le_of_lt (lt_pw (Γ := Γ) (le_refl two) B)))

/-- The threshold `N(B, p) = 2B² + 2B + p + 4`. -/
abbrev Nt (B p : PTm n) : PTm n := B + B + (B * (B + B) + succ (succ (succ (succ p))))

/-- `2^{p+4} B^N ≤ N!` for `N = N(B, p)`. -/
theorem first_term (B p : PTm n) :
    Γ ⊢[PRAAx] le (pw two (succ (succ (succ (succ p)))) * pw B (Nt B p)) (fact (Nt B p)) := by
  have h₁ := two_pow_fact (Γ := Γ) B (B * (B + B) + succ (succ (succ (succ p))))
  have h₂ := pow_bound (Γ := Γ) B
  have eB := natEq (pw_add (Γ := Γ) B (B + B) (B * (B + B) + succ (succ (succ (succ p)))))
  have e2 := natEq (pw_add (Γ := Γ) two (B * (B + B)) (succ (succ (succ (succ p)))))
  have eF := natEq (fact_pos (Γ := Γ) (B + B))
  ipra_le sl h₁ +
      𝔟 (pw two (B * (B + B) + succ (succ (succ (succ p))))) *
        𝔟 (pw B (B * (B + B) + succ (succ (succ (succ p))))) * 𝔟 (pred (fact (B + B))) +
      𝔟 (pw two (succ (succ (succ (succ p))))) *
        𝔟 (pw B (B * (B + B) + succ (succ (succ (succ p))))) * sl h₂ using
    rw [eB, e2, eF]; ring

/-! ## The tail bound -/

/-- (3.3), finite form: `S_k ≤ 2^{-p-3}`, i.e. `tsum k · 2^{p+3} ≤ (N + k)!` for `N = N(B, p)`. -/
theorem exp_tail (B p k : PTm n) :
    Γ ⊢[PRAAx] le (tsum (Nt B p) B k * pw two (succ (succ (succ p)))) (fact (Nt B p + k)) := by
  have hN : Γ ⊢[PRAAx] le (B + B) (Nt B p) := le_add_right _ _
  have r := ratio_inv hN k
  have f := first_term (Γ := Γ) B p
  have e4 := natEq (pw_succ (Γ := Γ) two (succ (succ (succ p))))
  have hF := fact_pos (Γ := Γ) (Nt B p)
  refine mul_le_cancel (d' := pred (fact (Nt B p)))
    (le_congr (congrMul hF (.eqRefl _)) (congrMul hF (.eqRefl _)) ?_)
  ipra_le 𝔟 (pw two (succ (succ (succ p)))) * sl r +
      𝔟 (pw two (succ (succ (succ p)))) *
        (𝔟 (pw B (Nt B p + k)) * 𝔟 (fact (Nt B p)) + 𝔟 (pw B (Nt B p + k)) * 𝔟 (fact (Nt B p))) +
      𝔟 (fact (Nt B p + k)) * sl f using
    rw [e4]; ring

end LeanProofs.IPRA.Analysis.ExponentialTail

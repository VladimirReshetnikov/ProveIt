import IPRADerivations.AnalyticNumberTheory.Harmonic

/-!
# The local Euler-factor bound `p^p ≤ 4 (p − 1)^p`

Packet: `analytic-number-theory/prime_reciprocal_ipra_2026-11-15`, Lemma `lem:local-factor`:
`(p/(p−1))^p ≤ 4` for `p ≥ 2`, in the integer form `p^p ≤ 4 (p − 1)^p`.

Instead of the paper's detour through `(1 + 1/a)^a ≤ 3`, we show that `(1 + 1/n)^{n+1}` decreases
(it equals `4` at `n = 1`), entirely with natural-number inequalities:

* `pw_mul_base`: `(ab)^m = a^m b^m`;
* `bernoulli`: `X^{m+1} + (m+1) X^m ≤ (X + 1)^{m+1}`;
* `decr`: `(n+2)^{n+2} n^{n+1} ≤ (n+1)^{n+1} (n+1)^{n+2}`, from Bernoulli at `X = n(n+2)`,
  `X + 1 = (n+1)²`: the surplus is `X^n + (n+1)·(Bernoulli surplus)`;
* `local_factor`: induction on `p`, cancelling the positive factor `(p−1)^p`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Powers of products -/

theorem pw_mul_base (a b m : PTm n) : Γ ⊢[PRAAx] pw (a * b) m ≐ pw a m * pw b m :=
  pw_mul_bases a b m

/-! ## Bernoulli's inequality -/

theorem bern_step {X m : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw X (succ m) + succ m * pw X m) (pw (succ X) (succ m))) :
    Γ ⊢[PRAAx] le (pw X (succ (succ m)) + succ (succ m) * pw X (succ m)) (pw (succ X) (succ (succ m))) := by
  have h := le_congr (by ipra_ring : Γ ⊢[PRAAx]
      pw X (succ m) + succ m * pw X m ≐ pw X (succ m) + succ m * pw X m * one)
    (congrAp2 powF (.eqRefl _) (succ_eq_add_one X)) ih
  exact le_congr (by ipra_ring) (congrAp2 powF (.eqRefl _) (succ_eq_add_one X).eqSymm)
    (pw_bernoulli_step h)

/-- `X^{m+1} + (m+1) X^m ≤ (X + 1)^{m+1}`. -/
theorem bernoulli (X m : PTm n) :
    Γ ⊢[PRAAx] le (pw X (succ m) + succ m * pw X m) (pw (succ X) (succ m)) :=
  pw_bernoulli_unit X m

/-! ## The decreasing step -/

/-- `(n+2)^{n+2} n^{n+1} ≤ (n+1)^{n+1} (n+1)^{n+2}`. -/
theorem decr (m : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ (succ m)) (succ (succ m)) * pw m (succ m))
      (pw (succ m) (succ m) * pw (succ m) (succ (succ m))) := by
  have hb := bernoulli (Γ := Γ) (m * succ (succ m)) m
  have eR₂ := natEq ((congrPw (Γ := Γ) (by ipra_ring :
      Γ ⊢[PRAAx] succ (m * succ (succ m)) ≐ succ m * succ m) (.eqRefl (succ m))).eqTrans
    (pw_mul_base (succ m) (succ m) (succ m)))
  refine le_of_eq_add (d := pw (m * succ (succ m)) m + succ m * monus (pw (succ (m * succ (succ m))) (succ m))
    (pw (m * succ (succ m)) (succ m) + succ m * pw (m * succ (succ m)) m)) ?_
  ipra_lc (Groth.ι (IPRA.Q.mk Γ m) + 1) * natEq (eq_add_of_le hb) - natEq (pw_succ (m * succ (succ m)) m) -
    (Groth.ι (IPRA.Q.mk Γ m) + 1) * eR₂ + Groth.ι (IPRA.Q.mk Γ (pw (succ m) (succ m))) *
    natEq (pw_succ (succ m) (succ m)) + (Groth.ι (IPRA.Q.mk Γ m) + 2) * natEq (pw_mul_base m (succ (succ m)) (succ m)) -
    Groth.ι (IPRA.Q.mk Γ (pw m (succ m))) * natEq (pw_succ (succ (succ m)) (succ m))

/-! ## The bound -/

theorem local_step {m : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw (succ (succ m)) (succ (succ m))) ((two * two) * pw (succ m) (succ (succ m)))) :
    Γ ⊢[PRAAx] le (pw (succ (succ (succ m))) (succ (succ (succ m))))
      ((two * two) * pw (succ (succ m)) (succ (succ (succ m)))) := by
  have d := decr (Γ := Γ) (succ m)
  have h₁ := le_mul_mono ih (le_refl (pw (succ (succ m)) (succ (succ (succ m)))))
  have hp := pw_pos (Γ := Γ) m (succ (succ m))
  have h₂ : Γ ⊢[PRAAx] le (pw (succ m) (succ (succ m)) * pw (succ (succ (succ m))) (succ (succ (succ m))))
      (pw (succ m) (succ (succ m)) * ((two * two) * pw (succ (succ m)) (succ (succ (succ m))))) := by
    refine le_congr (mul_comm _ _) ?_ (le_trans d h₁)
    ipra_ring
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) h₂)

/-- Variable `0 = p − 2`. -/
private abbrev localF : Fm PTm 1 :=
  le (pw (succ (succ (var 0))) (succ (succ (var 0)))) ((two * two) * pw (succ (var 0)) (succ (succ (var 0))))

private theorem local₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] localF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · refine le_congr (.eqRefl _) ?_ (le_refl _)
    refine withEq (pw_succ (Γ := []) (succ (succ zero) : PTm 0) (succ zero)) fun e₁ =>
      withEq (pw_succ (Γ := []) (succ (succ zero) : PTm 0) zero) fun e₂ =>
      withEq (pw_zero (Γ := []) (succ (succ zero) : PTm 0)) fun e₃ =>
      withEq (pw_succ (Γ := []) (succ zero : PTm 0) (succ zero)) fun e₄ =>
      withEq (pw_succ (Γ := []) (succ zero : PTm 0) zero) fun e₅ =>
      withEq (pw_zero (Γ := []) (succ zero : PTm 0)) fun e₆ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃, e₄, e₅, e₆]; ring
  · exact local_step Prf.hyp0

/-- `lem:local-factor`: `p^p ≤ 4 (p − 1)^p` for `p = m + 2 ≥ 2`. -/
theorem local_factor (m : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ (succ m)) (succ (succ m))) ((two * two) * pw (succ m) (succ (succ m))) := by
  have h := inst (Γ := Γ) local₀ (![m] : Fin 1 → PTm n)
  simpa using h

theorem local_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 localF :=
  closeUniv 1 (local_factor _)

end LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor

export_ipra AnalyticNumberTheory.LocalFactor (pw_mul_base)

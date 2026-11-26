import IPRADerivations.Analysis.Exponential.ExponentialSeries

/-!
# The finite exponential majorant

Packet: `analysis/barnes_g_ipra_2026-11-16`, `paper/sections/14_appendix_estimates.tex`, Lemma
`lem:exp-majorant` ("Finite exponential majorant"): "Let `u ∈ ℚ` satisfy `0 ≤ u < 1`. Then
`e^u ≤ 1/(1 − u)` and `0 ≤ e^u − 1 − u ≤ u²/(2(1 − u))`", proved from `j! ≥ 1`, `j! ≥ 2` for `j ≥ 2`,
and "the finite identity `(1 − u) ∑_{j<M} u^j = 1 − u^M`".

For `u = a/b` with `b = a + c` (`a = fst x`, `c = snd x`), all partial sums cleared of denominators and
defined by their own recursions:

* `Gg i x = ∑_{r<i} b^{i−1−r} a^r` (`G_0 = 0`, `G_{i+1} = b G_i + a^i`); `geom`: `c G_i + a^i = b^i`,
  the finite geometric identity;
* `Ee M x = M! b^M ∑_{k ≤ M} u^k/k!` (`E_0 = 1`, `E_{M+1} = (M + 1) b E_M + a^{M+1}`);
  `exp_le_geom`: `E_M ≤ M! G_{M+1}` (termwise `k! ≥ 1`);
* `exp_majorant`: `c E_M + M! a^{M+1} ≤ M! b^{M+1}`, i.e.
  `(1 − u) ∑_{k ≤ M} u^k/k! ≤ 1 − u^{M+1}`, the first bound at every finite stage;
* `Rr N x = (N + 1)! b^{N+1} ∑_{2 ≤ k ≤ N+1} u^k/k!` (`R_0 = 0`,
  `R_{N+1} = (N + 2) b R_N + a^{N+2}`); `exp_split`:
  `E_{N+1} = (N + 1)! b^{N+1} + (N + 1)! a b^N + R_N`, i.e. `R` is the partial sum minus `1 + u`;
* `rem_le_geom`: `2 R_N ≤ (N + 1)! a² G_N` (termwise `k! ≥ 2` for `k ≥ 2`);
* `rem_majorant`: `2c R_N + (N + 1)! a² a^N ≤ (N + 1)! a² b^N`, i.e.
  `2 (1 − u) ∑_{2 ≤ k ≤ N+1} u^k/k! ≤ u² (1 − u^N)`, the second bound at every finite stage.

The lower bound `0 ≤ e^u − 1 − u` is the nonnegativity of `R`. The passage to the limit and the complex
estimate are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ExponentialMajorant

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The three recursions -/

/-- Step variables: `0 = i`, `1 = G_i`, `2 = x`. -/
abbrev gStep : PTm 3 := (fstT (var 2) + sndT (var 2)) * var 1 + pw (fstT (var 2)) (var 0)
abbrev gF : PR 2 := rec2 zero gStep
/-- `G_i = ∑_{r<i} b^{i−1−r} a^r`. -/
abbrev Gg (i x : PTm n) : PTm n := ap2 gF i x

abbrev eStep : PTm 3 :=
  succ (var 0) * (fstT (var 2) + sndT (var 2)) * var 1 + pw (fstT (var 2)) (succ (var 0))
abbrev eF : PR 2 := rec2 (succ zero) eStep
/-- `E_M = M! b^M ∑_{k ≤ M} u^k/k!`. -/
abbrev Ee (M x : PTm n) : PTm n := ap2 eF M x

abbrev rStep : PTm 3 :=
  succ (succ (var 0)) * (fstT (var 2) + sndT (var 2)) * var 1 + pw (fstT (var 2)) (succ (succ (var 0)))
abbrev rF : PR 2 := rec2 zero rStep
/-- `R_N = (N + 1)! b^{N+1} ∑_{2 ≤ k ≤ N+1} u^k/k!`. -/
abbrev Rr (N x : PTm n) : PTm n := ap2 rF N x

theorem Gg_zero (x : PTm n) : Γ ⊢[PRAAx] Gg zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero gStep x
  simpa using h

theorem Gg_succ (i x : PTm n) :
    Γ ⊢[PRAAx] Gg (succ i) x ≐ (fstT x + sndT x) * Gg i x + pw (fstT x) i := by
  have h := rec2_succ (Γ := Γ) zero gStep i x
  simpa using h

theorem Ee_zero (x : PTm n) : Γ ⊢[PRAAx] Ee zero x ≐ succ zero := by
  have h := rec2_zero (Γ := Γ) (succ zero) eStep x
  simpa using h

theorem Ee_succ (M x : PTm n) :
    Γ ⊢[PRAAx] Ee (succ M) x ≐ succ M * (fstT x + sndT x) * Ee M x + pw (fstT x) (succ M) := by
  have h := rec2_succ (Γ := Γ) (succ zero) eStep M x
  simpa using h

theorem Rr_zero (x : PTm n) : Γ ⊢[PRAAx] Rr zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero rStep x
  simpa using h

theorem Rr_succ (N x : PTm n) :
    Γ ⊢[PRAAx] Rr (succ N) x ≐
      succ (succ N) * (fstT x + sndT x) * Rr N x + pw (fstT x) (succ (succ N)) := by
  have h := rec2_succ (Γ := Γ) zero rStep N x
  simpa using h

/-! ## The geometric identity -/

theorem geom_base (x : PTm n) :
    Γ ⊢[PRAAx] sndT x * Gg zero x + pw (fstT x) zero ≐ pw (fstT x + sndT x) zero := by
  ipra_lc 𝔟(sndT x) * natEq (Gg_zero (Γ := Γ) x) + natEq (pw_zero (Γ := Γ) (fstT x)) -
    natEq (pw_zero (Γ := Γ) (fstT x + sndT x))

theorem geom_step {i x : PTm n}
    (ih : Γ ⊢[PRAAx] sndT x * Gg i x + pw (fstT x) i ≐ pw (fstT x + sndT x) i) :
    Γ ⊢[PRAAx] sndT x * Gg (succ i) x + pw (fstT x) (succ i) ≐ pw (fstT x + sndT x) (succ i) := by
  ipra_lc 𝔟(sndT x) * natEq (Gg_succ (Γ := Γ) i x) + natEq (pw_succ (Γ := Γ) (fstT x) i) -
    natEq (pw_succ (Γ := Γ) (fstT x + sndT x) i) + (𝔟(fstT x) + 𝔟(sndT x)) * natEq ih

/-- Variables: `0 = i`, `1 = x`. -/
private abbrev geomF : Fm PTm 2 :=
  sndT (var 1) * Gg (var 0) (var 1) + pw (fstT (var 1)) (var 0) ≐ pw (fstT (var 1) + sndT (var 1)) (var 0)

private theorem geom₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] geomF := by
  refine ind _ trivial ?_ ?_
  · have e : geomF.subst (Syn.inst zero) =
        (sndT (var 0) * Gg zero (var 0) + pw (fstT (var 0)) zero ≐
          pw (fstT (var 0) + sndT (var 0)) zero : Fm PTm 1) := by
      simp
    rw [e]
    exact geom_base _
  · have e : geomF.subst (repl (succ (var 0))) =
        (sndT (var 1) * Gg (succ (var 0)) (var 1) + pw (fstT (var 1)) (succ (var 0)) ≐
          pw (fstT (var 1) + sndT (var 1)) (succ (var 0)) : Fm PTm 2) := by
      simp
    rw [e]
    exact geom_step Prf.hyp0

/-- The finite geometric identity `c G_i + a^i = b^i`, `b = a + c`. -/
theorem geom (i x : PTm n) :
    Γ ⊢[PRAAx] sndT x * Gg i x + pw (fstT x) i ≐ pw (fstT x + sndT x) i := by
  have h := inst (Γ := Γ) geom₀ (![i, x] : Fin 2 → PTm n)
  simpa using h

/-! ## The first bound -/

theorem el_base (x : PTm n) : Γ ⊢[PRAAx] le (Ee zero x) (fact zero * Gg (succ zero) x) := by
  have e₀ := natEq (Ee_zero (Γ := Γ) x)
  have f₀ := natEq (fact_zero (Γ := Γ) (zero : PTm n))
  have g₁ := natEq (Gg_succ (Γ := Γ) zero x)
  have g₀ := natEq (Gg_zero (Γ := Γ) x)
  have p₀ := natEq (pw_zero (Γ := Γ) (fstT x))
  ipra_le 0 using linear_combination 𝔟(Gg (succ zero) x) * f₀ + g₁ + (𝔟(fstT x) + 𝔟(sndT x)) * g₀ +
    p₀ - e₀

theorem el_step {M x : PTm n} (ih : Γ ⊢[PRAAx] le (Ee M x) (fact M * Gg (succ M) x)) :
    Γ ⊢[PRAAx] le (Ee (succ M) x) (fact (succ M) * Gg (succ (succ M)) x) := by
  have es := natEq (Ee_succ (Γ := Γ) M x)
  have fs := natEq (fact_succ (Γ := Γ) M zero)
  have gs := natEq (Gg_succ (Γ := Γ) (succ M) x)
  have fp := natEq (fact_pos (Γ := Γ) M)
  ipra_le (𝔟 M + 1) * (𝔟(fstT x) + 𝔟(sndT x)) * sl ih +
      (𝔟(pred (fact M)) * (𝔟 M + 1) + 𝔟 M) * 𝔟(pw (fstT x) (succ M)) using
    linear_combination 𝔟(Gg (succ (succ M)) x) * fs + 𝔟(fact M) * (𝔟 M + 1) * gs - es +
      (𝔟 M + 1) * 𝔟(pw (fstT x) (succ M)) * fp

/-- Variables: `0 = M`, `1 = x`. -/
private abbrev elF : Fm PTm 2 :=
  le (Ee (var 0) (var 1)) (fact (var 0) * Gg (succ (var 0)) (var 1))

private theorem el₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] elF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · have e : elF.subst (Syn.inst zero) =
        (le (Ee zero (var 0)) (fact zero * Gg (succ zero) (var 0)) : Fm PTm 1) := by
      simp
    rw [e]
    exact el_base _
  · have e : elF.subst (repl (succ (var 0))) =
        (le (Ee (succ (var 0)) (var 1)) (fact (succ (var 0)) * Gg (succ (succ (var 0))) (var 1)) :
          Fm PTm 2) := by
      simp
    rw [e]
    exact el_step Prf.hyp0

/-- `E_M ≤ M! G_{M+1}`: the partial sums of `e^u` are below the geometric partial sums. -/
theorem exp_le_geom (M x : PTm n) : Γ ⊢[PRAAx] le (Ee M x) (fact M * Gg (succ M) x) := by
  have h := inst (Γ := Γ) el₀ (![M, x] : Fin 2 → PTm n)
  simpa using h

/-- `lem:exp-majorant`, the first bound at the stage `M`: `c E_M + M! a^{M+1} ≤ M! b^{M+1}`, i.e.
`(1 − u) ∑_{k ≤ M} u^k/k! ≤ 1 − u^{M+1}`. -/
theorem exp_majorant (M x : PTm n) :
    Γ ⊢[PRAAx] le (sndT x * Ee M x + fact M * pw (fstT x) (succ M))
      (fact M * pw (fstT x + sndT x) (succ M)) := by
  have h := exp_le_geom (Γ := Γ) M x
  have ge := natEq (geom (Γ := Γ) (succ M) x)
  ipra_le 𝔟(sndT x) * sl h using linear_combination -𝔟(fact M) * ge

/-! ## The second bound -/

theorem rl_base (x : PTm n) :
    Γ ⊢[PRAAx] le (two * Rr zero x) (fact (succ zero) * (fstT x * fstT x) * Gg zero x) := by
  have r₀ := natEq (Rr_zero (Γ := Γ) x)
  have g₀ := natEq (Gg_zero (Γ := Γ) x)
  ipra_le 0 using linear_combination 𝔟(fact (succ zero)) * 𝔟(fstT x) * 𝔟(fstT x) * g₀ - 2 * r₀

theorem rl_step {N x : PTm n}
    (ih : Γ ⊢[PRAAx] le (two * Rr N x) (fact (succ N) * (fstT x * fstT x) * Gg N x)) :
    Γ ⊢[PRAAx] le (two * Rr (succ N) x)
      (fact (succ (succ N)) * (fstT x * fstT x) * Gg (succ N) x) := by
  have rs := natEq (Rr_succ (Γ := Γ) N x)
  have fs := natEq (fact_succ (Γ := Γ) (succ N) zero)
  have gs := natEq (Gg_succ (Γ := Γ) N x)
  have p₁ := natEq (pw_succ (Γ := Γ) (fstT x) (succ N))
  have p₂ := natEq (pw_succ (Γ := Γ) (fstT x) N)
  have fp := natEq (fact_pos (Γ := Γ) (succ N))
  ipra_le (𝔟 N + 2) * (𝔟(fstT x) + 𝔟(sndT x)) * sl ih +
      (𝔟(pred (fact (succ N))) * (𝔟 N + 2) + 𝔟 N) * 𝔟(fstT x) * 𝔟(fstT x) * 𝔟(pw (fstT x) N) using
    linear_combination 𝔟(fstT x) * 𝔟(fstT x) * 𝔟(Gg (succ N) x) * fs +
      𝔟(fact (succ N)) * (𝔟 N + 2) * 𝔟(fstT x) * 𝔟(fstT x) * gs - 2 * rs - 2 * p₁ -
      2 * 𝔟(fstT x) * p₂ + (𝔟 N + 2) * 𝔟(fstT x) * 𝔟(fstT x) * 𝔟(pw (fstT x) N) * fp

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev rlF : Fm PTm 2 :=
  le (two * Rr (var 0) (var 1)) (fact (succ (var 0)) * (fstT (var 1) * fstT (var 1)) * Gg (var 0) (var 1))

private theorem rl₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] rlF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · have e : rlF.subst (Syn.inst zero) =
        (le (two * Rr zero (var 0)) (fact (succ zero) * (fstT (var 0) * fstT (var 0)) * Gg zero (var 0)) :
          Fm PTm 1) := by
      simp
    rw [e]
    exact rl_base _
  · have e : rlF.subst (repl (succ (var 0))) =
        (le (two * Rr (succ (var 0)) (var 1))
          (fact (succ (succ (var 0))) * (fstT (var 1) * fstT (var 1)) * Gg (succ (var 0)) (var 1)) :
          Fm PTm 2) := by
      simp
    rw [e]
    exact rl_step Prf.hyp0

/-- `2 R_N ≤ (N + 1)! a² G_N`: the terms of order at least two against the geometric sum. -/
theorem rem_le_geom (N x : PTm n) :
    Γ ⊢[PRAAx] le (two * Rr N x) (fact (succ N) * (fstT x * fstT x) * Gg N x) := by
  have h := inst (Γ := Γ) rl₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

/-- `lem:exp-majorant`, the second bound at the stage `N + 1`:
`2c R_N + (N + 1)! a² a^N ≤ (N + 1)! a² b^N`, i.e.
`2 (1 − u) ∑_{2 ≤ k ≤ N+1} u^k/k! ≤ u² (1 − u^N)`. -/
theorem rem_majorant (N x : PTm n) :
    Γ ⊢[PRAAx] le (two * sndT x * Rr N x + fact (succ N) * (fstT x * fstT x) * pw (fstT x) N)
      (fact (succ N) * (fstT x * fstT x) * pw (fstT x + sndT x) N) := by
  have h := rem_le_geom (Γ := Γ) N x
  have ge := natEq (geom (Γ := Γ) N x)
  ipra_le 𝔟(sndT x) * sl h using
    linear_combination -𝔟(fact (succ N)) * 𝔟(fstT x) * 𝔟(fstT x) * ge

/-! ## The remainder is the partial sum minus `1 + u` -/

theorem split_base (x : PTm n) :
    Γ ⊢[PRAAx] Ee (succ zero) x ≐
      fact (succ zero) * pw (fstT x + sndT x) (succ zero) +
        fact (succ zero) * fstT x * pw (fstT x + sndT x) zero + Rr zero x := by
  have es := natEq (Ee_succ (Γ := Γ) zero x)
  have e₀ := natEq (Ee_zero (Γ := Γ) x)
  have f₁ := natEq (fact_succ (Γ := Γ) (zero : PTm n) zero)
  have f₀ := natEq (fact_zero (Γ := Γ) (zero : PTm n))
  have pb₁ := natEq (pw_succ (Γ := Γ) (fstT x + sndT x) zero)
  have pb₀ := natEq (pw_zero (Γ := Γ) (fstT x + sndT x))
  have pa₁ := natEq (pw_succ (Γ := Γ) (fstT x) zero)
  have pa₀ := natEq (pw_zero (Γ := Γ) (fstT x))
  have r₀ := natEq (Rr_zero (Γ := Γ) x)
  apply deriveNat; ipra_simps
  rw [es, e₀, f₁, f₀, pb₁, pb₀, pa₁, pa₀, r₀]; ring

theorem split_step {N x : PTm n}
    (ih : Γ ⊢[PRAAx] Ee (succ N) x ≐
      fact (succ N) * pw (fstT x + sndT x) (succ N) +
        fact (succ N) * fstT x * pw (fstT x + sndT x) N + Rr N x) :
    Γ ⊢[PRAAx] Ee (succ (succ N)) x ≐
      fact (succ (succ N)) * pw (fstT x + sndT x) (succ (succ N)) +
        fact (succ (succ N)) * fstT x * pw (fstT x + sndT x) (succ N) + Rr (succ N) x := by
  ipra_lc natEq (Ee_succ (Γ := Γ) (succ N) x) + (𝔟 N + 2) * (𝔟(fstT x) + 𝔟(sndT x)) * natEq ih -
    natEq (Rr_succ (Γ := Γ) N x) -
    (𝔟(pw (fstT x + sndT x) (succ (succ N))) + 𝔟(fstT x) * 𝔟(pw (fstT x + sndT x) (succ N))) * natEq (fact_succ (Γ := Γ) (succ N) zero) -
    𝔟(fact (succ N)) * (𝔟 N + 2) * natEq (pw_succ (Γ := Γ) (fstT x + sndT x) (succ N)) -
    𝔟(fact (succ N)) * (𝔟 N + 2) * 𝔟(fstT x) * natEq (pw_succ (Γ := Γ) (fstT x + sndT x) N)

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev splitF : Fm PTm 2 :=
  Ee (succ (var 0)) (var 1) ≐
    fact (succ (var 0)) * pw (fstT (var 1) + sndT (var 1)) (succ (var 0)) +
      fact (succ (var 0)) * fstT (var 1) * pw (fstT (var 1) + sndT (var 1)) (var 0) + Rr (var 0) (var 1)

private theorem split₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] splitF := by
  refine ind _ trivial ?_ ?_
  · have e : splitF.subst (Syn.inst zero) =
        (Ee (succ zero) (var 0) ≐
          fact (succ zero) * pw (fstT (var 0) + sndT (var 0)) (succ zero) +
            fact (succ zero) * fstT (var 0) * pw (fstT (var 0) + sndT (var 0)) zero + Rr zero (var 0) :
          Fm PTm 1) := by
      simp
    rw [e]
    exact split_base _
  · have e : splitF.subst (repl (succ (var 0))) =
        (Ee (succ (succ (var 0))) (var 1) ≐
          fact (succ (succ (var 0))) * pw (fstT (var 1) + sndT (var 1)) (succ (succ (var 0))) +
            fact (succ (succ (var 0))) * fstT (var 1) * pw (fstT (var 1) + sndT (var 1)) (succ (var 0)) +
            Rr (succ (var 0)) (var 1) : Fm PTm 2) := by
      simp
    rw [e]
    exact split_step Prf.hyp0

/-- `E_{N+1} = (N + 1)! b^{N+1} + (N + 1)! a b^N + R_N`: the remainder is the partial sum of `e^u`
minus `1 + u`. -/
theorem exp_split (N x : PTm n) :
    Γ ⊢[PRAAx] Ee (succ N) x ≐
      fact (succ N) * pw (fstT x + sndT x) (succ N) +
        fact (succ N) * fstT x * pw (fstT x + sndT x) N + Rr N x := by
  have h := inst (Γ := Γ) split₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA.Analysis.ExponentialMajorant

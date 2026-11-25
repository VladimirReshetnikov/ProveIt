import IPRADerivations.Probability.Minkowski
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.Foundations.ObservationEstimates
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Regular names on a common dyadic scale

Packets (`docs/proofs/foundations`):

* `ipra_finite_use_framework_2026-11-15`, `sections/06_quantitative.tex`, Lemma `lem:sample-stability`
  ("Finite sample stability") and the regularity part of Proposition `prop:add-contract` ("Addition
  contract", the output sample `c(k) = a(k + 2) + b(k + 2)`);
* `ipra_cbip_framework_2026-11-16`, Lemma "Finite sample stability";
* `ipra_finite_observation`, `prop:name-arithmetic` (addition, "use `c(k) = a(k+2) + b(k+2)` and add the
  two regularity bounds").

A regular name satisfies `|a(m) − a(n)| ≤ 2^{-m} + 2^{-n}`. On a common scale `2^N` (samples as numerators
over one denominator and all indices in play below `N`), the error `2^{-m}` is the number
`eps N m = 2^{N ∸ m}`:

* `monus_anti`, `eps_anti`: `m ≤ m′` gives `N ∸ m′ ≤ N ∸ m` and `eps N m′ ≤ eps N m`;
* `eps_half`: for `m < N`, `eps N m = 2 · eps N (m + 1)`;
* `sample_stability` (`lem:sample-stability`): for `m, n ≥ k + 3` and `k + 2 < N`, a regularity instance
  `a_m ≤ a_n + (eps m + eps n)` gives `a_m ≤ a_n + eps (k + 2)`, i.e. `|a(m) − a(n)| ≤ 2^{-k-2}`;
* `add_regular` (`prop:add-contract`): from the regularity instances of `a` and `b` at the indices
  `k + 2`, `l + 2`, the sum name satisfies `c(k) ≤ c(l) + (eps k + eps l)`.

* `reciprocal_gap` (`thm:guarded-inverse` of the first packet, "Apartness-guarded inverse"): for two
  samples with `α ≤ 2q` and `α ≤ 2q′` (each at least `α/2`) and `d = |q − q′|`, `d α² ≤ 4 d q q′`, i.e.
  `|1/q − 1/q′| = d/(q q′) ≤ 4d/α²`.

Inequalities are one-sided; the other side is the same statement with the indices exchanged.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DyadicNames

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Minkowski (le_add_monus monus_le_of_le_add)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (monus_succ_of_lt)
open LeanProofs.IPRA.Foundations.ObservationEstimates (pw_exp_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `2^{-m}` on the scale `2^N`. -/
abbrev eps (N m : PTm n) : PTm n := pw two (monus N m)

theorem monus_anti {N m m' : PTm n} (h : Γ ⊢[PRAAx] le m m') :
    Γ ⊢[PRAAx] le (monus N m') (monus N m) := by
  have h₁ := le_add_monus (Γ := Γ) N m
  have h₂ : Γ ⊢[PRAAx] le N (m' + monus N m) := by ipra_le sl h₁ + sl h
  exact monus_le_of_le_add h₂

/-- The errors decrease with the index. -/
theorem eps_anti {N m m' : PTm n} (h : Γ ⊢[PRAAx] le m m') : Γ ⊢[PRAAx] le (eps N m') (eps N m) :=
  pw_exp_le (G' := one) (monus_anti h)

/-- `2^{-m} = 2 · 2^{-(m+1)}` below the scale. -/
theorem eps_half {N m : PTm n} (h : Γ ⊢[PRAAx] lt m N) :
    Γ ⊢[PRAAx] eps N m ≐ two * eps N (succ m) := by
  ipra_lc natEq (congrAp2 powF (monus_succ_of_lt h) (Prf.eqRefl (two : PTm n))) +
    natEq (pw_succ (Γ := Γ) two (monus N (succ m)))

/-- `lem:sample-stability`: samples of index at least `k + 3` differ by at most `2^{-k-2}`. -/
theorem sample_stability {N k m m' am am' : PTm n} (hk : Γ ⊢[PRAAx] lt (succ (succ k)) N)
    (hm : Γ ⊢[PRAAx] le (succ (succ (succ k))) m) (hm' : Γ ⊢[PRAAx] le (succ (succ (succ k))) m')
    (hreg : Γ ⊢[PRAAx] le am (am' + (eps N m + eps N m'))) :
    Γ ⊢[PRAAx] le am (am' + eps N (succ (succ k))) := by
  have e₁ := eps_anti (N := N) hm
  have e₂ := eps_anti (N := N) hm'
  have hh := natEq (eps_half hk)
  ipra_le sl hreg + sl e₁ + sl e₂ using linear_combination hh

/-- `prop:add-contract`: the sum name `c(k) = a(k + 2) + b(k + 2)` is regular. -/
theorem add_regular {N k l ak al bk bl : PTm n} (hk : Γ ⊢[PRAAx] lt (succ k) N)
    (hl : Γ ⊢[PRAAx] lt (succ l) N)
    (ha : Γ ⊢[PRAAx] le ak (al + (eps N (succ (succ k)) + eps N (succ (succ l)))))
    (hb : Γ ⊢[PRAAx] le bk (bl + (eps N (succ (succ k)) + eps N (succ (succ l))))) :
    Γ ⊢[PRAAx] le (ak + bk) (al + bl + (eps N k + eps N l)) := by
  have hk' : Γ ⊢[PRAAx] le (succ (succ k)) N := hk
  have hl' : Γ ⊢[PRAAx] le (succ (succ l)) N := hl
  have hk0 : Γ ⊢[PRAAx] le (succ k) N := by ipra_le sl hk' + 1
  have hl0 : Γ ⊢[PRAAx] le (succ l) N := by ipra_le sl hl' + 1
  have h1k := natEq (eps_half (m := k) hk0)
  have h2k := natEq (eps_half hk)
  have h1l := natEq (eps_half (m := l) hl0)
  have h2l := natEq (eps_half hl)
  ipra_le sl ha + sl hb + 2 * 𝔟 (eps N (succ (succ k))) + 2 * 𝔟 (eps N (succ (succ l))) using
    linear_combination h1k + 2 * h2k + h1l + 2 * h2l

/-- `thm:guarded-inverse`: `|1/q − 1/q′| ≤ 4 |q − q′| / α²` for samples at least `α/2`, cleared of
denominators. -/
theorem reciprocal_gap {d α q q' : PTm n} (h₁ : Γ ⊢[PRAAx] le α (q + q))
    (h₂ : Γ ⊢[PRAAx] le α (q' + q')) : Γ ⊢[PRAAx] le (d * (α * α)) (num 4 * (d * (q * q'))) := by
  ipra_le 𝔟 d * (sl h₁ * (2 * 𝔟 q') + 𝔟 α * sl h₂)

end LeanProofs.IPRA.Foundations.DyadicNames

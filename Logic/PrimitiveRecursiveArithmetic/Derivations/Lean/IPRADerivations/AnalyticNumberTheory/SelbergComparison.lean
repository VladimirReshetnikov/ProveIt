import IPRADerivations.AnalyticNumberTheory.TauLogAbel

/-!
# The comparison-function error (`pnt_ipra_constructive_2026-11-14`, `sb:comparison-error`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:divisor-approx`,
inequality `sb:comparison-error`: the comparison function `f(n) = τ(n) log n − 2cτ(n) + 4c²`
(`sb:comparison-function`) satisfies `|Σ_{n≤y} (f(n) − (log n)²)| ≤ 80√y(log y + 1)`.

With the packet's rational logarithm `λ_K`, `F = L!`, `u = F λ_K(N)`, `C = F c` (`c = H_X − λ_K(X)`),
`D = D(N)`, the Abel sum `A = A(N)` (`F T(N) = D u − A`, `TauLogAbel`) and `Q = Q(N) = F² P_2(N)`
(`HarmonicLogSquareSum`), the comparison sum in `F²`-units is

  `F² Σ_{n≤N} f(n) = F D u − F A − 2C F D + 4C² N`.

* `divisor_at`: `sb:divisor-bound` at `y = N` with `m = ⌊√N⌋` (all side conditions discharged);
* `comparison_upper`: `F² Σ f − Q ≤ 19 m F u + 22 m F C + F u + (u + 2C) S(N) + 2F S(N)`;
* `comparison_lower`: `Q − F² Σ f ≤ F u + 2u S(N) + 19 m F u + 16 m F C + 2F S(N)`;

i.e. `|Σ_{n≤N}(f(n) − λ(n)²)| ≤ 19⌊√N⌋λ + 22⌊√N⌋c + λ + (λ + 2)H_N + 2H_N + …`, inside the packet's
`80√y(log y + 1)` (`c ≤ 1`, `H_N ≤ λ + 1 + ⋯`). The certificates (the divisor bounds multiplied by `u ≥ 0`
and by `2C ≥ 0`, `TauLogAbel.tau_abel`, `HarmonicLogSquareSum.log_square_sum`) were found by exact
polynomial residuals, which vanish identically.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SelbergComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U Qs log_square_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorBound (divisor_upper divisor_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.TauLogAbel (As CT Tm tau_abel c_nonneg isqrt_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `16T`, `19T`, `22T` as terms. -/
abbrev c16 (T : PTm n) : PTm n := two * (two * (two * (two * T)))
abbrev c19 (T : PTm n) : PTm n := c16 T + two * T + T
abbrev c22 (T : PTm n) : PTm n := c16 T + two * (two * T) + two * T

/-- `sb:divisor-bound` at `y = k + 1`, `m = ⌊√(k+1)⌋`, for `k + 1 ≤ min(X, K)`, `K ≥ 1`, `KX ≤ L`. -/
theorem divisor_at {k K L X : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * X) L)
    (hyX : Γ ⊢[PRAAx] le (succ k) X) (hyK : Γ ⊢[PRAAx] le (succ k) K) :
    Γ ⊢[PRAAx] le (fact L * S (succ k) (succ k) + two * (succ k * S (K * X) (fact L)) + fact L * succ k)
        (succ k * S (K * succ k) (fact L) + succ k * S K (fact L) + two * (succ k * S X (fact L)) +
          two * (two * (two * (isqrt (succ k) * fact L)))) ⋏
      le (succ k * S (K * succ k) (fact L) + succ k * S K (fact L) + two * (succ k * S X (fact L)))
        (fact L * S (succ k) (succ k) + two * (succ k * S (K * X) (fact L)) + fact L * succ k +
          (two * (two * (two * (isqrt (succ k) * fact L))) + two * (isqrt (succ k) * fact L) +
            isqrt (succ k) * fact L)) := by
  have hm1 := isqrt_pos (Γ := Γ) k
  have h1 := isqrt_le (Γ := Γ) (succ k)
  have hm2 : Γ ⊢[PRAAx] lt (succ k) (succ (isqrt (succ k)) * succ (isqrt (succ k))) :=
    le_congr (.eqRefl _) (by ipra_ring) (lt_isqrt_succ_sq (succ k))
  have hmy : Γ ⊢[PRAAx] le (isqrt (succ k)) (succ k) := by
    have t := le_scale (isqrt (succ k)) hm1
    exact le_trans (by ipra_le sl t) h1
  have hmX := le_trans hmy hyX
  have hXL : Γ ⊢[PRAAx] le X L := le_trans (by have t := le_scale X hK; ipra_le sl t) hL
  have hmL := le_trans hmX hXL
  have hLy := le_trans (le_scale K hyX) hL
  exact .andI (divisor_upper hm1 h1 hm2 hmX hK hL hLy hmL) (divisor_lower hm1 h1 hm2 hmX hK hyK hL hLy hmL)

/-- `F² Σ_{n≤N} f(n) − Q(N) ≤ 19mFu + 22mFC + Fu + (u + 2C)S(N) + 2F S(N)` at `N = k + 1 ≤ min(X, K)`. -/
theorem comparison_upper {k K L X : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * X) L)
    (hyX : Γ ⊢[PRAAx] le (succ k) X) (hyK : Γ ⊢[PRAAx] le (succ k) K) :
    Γ ⊢[PRAAx] le (fact L * (S (succ k) (succ k) * U (succ k) K (fact L)) +
          two * (two * (CT K X (fact L) * (CT K X (fact L) * succ k))))
      (Qs (succ k) K (fact L) + fact L * As (succ k) K (fact L) +
        two * (CT K X (fact L) * (fact L * S (succ k) (succ k))) +
        (c19 (isqrt (succ k) * (fact L * U (succ k) K (fact L))) +
          c22 (isqrt (succ k) * (fact L * CT K X (fact L))) + fact L * U (succ k) K (fact L) +
          (U (succ k) K (fact L) + two * CT K X (fact L)) * S (succ k) (fact L) +
          two * (fact L * S (succ k) (fact L)))) := by
  have dv := divisor_at hK hL hyX hyK
  have ta := tau_abel hK hL hyX hyK
  have J := log_square_sum (k := k) hK (le_trans (le_scale K hyX) hL)
  have hX : Γ ⊢[PRAAx] le one X :=
    le_trans (le_of_eq_add (d := k) (by ipra_ring) : Γ ⊢[PRAAx] le one (succ k)) hyX
  have m1x : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have Eu := natEq (eq_add_of_le m1x)
  have EC := natEq (eq_add_of_le (c_nonneg hK hX hL))
  have s1 := le_scale (U (succ k) K (fact L)) (Prf.andE₁ dv)
  have s2 := le_scale (two * CT K X (fact L)) (Prf.andE₂ dv)
  ipra_le sl s1 + sl s2 + sl (Prf.andE₂ ta) + sl (Prf.andE₂ J) with
    (𝔞 k + 1) * (𝔞 (U (succ k) K (fact L)) - 2 * 𝔞 (CT K X (fact L)) - 𝔞 (fact L)) * (Eu + 2 * EC)

/-- `Q(N) − F² Σ_{n≤N} f(n) ≤ Fu + 2u S(N) + 19mFu + 16mFC + 2F S(N)` at `N = k + 1 ≤ min(X, K)`. -/
theorem comparison_lower {k K L X : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le (K * X) L)
    (hyX : Γ ⊢[PRAAx] le (succ k) X) (hyK : Γ ⊢[PRAAx] le (succ k) K) :
    Γ ⊢[PRAAx] le (Qs (succ k) K (fact L) + fact L * As (succ k) K (fact L) +
          two * (CT K X (fact L) * (fact L * S (succ k) (succ k))))
      (fact L * (S (succ k) (succ k) * U (succ k) K (fact L)) +
        two * (two * (CT K X (fact L) * (CT K X (fact L) * succ k))) +
        (fact L * U (succ k) K (fact L) + two * (U (succ k) K (fact L) * S (succ k) (fact L)) +
          c19 (isqrt (succ k) * (fact L * U (succ k) K (fact L))) +
          c16 (isqrt (succ k) * (fact L * CT K X (fact L))) +
          two * (fact L * S (succ k) (fact L)))) := by
  have dv := divisor_at hK hL hyX hyK
  have ta := tau_abel hK hL hyX hyK
  have J := log_square_sum (k := k) hK (le_trans (le_scale K hyX) hL)
  have hX : Γ ⊢[PRAAx] le one X :=
    le_trans (le_of_eq_add (d := k) (by ipra_ring) : Γ ⊢[PRAAx] le one (succ k)) hyX
  have m1x : Γ ⊢[PRAAx] le (S K (fact L)) (S (K * succ k) (fact L)) :=
    S_mono (fact L) (le_of_eq_add (d := K * k) (by ipra_ring))
  have Eu := natEq (eq_add_of_le m1x)
  have EC := natEq (eq_add_of_le (c_nonneg hK hX hL))
  have s1 := le_scale (two * CT K X (fact L)) (Prf.andE₁ dv)
  have s2 := le_scale (U (succ k) K (fact L)) (Prf.andE₂ dv)
  ipra_le sl (Prf.andE₁ J) + sl (Prf.andE₁ ta) + sl s1 + sl s2 with
    -((𝔞 k + 1) * (𝔞 (U (succ k) K (fact L)) - 2 * 𝔞 (CT K X (fact L)) - 𝔞 (fact L))) * (Eu + 2 * EC)

end LeanProofs.IPRA.AnalyticNumberTheory.SelbergComparison

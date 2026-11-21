import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.Gcd

/-!
# Cauchy–Schwarz for a positive Hermitian form from num 2 positivity instances

Packet: `analysis/quantum_ipra_2026-11-20`, `finite.tex`, Lemma `lem:q-forms`: "A positive Hermitian form `h`
satisfies `|h(x, y)|² ≤ h(x, x) h(y, y)`."

Write `a = h(x, x)`, `s = h(y, y)` and `N = |t|²` for `t = h(x, y)` (natural numerators on a common scale).
Positivity of `h` at the num 2 vectors `s x − t̄ y` and `x − (a + 1) t̄ y` expands, by sesquilinearity, to the
num 2 polynomial inequalities

* `s N ≤ s² a` (that is, `h(sx − t̄y, sx − t̄y) = s (s a − |t|²) ≥ 0`), and
* `2 (a + 1) N ≤ a + (a + 1)² N s` (that is, `h(x − (a+1)t̄y, ·) = a − 2(a+1)|t|² + (a+1)² |t|² s ≥ 0`).

`form_cauchy_schwarz` derives `N ≤ a s` from these, by the case distinction `s = 0` or `s ≥ 1` on the
natural number `s`: for `s ≥ 1` the first instance is cancelled by `s`; for `s = 0` the second forces `N = 0`.
No division and no real square root is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.Quantum.FormCauchySchwarz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `lem:q-forms`: `|h(x, y)|² ≤ h(x, x) h(y, y)` from num 2 positivity instances. -/
theorem form_cauchy_schwarz {a s N : PTm n} (h1 : Γ ⊢[PRAAx] le (s * N) (s * s * a))
    (h2 : Γ ⊢[PRAAx] le (num 2 * succ a * N) (a + succ a * succ a * N * s)) :
    Γ ⊢[PRAAx] le N (a * s) := by
  refine .orE (zero_or_succ s) ?_ ?_
  · -- `s = 0`: the second instance gives `2(a+1)N ≤ a`, so `N = 0`.
    let Δ := (s ≐ zero) :: Γ
    have es := natEq (Prf.hyp0 : Δ ⊢[PRAAx] s ≐ zero)
    have h2' : Δ ⊢[PRAAx] le (num 2 * succ a * N) (a + succ a * succ a * N * s) := h2.wk
    refine .orE (zero_or_succ N) ?_ ?_
    · have eN := natEq (Prf.hyp0 : ((N ≐ zero) :: Δ) ⊢[PRAAx] N ≐ zero)
      ipra_le 𝔟 a * 𝔟 s with eN
    · let Δ' := (N ≐ succ (pred N)) :: Δ
      have eN := natEq (Prf.hyp0 : Δ' ⊢[PRAAx] N ≐ succ (pred N))
      have es' := natEq (Prf.hyp1 : Δ' ⊢[PRAAx] s ≐ zero)
      have h2'' : Δ' ⊢[PRAAx] le (num 2 * succ a * N) (a + succ a * succ a * N * s) := h2'.wk
      have hlt : Δ' ⊢[PRAAx] lt (a + succ a * succ a * N * s) (num 2 * succ a * N) := by
        show Δ' ⊢[PRAAx] le (succ (a + succ a * succ a * N * s)) (num 2 * succ a * N)
        ipra_le 𝔟 a + 1 + 2 * (𝔟 a + 1) * 𝔟 (pred N) with
          (2 * 𝔟 a + 2) * eN - (𝔟 a + 1) ^ 2 * 𝔟 N * es'
      exact le_lt_absurd _ h2'' hlt
  · -- `s ≥ 1`: cancel `s` in `s N ≤ s (s a)`.
    let Δ := (s ≐ succ (pred s)) :: Γ
    have e := natEq (Prf.hyp0 : Δ ⊢[PRAAx] s ≐ succ (pred s))
    have h1w : Δ ⊢[PRAAx] le (s * N) (s * s * a) := h1.wk
    have h1' : Δ ⊢[PRAAx] le (succ (pred s) * N) (succ (pred s) * (a * s)) := by
      ipra_le sl h1w with (𝔟 N - 𝔟 a * 𝔟 s) * e
    exact mul_le_cancel h1'

end LeanProofs.IPRA.Analysis.Quantum.FormCauchySchwarz

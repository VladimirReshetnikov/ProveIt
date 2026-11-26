import IPRADerivations.AnalyticNumberTheory.HarmonicMertensLower
import IPRADerivations.DiophantineNumberTheory.HurwitzLoop
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The signed logarithmic mean for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, inequality
`sb:signed-integral` (`|∫_a^b R(u)/u² du| ≤ 20`), which is `con:signed` after `x = e^w`. The packet proves it
from the exact telescoping identity `∫_1^x R(t)/t² dt = A_1(x) − ψ(x)/x − log x` (`A_1(x) = ∑_{n≤x} Λ(n)/n`)
and the bound `|A_1(x) − ψ(x)/x − log x| ≤ 10`; the integral is notation for that finite sum. At integer
`x = N`, for the packet's rational logarithm `λ_M` (common denominator `F = L!`, mesh `M ≥ N`), write
`Q(N) = A_1(N) − ψ(N)/N − λ_M(N)`, with common denominator `D = N · N! · F`:

* `signed_upper`: `Q(N) ≤ 5`, i.e. `N S_w(N) + N N! S(M) ≤ N! Ψ_w(N) + N N! (S(MN) + 5F)`;
* `signed_lower`: `Q(N) ≥ −6`, i.e. `N N! S(MN) + N! Ψ_w(N) ≤ N S_w(N) + N N! (S(M) + 6F)`.

So `|Q(N)| ≤ 6` and `|Q(b) − Q(a)| ≤ 12 ≤ 20` for all integer endpoints — the finite-stage
`sb:signed-integral`. The inputs are `mertens_upper`, `mertens_lower` and `psi_le`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicSignedMean

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt psi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale mertens_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (mertens_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (Sw)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi pos_of_lt_zero)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `N ⌊F/M⌋ ≤ F` for `1 ≤ N ≤ M`. -/
theorem nq_le {N M F : PTm n} (hM : Γ ⊢[PRAAx] le one M) (hNM : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (N * quo F M) F := by
  have qm := DiophantineNumberTheory.HurwitzLoop.quo_mul_le (x := F) (pos_of_lt_zero hM)
  have l : Γ ⊢[PRAAx] le (N * quo F M) (quo F M * M) := by
    refine le_of_eq_add (d := quo F M * monus M N) ?_
    ipra_lc 𝔞 (quo F M) * natEq (eq_add_of_le hNM)
  exact le_trans l qm

/-- `sb:signed-integral`, upper half: `Q(N) = A_1(N) − ψ(N)/N − λ_M(N) ≤ 5`. -/
theorem signed_upper {N M L : PTm n} (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M)
    (hNN : Γ ⊢[PRAAx] le (M * pw N N) L) (h2 : Γ ⊢[PRAAx] le (M * pw two (two * (two * N))) L) :
    Γ ⊢[PRAAx] le (N * Sw wt N (pairT M (fact L)) + N * fact N * S M (fact L))
      (fact N * Psi wt N (pairT M (fact L)) + N * fact N * (S (M * N) (fact L) + (fact L + two * (two * fact L)))) := by
  have mu := le_scale N (mertens_upper hN hM hNN h2)
  have q1 := le_scale (N * fact N) (nq_le (N := one) (F := fact L) hM hM)
  ipra_le sl mu + sl q1 + 𝔞 (fact N) * 𝔞 (Psi wt N (pairT M (fact L)))

/-- `sb:signed-integral`, lower half: `Q(N) ≥ −6` for `N ≤ M`. -/
theorem signed_lower {N M L : PTm n} (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M)
    (hNM : Γ ⊢[PRAAx] le N M) (hL : Γ ⊢[PRAAx] le (M * N) L)
    (h2 : Γ ⊢[PRAAx] le (M * pw two (two * (two * N))) L) :
    Γ ⊢[PRAAx] le (N * fact N * S (M * N) (fact L) + fact N * Psi wt N (pairT M (fact L)))
      (N * Sw wt N (pairT M (fact L)) + N * fact N * (S M (fact L) + (two * fact L + two * (two * fact L)))) := by
  have ml := le_scale N (mertens_lower hN hM hL)
  have q1 := le_scale (N * fact N) (nq_le (F := fact L) hM hNM)
  have ps := le_scale (fact N) (psi_le hM h2)
  ipra_le sl ml + sl q1 + sl ps

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicSignedMean

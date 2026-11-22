import IPRADerivations.Algebra.PowerDifference
import IPRADerivations.Core.OrderCertificates

/-!
# Rational widths with a surplus for simultaneous Dirichlet approximation

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:simultaneous`, Subsection "Choose
rational widths with a surplus". With `X = N + 1/2`, `g = 1/(N(2N+1))`, `H = 4dN(2N+1)`, `T = 1/X + g/4`, the width
`R = k/H` is the least `k ≤ H` with `(k/H)^d ≥ T`, and `S = (k + 1)/H`. Cleared of denominators, with
`c = 4N(2N+1)`, `H = d c` and `T = (8N + 1)/(c)`, the condition "`k` qualifies" reads `(8N + 1) H^d ≤ c k^d`.

* `widths_top` (the finite Bernoulli inequality): `H − 1` qualifies, so the search ends with `k ≤ H − 1`:
  `(1 − 1/H)^d ≥ 1 − d/H = 1 − g/4 > T`;
* `widths_S` (`eq:sim-S`): if `k − 1` does not qualify and `k + 1 ≤ H`, then `N S^d < 1`, i.e.
  `N (k + 1)^d < H^d`, using the finite factorization `b^d − a^d ≤ d (b − a)` on `[0, 1]`
  (`PowerDifference.power_diff`, `gd_le`).

Here `N = N' + 1`, `d = d' + 1` and `c = 8N'² + 20N' + 12`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousWidths

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.PowerDifference (gd power_diff gd_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `c − 1 = 4N(2N+1) − 1` for `N = N' + 1`. -/
abbrev cPred (N' : PTm n) : PTm n := num 8 * N' * N' + num 20 * N' + num 11
/-- `c = 4N(2N+1)`. -/
abbrev cT (N' : PTm n) : PTm n := succ (cPred N')
/-- `H = 4dN(2N+1) = d c`. -/
abbrev HT (N' d' : PTm n) : PTm n := succ d' * cT N'
/-- `H − 1`. -/
abbrev hT (N' d' : PTm n) : PTm n := d' * cT N' + cPred N'
/-- `8N + 1`. -/
abbrev aT (N' : PTm n) : PTm n := num 8 * N' + num 9

/-- `H − 1` qualifies: `(8N + 1) H^d ≤ c (H − 1)^d`. -/
theorem widths_top (N' d' : PTm n) :
    Γ ⊢[PRAAx] le (aT N' * pw (HT N' d') (succ d')) (cT N' * pw (hT N' d') (succ d')) := by
  have hy : Γ ⊢[PRAAx] le (hT N' d') (HT N' d') :=
    le_of_eq_add (d := one) (by apply deriveNat; ipra_simps; ring)
  have gl := gd_le d' (le_refl (HT N' d')) hy
  have pd := natEq (power_diff (Γ := Γ) (HT N' d') (hT N' d') (succ d'))
  have ps := natEq (pw_succ (Γ := Γ) (HT N' d') d')
  ipra_le (8 * 𝔟 N' ^ 2 + 20 * 𝔟 N' + 12) * sl gl +
      𝔟 (pw (HT N' d') d') * 𝔟 (HT N' d') * (8 * 𝔟 N' ^ 2 + 12 * 𝔟 N' + 2) with
    (-(8 * 𝔟 N' ^ 2 + 20 * 𝔟 N' + 12)) * pd + (8 * 𝔟 N' ^ 2 + 12 * 𝔟 N' + 3) * ps

/-- `1 ≤ H^{d'}`. -/
theorem one_le_pw (N' d' : PTm n) : Γ ⊢[PRAAx] le one (pw (HT N' d') d') := by
  have h1 : Γ ⊢[PRAAx] le one (HT N' d') := le_of_eq_add (d := hT N' d') (by apply deriveNat; ipra_simps; ring)
  exact le_congr (pw_one_base d') (.eqRefl _) (pw_le_pw d' h1)

/-- `eq:sim-S`: if `k − 1` does not qualify and `k + 1 ≤ H`, then `N (k + 1)^d < H^d`. -/
theorem widths_S {N' d' k' : PTm n}
    (hmin : Γ ⊢[PRAAx] lt (cT N' * pw k' (succ d')) (aT N' * pw (HT N' d') (succ d')))
    (hk : Γ ⊢[PRAAx] le (succ (succ k')) (HT N' d')) :
    Γ ⊢[PRAAx] lt (succ N' * pw (succ (succ k')) (succ d')) (pw (HT N' d') (succ d')) := by
  have hy : Γ ⊢[PRAAx] le k' (HT N' d') :=
    le_trans (le_of_eq_add (d := num 2) (by apply deriveNat; ipra_simps; ring)) hk
  have gl := gd_le d' hk hy
  have pd := natEq (power_diff (Γ := Γ) (succ (succ k')) k' (succ d'))
  have ps := natEq (pw_succ (Γ := Γ) (HT N' d') d')
  have hp := one_le_pw (Γ := Γ) N' d'
  have hm : Γ ⊢[PRAAx] le (succ (cT N' * pw k' (succ d'))) (aT N' * pw (HT N' d') (succ d')) := hmin
  show Γ ⊢[PRAAx] le (succ (succ N' * pw (succ (succ k')) (succ d'))) (pw (HT N' d') (succ d'))
  refine mul_le_cancel (d' := cPred N') ?_
  ipra_le (8 * 𝔟 N' ^ 2 + 20 * 𝔟 N' + 12) *
        ((𝔟 N' + 1) * (𝔟 d' + 1) * sl hp + 𝔟 N' * 𝔟 d' + 𝔟 N' + 𝔟 d') +
      (𝔟 N' + 1) + (𝔟 N' + 1) * sl hm + 2 * (8 * 𝔟 N' ^ 2 + 20 * 𝔟 N' + 12) * (𝔟 N' + 1) * sl gl with
    (-((8 * 𝔟 N' ^ 2 + 20 * 𝔟 N' + 12) * (𝔟 N' + 1))) * pd + 3 * (𝔟 N' + 1) * ps

end LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousWidths

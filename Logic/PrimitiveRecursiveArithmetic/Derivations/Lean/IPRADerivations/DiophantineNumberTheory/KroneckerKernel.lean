import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid
import IPRADerivations.Core.Header

/-!
# The kernel-tail constant of the quantitative Kronecker theorem

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:kronecker`, `eq:k-constants` and
`eq:kernel-tail`: with `t = 2s`, `k = d + 1`, `r = 4·3^d (d+1)^{d+1} t^{2d+2}` and `A = (2r+1)^d`,
"`(k t²/r)^k = 1/(4(3r)^d) ≤ 1/(4(2r+1)^d) = 1/(4A)`". Cleared of denominators:

* `kernel_const`: `4 (3r)^d (k t²)^k = r^k`;
* `kernel_tail`: `4 (2r+1)^d (k t²)^k ≤ r^k` (since `2r + 1 ≤ 3r` for `r ≥ 1`), i.e. `(k t²/r)^k ≤ 1/(4A)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.KroneckerKernel

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (one_le_pw_of)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `r = 4·3^d (d+1)^{d+1} (t²)^{d+1}`. -/
abbrev rT (d t : PTm n) : PTm n := num 4 * pw (num 3) d * pw (succ d) (succ d) * pw (t * t) (succ d)

/-- `eq:kernel-tail`: `4 (3r)^d (k t²)^k = r^k` with `k = d + 1`. -/
theorem kernel_const (d t : PTm n) :
    Γ ⊢[PRAAx] num 4 * pw (num 3 * rT d t) d * pw (succ d * (t * t)) (succ d) ≐ pw (rT d t) (succ d) := by
  have e1 := natEq (mul_pw (Γ := Γ) (num 3) (rT d t) d)
  have e2 := natEq (mul_pw (Γ := Γ) (succ d) (t * t) (succ d))
  have e3 := natEq (pw_succ (Γ := Γ) (rT d t) d)
  apply deriveNat; ipra_simps
  rw [e1, e2, e3]; ring

/-- `eq:kernel-tail`: `4 (2r+1)^d (k t²)^k ≤ r^k`, i.e. `(k t²/r)^k ≤ 1/(4A)`, for `t ≥ 1`. -/
theorem kernel_tail {d t : PTm n} (ht : Γ ⊢[PRAAx] le one t) :
    Γ ⊢[PRAAx] le (num 4 * pw (num 2 * rT d t + one) d * pw (succ d * (t * t)) (succ d)) (pw (rT d t) (succ d)) := by
  have htt : Γ ⊢[PRAAx] le one (t * t) := by ipra_le (𝔟 t + 1) * sl ht
  have h3 := one_le_pw_of d (show Γ ⊢[PRAAx] le one (num 3) by ipra_le 2)
  have hk := one_le_pw_of (succ d) (show Γ ⊢[PRAAx] le one (succ d) by ipra_le 𝔟 d)
  have hT := one_le_pw_of (succ d) htt
  -- `r ≥ 1`, so `2r + 1 ≤ 3r`
  have hr : Γ ⊢[PRAAx] le one (rT d t) := by
    ipra_le 4 * (sl h3 * sl hk * sl hT + sl h3 * sl hk + sl h3 * sl hT + sl hk * sl hT + sl h3 + sl hk + sl hT) + 3
  have h23 : Γ ⊢[PRAAx] le (num 2 * rT d t + one) (num 3 * rT d t) := by ipra_le sl hr
  have m := pw_le_pw d h23
  have c := kernel_const (Γ := Γ) d t
  refine le_congr (.eqRefl _) c ?_
  ipra_le 4 * 𝔟 (pw (succ d * (t * t)) (succ d)) * sl m

end LeanProofs.IPRA.DiophantineNumberTheory.KroneckerKernel

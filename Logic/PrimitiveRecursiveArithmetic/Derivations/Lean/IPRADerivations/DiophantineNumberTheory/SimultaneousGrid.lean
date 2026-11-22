import IPRADerivations.DiophantineNumberTheory.SimultaneousWidths
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# The skew-grid count for simultaneous Dirichlet approximation

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:simultaneous`, Subsection "Count a
finite skew grid": with `M = 16Nd(N+1)`, `A = MX = 8Nd(N+1)(2N+1)` and `B = ⌊MR⌋` (`R = k/H`),
"`AB^d/M^{d+1} = Xz^d > XR^d − Xd/M ≥ 1 + 1/(8N) − Xd/M > 1` ... Hence `AB^d ≥ M^{d+1} + 1`."

Cleared of denominators (`SimultaneousWidths`: `c = 4N(2N+1)`, `H = dc`, `k` qualifies when
`(8N + 1) H^d ≤ c k^d`), with `B` given by `HB ≤ Mk < H(B + 1)`:

* `grid_count`: `M^{d+1} < A B^d`.

The proof multiplies by `c H^d`: the power difference `(Mk)^d − (HB)^d = (Mk − HB) gd` with
`gd ≤ d (MH)^{d−1}` (`PowerDifference`) and `Mk − HB < H` bound the loss, and the surplus
`A(M − H) − c = c Q` with `Q = 8Nd²(N+1)(2N+3) − 1 ≥ 79` absorbs it; the certificate was found with `sympy`.
`cancel_pos` cancels the positive factor `H^d`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.PowerDifference (gd power_diff gd_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousWidths (cPred cT HT hT aT)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `M = 16Nd(N+1)`. -/
abbrev MT (N' d' : PTm n) : PTm n := num 16 * succ N' * succ d' * succ (succ N')
/-- `A = MX = 8Nd(N+1)(2N+1)`. -/
abbrev AT (N' d' : PTm n) : PTm n := num 8 * succ N' * succ d' * succ (succ N') * (num 2 * succ N' + one)

/-- Cancel a positive factor. -/
theorem cancel_pos {X a b : PTm n} (hX : Γ ⊢[PRAAx] le one X) (h : Γ ⊢[PRAAx] le (X * a) (X * b)) :
    Γ ⊢[PRAAx] le a b := by
  refine .orE (zero_or_succ X) ?_ ?_
  · exact le_lt_absurd _ (a := one) (b := zero) (le_congr (.eqRefl _) Prf.hyp0 hX.wk) (zero_lt_succ zero)
  · refine mul_le_cancel (d' := pred X) ?_
    exact le_congr (congrMul Prf.hyp0 (.eqRefl _)) (congrMul Prf.hyp0 (.eqRefl _)) h.wk

theorem one_le_pw_of {X : PTm n} (m : PTm n) (h : Γ ⊢[PRAAx] le one X) : Γ ⊢[PRAAx] le one (pw X m) :=
  le_congr (pw_one_base m) (.eqRefl _) (pw_le_pw m h)

/-- `thm:simultaneous`, the grid count: `M^{d+1} < A B^d` for `HB ≤ Mk < H(B + 1)`, `k ≤ H` qualifying. -/
theorem grid_count {N' d' k B : PTm n}
    (hq : Γ ⊢[PRAAx] le (aT N' * pw (HT N' d') (succ d')) (cT N' * pw k (succ d')))
    (hkH : Γ ⊢[PRAAx] le k (HT N' d'))
    (hf1 : Γ ⊢[PRAAx] le (HT N' d' * B) (MT N' d' * k))
    (hf2 : Γ ⊢[PRAAx] lt (MT N' d' * k) (HT N' d' * B + HT N' d')) :
    Γ ⊢[PRAAx] lt (pw (MT N' d') (succ (succ d'))) (AT N' d' * pw B (succ d')) := by
  have hx : Γ ⊢[PRAAx] le (MT N' d' * k) (MT N' d' * HT N' d') := by ipra_le 𝔟 (MT N' d') * sl hkH
  have hy := le_trans hf1 hx
  have gl := gd_le d' hx hy
  have pd := natEq (power_diff (Γ := Γ) (MT N' d' * k) (HT N' d' * B) (succ d'))
  have e1 := natEq (mul_pw (Γ := Γ) (MT N' d') k (succ d'))
  have e2 := natEq (mul_pw (Γ := Γ) (HT N' d') B (succ d'))
  have e3 := natEq (mul_pw (Γ := Γ) (MT N' d') (HT N' d') d')
  have e4 := natEq (pw_succ (Γ := Γ) (MT N' d') d')
  have e5 := natEq (pw_succ (Γ := Γ) (HT N' d') d')
  have e6 := natEq (pw_succ (Γ := Γ) (MT N' d') (succ d'))
  have hM1 : Γ ⊢[PRAAx] le one (MT N' d') := by
    ipra_le 16 * 𝔟 N' ^ 2 * 𝔟 d' + 16 * 𝔟 N' ^ 2 + 48 * 𝔟 N' * 𝔟 d' + 48 * 𝔟 N' + 32 * 𝔟 d' + 31
  have hH1 : Γ ⊢[PRAAx] le one (HT N' d') :=
    le_of_eq_add (d := hT N' d') (by apply deriveNat; ipra_simps; ring)
  have hm := one_le_pw_of d' hM1
  have hh := one_le_pw_of (succ d') hH1
  have hf2' : Γ ⊢[PRAAx] le (succ (MT N' d' * k)) (HT N' d' * B + HT N' d') := hf2
  have main : Γ ⊢[PRAAx] le (cT N' * (pw (HT N' d') (succ d') * succ (pw (MT N' d') (succ (succ d')))))
      (cT N' * (pw (HT N' d') (succ d') * (AT N' d' * pw B (succ d')))) := by
    ipra_le 𝔟 (pw (HT N' d') (succ d')) * (sl hm * (8 * (𝔟 N' + 1) * (𝔟 d' + 1) * ((𝔟 N' + 1) + 1) * (2 * (𝔟 N' + 1) + 1)) * (4 * (𝔟 N' + 1) * (2 * 𝔟 N' + 5) * (𝔟 d' + 1)) + (4 * (𝔟 N' + 1) * (2 * (𝔟 N' + 1) + 1)) * (16 * 𝔟 N' ^ 3 * 𝔟 d' ^ 2 + 32 * 𝔟 N' ^ 3 * 𝔟 d' + 16 * 𝔟 N' ^ 3 + 88 * 𝔟 N' ^ 2 * 𝔟 d' ^ 2 + 176 * 𝔟 N' ^ 2 * 𝔟 d' + 88 * 𝔟 N' ^ 2 + 152 * 𝔟 N' * 𝔟 d' ^ 2 + 304 * 𝔟 N' * 𝔟 d' + 152 * 𝔟 N' + 80 * 𝔟 d' ^ 2 + 160 * 𝔟 d' + 79)) +
        (8 * (𝔟 N' + 1) * (𝔟 d' + 1) * ((𝔟 N' + 1) + 1) * (2 * (𝔟 N' + 1) + 1)) * (16 * (𝔟 N' + 1) * (𝔟 d' + 1) * ((𝔟 N' + 1) + 1)) * 𝔟 (pw (MT N' d') d') * sl hq + (4 * (𝔟 N' + 1) * (2 * (𝔟 N' + 1) + 1)) * (8 * (𝔟 N' + 1) * (𝔟 d' + 1) * ((𝔟 N' + 1) + 1) * (2 * (𝔟 N' + 1) + 1)) * ((𝔟 d' + 1) * (4 * (𝔟 N' + 1) * (2 * (𝔟 N' + 1) + 1))) * sl gl +
        (4 * (𝔟 N' + 1) * (2 * (𝔟 N' + 1) + 1)) * (8 * (𝔟 N' + 1) * (𝔟 d' + 1) * ((𝔟 N' + 1) + 1) * (2 * (𝔟 N' + 1) + 1)) * 𝔟 (gd (MT N' d' * k) (HT N' d' * B) (succ d')) * (1 + sl hf2') using
      simp only [e1, e2, e3, e4, e5, e6] at pd ⊢
      linear_combination (-((4 * (𝔟 N' + 1) * (2 * (𝔟 N' + 1) + 1)) * (8 * (𝔟 N' + 1) * (𝔟 d' + 1) * ((𝔟 N' + 1) + 1) * (2 * (𝔟 N' + 1) + 1)))) * pd
  show Γ ⊢[PRAAx] le (succ (pw (MT N' d') (succ (succ d')))) (AT N' d' * pw B (succ d'))
  exact cancel_pos hh (mul_le_cancel (d' := cPred N') main)

end LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid

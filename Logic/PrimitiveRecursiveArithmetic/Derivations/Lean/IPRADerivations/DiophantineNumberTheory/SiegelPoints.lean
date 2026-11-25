import IPRADerivations.DiophantineNumberTheory.Siegel
import IPRADerivations.DiophantineNumberTheory.SuperellipticFamily
import IPRADerivations.Core.LinearCombination

/-!
# The integral points of `y² = x^{2m} + x + 1`, completed

Packet: `diophantine-number-theory/siegel_ipra`, `paper/03_runge.tex`, Theorem `thm:runge-all-genera`
("Uniform exact classification"): for every `m ≥ 2` the integral solutions of `y² = x^{2m} + x + 1` are
exactly `(−1, −1)`, `(−1, 1)`, `(0, −1)`, `(0, 1)`.

`Siegel.siegel_nonneg` and `Siegel.siegel_nonpos` force `x ∈ {0, −1}` (with `x = t` or `x = −t`, `t` a
natural number, `s = t^{m'+1}`). This module supplies the rest, with `y = ±u` for a natural `u` (both signs
give the same `u² = y²`):

* `u_eq_one`: `u² = 1` gives `u = 1`;
* `pos_points`: `x = t = 0` and `u² = s² + t + 1` give `u = 1`;
* `neg_points`: `x = −t` with `t ∈ {0, 1}` and `u² + t = s² + 1` give `u = 1`;
* `point_zero`, `point_neg_one`: the four points satisfy the equation (`1 = 0 + 0 + 1` and
  `1 + 1 = 1 + 1`, uniformly in `m`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.SiegelPoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily (s_eq_one one_pw zero_pw congrPwBase)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `u² = 1` gives `u = 1`. -/
theorem u_eq_one {u : PTm k} (h : Γ ⊢[PRAAx] u * u ≐ one) : Γ ⊢[PRAAx] u ≐ one :=
  s_eq_one (e := one) ((pw_succ u one).eqTrans ((congrMul (pw_one u) (.eqRefl u)).eqTrans h))

/-- `x = 0`: `u² = s² + 0 + 1` with `s = 0^{m'+1}` gives `u = 1`. -/
theorem pos_points {u t m' : PTm k}
    (h : Γ ⊢[PRAAx] u * u ≐ pw t (succ m') * pw t (succ m') + t + one) (ht : Γ ⊢[PRAAx] t ≐ zero) :
    Γ ⊢[PRAAx] u ≐ one := by
  refine u_eq_one ?_
  ipra_lc natEq h +
    (Groth.ι (Q.mk Γ (pw t (succ m'))) + 0) * natEq ((congrPwBase (succ m') ht).eqTrans (zero_pw (Γ := Γ) m')) +
    natEq ht

/-- `x = −t` with `t ∈ {0, 1}`: `u² + t = s² + 1` with `s = t^{m'+1}` gives `u = 1`. -/
theorem neg_points {u t m' : PTm k}
    (h : Γ ⊢[PRAAx] u * u + t ≐ pw t (succ m') * pw t (succ m') + one)
    (ht : Γ ⊢[PRAAx] (t ≐ zero) ⋎ (t ≐ one)) : Γ ⊢[PRAAx] u ≐ one := by
  refine .orE ht ?_ ?_
  · have h0 : ((t ≐ zero) :: Γ) ⊢[PRAAx] t ≐ zero := Prf.hyp0
    have h' : ((t ≐ zero) :: Γ) ⊢[PRAAx] u * u + t ≐ pw t (succ m') * pw t (succ m') + one := h.wk
    have es := natEq ((congrPwBase (succ m') h0).eqTrans (zero_pw (Γ := (t ≐ zero) :: Γ) m'))
    have e := natEq h'
    have et := natEq h0
    refine u_eq_one ?_
    ipra_lc e - et + Groth.ι (Q.mk ((t ≐ zero) :: Γ) (pw t (succ m'))) * es
  · have h1 : ((t ≐ one) :: Γ) ⊢[PRAAx] t ≐ one := Prf.hyp0
    have h' : ((t ≐ one) :: Γ) ⊢[PRAAx] u * u + t ≐ pw t (succ m') * pw t (succ m') + one := h.wk
    have es := natEq ((congrPwBase (succ m') h1).eqTrans (one_pw (Γ := (t ≐ one) :: Γ) (succ m')))
    have e := natEq h'
    have et := natEq h1
    refine u_eq_one ?_
    ipra_lc e - et + (Groth.ι (Q.mk ((t ≐ one) :: Γ) (pw t (succ m'))) + 1) * es

/-- `(0, ±1)`: `1 = (0^{m'+1})² + 0 + 1`. -/
theorem point_zero (m' : PTm k) :
    Γ ⊢[PRAAx] one * one ≐ pw zero (succ m') * pw zero (succ m') + zero + one := by
  ipra_lc (-Groth.ι (Q.mk Γ (pw zero (succ m')))) * natEq (zero_pw (Γ := Γ) m')

/-- `(−1, ±1)`: `1 + 1 = (1^{m'+1})² + 1`. -/
theorem point_neg_one (m' : PTm k) :
    Γ ⊢[PRAAx] one * one + one ≐ pw one (succ m') * pw one (succ m') + one := by
  ipra_lc (-Groth.ι (Q.mk Γ (pw one (succ m'))) - 1) * natEq (one_pw (Γ := Γ) (succ m'))

end LeanProofs.IPRA.DiophantineNumberTheory.SiegelPoints

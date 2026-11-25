import IPRADerivations.DiophantineNumberTheory.EllipticSearch
import IPRADerivations.Core.IntOrder
import IPRADerivations.Core.LinearCombination

/-!
# The finite rational squeeze

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:squeeze`: "Let `x, y ∈ ℚ`. If for every positive integer
`K` one has `x ≤ y + 1/K`, then `x ≤ y`. ... If `x > y`, write their difference using the product `v` of their
positive denominators. Its positive integer numerator is at least `1`, so `x − y ≥ 1/v`. Substitute the explicit
integer `K = 2v` in the hypothesized inequality to get `x − y ≤ 1/(2v)`, a contradiction. ... a single computable
instance of the displayed family of inequalities suffices."

With `x = p/u`, `y = q/v` (`p, q` integer terms, `u = u' + 1`, `v = v' + 1`) and the single instance `K = 2uv`,
cleared by `uvK`:

* `squeeze`: `K p v ≤ K q u + uv` gives `p v ≤ q u`, i.e. `x ≤ y`. (The lower version is the same statement with
  `x` and `y` interchanged.)
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperySqueeze

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The case `p v − q u ≥ 1` contradicts the instance `K = 2uv`. -/
theorem squeeze_absurd {Δ : List (Fm PTm n)} {p q : ZT n} {u' v' : PTm n}
    (h : Δ ⊢[PRAAx] zle (ZT.ofNat (num 2 * succ u' * succ v') * (p * ZT.ofNat (succ v'))) (ZT.ofNat (num 2 * succ u' * succ v') * (q * ZT.ofNat (succ u')) + ZT.ofNat (succ u' * succ v'))) (hlt : Δ ⊢[PRAAx] le (succ ((q * ZT.ofNat (succ u')).pos + (p * ZT.ofNat (succ v')).neg)) ((p * ZT.ofNat (succ v')).pos + (q * ZT.ofNat (succ u')).neg)) : Δ ⊢[PRAAx] Fm.bot := by
  have w := natEq (eq_add_of_le hlt)
  have h2 : ZT.toZ Δ (p * ZT.ofNat (succ v')) - ZT.toZ Δ (q * ZT.ofNat (succ u')) = 1 + Groth.ι (Q.mk Δ (monus ((p * ZT.ofNat (succ v')).pos + (q * ZT.ofNat (succ u')).neg) (succ ((q * ZT.ofNat (succ u')).pos + (p * ZT.ofNat (succ v')).neg)))) := by
    rw [toZ_def, toZ_def]
    simp only [Q.mk_add, Q.mk_succ, map_add, map_one] at w
    linear_combination w
  have e := zle_toZ h
  simp only [ZT.toZ_mul, ZT.toZ_add, ZT.toZ_ofNat] at e h2
  have big : Δ ⊢[PRAAx] le (num 2 * (succ u' * succ v')) (succ u' * succ v') := by
    refine le_of_eq_add (d := num 2 * (succ u' * succ v') * monus ((p * ZT.ofNat (succ v')).pos + (q * ZT.ofNat (succ u')).neg) (succ ((q * ZT.ofNat (succ u')).pos + (p * ZT.ofNat (succ v')).neg)) +
      monus ((ZT.ofNat (num 2 * succ u' * succ v') * (q * ZT.ofNat (succ u')) + ZT.ofNat (succ u' * succ v')).pos + (ZT.ofNat (num 2 * succ u' * succ v') * (p * ZT.ofNat (succ v'))).neg) ((ZT.ofNat (num 2 * succ u' * succ v') * (p * ZT.ofNat (succ v'))).pos + (ZT.ofNat (num 2 * succ u' * succ v') * (q * ZT.ofNat (succ u')) + ZT.ofNat (succ u' * succ v')).neg)) ?_
    ipra_lc -e + (2 * (𝔟 u' + 1) * (𝔟 v' + 1)) * h2
  refine le_lt_absurd _ big ?_
  show Δ ⊢[PRAAx] le (succ (succ u' * succ v')) (num 2 * (succ u' * succ v'))
  ipra_le 𝔟 u' * 𝔟 v' + 𝔟 u' + 𝔟 v'

/-- `lem:squeeze`: the instance `K = 2uv` of `x ≤ y + 1/K` gives `x ≤ y`. -/
theorem squeeze {p q : ZT n} {u' v' : PTm n} (h : Γ ⊢[PRAAx] zle (ZT.ofNat (num 2 * succ u' * succ v') * (p * ZT.ofNat (succ v'))) (ZT.ofNat (num 2 * succ u' * succ v') * (q * ZT.ofNat (succ u')) + ZT.ofNat (succ u' * succ v'))) :
    Γ ⊢[PRAAx] zle (p * ZT.ofNat (succ v')) (q * ZT.ofNat (succ u')) :=
  .orE (lt_or_le ((q * ZT.ofNat (succ u')).pos + (p * ZT.ofNat (succ v')).neg) ((p * ZT.ofNat (succ v')).pos + (q * ZT.ofNat (succ u')).neg)) (.botE _ (squeeze_absurd h.wk Prf.hyp0)) Prf.hyp0

end LeanProofs.IPRA.DiophantineNumberTheory.AperySqueeze

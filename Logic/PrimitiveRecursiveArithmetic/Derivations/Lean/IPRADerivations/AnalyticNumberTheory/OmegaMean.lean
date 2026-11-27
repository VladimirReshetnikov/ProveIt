import IPRADerivations.AnalyticNumberTheory.MertensTotient
import IPRADerivations.AnalyticNumberTheory.PiTheta

/-!
# The sum of the number of prime divisors

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, Theorem `an:means`,
first identity: `∑_{n ≤ X} ω(n) = ∑_{p ≤ X} ⌊X/p⌋`.

The number of distinct prime divisors is the convolution `ω = [prime] * 𝟏`, that is
`ω(n) = ∑_{d ≤ n} [d ∣ n] [d prime]`, with the prime indicator `PiTheta.piB`. The identity is the weighted
summatory identity `MertensTotient.floor_summatory` at the weight `[prime]`.

* `omegaB`: the body `ω(n)`;
* `sg_isP`: `[d ≥ 1] [d prime] = [d prime]`;
* `PFB`: the body `[d prime] ⌊x/d⌋`, and `prime_term`;
* **`omega_sum`**: `∑_{n ≤ x} ω(n) = ∑_{d ≤ x} [d prime] ⌊x/d⌋`.

The identity for `Ω` and the comparison with `∑ 1/p` are not derived here.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.OmegaMean

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (piB inst2_piB)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `ω(n) = ([prime] * 𝟏)(n)`, the number of distinct prime divisors of `n`; variable `0 = n`. -/
abbrev omegaB : PTm 2 := cvF piB one

/-- `[d ≥ 1] [d prime] = [d prime]`. -/
theorem sg_isP (d : PTm n) : Γ ⊢[PRAAx] sg d * isP d ≐ isP d := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have pz : ((d ≐ zero) :: Γ) ⊢[PRAAx] isP d ≐ zero := (congrIsP h0).eqTrans isP_zero
    exact ((congrMul (.eqRefl _) pz).eqTrans (mul_zero _)).eqTrans pz.eqSymm
  · have hp : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    exact (congrMul (sg_pos hp) (.eqRefl _)).eqTrans (one_mul _)

/-- `[d prime] ⌊x/d⌋`, over `0 = d`, `1 = x`. -/
abbrev PFB : PTm 2 := isP (var 0) * quo (var 1) (var 0)

theorem inst2_PFB (d x : PTm n) : inst2 PFB d x = isP d * quo x d := by
  simp [inst2, FactorVector.subst_isP]

/-- The term of the floor sum at the weight `[prime]`. -/
theorem prime_term (d x y : PTm n) : Γ ⊢[PRAAx] inst2 (RB piB one) d (pairT x y) ≐ inst2 PFB d x := by
  have h := floor_term (Γ := Γ) piB d x y
  rw [inst2_piB] at h
  rw [inst2_PFB]
  exact h.eqTrans (congrMul (sg_isP d) (.eqRefl _))

/-- **`an:means`, first identity**: `∑_{n ≤ x} ω(n) = ∑_{d ≤ x} [d prime] ⌊x/d⌋`. -/
theorem omega_sum (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF omegaB) (succ x) zero ≐ ap2 (sumF PFB) (succ x) x := by
  refine (floor_summatory piB x zero).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  have sz : Syn.shift (pairT x (zero : PTm n)) = pairT (Syn.shift x) zero := by simp [Syn.shift]
  rw [sz]
  exact prime_term _ _ _

end LeanProofs.IPRA.AnalyticNumberTheory.OmegaMean

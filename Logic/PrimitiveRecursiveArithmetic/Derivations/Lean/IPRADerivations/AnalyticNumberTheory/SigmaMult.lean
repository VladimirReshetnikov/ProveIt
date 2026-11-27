import IPRADerivations.AnalyticNumberTheory.DivisorFactor

/-!
# Multiplicativity of the divisor sum `σ` (`robin_ipra_research_2026-11-19`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex` ("multiplicativity of `σ`")
and `report.tex` (`thm:three`, Robin's inequality for integers with at most three distinct prime factors, where `σ` of a
product of coprime prime powers is the product of the factors' `σ`).

* `sig K = Σ_{d ≤ K} [d ∣ K] d` (`sB`, `sig`);
* `sigma_mul`: `σ(mN) = σ(m) σ(N)` for `m, N ≥ 1` with `gcd(m, N) = 1`, the instance `g(d) = d` of
  `DivisorFactor.divisor_factor`, with `Σ_{b ∣ N} ab = a σ(N)` (`Lotus.sum_const_mul`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[d ∣ K] d` over `0 = d`, `1 = K`. -/
def sB : PTm 2 := eqb (rem (var 1) (var 0)) zero * var 0

/-- `σ(K) = Σ_{d<K+1} [d ∣ K] d`. -/
abbrev sig (K : PTm n) : PTm n := ap2 (sumF sB) (succ K) K

theorem inst2_sB (d K : PTm n) : inst2 sB d K = eqb (rem K d) zero * d := by simp [inst2, sB]

theorem inst2_v0 {k : ℕ} (i z : PTm k) : inst2 (var 0 : PTm 2) i z = i := by simp [inst2]

/-- `Σ_{b<N+1} [b ∣ N] (ab) = a σ(N)`. -/
theorem inner_sum (a m N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (riB (var 0))) (succ N) (pairT a (Xp m N y)) ≐ a * sig N := by
  refine Prf.eqTrans ?_ (sum_const_mul sB (succ N) a N)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [inst2_cmB, inst2_sB, shift_pairT]
  refine (riB_at (var 0) _ _ _ _ _).eqTrans ?_
  rw [inst2_v0]
  refine Prf.eqTrans ?_ (congrMul (fst_pair _ _).eqSymm
    (congrMul (congrEqb' (congrAp2 remF (snd_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)) (.eqRefl _)))
  ipra_ring

/-- `σ(mN) = σ(m) σ(N)` for coprime `m, N ≥ 1`. -/
theorem sigma_mul {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) : Γ ⊢[PRAAx] sig (m * N) ≐ sig m * sig N := by
  -- the left side is the divisor sum of `g(d) = d`
  have l : Γ ⊢[PRAAx] sig (m * N) ≐ ap2 (sumF (lB (var 0))) (succ (m * N)) (Xp m N zero) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_sB, shift_pairT]
    refine Prf.eqTrans ?_ (lB_at (var 0) _ _ _ _).eqSymm
    rw [inst2_v0]
    have e : Syn.shift (m * N) = Syn.shift m * Syn.shift N := by simp [Syn.shift]
    rw [e]
    exact .eqRefl _
  -- the right side
  have r : Γ ⊢[PRAAx] ap2 (sumF (rB (var 0))) (succ m) (Xp m N zero) ≐
      ap2 (sumF (cmB sB)) (succ m) (pairT (sig N) m) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [inst2_cmB, inst2_sB, shift_pairT]
    refine (rB_at (var 0) _ _ _ _).eqTrans ?_
    refine (congrMul (.eqRefl _) (inner_sum _ _ _ _)).eqTrans ?_
    have e : Syn.shift (sig N) = sig (Syn.shift N) := by simp [Syn.shift]
    rw [e]
    refine Prf.eqTrans ?_ (congrMul (fst_pair _ _).eqSymm
      (congrMul (congrEqb' (congrAp2 remF (snd_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)) (.eqRefl _)))
    ipra_ring
  have f := divisor_factor (var 0) hm hN hc zero
  refine l.eqTrans (f.eqTrans (r.eqTrans ((sum_const_mul sB (succ m) (sig N) m).eqTrans ?_)))
  exact mul_comm _ _

end LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult

export_ipra AnalyticNumberTheory.SigmaMult (sig sigma_mul)

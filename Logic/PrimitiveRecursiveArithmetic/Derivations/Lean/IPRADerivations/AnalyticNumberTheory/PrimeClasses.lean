import IPRADerivations.AnalyticNumberTheory.PrimeRank

/-!
# Primes in the residue classes of a modulus

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/foundations.tex`, "Congruence classes":
`π_{a,r}(N) = ∑_{m ≤ N} b(m) [m mod a = r]`, and every prime contributes to exactly one class, so
`∑_{r < a} π_{a,r}(N) = π(N)` for `a ≥ 1`.

* `clB`: the body `[m prime] [m mod a = r]`; `pcl a r N = π_{a,r}(N)`;
* `row_sum`: `∑_{r < a} [m prime] [m mod a = r] = [m prime]` for `a ≥ 1`, a delta sum (`Fubini.sum_delta`) at
  `r = m mod a < a`;
* `class_at`: the term `r` of the outer sum is `π_{a,r}(N)`;
* **`class_partition`**: `∑_{r < a} π_{a,r}(N) = π(N)`, by `Fubini.fubini`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimeClasses

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (piB inst2_piB)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `[m prime] [m mod a = r]`, over `0 = m`, `1 = r`, `2 = a`. -/
abbrev clB : PTm 3 := isP (var 0) * eqb (rem (var 0) (var 2)) (var 1)

theorem inst3_clB (m r a : PTm n) : inst3 clB m r a = isP m * eqb (rem m a) r := by simp [inst3]

/-- `π_{a,r}(N) = ∑_{m ≤ N} [m prime] [m mod a = r]`. -/
abbrev pcl (a r N : PTm n) : PTm n := ap2 (sumF (colB clB)) (succ N) (pairT r a)

/-- The weight `[m prime]` of the delta sum, over `1 = m`. -/
abbrev GP : PTm 2 := isP (var 1)

theorem inst2_GP (j m : PTm n) : inst2 GP j m = isP m := by simp [inst2]

theorem row_term (m a j : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB clB) j (pairT m a) ≐ inst2 (dB GP) j (pairT (rem m a) m) := by
  rw [inst2_rowB, inst3_clB, inst2_dB, inst2_GP]
  exact (congrMul (congrIsP (fst_pair _ _))
    (Mobius.congrEqb' (congrAp2 remF (fst_pair _ _) (snd_pair _ _)) (.eqRefl _))).eqTrans
    ((mul_comm _ _).eqTrans (congrMul (Mobius.congrEqb' (fst_pair _ _).eqSymm (.eqRefl _))
      (congrIsP (snd_pair _ _).eqSymm)))

/-- `∑_{r < a} [m prime] [m mod a = r] = [m prime]` for `a ≥ 1`. -/
theorem row_sum {a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB clB)) a (pairT m a) ≐ isP m := by
  have d := sum_delta (Γ := Γ) GP (N := a) (c := rem m a) (x := m) (Multiplicative.rem_lt' ha m)
  rw [inst2_GP] at d
  refine (sum_congr_bounded (rowB clB) (dB GP) (pairT m a) (pairT (rem m a) m) a (.allI (.impI ?_))).eqTrans d
  have sr : Syn.shift (rem m a) = rem (Syn.shift m) (Syn.shift a) := by simp [Syn.shift]
  rw [shift_pairT, shift_pairT, sr]
  exact row_term _ _ _

/-- The term `r` of the outer sum is `π_{a,r}(N)`. -/
theorem class_at (a r N : PTm n) : Γ ⊢[PRAAx] inst2 (pB clB) r (pairT (succ N) a) ≐ pcl a r N := by
  rw [inst2_pB]
  exact congrAp2 (sumF (colB clB)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

/-- **Every prime lies in exactly one class**: `∑_{r < a} π_{a,r}(N) = π(N)` for `a ≥ 1`. -/
theorem class_partition {a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (pB clB)) a (pairT (succ N) a) ≐ pc N := by
  refine (fubini clB (succ N) a a).eqSymm.eqTrans ?_
  refine sum_congr_bounded (oB clB) piB (pairT a a) zero (succ N) (.allI (.impI ?_))
  rw [shift_pairT, inst2_piB]
  exact (oB_at clB _ _ _).eqTrans (row_sum (shift_pos ha).wk _)

end LeanProofs.IPRA.AnalyticNumberTheory.PrimeClasses

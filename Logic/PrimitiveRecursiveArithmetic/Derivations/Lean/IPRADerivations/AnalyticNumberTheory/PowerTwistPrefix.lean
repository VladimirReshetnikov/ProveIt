import IPRADerivations.AnalyticNumberTheory.PowerDivisorPrefix

/-!
# The prefix identity for divisor-twisted bodies (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "For residues … The forward formula now uses `A_{q,b_d}` at its `d`th term and skips the nonunits."

In the progression rows the coefficient attached to a pair `(d, m)` with `d^h m = n` depends on `d` (through the
residue `b_{d^h}`). This module repeats `PowerDivisorPrefix.prefix_identity` for a body `a(m, ⟨j, y⟩)` that receives the
divisor index `j` (`d = j + 1`) in its parameter:

* `Bt(N) = Σ_{j<N} A(⌊N/(j+1)^h⌋, ⟨j, y⟩)` (`tBt`), with `A(M, x) = Σ_{m<M} a(m+1, x)` (`PowerDivisorPrefix.Apre`);
* `b_h(n) = Σ_{j<n} [(j+1)^h ∣ n] a(n/(j+1)^h, ⟨j, y⟩)` (`tbval`) and `B_h(N) = Σ_{i<N} b_h(i+1)` (`tBpre`);
* `twist_prefix`: `Bt(N) = B_h(N)` for `h ≥ 1`, by the same quantifier-free induction on `N`
  (`PowerDivisorPrefix.step_pt` at the parameter `⟨j, y⟩`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerTwistPrefix

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix (Apre step_pt)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (quo_small)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (a : PTm 2)

/-! ## The sums -/

/-- The term `A(⌊N/(j+1)^h⌋, ⟨j, y⟩)` over `0 = j`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def tbtB : PTm 2 :=
  ap2 (sumF (shiftBody a)) (quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1)))))
    (pairT (var 0) (sndT (var 1)))

/-- `Bt(N) = Σ_{j<N} A(⌊N/(j+1)^h⌋, ⟨j, y⟩)`. -/
abbrev tBt (N h y : PTm n) : PTm n := ap2 (sumF (tbtB a)) N (pairT (pairT N h) y)

/-- The summand `[(j+1)^h ∣ n] a(n/(j+1)^h, ⟨j, y⟩)` over `0 = j`, `1 = ⟨⟨n, h⟩, y⟩`. -/
def tcB : PTm 2 :=
  eqb (rem (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1))))) zero *
    Syn.subst ![quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1)))), pairT (var 0) (sndT (var 1))] a

/-- `b_h(n) = Σ_{j<n} [(j+1)^h ∣ n] a(n/(j+1)^h, ⟨j, y⟩)`. -/
abbrev tbval (m h y : PTm n) : PTm n := ap2 (sumF (tcB a)) m (pairT (pairT m h) y)

/-- The summand `b_h(i+1)` over `0 = i`, `1 = ⟨h, y⟩`. -/
def tbpB : PTm 2 :=
  ap2 (sumF (tcB a)) (succ (var 0)) (pairT (pairT (succ (var 0)) (fstT (var 1))) (sndT (var 1)))

/-- `B_h(N) = Σ_{i<N} b_h(i+1)`. -/
abbrev tBpre (N h y : PTm n) : PTm n := ap2 (sumF (tbpB a)) N (pairT h y)

theorem inst2_tbtB (d P : PTm n) :
    inst2 (tbtB a) d P = Apre a (quo (fstT (fstT P)) (pw (succ d) (sndT (fstT P)))) (pairT d (sndT P)) := by
  simp [inst2, tbtB]

theorem inst2_tcB (j P : PTm n) :
    inst2 (tcB a) j P = eqb (rem (fstT (fstT P)) (pw (succ j) (sndT (fstT P)))) zero *
      inst2 a (quo (fstT (fstT P)) (pw (succ j) (sndT (fstT P)))) (pairT j (sndT P)) := by
  have ha : Syn.subst ![j, P] (Syn.subst ![quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1)))),
      pairT (var 0) (sndT (var 1))] a) =
      inst2 a (quo (fstT (fstT P)) (pw (succ j) (sndT (fstT P)))) (pairT j (sndT P)) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, tcB, PTm.subst_mul, ha]
  simp

theorem inst2_tbpB (i P : PTm n) :
    inst2 (tbpB a) i P = ap2 (sumF (tcB a)) (succ i) (pairT (pairT (succ i) (fstT P)) (sndT P)) := by
  simp [inst2, tbpB]

theorem tbtB_at (d N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (tbtB a) d (pairT (pairT N h) y) ≐ Apre a (quo N (pw (succ d) h)) (pairT d y) := by
  rw [inst2_tbtB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrAp2 _ (congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _))) (congrPairT (.eqRefl _) (snd_pair _ _))

theorem tcB_at (j N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (tcB a) j (pairT (pairT N h) y) ≐
      eqb (rem N (pw (succ j) h)) zero * inst2 a (quo N (pw (succ j) h)) (pairT j y) := by
  rw [inst2_tcB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  have eq : Γ ⊢[PRAAx] pw (succ j) (sndT (fstT (pairT (pairT N h) y))) ≐ pw (succ j) h := congrAp2 powF e2 (.eqRefl _)
  exact congrMul (congrEqb' (congrAp2 remF e1 eq) (.eqRefl _))
    (congrInst2 a (congrAp2 quoF e1 eq) (congrPairT (.eqRefl _) (snd_pair _ _)))

theorem tbpB_at (i h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (tbpB a) i (pairT h y) ≐ tbval a (succ i) h y := by
  rw [inst2_tbpB]
  exact congrAp2 _ (.eqRefl _) (congrPairT (congrPairT (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-! ## The prefix identity -/

/-- `Σ_{j<N} A(⌊N/(j+1)^h⌋, ⟨j, y⟩) = Σ_{i<N} b_h(i+1)` for `h ≥ 1`. -/
theorem twist_prefix {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] tBt a N h y ≐ tBpre a N h y := by
  refine PowerDivisorPrefix.prefix_identity_of a (tbtB a) (tcB a) (tbpB a)
    (pairT (var 0) (var 1)) ?_ ?_ (tbpB_at a) hh N y
  · intro m Δ j M h' y'
    simpa [inst2] using tbtB_at (Γ := Δ) a j M h' y'
  · intro m Δ j M h' y'
    simpa [inst2] using tcB_at (Γ := Δ) a j M h' y'

end LeanProofs.IPRA.AnalyticNumberTheory.PowerTwistPrefix

export_ipra AnalyticNumberTheory.PowerTwistPrefix (tBt)

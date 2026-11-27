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
  have hall : Γ ⊢[PRAAx] Fm.all (tBt a (var 0) (Syn.shift h) (Syn.shift y) ≐
      tBpre a (var 0) (Syn.shift h) (Syn.shift y)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (sum_zero _ _).eqTrans (sum_zero _ _).eqSymm
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift]
      let φ : Fm PTm (n + 1) := tBt a (var 0) (Syn.shift h) (Syn.shift y) ≐ tBpre a (var 0) (Syn.shift h) (Syn.shift y)
      let Δ : List (Fm PTm (n + 1)) := φ :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] φ := Prf.hyp0
      have hh' : Δ ⊢[PRAAx] le one (Syn.shift h) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift h) := by simpa [Fm.shift, Syn.shift] using hh.shift
        exact b.wk
      have hp : Δ ⊢[PRAAx] Syn.shift h ≐ succ (pred (Syn.shift h)) := pos_of_one_le hh'
      have sp : Δ ⊢[PRAAx] ap2 (sumF (tbtB a)) (succ (var 0)) (pairT (pairT (succ (var 0)) (Syn.shift h)) (Syn.shift y)) ≐
          ap2 (sumF (tbtB a)) (succ (var 0)) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) +
            ap2 (sumF (tcB a)) (succ (var 0)) (pairT (pairT (succ (var 0)) (Syn.shift h)) (Syn.shift y)) := by
        refine sum_add2 (tbtB a) (tcB a) (tbtB a) (.allI (.impI ?_))
        rw [show Syn.shift (pairT (pairT (succ (var 0)) (Syn.shift h)) (Syn.shift y)) =
            pairT (pairT (succ (var 1)) (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift y)) by simp [Syn.shift],
          show Syn.shift (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) =
            pairT (pairT (var 1) (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift y)) by simp [Syn.shift]]
        let Λ : List (Fm PTm (n + 2)) := lt (var 0) (Syn.shift (succ (var 0))) :: Δ.map Fm.shift
        have hq : Λ ⊢[PRAAx] pw (succ (var 0)) (Syn.shift (Syn.shift h)) ≐
            succ (pred (pw (succ (var 0)) (Syn.shift (Syn.shift h)))) :=
          pos_of_one_le (one_le_pw' (by ipra_le 𝔞 (var 0)) _)
        refine (tbtB_at a _ _ _ _).eqTrans ((step_pt a hq).eqTrans ?_)
        exact congrAdd (tbtB_at a _ _ _ _).eqSymm (tcB_at a _ _ _ _).eqSymm
      have hlt : Δ ⊢[PRAAx] lt (var 0) (pw (succ (var 0)) (Syn.shift h)) := by
        have s := le_self_pw (Γ := Δ) (var 0) (pred (Syn.shift h))
        exact le_congr (.eqRefl _) (congrAp2 powF hp.eqSymm (.eqRefl _)) s
      have hq0 : Δ ⊢[PRAAx] pw (succ (var 0)) (Syn.shift h) ≐ succ (pred (pw (succ (var 0)) (Syn.shift h))) :=
        pos_of_one_le (one_le_pw' (by ipra_le 𝔞 (var 0)) _)
      have last : Δ ⊢[PRAAx] inst2 (tbtB a) (var 0) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) ≐ zero :=
        (tbtB_at a _ _ _ _).eqTrans ((congrAp2 _ (quo_small hq0 hlt) (.eqRefl _)).eqTrans (sum_zero _ _))
      have s1 : Δ ⊢[PRAAx] ap2 (sumF (tbtB a)) (succ (var 0)) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) ≐
          tBt a (var 0) (Syn.shift h) (Syn.shift y) :=
        (sum_succ _ _ _).eqTrans ((congrAdd (.eqRefl _) last).eqTrans (add_zero _))
      have s2 : Δ ⊢[PRAAx] tBpre a (succ (var 0)) (Syn.shift h) (Syn.shift y) ≐
          tBpre a (var 0) (Syn.shift h) (Syn.shift y) + tbval a (succ (var 0)) (Syn.shift h) (Syn.shift y) :=
        (sum_succ _ _ _).eqTrans (congrAdd (.eqRefl _) (tbpB_at a _ _ _))
      exact sp.eqTrans ((congrAdd (s1.eqTrans ih) (.eqRefl _)).eqTrans s2.eqSymm)
  have r := Prf.allE N hall
  simpa [Syn.subst_inst_shift] using r

end LeanProofs.IPRA.AnalyticNumberTheory.PowerTwistPrefix

export_ipra AnalyticNumberTheory.PowerTwistPrefix (tBt)

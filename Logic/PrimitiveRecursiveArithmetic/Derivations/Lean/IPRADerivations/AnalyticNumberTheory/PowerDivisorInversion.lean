import IPRADerivations.AnalyticNumberTheory.PowerDivisorRow
import IPRADerivations.AnalyticNumberTheory.MobiusBounds
import IPRADerivations.AnalyticNumberTheory.EulerProduct

/-!
# Möbius inversion along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "`A(N) = Σ_{d=1}^N μ(d) B_h(⌊N/d^h⌋)`. For the second identity, substitute the first into the
right side, use `⌊⌊N/d^h⌋/e^h⌋ = ⌊N/(de)^h⌋`, and group pairs by `s = de`. The coefficient of `A(⌊N/s^h⌋)` is
`Σ_{d∣s} μ(d) = [s = 1]` … Terms with `s^h > N` vanish. This proves finite inversion."

With `μ = μ⁺ − μ⁻` (`AnalyticNumberTheory/Mobius`, prime bound `N + 1`) and `G(m) = A(⌊N/m^h⌋)`:

* for a weight body `w(d)`, `R_w(N) = Σ_{d<N+1} sg(d) w(d) B_h(⌊N/d^h⌋)` (`RS`) equals
  `Σ_{m<N+1} sg(m) G(m) · Σ_{d<N+1} sg(d)[d ∣ m] w(d)` (`rs_columns`): each row is `PowerDivisorRow.row_identity`
  (`row_pt`), and the double sum is exchanged by `Core/Fubini` (`col_pt`);
* `inversion`: `R_{μ⁺}(N) = R_{μ⁻}(N) + A(N)`, i.e. `A(N) = Σ_{d≤N} μ(d) B_h(⌊N/d^h⌋)`: the column sums are
  `Σ_{d∣m} μ⁺(d) = Σ_{d∣m} μ⁻(d) + [m = 1]` (`MobiusBounds.cancel_gen`), and the delta term is `G(1) = A(N)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (GP GN G_at cancel_gen congrMu)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrEqb' congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (quo_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (a w : PTm 2)

/-! ## The weighted sums -/

/-- The parameter `⟨⟨N, h⟩, y⟩`. -/
abbrev Zp (N h y : PTm n) : PTm n := pairT (pairT N h) y

/-- `sg(d) w(d) B_h(⌊N/d^h⌋)` over `0 = d`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def rB : PTm 2 := sg (var 0) * w *
  ap2 (sumF (bpB a)) (quo (fstT (fstT (var 1))) (pw (var 0) (sndT (fstT (var 1))))) (pairT (sndT (fstT (var 1))) (sndT (var 1)))

/-- `R_w(N) = Σ_{d<N+1} sg(d) w(d) B_h(⌊N/d^h⌋)`. -/
abbrev RS (N h y : PTm n) : PTm n := ap2 (sumF (rB a w)) (succ N) (Zp N h y)

/-- `(sg(d) w(d)) ([d ∣ m] sg(m) G(m))` over `0 = d`, `1 = m`, `2 = ⟨⟨N, h⟩, y⟩`. -/
def a3 : PTm 3 := (sg (var 0) * Syn.subst ![var 0, var 2] w) *
  (eqb (rem (var 1) (var 0)) zero * sg (var 1) * Syn.subst ![var 1, var 2] (GB a))

/-- `sg(d)[d ∣ m] w(d)` over `0 = d`, `1 = ⟨m, ⟨⟨N, h⟩, y⟩⟩`. -/
def kB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * Syn.subst ![var 0, sndT (var 1)] w

theorem inst2_rB (d P : PTm n) : inst2 (rB a w) d P = sg d * inst2 w d P *
    ap2 (sumF (bpB a)) (quo (fstT (fstT P)) (pw d (sndT (fstT P)))) (pairT (sndT (fstT P)) (sndT P)) := by
  simp [inst2, rB]

theorem inst3_a3 (d m P : PTm n) : inst3 (a3 a w) d m P = (sg d * inst2 w d P) *
    (eqb (rem m d) zero * sg m * inst2 (GB a) m P) := by
  have hw : Syn.subst ![d, m, P] (Syn.subst ![var 0, var 2] w) = inst2 w d P := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have hg : Syn.subst ![d, m, P] (Syn.subst ![var 1, var 2] (GB a)) = inst2 (GB a) m P := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, a3, PTm.subst_mul, hw, hg]
  simp

theorem inst2_kB (d P : PTm n) : inst2 (kB w) d P =
    (sg d * eqb (rem (fstT P) d) zero) * inst2 w d (sndT P) := by
  have hw : Syn.subst ![d, P] (Syn.subst ![var 0, sndT (var 1)] w) = inst2 w d (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, kB, PTm.subst_mul, hw]
  simp

theorem rB_at (d N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (rB a w) d (Zp N h y) ≐ sg d * inst2 w d (Zp N h y) * Bpre a (quo N (pw d h)) h y := by
  rw [inst2_rB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrMul (.eqRefl _) (congrAp2 _ (congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _)))
    (congrPairT e2 (snd_pair _ _)))

/-! ## Rows -/

/-- Row `d`: `sg(d) w(d) B_h(⌊N/d^h⌋) = Σ_{m<N+1} a3(d, m)`. -/
theorem row_pt {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (d N y : PTm n) :
    Γ ⊢[PRAAx] inst2 (rB a w) d (Zp N h y) ≐ ap2 (sumF (rowB (a3 a w))) (succ N) (pairT d (Zp N h y)) := by
  refine (rB_at a w _ _ _ _).eqTrans ?_
  refine .orE (lt_or_le zero d) ?_ ?_
  · let C : List (Fm PTm n) := lt zero d :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := pos_of_one_le Prf.hyp0
    have ri := row_identity a hd hh.wk N y
    refine (congrMul (.eqRefl _) ri).eqTrans ?_
    refine (sum_const_mul (dmB a) (succ N) (sg d * inst2 w d (Zp N h y)) (pairT d (Zp N h y))).eqSymm.eqTrans ?_
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (pairT (sg d * inst2 w d (Zp N h y)) (pairT d (Zp N h y))) =
        pairT (sg (Syn.shift d) * inst2 w (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))
          (pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) by simp [Syn.shift],
      show Syn.shift (pairT d (Zp N h y)) = pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift],
      inst2_cmB, inst2_rowB, inst3_a3, inst2_dmB]
    let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)
    let K : PTm (n + 1) := sg (Syn.shift d) * inst2 w (Syn.shift d) P
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: C.map Fm.shift
    have f1 : Λ ⊢[PRAAx] fstT (pairT K (pairT (Syn.shift d) P)) ≐ K := fst_pair _ _
    have f2 : Λ ⊢[PRAAx] sndT (pairT K (pairT (Syn.shift d) P)) ≐ pairT (Syn.shift d) P := snd_pair _ _
    have f3 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift d) P) ≐ Syn.shift d := fst_pair _ _
    have f4 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift d) P) ≐ P := snd_pair _ _
    have lhs : Λ ⊢[PRAAx] fstT (pairT K (pairT (Syn.shift d) P)) *
        (eqb (rem (var 0) (fstT (sndT (pairT K (pairT (Syn.shift d) P))))) zero * sg (var 0) *
          inst2 (GB a) (var 0) (sndT (sndT (pairT K (pairT (Syn.shift d) P))))) ≐
        K * (eqb (rem (var 0) (Syn.shift d)) zero * sg (var 0) * inst2 (GB a) (var 0) P) :=
      congrMul f1 (congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) ((congrFst f2).eqTrans f3)) (.eqRefl _))
        (.eqRefl _)) (congrInst2 (GB a) (.eqRefl _) ((congrSnd f2).eqTrans f4)))
    have rhs : Λ ⊢[PRAAx] (sg (fstT (pairT (Syn.shift d) P)) *
        inst2 w (fstT (pairT (Syn.shift d) P)) (sndT (pairT (Syn.shift d) P))) *
        (eqb (rem (var 0) (fstT (pairT (Syn.shift d) P))) zero * sg (var 0) *
          inst2 (GB a) (var 0) (sndT (pairT (Syn.shift d) P))) ≐
        K * (eqb (rem (var 0) (Syn.shift d)) zero * sg (var 0) * inst2 (GB a) (var 0) P) :=
      congrMul (congrMul (congrSg f3) (congrInst2 w f3 f4))
        (congrMul (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) f3) (.eqRefl _)) (.eqRefl _))
          (congrInst2 (GB a) (.eqRefl _) f4))
    exact lhs.eqTrans rhs.eqSymm
  · let C : List (Fm PTm n) := le d zero :: Γ
    have hd : C ⊢[PRAAx] d ≐ zero := (monus_zero d).eqSymm.eqTrans Prf.hyp0
    have s0 : C ⊢[PRAAx] sg d ≐ zero := (congrSg hd).eqTrans sg_zero
    refine ((congrMul (congrMul s0 (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans ?_
    refine (sum_zero_of_all _ _ (.allI ?_) _).eqSymm
    rw [show Syn.shift (pairT d (Zp N h y)) = pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift], inst2_rowB, inst3_a3]
    have s0' : (C.map Fm.shift) ⊢[PRAAx] sg (fstT (pairT (Syn.shift d) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))) ≐
        zero := by
      have b : (C.map Fm.shift) ⊢[PRAAx] sg (Syn.shift d) ≐ zero := by simpa [Fm.shift, Syn.shift] using s0.shift
      exact (congrSg (fst_pair _ _)).eqTrans b
    exact (congrMul ((congrMul s0' (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (zero_mul _)

/-! ## Columns -/

/-- Column `m`: `Σ_{d<N+1} a3(d, m) = sg(m) G(m) · Σ_{d<N+1} sg(d)[d ∣ m] w(d)`. -/
theorem col_pt (m N h y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (a3 a w))) (succ N) (pairT m (Zp N h y)) ≐
      (sg m * inst2 (GB a) m (Zp N h y)) * ap2 (sumF (kB w)) (succ N) (pairT m (Zp N h y)) := by
  refine Prf.eqTrans ?_ (sum_const_mul (kB w) (succ N) (sg m * inst2 (GB a) m (Zp N h y)) (pairT m (Zp N h y)))
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (pairT m (Zp N h y)) = pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
      simp [Syn.shift],
    show Syn.shift (pairT (sg m * inst2 (GB a) m (Zp N h y)) (pairT m (Zp N h y))) =
      pairT (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))
        (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) by simp [Syn.shift],
    inst2_colB, inst3_a3, inst2_cmB, inst2_kB]
  let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift
  let P : PTm (n + 1) := Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)
  have f1 : Λ ⊢[PRAAx] fstT (pairT (Syn.shift m) P) ≐ Syn.shift m := fst_pair _ _
  have f2 : Λ ⊢[PRAAx] sndT (pairT (Syn.shift m) P) ≐ P := snd_pair _ _
  have g1 : Λ ⊢[PRAAx] fstT (pairT (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P) (pairT (Syn.shift m) P)) ≐
      sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P := fst_pair _ _
  have g2 : Λ ⊢[PRAAx] sndT (pairT (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P) (pairT (Syn.shift m) P)) ≐
      pairT (Syn.shift m) P := snd_pair _ _
  have lhs : Λ ⊢[PRAAx] (sg (var 0) * inst2 w (var 0) (sndT (pairT (Syn.shift m) P))) *
      (eqb (rem (fstT (pairT (Syn.shift m) P)) (var 0)) zero * sg (fstT (pairT (Syn.shift m) P)) *
        inst2 (GB a) (fstT (pairT (Syn.shift m) P)) (sndT (pairT (Syn.shift m) P))) ≐
      (sg (var 0) * inst2 w (var 0) P) *
        (eqb (rem (Syn.shift m) (var 0)) zero * sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P) :=
    congrMul (congrMul (.eqRefl _) (congrInst2 w (.eqRefl _) f2))
      (congrMul (congrMul (congrEqb' (congrAp2 remF f1 (.eqRefl _)) (.eqRefl _)) (congrSg f1)) (congrInst2 (GB a) f1 f2))
  have rhs : Λ ⊢[PRAAx] fstT (pairT (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P) (pairT (Syn.shift m) P)) *
      ((sg (var 0) * eqb (rem (fstT (sndT (pairT (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P)
        (pairT (Syn.shift m) P)))) (var 0)) zero) *
        inst2 w (var 0) (sndT (sndT (pairT (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P) (pairT (Syn.shift m) P))))) ≐
      (sg (Syn.shift m) * inst2 (GB a) (Syn.shift m) P) *
        ((sg (var 0) * eqb (rem (Syn.shift m) (var 0)) zero) * inst2 w (var 0) P) :=
    congrMul g1 (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF ((congrFst g2).eqTrans f1) (.eqRefl _))
      (.eqRefl _))) (congrInst2 w (.eqRefl _) ((congrSnd g2).eqTrans f2)))
  refine lhs.eqTrans (Prf.eqTrans ?_ rhs.eqSymm)
  ipra_ring

/-- `R_w(N) = Σ_{m<N+1} sg(m) G(m) · Σ_{d<N+1} sg(d)[d ∣ m] w(d)`. -/
theorem rs_columns {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] RS a w N h y ≐ ap2 (sumF (pB (a3 a w))) (succ N) (pairT (succ N) (Zp N h y)) := by
  have r : Γ ⊢[PRAAx] RS a w N h y ≐ ap2 (sumF (oB (a3 a w))) (succ N) (pairT (succ N) (Zp N h y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [show Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) by simp [Syn.shift],
      show Syn.shift (pairT (succ N) (Zp N h y)) = pairT (succ (Syn.shift N)) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
        simp [Syn.shift]]
    have hh' : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift h) := by
      have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift h) := by simpa [Fm.shift, Syn.shift] using hh.shift
      exact b.wk
    exact (row_pt a w hh' (var 0) (Syn.shift N) (Syn.shift y)).eqTrans (oB_at (a3 a w) _ _ _).eqSymm
  exact r.eqTrans (fubini (a3 a w) (succ N) (succ N) (Zp N h y))

/-! ## The inversion -/

/-- `μ⁺_{N+1}(d)` over `0 = d`, `1 = ⟨⟨N, h⟩, y⟩`. -/
abbrev wP : PTm 2 := muP (succ (fstT (fstT (var 1)))) (var 0)
/-- `μ⁻_{N+1}(d)`. -/
abbrev wN : PTm 2 := muN (succ (fstT (fstT (var 1)))) (var 0)

/-- The delta term `sg(m) G(m)` read at `m = 1` by `dB`. -/
abbrev sGB : PTm 2 := sg (var 0) * GB a

theorem inst2_sGB (m P : PTm n) : inst2 (sGB a) m P = sg m * inst2 (GB a) m P := by simp [inst2]

theorem pB_at (b : PTm 3) (m M Z : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB b) m (pairT M Z) ≐ ap2 (sumF (colB b)) M (pairT m Z) := by
  rw [inst2_pB]
  exact congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

/-- The column sums of `μ^±` are the divisor sums `Σ_{d ∣ m} μ^±(d)` of `MobiusBounds`. -/
theorem kB_mu (m N h y : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (kB wP)) (succ N) (pairT m (Zp N h y)) ≐ ap2 (sumF GP) (succ N) (pairT (succ N) m)) ⋏
      (ap2 (sumF (kB wN)) (succ N) (pairT m (Zp N h y)) ≐ ap2 (sumF GN) (succ N) (pairT (succ N) m)) := by
  have hz : ∀ (Δ : List (Fm PTm (n + 1))) (d : PTm (n + 1)),
      Δ ⊢[PRAAx] (inst2 (kB wP) d (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) ≐
          inst2 GP d (pairT (succ (Syn.shift N)) (Syn.shift m))) ⋏
        (inst2 (kB wN) d (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) ≐
          inst2 GN d (pairT (succ (Syn.shift N)) (Syn.shift m))) := by
    intro Δ d
    rw [inst2_kB, inst2_kB]
    have g := G_at (Γ := Δ) d (succ (Syn.shift N)) (Syn.shift m)
    have f1 : Δ ⊢[PRAAx] fstT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) ≐ Syn.shift m :=
      fst_pair _ _
    have f2 : Δ ⊢[PRAAx] succ (fstT (fstT (sndT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))))) ≐
        succ (Syn.shift N) :=
      congrSucc ((congrFst ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))).eqTrans (fst_pair _ _))
    have c := congrMu (Γ := Δ) (d := d) f2
    have e : Δ ⊢[PRAAx] sg d * eqb (rem (fstT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))) d) zero ≐
        sg d * eqb (rem (Syn.shift m) d) zero :=
      congrMul (.eqRefl _) (congrEqb' (congrAp2 remF f1 (.eqRefl _)) (.eqRefl _))
    refine .andI ?_ ?_
    · have hw : inst2 (wP : PTm 2) d (sndT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))) =
          muP (succ (fstT (fstT (sndT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))))))) d := by
        simp [inst2]
      rw [hw]
      exact (congrMul e (Prf.andE₁ c)).eqTrans (Prf.andE₁ g).eqSymm
    · have hw : inst2 (wN : PTm 2) d (sndT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)))) =
          muN (succ (fstT (fstT (sndT (pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))))))) d := by
        simp [inst2]
      rw [hw]
      exact (congrMul e (Prf.andE₂ c)).eqTrans (Prf.andE₂ g).eqSymm
  have sh : Syn.shift (pairT m (Zp N h y)) = pairT (Syn.shift m) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) := by
    simp [Syn.shift]
  have sh2 : Syn.shift (pairT (succ N) m) = pairT (succ (Syn.shift N)) (Syn.shift m) := by simp [Syn.shift]
  refine .andI (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  · rw [sh, sh2]; exact Prf.andE₁ (hz _ _)
  · rw [sh, sh2]; exact Prf.andE₂ (hz _ _)

/-- Column `m ≤ N` of the difference: `col⁺(m) = col⁻(m) + [m = 1] sg(m) G(m)`. -/
theorem col_cancel {m N h y : PTm n} (hm : Γ ⊢[PRAAx] lt m (succ N)) :
    Γ ⊢[PRAAx] inst2 (pB (a3 a wP)) m (pairT (succ N) (Zp N h y)) ≐
      inst2 (pB (a3 a wN)) m (pairT (succ N) (Zp N h y)) + inst2 (dB (sGB a)) m (pairT one (Zp N h y)) := by
  have cp := (pB_at (Γ := Γ) (a3 a wP) m (succ N) (Zp N h y)).eqTrans
    ((col_pt a wP m N h y).eqTrans (congrMul (.eqRefl _) (Prf.andE₁ (kB_mu m N h y))))
  have cn := (pB_at (Γ := Γ) (a3 a wN) m (succ N) (Zp N h y)).eqTrans
    ((col_pt a wN m N h y).eqTrans (congrMul (.eqRefl _) (Prf.andE₂ (kB_mu m N h y))))
  have dl : Γ ⊢[PRAAx] inst2 (dB (sGB a)) m (pairT one (Zp N h y)) ≐ eqb one m * (sg m * inst2 (GB a) m (Zp N h y)) := by
    rw [inst2_dB, inst2_sGB]
    exact congrMul (congrEqb' (fst_pair _ _) (.eqRefl _))
      (congrMul (.eqRefl _) (congrInst2 (GB a) (.eqRefl _) (snd_pair _ _)))
  refine cp.eqTrans (Prf.eqTrans ?_ (congrAdd cn dl).eqSymm)
  refine .orE (lt_or_le zero m) ?_ ?_
  · let C : List (Fm PTm n) := lt zero m :: Γ
    have hk : C ⊢[PRAAx] m ≐ succ (pred m) := pos_of_one_le Prf.hyp0
    have cg := cancel_gen (Γ := C) hk (N := succ N) (K := succ N) hm.wk hm.wk
    refine (congrMul (.eqRefl _) cg).eqTrans ((mul_add _ _ _).eqTrans (congrAdd (.eqRefl _) ?_))
    exact (mul_comm _ _).eqTrans (congrMul (eqb_comm' m one) (.eqRefl _))
  · let C : List (Fm PTm n) := le m zero :: Γ
    have hz : C ⊢[PRAAx] m ≐ zero := (monus_zero m).eqSymm.eqTrans Prf.hyp0
    have hX : C ⊢[PRAAx] sg m * inst2 (GB a) m (Zp N h y) ≐ zero :=
      (congrMul ((congrSg hz).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)
    refine ((congrMul hX (.eqRefl _)).eqTrans (zero_mul _)).eqTrans ?_
    refine (Prf.eqTrans ?_ (congrAdd ((congrMul hX (.eqRefl _)).eqTrans (zero_mul _))
      ((congrMul (.eqRefl _) hX).eqTrans (mul_zero _))).eqSymm)
    exact (add_zero _).eqSymm

/-- `G(1) = A(N)`. -/
theorem G_one (N h y : PTm n) : Γ ⊢[PRAAx] inst2 (sGB a) one (Zp N h y) ≐ Apre a N y := by
  rw [inst2_sGB]
  refine ((congrMul (sg_succ _) (GB_at a _ _ _ _)).eqTrans (one_mul _)).eqTrans (congrAp2 _ ?_ (.eqRefl _))
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := pos_of_one_le (le_refl _)
  exact (congrAp2 quoF (.eqRefl _) (pw_one_base h)).eqTrans (quo_mul h1 (one_mul N).eqSymm)

/-- `thm:powerdivisor`, finite inversion: `Σ_{d≤N} μ⁺(d) B_h(⌊N/d^h⌋) = Σ_{d≤N} μ⁻(d) B_h(⌊N/d^h⌋) + A(N)`,
i.e. `A(N) = Σ_{d=1}^N μ(d) B_h(⌊N/d^h⌋)`, for every coefficient body `a` and `h ≥ 1`. -/
theorem inversion {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] RS a wP N h y ≐ RS a wN N h y + Apre a N y := by
  refine (rs_columns a wP hh N y).eqTrans ?_
  refine Prf.eqTrans ?_ (congrAdd (rs_columns a wN hh N y).eqSymm (.eqRefl _))
  have sp := sum_add2 (Γ := Γ) (pB (a3 a wN)) (dB (sGB a)) (pB (a3 a wP)) (K := succ N)
    (x := pairT (succ N) (Zp N h y)) (x' := pairT one (Zp N h y)) (z := pairT (succ N) (Zp N h y))
    (.allI (.impI (by
      rw [show Syn.shift (pairT (succ N) (Zp N h y)) =
          pairT (succ (Syn.shift N)) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by simp [Syn.shift],
        show Syn.shift (pairT one (Zp N h y)) = pairT one (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) by
          simp [Syn.shift]]
      have hm : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) := by
        have b := (Prf.hyp0 : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
        simpa [Syn.shift] using b
      exact col_cancel a hm)))
  refine sp.eqTrans (congrAdd (.eqRefl _) ?_)
  -- the delta sum is `G(1) = A(N)`
  refine .orE (lt_or_le zero N) ?_ ?_
  · have h1 : (lt zero N :: Γ) ⊢[PRAAx] lt one (succ N) := by have b : (lt zero N :: Γ) ⊢[PRAAx] lt zero N := Prf.hyp0; ipra_le sl b
    exact (sum_delta (sGB a) h1).eqTrans (G_one a N h y)
  · let C : List (Fm PTm n) := le N zero :: Γ
    have hz : C ⊢[PRAAx] N ≐ zero := (monus_zero N).eqSymm.eqTrans Prf.hyp0
    have d0 : C ⊢[PRAAx] ap2 (sumF (dB (sGB a))) (succ N) (pairT one (Zp N h y)) ≐ zero := by
      refine (congrAp2 _ (congrSucc hz) (.eqRefl _)).eqTrans ((sum_succ _ _ _).eqTrans ?_)
      refine (congrAdd (sum_zero _ _) ?_).eqTrans (add_zero _)
      change C ⊢[PRAAx] inst2 (dB (sGB a)) zero (pairT one (Zp N h y)) ≐ zero
      rw [inst2_dB]
      have e : C ⊢[PRAAx] eqb (fstT (pairT one (Zp N h y))) zero ≐ zero :=
        (congrEqb' (fst_pair _ _) (.eqRefl _)).eqTrans
          (LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc.eqb_succ_zero zero)
      exact (congrMul e (.eqRefl _)).eqTrans (zero_mul _)
    have a0 : C ⊢[PRAAx] Apre a N y ≐ zero := (congrAp2 _ hz (.eqRefl _)).eqTrans (sum_zero _ _)
    exact d0.eqTrans a0.eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion

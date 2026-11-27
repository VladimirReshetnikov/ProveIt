import IPRADerivations.AnalyticNumberTheory.PowerTransfer

/-!
# The prefix of a convolution along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "At a finite cutoff, collecting the pairs `(d, m)` with `d^h m ≤ N` gives
`B_h(N) = Σ_{d=1}^N A(⌊N/d^h⌋)`."

For a coefficient body `a(n, y)` and an exponent `h ≥ 1`:

* `A(M) = Σ_{m<M} a(m+1)` (`Apre`);
* `b_h(n) = Σ_{j<n} [(j+1)^h ∣ n] a(n/(j+1)^h)` (`bval`, the divisors `d^h ∣ n` with `d = j + 1 ≤ n`), and its
  prefix `B_h(N) = Σ_{i<N} b_h(i+1)` (`Bpre`);
* `Bt(N) = Σ_{d<N} A(⌊N/(d+1)^h⌋)` (`Bt`).

`prefix_identity`: `Bt(N) = B_h(N)`, by quantifier-free induction on `N` instead of a pair count. With
`q = (d+1)^h ≥ 1`, `⌊(N+1)/q⌋ = ⌊N/q⌋ + [q ∣ N+1]` (`SummatoryPhi.quo_succ`), so
`A(⌊(N+1)/q⌋) = A(⌊N/q⌋) + [q ∣ N+1] a((N+1)/q)` (`step_pt`, by the two values of the indicator); summed over
`d ≤ N` the indicator terms are exactly `b_h(N+1)`, and the new term `d = N` of `Bt(N)` is `A(⌊N/(N+1)^h⌋) = A(0) = 0`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix

open_ipra exports
open LeanProofs.IPRA.Combinatorics.LegendreDigits (quo_small)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

variable (a : PTm 2)

/-! ## The sums -/

/-- `A(M, y) = Σ_{m<M} a(m+1, y)`. -/
abbrev Apre (M y : PTm n) : PTm n := ap2 (sumF (shiftBody a)) M y

/-- The term `A(⌊N/(d+1)^h⌋)` over `0 = d`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def btB : PTm 2 :=
  ap2 (sumF (shiftBody a)) (quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1))))) (sndT (var 1))

/-- `Bt(N) = Σ_{d<N} A(⌊N/(d+1)^h⌋)`. -/
abbrev Bt (N h y : PTm n) : PTm n := ap2 (sumF (btB a)) N (pairT (pairT N h) y)

/-- The summand `[(j+1)^h ∣ n] a(n/(j+1)^h)` over `0 = j`, `1 = ⟨⟨n, h⟩, y⟩`. -/
def cB : PTm 2 :=
  eqb (rem (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1))))) zero *
    Syn.subst ![quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1)))), sndT (var 1)] a

/-- `b_h(n) = Σ_{j<n} [(j+1)^h ∣ n] a(n/(j+1)^h)`. -/
abbrev bval (m h y : PTm n) : PTm n := ap2 (sumF (cB a)) m (pairT (pairT m h) y)

/-- The summand `b_h(i+1)` over `0 = i`, `1 = ⟨h, y⟩`. -/
def bpB : PTm 2 :=
  ap2 (sumF (cB a)) (succ (var 0)) (pairT (pairT (succ (var 0)) (fstT (var 1))) (sndT (var 1)))

/-- `B_h(N) = Σ_{i<N} b_h(i+1)`. -/
abbrev Bpre (N h y : PTm n) : PTm n := ap2 (sumF (bpB a)) N (pairT h y)

theorem inst2_btB (d P : PTm n) :
    inst2 (btB a) d P = Apre a (quo (fstT (fstT P)) (pw (succ d) (sndT (fstT P)))) (sndT P) := by
  simp [inst2, btB]

theorem inst2_cB (j P : PTm n) :
    inst2 (cB a) j P = eqb (rem (fstT (fstT P)) (pw (succ j) (sndT (fstT P)))) zero *
      inst2 a (quo (fstT (fstT P)) (pw (succ j) (sndT (fstT P)))) (sndT P) := by
  have ha : Syn.subst ![j, P] (Syn.subst ![quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1)))),
      sndT (var 1)] a) = inst2 a (quo (fstT (fstT P)) (pw (succ j) (sndT (fstT P)))) (sndT P) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, cB, PTm.subst_mul, ha]
  simp

theorem inst2_bpB (i P : PTm n) :
    inst2 (bpB a) i P = ap2 (sumF (cB a)) (succ i) (pairT (pairT (succ i) (fstT P)) (sndT P)) := by
  simp [inst2, bpB]

theorem btB_at (d N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (btB a) d (pairT (pairT N h) y) ≐ Apre a (quo N (pw (succ d) h)) y := by
  rw [inst2_btB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrAp2 _ (congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _))) (snd_pair _ _)

theorem cB_at (j N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (cB a) j (pairT (pairT N h) y) ≐
      eqb (rem N (pw (succ j) h)) zero * inst2 a (quo N (pw (succ j) h)) y := by
  rw [inst2_cB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  have eq : Γ ⊢[PRAAx] pw (succ j) (sndT (fstT (pairT (pairT N h) y))) ≐ pw (succ j) h := congrAp2 powF e2 (.eqRefl _)
  exact congrMul (congrEqb' (congrAp2 remF e1 eq) (.eqRefl _))
    (congrInst2 a (congrAp2 quoF e1 eq) (snd_pair _ _))

theorem bpB_at (i h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (bpB a) i (pairT h y) ≐ bval a (succ i) h y := by
  rw [inst2_bpB]
  exact congrAp2 _ (.eqRefl _) (congrPairT (congrPairT (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-! ## One step of the floor -/

/-- `A(⌊(N+1)/q⌋) = A(⌊N/q⌋) + [q ∣ N+1] a((N+1)/q)` for `q ≥ 1`. -/
theorem step_pt {N q y : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) :
    Γ ⊢[PRAAx] Apre a (quo (succ N) q) y ≐
      Apre a (quo N q) y + eqb (rem (succ N) q) zero * inst2 a (quo (succ N) q) y := by
  have qs := LeanProofs.IPRA.AnalyticNumberTheory.SummatoryPhi.quo_succ (N := N) hq
  refine .orE (eqb_cases (Γ := Γ) (rem (succ N) q) zero) ?_ ?_
  · let C : List (Fm PTm n) := (eqb (rem (succ N) q) zero ≐ zero) :: Γ
    have e0 : C ⊢[PRAAx] eqb (rem (succ N) q) zero ≐ zero := Prf.hyp0
    have qq : C ⊢[PRAAx] quo (succ N) q ≐ quo N q :=
      qs.wk.eqTrans ((congrAdd (.eqRefl _) e0).eqTrans (add_zero _))
    refine (congrAp2 _ qq (.eqRefl _)).eqTrans ?_
    exact ((congrAdd (.eqRefl _) ((congrMul e0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (add_zero _)).eqSymm
  · let C : List (Fm PTm n) := (eqb (rem (succ N) q) zero ≐ one) :: Γ
    have e1 : C ⊢[PRAAx] eqb (rem (succ N) q) zero ≐ one := Prf.hyp0
    have qq : C ⊢[PRAAx] quo (succ N) q ≐ succ (quo N q) :=
      qs.wk.eqTrans ((congrAdd (.eqRefl _) e1).eqTrans (by ipra_ring))
    have ss : C ⊢[PRAAx] Apre a (succ (quo N q)) y ≐ Apre a (quo N q) y + inst2 (shiftBody a) (quo N q) y :=
      sum_succ _ _ _
    rw [inst2_shiftBody] at ss
    refine (congrAp2 _ qq (.eqRefl _)).eqTrans (ss.eqTrans ?_)
    refine congrAdd (.eqRefl _) ?_
    exact ((congrInst2 a qq.eqSymm (.eqRefl _)).eqTrans (one_mul _).eqSymm).eqTrans
      (congrMul e1.eqSymm (.eqRefl _))

/-! ## The prefix identity -/

/-- The prefix identity also allows each divisor index to supply its own parameter. -/
theorem prefix_identity_of (outer correction prefixBody param : PTm 2)
    (outerAt : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (j M h y : PTm m), Δ ⊢[PRAAx]
      inst2 outer j (pairT (pairT M h) y) ≐ Apre a (quo M (pw (succ j) h)) (inst2 param j y))
    (correctionAt : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (j M h y : PTm m), Δ ⊢[PRAAx]
      inst2 correction j (pairT (pairT M h) y) ≐
        eqb (rem M (pw (succ j) h)) zero * inst2 a (quo M (pw (succ j) h)) (inst2 param j y))
    (prefixAt : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i h y : PTm m), Δ ⊢[PRAAx]
      inst2 prefixBody i (pairT h y) ≐ ap2 (sumF correction) (succ i) (pairT (pairT (succ i) h) y))
    {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF outer) N (pairT (pairT N h) y) ≐ ap2 (sumF prefixBody) N (pairT h y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF outer) (var 0) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) ≐
      ap2 (sumF prefixBody) (var 0) (pairT (Syn.shift h) (Syn.shift y))) := by
    ipra_qfind [subst_ap2, subst_pairT]
    · exact (sum_zero _ _).eqTrans (sum_zero _ _).eqSymm
    · let φ : Fm PTm (n + 1) := ap2 (sumF outer) (var 0) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) ≐
        ap2 (sumF prefixBody) (var 0) (pairT (Syn.shift h) (Syn.shift y))
      let Δ : List (Fm PTm (n + 1)) := φ :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] φ := Prf.hyp0
      have hShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift h) := by
        simpa [Fm.shift, Syn.shift] using hh.shift
      have hp : Δ ⊢[PRAAx] Syn.shift h ≐ succ (pred (Syn.shift h)) := pos_of_one_le hShift.wk
      have split : Δ ⊢[PRAAx]
          ap2 (sumF outer) (succ (var 0)) (pairT (pairT (succ (var 0)) (Syn.shift h)) (Syn.shift y)) ≐
          ap2 (sumF outer) (succ (var 0)) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) +
            ap2 (sumF correction) (succ (var 0)) (pairT (pairT (succ (var 0)) (Syn.shift h)) (Syn.shift y)) := by
        refine sum_add2 outer correction outer (.allI (.impI ?_))
        rw [show Syn.shift (pairT (pairT (succ (var 0)) (Syn.shift h)) (Syn.shift y)) =
            pairT (pairT (succ (var 1)) (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift y)) by simp [Syn.shift],
          show Syn.shift (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) =
            pairT (pairT (var 1) (Syn.shift (Syn.shift h))) (Syn.shift (Syn.shift y)) by simp [Syn.shift]]
        let Λ : List (Fm PTm (n + 2)) := lt (var 0) (Syn.shift (succ (var 0))) :: Δ.map Fm.shift
        have hq : Λ ⊢[PRAAx] pw (succ (var 0)) (Syn.shift (Syn.shift h)) ≐
            succ (pred (pw (succ (var 0)) (Syn.shift (Syn.shift h)))) :=
          pos_of_one_le (one_le_pw' (by ipra_le 𝔞 (var 0)) _)
        refine (outerAt _ _ _ _).eqTrans ((step_pt a hq).eqTrans ?_)
        exact congrAdd (outerAt _ _ _ _).eqSymm (correctionAt _ _ _ _).eqSymm
      have hlt : Δ ⊢[PRAAx] lt (var 0) (pw (succ (var 0)) (Syn.shift h)) :=
        le_congr (.eqRefl _) (congrAp2 powF hp.eqSymm (.eqRefl _)) (le_self_pw _ _)
      have hq : Δ ⊢[PRAAx] pw (succ (var 0)) (Syn.shift h) ≐ succ (pred (pw (succ (var 0)) (Syn.shift h))) :=
        pos_of_one_le (one_le_pw' (by ipra_le 𝔞 (var 0)) _)
      have last : Δ ⊢[PRAAx] inst2 outer (var 0) (pairT (pairT (var 0) (Syn.shift h)) (Syn.shift y)) ≐ zero :=
        (outerAt _ _ _ _).eqTrans ((congrAp2 _ (quo_small hq hlt) (.eqRefl _)).eqTrans (sum_zero _ _))
      have oldSum := (sum_succ _ _ _).eqTrans ((congrAdd (.eqRefl _) last).eqTrans (add_zero _))
      have nextPrefix := (sum_succ (Γ := Δ) prefixBody (var 0) (pairT (Syn.shift h) (Syn.shift y))).eqTrans
        (congrAdd (.eqRefl _) (prefixAt (var 0) (Syn.shift h) (Syn.shift y)))
      exact split.eqTrans ((congrAdd (oldSum.eqTrans ih) (.eqRefl _)).eqTrans nextPrefix.eqSymm)
  simpa [Syn.subst_inst_shift] using hall.allE N

/-- `Σ_{d<N} A(⌊N/(d+1)^h⌋) = Σ_{i<N} b_h(i+1)` for `h ≥ 1`. -/
theorem prefix_identity {h : PTm n} (hh : Γ ⊢[PRAAx] le one h) (N y : PTm n) :
    Γ ⊢[PRAAx] Bt a N h y ≐ Bpre a N h y := by
  refine prefix_identity_of a (btB a) (cB a) (bpB a) (var 1) ?_ ?_ (bpB_at a) hh N y
  · intro m Δ j M h' y'
    simpa [inst2] using btB_at (Γ := Δ) a j M h' y'
  · intro m Δ j M h' y'
    simpa [inst2] using cB_at (Γ := Δ) a j M h' y'

end LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix

export_ipra AnalyticNumberTheory.PowerDivisorPrefix (Apre)

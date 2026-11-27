import IPRADerivations.AnalyticNumberTheory.PowerDivisorInversion

/-!
# The growth transfer `A ⇒ B_h` (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "Write its `d`th term as `t_d`, set `m_d = ⌊N/d^h⌋` … the bound at `2r` gives
`|t_d|^{4r} ≤ c m_d^{2r+1}` … As `d²m_d ≤ N` …" — here for the forward sum `B_h(N) = Σ_{d≤N} A(m_d)`.

For signed coefficients `a = a⁺ − a⁻` (two bodies), `h ≥ 2`, `r ≥ 1`:

* `mqB`, `mq_at`: `m_d = ⌊N/d^h⌋` as a body; `arg_bound`: `d² m_d ≤ N` (`d² ≤ d^h`, `d^h⌊N/d^h⌋ ≤ N`);
* `forward_core`: if `|A(M)|^{4r} ≤ c M^{2r+1}` for every `M`, then `|B_h(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}`:
  `PowerTransfer.transfer` with `t_d = A(m_d)` and `PowerDivisorPrefix.prefix_identity` for `a⁺` and `a⁻`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorPrefix
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorRow (pw_pos1)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion (Zp)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (transfer ArgBound TermBound k4 r8)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorInversion (RS rB rB_at wP wN inversion)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (muP muN congrEqb' om sq)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `m_d = ⌊N/(i+1)^h⌋` over `0 = i`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def mqB : PTm 2 := quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1))))

theorem inst2_mqB (i P : PTm n) : inst2 mqB i P = quo (fstT (fstT P)) (pw (succ i) (sndT (fstT P))) := by
  simp [inst2, mqB]

theorem mq_at (i N h y : PTm n) : Γ ⊢[PRAAx] inst2 mqB i (Zp N h y) ≐ quo N (pw (succ i) h) := by
  rw [inst2_mqB]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _))

/-- `(i+1)² ⌊N/(i+1)^h⌋ ≤ N` for `h ≥ 2`. -/
theorem arg_bound_pt {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (i N : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ i) two * quo N (pw (succ i) h)) N := by
  have hi : Γ ⊢[PRAAx] succ i ≐ succ (pred (succ i)) := pos_of_one_le (by ipra_le 𝔞 i)
  have p := pw_le_exp hi hh
  have q := quo_mul_le (x := N) (pw_pos1 (Γ := Γ) (h := h) i)
  have m := mul_le_mul_right (quo N (pw (succ i) h)) p
  exact le_trans m (le_congr (mul_comm _ _) (.eqRefl _) q)

theorem arg_bound {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (N y : PTm n) :
    Γ ⊢[PRAAx] ArgBound mqB N (Zp N h y) := by
  refine .allI (.impI ?_)
  rw [show Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) by simp [Syn.shift]]
  have hh' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift h) := by
    have b : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift h) := by simpa [Fm.shift, Syn.shift] using hh.shift
    exact b.wk
  exact le_congr (congrMul (.eqRefl _) (mq_at _ _ _ _)).eqSymm (.eqRefl _) (arg_bound_pt hh' (var 0) (Syn.shift N))

/-! ## Instantiating a shifted universal at a term -/

/-- The substitution `0 ↦ t`, `j + 1 ↦ j + 1` fixes shifted terms. -/
theorem subst_cons_shift (t : PTm (n + 1)) (s : PTm n) :
    Syn.subst (Fin.cases t (fun j => var j.succ) : Fin (n + 1) → PTm (n + 1)) (Syn.shift s) = Syn.shift s := by
  simp only [Syn.shift, Syn.subst_subst]
  congr 1

/-- `∀x φ` gives `φ[0 := t]` in the shifted context, for any term `t` (which may mention `var 0`). -/
theorem allE_shift {φ : Fm PTm (n + 1)} (h : Γ ⊢[PRAAx] Fm.all φ) (t : PTm (n + 1)) :
    (Γ.map Fm.shift) ⊢[PRAAx] φ.subst (Fin.cases t (fun j => var j.succ)) := by
  have b := Prf.allE t h.shift
  have e : (φ.subst (up (fun i => var i.succ))).subst (Syn.inst t) = φ.subst (Fin.cases t (fun j => var j.succ)) := by
    rw [Fm.subst_subst]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [e] at b
  exact b

variable (aP aN : PTm 2)

/-- The input bound `|A(M)|^{4r} ≤ c M^{2r+1}` for every `M`. -/
abbrev InA (y r c : PTm n) : Fm PTm n :=
  Fm.all (le (pw (absd (Apre aP (var 0) (Syn.shift y)) (Apre aN (var 0) (Syn.shift y))) (k4 (Syn.shift r)))
    (Syn.shift c * pw (var 0) (succ (two * Syn.shift r))))

/-- `|B_h(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` from `|A(M)|^{4r} ≤ c M^{2r+1}` (`h ≥ 2`, `r ≥ 1`). -/
theorem forward_core {h r c : PTm n} (hh : Γ ⊢[PRAAx] le two h) (hr : Γ ⊢[PRAAx] le one r)
    (y : PTm n) (hA : Γ ⊢[PRAAx] InA aP aN y r c) (N : PTm n) :
    Γ ⊢[PRAAx] le (pw (absd (Bpre aP N h y) (Bpre aN N h y)) (two * r))
      (succ c * pw (r8 r) (two * r) * pw N (succ r)) := by
  have hh1 : Γ ⊢[PRAAx] le one h := by ipra_le sl hh + 1
  have ht : Γ ⊢[PRAAx] TermBound (btB aP) (btB aN) mqB N (Zp N h y) r c := by
    refine .allI (.impI ?_)
    rw [show Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) by simp [Syn.shift]]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hA' : Λ ⊢[PRAAx] le (pw (absd (Apre aP (quo (Syn.shift N) (pw (succ (var 0)) (Syn.shift h))) (Syn.shift y))
        (Apre aN (quo (Syn.shift N) (pw (succ (var 0)) (Syn.shift h))) (Syn.shift y))) (k4 (Syn.shift r)))
        (Syn.shift c * pw (quo (Syn.shift N) (pw (succ (var 0)) (Syn.shift h))) (succ (two * Syn.shift r))) := by
      have b := allE_shift hA (quo (Syn.shift N) (pw (succ (var 0)) (Syn.shift h)))
      simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_monus, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Fin.cases_zero, subst_cons_shift] at b
      exact b.wk
    have e1 := btB_at (Γ := Λ) aP (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have e2 := btB_at (Γ := Λ) aN (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have e3 := mq_at (Γ := Λ) (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    exact le_congr (congrPw (congrAdd (congrMonus e1 e2) (congrMonus e2 e1)) (.eqRefl _)).eqSymm
      (congrMul (.eqRefl _) (congrPw e3 (.eqRefl _))).eqSymm hA'
  have tr := transfer (btB aP) (btB aN) mqB hr (arg_bound hh N y) ht
  have s1 := prefix_identity aP hh1 N y
  have s2 := prefix_identity aN hh1 N y
  exact le_congr (congrPw (congrAdd (congrMonus s1 s2) (congrMonus s2 s1)) (.eqRefl _)) (.eqRefl _) tr

/-! ## The backward transfer `B_h ⇒ A` -/

/-- `μ⁺ + μ⁻ ≤ 1`. -/
theorem mu_sum_le (N d : PTm n) : Γ ⊢[PRAAx] le (muP N d + muN N d) one := by
  have b1 := eqb_le_one (Γ := Γ) (sq N d) zero
  refine .orE (eqb_cases (Γ := Γ) (rem (om N d) two) zero) ?_ ?_
  · let C : List (Fm PTm n) := (eqb (rem (om N d) two) zero ≐ zero) :: Γ
    have b2 := eqb_le_one (Γ := C) (rem (om N d) two) one
    have m := le_mul_mono b1.wk b2
    have zz := natEq ((congrMul (.eqRefl (eqb (sq N d) zero)) (Prf.hyp0 : C ⊢[PRAAx] eqb (rem (om N d) two) zero ≐ zero)).eqTrans (mul_zero _))
    ipra_le sl m with -zz
  · let C : List (Fm PTm n) := (eqb (rem (om N d) two) zero ≐ one) :: Γ
    have r0 : C ⊢[PRAAx] rem (om N d) two ≐ zero := LeanProofs.IPRA.Foundations.BoundedReflection.eq_of_eqb Prf.hyp0
    have e1 : C ⊢[PRAAx] eqb (rem (om N d) two) one ≐ zero :=
      (congrEqb' r0 (.eqRefl _)).eqTrans (eqb_zero_of_lt (le_refl _))
    have p1 := natEq ((congrMul (.eqRefl (eqb (sq N d) zero)) (Prf.hyp0 : C ⊢[PRAAx] eqb (rem (om N d) two) zero ≐ one)).eqTrans
      (LeanProofs.IPRA.AnalyticNumberTheory.PowerBudget.mul_one' _))
    have p2 := natEq ((congrMul (.eqRefl (eqb (sq N d) zero)) e1).eqTrans (mul_zero _))
    ipra_le sl b1.wk with -p1 - p2

/-- `|(pb + qc) − (pc + qb)| ≤ |b − c|` for `p + q ≤ 1`. -/
theorem mu_mix {p q b c : PTm n} (hpq : Γ ⊢[PRAAx] le (p + q) one) :
    Γ ⊢[PRAAx] le (absd (p * b + q * c) (p * c + q * b)) (absd b c) := by
  have l1 := le_absd_l (Γ := Γ) b c
  have l2 := le_absd_r (Γ := Γ) b c
  have m1 := le_mul_mono (le_refl p) l1
  have m2 := le_mul_mono (le_refl q) l2
  have m3 := le_mul_mono (le_refl p) l2
  have m4 := le_mul_mono (le_refl q) l1
  have m5 := mul_le_mul_right (absd b c) hpq
  refine absd_le ?_ ?_
  · ipra_le sl m1 + sl m2 + sl m5
  · ipra_le sl m3 + sl m4 + sl m5

/-- `B(⌊N/(i+1)^h⌋)` over `0 = i`, `1 = ⟨⟨N, h⟩, y⟩`. -/
def BqB (a : PTm 2) : PTm 2 :=
  ap2 (sumF (bpB a)) (quo (fstT (fstT (var 1))) (pw (succ (var 0)) (sndT (fstT (var 1)))))
    (pairT (sndT (fstT (var 1))) (sndT (var 1)))

/-- `μ⁺(i+1)`, `μ⁻(i+1)` at the prime bound `N + 1`. -/
abbrev mPB : PTm 2 := muP (succ (fstT (fstT (var 1)))) (succ (var 0))
abbrev mNB : PTm 2 := muN (succ (fstT (fstT (var 1)))) (succ (var 0))

/-- `t⁺ = μ⁺ B⁺ + μ⁻ B⁻` and `t⁻ = μ⁺ B⁻ + μ⁻ B⁺`. -/
def tPB : PTm 2 := mPB * BqB aP + mNB * BqB aN
def tNB : PTm 2 := mPB * BqB aN + mNB * BqB aP

theorem BqB_at (a : PTm 2) (i N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (BqB a) i (Zp N h y) ≐ Bpre a (quo N (pw (succ i) h)) h y := by
  have hs : inst2 (BqB a) i (Zp N h y) = ap2 (sumF (bpB a)) (quo (fstT (fstT (Zp N h y))) (pw (succ i)
      (sndT (fstT (Zp N h y))))) (pairT (sndT (fstT (Zp N h y))) (sndT (Zp N h y))) := by simp [inst2, BqB]
  rw [hs]
  have e1 : Γ ⊢[PRAAx] fstT (fstT (pairT (pairT N h) y)) ≐ N := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
  have e2 : Γ ⊢[PRAAx] sndT (fstT (pairT (pairT N h) y)) ≐ h := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
  exact congrAp2 _ (congrAp2 quoF e1 (congrAp2 powF e2 (.eqRefl _))) (congrPairT e2 (snd_pair _ _))

theorem mu_at (i N h y : PTm n) :
    Γ ⊢[PRAAx] (inst2 (mPB : PTm 2) i (Zp N h y) ≐ muP (succ N) (succ i)) ⋏
      (inst2 (mNB : PTm 2) i (Zp N h y) ≐ muN (succ N) (succ i)) := by
  have hP : inst2 (mPB : PTm 2) i (Zp N h y) = muP (succ (fstT (fstT (Zp N h y)))) (succ i) := by simp [inst2]
  have hN : inst2 (mNB : PTm 2) i (Zp N h y) = muN (succ (fstT (fstT (Zp N h y)))) (succ i) := by simp [inst2]
  rw [hP, hN]
  have e1 : Γ ⊢[PRAAx] succ (fstT (fstT (pairT (pairT N h) y))) ≐ succ N :=
    congrSucc ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _))
  exact congrMu e1

/-- The input bound `|B_h(M)|^{4r} ≤ c M^{2r+1}` for every `M`. -/
abbrev InB (h y r c : PTm n) : Fm PTm n :=
  Fm.all (le (pw (absd (Bpre aP (var 0) (Syn.shift h) (Syn.shift y)) (Bpre aN (var 0) (Syn.shift h) (Syn.shift y)))
    (k4 (Syn.shift r))) (Syn.shift c * pw (var 0) (succ (two * Syn.shift r))))

/-- `R_w(N) = Σ_{i<N} sg(i+1) w(i+1) B_h(⌊N/(i+1)^h⌋)` (the term `d = 0` vanishes). -/
theorem rs_shift (a w : PTm 2) (N h y : PTm n) :
    Γ ⊢[PRAAx] RS a w N h y ≐ ap2 (sumF (shiftBody (rB a w))) N (Zp N h y) := by
  refine (sum_shift _ _ _).eqTrans ((congrAdd ?_ (.eqRefl _)).eqTrans (zero_add _))
  exact (rB_at a w _ _ _ _).eqTrans ((congrMul (congrMul sg_zero (.eqRefl _)) (.eqRefl _)).eqTrans
    ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _)))

theorem rB_succ (a w : PTm 2) (i N h y : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody (rB a w)) i (Zp N h y) ≐ inst2 w (succ i) (Zp N h y) * Bpre a (quo N (pw (succ i) h)) h y := by
  rw [inst2_shiftBody]
  exact (rB_at a w _ _ _ _).eqTrans (congrMul ((congrMul (sg_succ _) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _))

theorem inst2_wP_succ (i N h y : PTm n) :
    Γ ⊢[PRAAx] (inst2 (wP : PTm 2) (succ i) (Zp N h y) ≐ muP (succ N) (succ i)) ⋏
      (inst2 (wN : PTm 2) (succ i) (Zp N h y) ≐ muN (succ N) (succ i)) := by
  have hP : inst2 (wP : PTm 2) (succ i) (Zp N h y) = muP (succ (fstT (fstT (Zp N h y)))) (succ i) := by simp [inst2]
  have hN : inst2 (wN : PTm 2) (succ i) (Zp N h y) = muN (succ (fstT (fstT (Zp N h y)))) (succ i) := by simp [inst2]
  rw [hP, hN]
  exact congrMu (congrSucc ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)))

/-- `Σ_{i<N} t⁺ = R_{μ⁺}(a⁺) + R_{μ⁻}(a⁻)` and `Σ_{i<N} t⁻ = R_{μ⁺}(a⁻) + R_{μ⁻}(a⁺)`. -/
theorem t_sums (N h y : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (tPB aP aN)) N (Zp N h y) ≐ RS aP wP N h y + RS aN wN N h y) ⋏
      (ap2 (sumF (tNB aP aN)) N (Zp N h y) ≐ RS aN wP N h y + RS aP wN N h y) := by
  have pt : ∀ (Δ : List (Fm PTm (n + 1))) (i : PTm (n + 1)),
      Δ ⊢[PRAAx] (inst2 (tPB aP aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐
          inst2 (shiftBody (rB aP wP)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
          inst2 (shiftBody (rB aN wN)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) ⋏
        (inst2 (tNB aP aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐
          inst2 (shiftBody (rB aN wP)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
          inst2 (shiftBody (rB aP wN)) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y))) := by
    intro Δ i
    have hP : inst2 (tPB aP aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) =
        inst2 (mPB : PTm 2) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aP) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
        inst2 (mNB : PTm 2) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) := by simp [inst2, tPB]
    have hN : inst2 (tNB aP aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) =
        inst2 (mPB : PTm 2) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aN) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
        inst2 (mNB : PTm 2) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aP) i (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) := by simp [inst2, tNB]
    rw [hP, hN]
    have mu := mu_at (Γ := Δ) i (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have wu := inst2_wP_succ (Γ := Δ) i (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have bP := BqB_at (Γ := Δ) aP i (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have bN := BqB_at (Γ := Δ) aN i (Syn.shift N) (Syn.shift h) (Syn.shift y)
    refine .andI ?_ ?_
    · exact (congrAdd (congrMul (Prf.andE₁ mu) bP) (congrMul (Prf.andE₂ mu) bN)).eqTrans
        (congrAdd ((rB_succ aP wP _ _ _ _).eqTrans (congrMul (Prf.andE₁ wu) (.eqRefl _))).eqSymm
          ((rB_succ aN wN _ _ _ _).eqTrans (congrMul (Prf.andE₂ wu) (.eqRefl _))).eqSymm)
    · exact (congrAdd (congrMul (Prf.andE₁ mu) bN) (congrMul (Prf.andE₂ mu) bP)).eqTrans
        (congrAdd ((rB_succ aN wP _ _ _ _).eqTrans (congrMul (Prf.andE₁ wu) (.eqRefl _))).eqSymm
          ((rB_succ aP wN _ _ _ _).eqTrans (congrMul (Prf.andE₂ wu) (.eqRefl _))).eqSymm)
  have sh : Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) := by simp [Syn.shift]
  refine .andI ?_ ?_
  · refine (sum_add2 (shiftBody (rB aP wP)) (shiftBody (rB aN wN)) (tPB aP aN) (.allI (.impI ?_))).eqTrans
      (congrAdd (rs_shift aP wP N h y).eqSymm (rs_shift aN wN N h y).eqSymm)
    rw [sh]; exact Prf.andE₁ (pt _ _)
  · refine (sum_add2 (shiftBody (rB aN wP)) (shiftBody (rB aP wN)) (tNB aP aN) (.allI (.impI ?_))).eqTrans
      (congrAdd (rs_shift aN wP N h y).eqSymm (rs_shift aP wN N h y).eqSymm)
    rw [sh]; exact Prf.andE₂ (pt _ _)

/-- `|A(N)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` from `|B_h(M)|^{4r} ≤ c M^{2r+1}` (`h ≥ 2`, `r ≥ 1`). -/
theorem backward_core {h r c : PTm n} (hh : Γ ⊢[PRAAx] le two h) (hr : Γ ⊢[PRAAx] le one r)
    (y : PTm n) (hB : Γ ⊢[PRAAx] InB aP aN h y r c) (N : PTm n) :
    Γ ⊢[PRAAx] le (pw (absd (Apre aP N y) (Apre aN N y)) (two * r))
      (succ c * pw (r8 r) (two * r) * pw N (succ r)) := by
  have hh1 : Γ ⊢[PRAAx] le one h := by ipra_le sl hh + 1
  have ht : Γ ⊢[PRAAx] TermBound (tPB aP aN) (tNB aP aN) mqB N (Zp N h y) r c := by
    refine .allI (.impI ?_)
    rw [show Syn.shift (Zp N h y) = Zp (Syn.shift N) (Syn.shift h) (Syn.shift y) by simp [Syn.shift]]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    let M : PTm (n + 1) := quo (Syn.shift N) (pw (succ (var 0)) (Syn.shift h))
    have hB' : Λ ⊢[PRAAx] le (pw (absd (Bpre aP M (Syn.shift h) (Syn.shift y)) (Bpre aN M (Syn.shift h) (Syn.shift y)))
        (k4 (Syn.shift r))) (Syn.shift c * pw M (succ (two * Syn.shift r))) := by
      have b := allE_shift hB M
      simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_monus, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, subst_pairT, Syn.subst_var, Fin.cases_zero, subst_cons_shift] at b
      exact b.wk
    have hP : inst2 (tPB aP aN) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) =
        inst2 (mPB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aP) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
        inst2 (mNB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aN) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) := by simp [inst2, tPB]
    have hN : inst2 (tNB aP aN) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) =
        inst2 (mPB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aN) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
        inst2 (mNB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aP) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) := by simp [inst2, tNB]
    rw [hP, hN]
    have mu := mu_at (Γ := Λ) (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have bP := BqB_at (Γ := Λ) aP (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have bN := BqB_at (Γ := Λ) aN (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have e3 := mq_at (Γ := Λ) (var 0) (Syn.shift N) (Syn.shift h) (Syn.shift y)
    have mix := mu_mix (Γ := Λ) (b := Bpre aP M (Syn.shift h) (Syn.shift y)) (c := Bpre aN M (Syn.shift h) (Syn.shift y))
      (mu_sum_le (succ (Syn.shift N)) (succ (var 0)))
    have ep : Λ ⊢[PRAAx] inst2 (mPB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
        inst2 (BqB aP) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
        inst2 (mNB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aN) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐
        muP (succ (Syn.shift N)) (succ (var 0)) * Bpre aP M (Syn.shift h) (Syn.shift y) +
          muN (succ (Syn.shift N)) (succ (var 0)) * Bpre aN M (Syn.shift h) (Syn.shift y) :=
      congrAdd (congrMul (Prf.andE₁ mu) bP) (congrMul (Prf.andE₂ mu) bN)
    have en : Λ ⊢[PRAAx] inst2 (mPB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
        inst2 (BqB aN) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) +
        inst2 (mNB : PTm 2) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) *
          inst2 (BqB aP) (var 0) (Zp (Syn.shift N) (Syn.shift h) (Syn.shift y)) ≐
        muP (succ (Syn.shift N)) (succ (var 0)) * Bpre aN M (Syn.shift h) (Syn.shift y) +
          muN (succ (Syn.shift N)) (succ (var 0)) * Bpre aP M (Syn.shift h) (Syn.shift y) :=
      congrAdd (congrMul (Prf.andE₁ mu) bN) (congrMul (Prf.andE₂ mu) bP)
    have pw1 := pw_le_pw (k4 (Syn.shift r)) mix
    refine le_congr (congrPw (congrAdd (congrMonus ep en) (congrMonus en ep)) (.eqRefl _)).eqSymm
      (congrMul (.eqRefl _) (congrPw e3 (.eqRefl _))).eqSymm (le_trans pw1 hB')
  have tr := transfer (tPB aP aN) (tNB aP aN) mqB hr (arg_bound hh N y) ht
  have ts := t_sums aP aN (Γ := Γ) N h y
  have iP := natEq (inversion aP hh1 N y (Γ := Γ))
  have iN := natEq (inversion aN hh1 N y (Γ := Γ))
  have s1 := natEq (Prf.andE₁ ts)
  have s2 := natEq (Prf.andE₂ ts)
  have la := le_absd_l (Γ := Γ) (ap2 (sumF (tPB aP aN)) N (Zp N h y)) (ap2 (sumF (tNB aP aN)) N (Zp N h y))
  have lb := le_absd_r (Γ := Γ) (ap2 (sumF (tPB aP aN)) N (Zp N h y)) (ap2 (sumF (tNB aP aN)) N (Zp N h y))
  have hA : Γ ⊢[PRAAx] le (absd (Apre aP N y) (Apre aN N y))
      (absd (ap2 (sumF (tPB aP aN)) N (Zp N h y)) (ap2 (sumF (tNB aP aN)) N (Zp N h y))) := by
    refine absd_le ?_ ?_
    · ipra_le sl la with s1 - s2 + iP - iN
    · ipra_le sl lb with s2 - s1 - iP + iN
  exact le_trans (pw_le_pw _ hA) tr

/-! ## The growth sentences and their equivalence -/

/-- `|S(N)|^{2(k+1)} ≤ c N^{k+2}` for the signed sequence `S = s⁺ − s⁻` with parameter `x`. -/
abbrev Mat (sP sN : PTm 2) (x k c N : PTm n) : Fm PTm n :=
  le (pw (absd (inst2 sP N x) (inst2 sN N x)) (two * succ k)) (c * pw N (succ (succ k)))

theorem subst_Mat {m : ℕ} (σ : Fin n → PTm m) (sP sN : PTm 2) (x k c N : PTm n) :
    (Mat sP sN x k c N).subst σ = Mat sP sN (Syn.subst σ x) (Syn.subst σ k) (Syn.subst σ c) (Syn.subst σ N) := by
  simp [Mat, subst_le, subst_ap2, subst_inst2]

/-- The growth statement `∀k ∃c ∀N |S(N)|^{2(k+1)} ≤ c N^{k+2}`. -/
abbrev GrowthS (sP sN : PTm 2) (x : PTm n) : Fm PTm n :=
  Fm.all (Fm.ex (Fm.all (Mat sP sN (Syn.shift (Syn.shift (Syn.shift x))) (var 2) (var 1) (var 0))))

/-! Substitution at the three bound variables. -/

theorem up3_v0 {a b : ℕ} (σ : Fin a → PTm b) : Syn.subst (up (up (up σ))) (var 0 : PTm (a + 3)) = var 0 := rfl
theorem up3_v1 {a b : ℕ} (σ : Fin a → PTm b) : Syn.subst (up (up (up σ))) (var 1 : PTm (a + 3)) = var 1 := rfl
theorem up3_v2 {a b : ℕ} (σ : Fin a → PTm b) : Syn.subst (up (up (up σ))) (var 2 : PTm (a + 3)) = var 2 := rfl
theorem up2_v0 {a b : ℕ} (σ : Fin (a + 1) → PTm b) : Syn.subst (up (up σ)) (var 0 : PTm (a + 3)) = var 0 := rfl
theorem up2_v1 {a b : ℕ} (σ : Fin (a + 1) → PTm b) : Syn.subst (up (up σ)) (var 1 : PTm (a + 3)) = var 1 := rfl
theorem up2_v2 {a b : ℕ} (σ : Fin (a + 1) → PTm b) :
    Syn.subst (up (up σ)) (var 2 : PTm (a + 3)) = Syn.shift (Syn.shift (σ 0)) := rfl
theorem up1_v0 {a b : ℕ} (σ : Fin (a + 2) → PTm b) : Syn.subst (up σ) (var 0 : PTm (a + 3)) = var 0 := rfl
theorem up1_v1 {a b : ℕ} (σ : Fin (a + 2) → PTm b) : Syn.subst (up σ) (var 1 : PTm (a + 3)) = Syn.shift (σ 0) := rfl
theorem up1_v2 {a b : ℕ} (σ : Fin (a + 2) → PTm b) : Syn.subst (up σ) (var 2 : PTm (a + 3)) = Syn.shift (σ 1) := rfl
theorem inst_v0 {a : ℕ} (t : PTm a) : (Syn.inst t : Fin (a + 1) → PTm a) 0 = t := rfl
theorem inst_v1 {a : ℕ} (t : PTm (a + 1)) : (Syn.inst t : Fin (a + 2) → PTm (a + 1)) 1 = var 0 := rfl

/-- The prefix `A(M, y)` as a body. -/
def AB (a : PTm 2) : PTm 2 := ap2 (sumF (shiftBody a)) (var 0) (var 1)
/-- The prefix `B_h(M)` as a body over `⟨h, y⟩`. -/
def BB (a : PTm 2) : PTm 2 := ap2 (sumF (bpB a)) (var 0) (var 1)

theorem inst2_AB (a : PTm 2) (M y : PTm n) : inst2 (AB a) M y = Apre a M y := by simp [inst2, AB]
theorem inst2_BB (a : PTm 2) (M P : PTm n) : inst2 (BB a) M P = ap2 (sumF (bpB a)) M P := by simp [inst2, BB]

/-- The output constant `(c+1)(8r)^{2r}` at `r = k+1`. -/
abbrev Cout (k c : PTm n) : PTm n := succ c * pw (r8 (succ k)) (two * succ k)

/-- The exponents of the input at `k' = 2k+1` are those of `r = k+1` at `4r`, `2r+1`. -/
theorem exps (k : PTm n) :
    (Γ ⊢[PRAAx] two * succ (succ (two * k)) ≐ k4 (succ k)) ∧
      (Γ ⊢[PRAAx] succ (succ (succ (two * k))) ≐ succ (two * succ k)) :=
  ⟨by ipra_ring, by ipra_ring⟩

theorem upf_one {a b : ℕ} (σ : Fin (a + 1) → PTm b) : (up σ : Fin (a + 2) → PTm (b + 1)) 1 = Syn.shift (σ 0) := rfl
theorem upf_two {a b : ℕ} (σ : Fin (a + 2) → PTm b) : (up σ : Fin (a + 3) → PTm (b + 1)) 2 = Syn.shift (σ 1) := rfl
theorem two_le_shift {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift h) := by
  simpa [Fm.shift, Syn.shift] using hh.shift
theorem subst_sh {a : ℕ} (u : PTm a) : Syn.subst (fun i => var i.succ) u = Syn.shift u := rfl

/-- The forward core in the matrix form of the sentences. -/
theorem forward_mat (aP aN : PTm 2) {h k c : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n)
    (hA : Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) (Syn.shift y) (Syn.shift (succ (two * k))) (Syn.shift c) (var 0)))
    (N : PTm n) : Γ ⊢[PRAAx] Mat (BB aP) (BB aN) (pairT h y) k (Cout k c) N := by
  have hr : Γ ⊢[PRAAx] le one (succ k) := by ipra_le 𝔞 k
  have hA' : Γ ⊢[PRAAx] InA aP aN y (succ k) c := by
    refine .allI ?_
    have b := hA.allOpen
    simp only [Mat, inst2_AB] at b
    rw [show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
    rw [show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
    have ex := exps (Γ := Γ.map Fm.shift) (Syn.shift k)
    exact le_congr (congrPw (.eqRefl _) ex.1) (congrMul (.eqRefl _) (congrPw (.eqRefl _) ex.2)) b
  have f := forward_core aP aN hh hr y hA' N
  simp only [Mat, inst2_BB]
  exact f

/-- `∀k ∃c φ(k, c) ⟶ ∀k ∃c ψ(k, c)`: for a fresh `k` the hypothesis is used at `E(k)`, and its witness `c` gives
the witness `C(k, c)`. -/
theorem all_ex_imp_at {φ ψ : Fm PTm (n + 2)} (E : PTm (n + 1)) (C : PTm (n + 2))
    (H : ((φ.subst (up (up fun i => var i.succ))).subst (up (Syn.inst E)) :: (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      (ψ.subst (up fun i => var i.succ)).subst (Syn.inst C)) :
    Γ ⊢[PRAAx] Fm.all (Fm.ex φ) ⟶ Fm.all (Fm.ex ψ) :=
  .impI (.allI (.exE (Prf.allE E (Prf.hyp0 (Γ := Γ) (φ := Fm.all (Fm.ex φ))).shift)
    (.exI C (H.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _))))))

/-- `all_ex_imp_at` with the hypothesis used at the same `k`. -/
theorem all_ex_imp {φ ψ : Fm PTm (n + 2)} (C : PTm (n + 2))
    (H : (φ :: (Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx] (ψ.subst (up fun i => var i.succ)).subst (Syn.inst C)) :
    Γ ⊢[PRAAx] Fm.all (Fm.ex φ) ⟶ Fm.all (Fm.ex ψ) :=
  .impI (.allI (.exE (Prf.hyp0 (Γ := Γ) (φ := Fm.all (Fm.ex φ))).allOpen
    (.exI C (H.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _))))))

/-- One `∀N` of the forward direction, with the binder forms as equations. -/
theorem forward_all (aP aN : PTm 2) {y h k c : PTm n} {K C X K' C' : PTm (n + 1)}
    (hK : K = Syn.shift (succ (two * k))) (hC : C = Syn.shift c) (hX : X = Syn.shift (pairT h y))
    (hK' : K' = Syn.shift k) (hC' : C' = Syn.shift (Cout k c)) (hh : Γ ⊢[PRAAx] le two h)
    (H : Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) (Syn.shift y) K C (var 0))) :
    Γ ⊢[PRAAx] Fm.all (Mat (BB aP) (BB aN) X K' C' (var 0)) := by
  subst hK hC hX hK' hC'
  refine .allI ?_
  have H1 := H.shift
  simp only [Fm.shift, Fm.subst_all, subst_Mat, subst_up_shift_pal, Syn.up_zero, Syn.subst_var, subst_sh] at H1
  have e1 : Syn.shift (Syn.shift (succ (two * k))) = Syn.shift (succ (two * Syn.shift k)) := by
    simp [Syn.shift]
  rw [e1] at H1
  have f := forward_mat aP aN (k := Syn.shift k) (c := Syn.shift c) (two_le_shift hh) (Syn.shift y) H1 (var 0)
  have e2 : Syn.shift (pairT h y) = pairT (Syn.shift h) (Syn.shift y) := by simp [Syn.shift]
  have e3 : Syn.shift (Cout k c) = Cout (Syn.shift k) (Syn.shift c) := by simp [Syn.shift]
  rw [e2, e3]
  exact f

/-- `thm:powerdivisor`, `A ⇒ B_h`: the growth statement of `A` gives that of `B_h` (`h ≥ 2`). -/
theorem growth_forward (aP aN : PTm 2) {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n) :
    Γ ⊢[PRAAx] GrowthS (AB aP) (AB aN) y ⟶ GrowthS (BB aP) (BB aN) (pairT h y) := by
  refine all_ex_imp_at (succ (two * var 0)) (Cout (var 1) (var 0)) ?_
  simp only [Fm.subst_all, subst_Mat, inst_v0, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ]
  exact forward_all aP aN (y := Syn.shift (Syn.shift y)) (h := Syn.shift (Syn.shift h)) (k := var 1) (c := var 0)
    (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
    (two_le_shift (two_le_shift hh)).wk Prf.hyp0

/-- The backward core in the matrix form of the sentences. -/
theorem backward_mat (aP aN : PTm 2) {h k c : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n)
    (hB : Γ ⊢[PRAAx] Fm.all (Mat (BB aP) (BB aN) (pairT (Syn.shift h) (Syn.shift y)) (Syn.shift (succ (two * k)))
      (Syn.shift c) (var 0)))
    (N : PTm n) : Γ ⊢[PRAAx] Mat (AB aP) (AB aN) y k (Cout k c) N := by
  have hr : Γ ⊢[PRAAx] le one (succ k) := by ipra_le 𝔞 k
  have hB' : Γ ⊢[PRAAx] InB aP aN h y (succ k) c := by
    refine .allI ?_
    have b := hB.allOpen
    simp only [Mat, inst2_BB] at b
    rw [show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
    rw [show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
    have ex := exps (Γ := Γ.map Fm.shift) (Syn.shift k)
    exact le_congr (congrPw (.eqRefl _) ex.1) (congrMul (.eqRefl _) (congrPw (.eqRefl _) ex.2)) b
  have f := backward_core aP aN hh hr y hB' N
  simp only [Mat, inst2_AB]
  exact f

/-- One `∀N` of the backward direction, with the binder forms as equations. -/
theorem backward_all (aP aN : PTm 2) {y h k c : PTm n} {X K C X' K' C' : PTm (n + 1)}
    (hX : X = Syn.shift (pairT h y)) (hK : K = Syn.shift (succ (two * k))) (hC : C = Syn.shift c)
    (hX' : X' = Syn.shift y) (hK' : K' = Syn.shift k) (hC' : C' = Syn.shift (Cout k c)) (hh : Γ ⊢[PRAAx] le two h)
    (H : Γ ⊢[PRAAx] Fm.all (Mat (BB aP) (BB aN) X K C (var 0))) :
    Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) X' K' C' (var 0)) := by
  subst hX hK hC hX' hK' hC'
  refine .allI ?_
  have H1 := H.shift
  simp only [Fm.shift, Fm.subst_all, subst_Mat, subst_up_shift_pal, Syn.up_zero, Syn.subst_var, subst_sh] at H1
  have e1 : Syn.shift (Syn.shift (succ (two * k))) = Syn.shift (succ (two * Syn.shift k)) := by
    simp [Syn.shift]
  have e0 : Syn.shift (Syn.shift (pairT h y)) =
      pairT (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift y)) := by simp [Syn.shift]
  rw [e1, e0] at H1
  have f := backward_mat aP aN (k := Syn.shift k) (c := Syn.shift c) (two_le_shift hh) (Syn.shift y) H1 (var 0)
  have e3 : Syn.shift (Cout k c) = Cout (Syn.shift k) (Syn.shift c) := by simp [Syn.shift]
  rw [e3]
  exact f

/-- `thm:powerdivisor`, `B_h ⇒ A`: the growth statement of `B_h` gives that of `A` (`h ≥ 2`). -/
theorem growth_backward (aP aN : PTm 2) {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n) :
    Γ ⊢[PRAAx] GrowthS (BB aP) (BB aN) (pairT h y) ⟶ GrowthS (AB aP) (AB aN) y := by
  refine all_ex_imp_at (succ (two * var 0)) (Cout (var 1) (var 0)) ?_
  simp only [Fm.subst_all, subst_Mat, inst_v0, subst_up_shift_pal, Syn.subst_inst_shift, Syn.up_zero, upf_one, upf_two,
    Syn.subst_var, subst_sh, Fin.succ_zero_eq_one, Syn.shift_var, Syn.up_succ, Syn.inst_succ]
  exact backward_all aP aN (y := Syn.shift (Syn.shift y)) (h := Syn.shift (Syn.shift h)) (k := var 1) (c := var 0)
    (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
    (by simp [Syn.shift]) (two_le_shift (two_le_shift hh)).wk Prf.hyp0

/-- `thm:powerdivisor` (one exponent `h ≥ 2`, arbitrary signed coefficients `a = a⁺ − a⁻`): in iPRA,
`(∀k ∃c ∀N |A(N)|^{2(k+1)} ≤ c N^{k+2}) ↔ (∀k ∃c ∀N |B_h(N)|^{2(k+1)} ≤ c N^{k+2})`, with the explicit witness
`C_r(c) = (c+1)(8r)^{2r}` from the input witness at `2r`, `r = k + 1`, in both directions. -/
theorem growth_iff (aP aN : PTm 2) {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (GrowthS (AB aP) (AB aN) y) (GrowthS (BB aP) (BB aN) (pairT h y)) :=
  .andI (growth_forward aP aN hh y) (growth_backward aP aN hh y)

end LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth

export_ipra AnalyticNumberTheory.PowerDivisorGrowth (InA)

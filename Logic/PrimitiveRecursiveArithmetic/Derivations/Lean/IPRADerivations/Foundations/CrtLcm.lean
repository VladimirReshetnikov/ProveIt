import IPRADerivations.Foundations.CrtCoprime
import IPRADerivations.AnalyticNumberTheory.BinomialLcm
import IPRADerivations.AnalyticNumberTheory.ValuationAdd

/-!
# Least common multiples of finite families

Infrastructure for `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, `el:crt`
(the Chinese remainder theorem for a finite system of moduli, with representative below
`L = lcm(m_0, …, m_{k−1})`).

With `lcm(A, B) = ⌊AB / gcd(A, B)⌋` (`TotientCorollaries.lcm`):

* `lcm_crt`: `lcm(A, B) = A ⌊B / gcd(A, B)⌋`, the modulus of `ChineseRemainder.crt_unique_at`;
* `lcm_cong`, `lcm_dvd_of`: congruence modulo `A` and modulo `B` gives congruence modulo `lcm(A, B)`; a common
  multiple of `A` and `B` is a multiple of `lcm(A, B)`; `dvd_lcm_left`, `dvd_lcm_right`, `lcm_mono`;
* `dist_val`, **`dist_dvd`**: `gcd(lcm(A, B), C) ∣ lcm(gcd(A, C), gcd(B, C))`, compared prime by prime:
  `min(max(a, b), c) ≤ max(min(a, c), min(b, c))` for the valuations (`BinomialLcm.dvd_of_val_le`);
* for a family of moduli `m_i = mB(i, y) + 1` (as in `CrtCoprime`): `Lc K y = lcm(m_0, …, m_{K−1})` by primitive
  recursion, `Lc_succ`, `Lc_pos`, **`m_dvd_Lc`** (`m_i ∣ Lc K` for `i < K`), **`Lc_cong`** (`x ≡ z (mod m_i)` for
  every `i < K` gives `x ≡ z (mod Lc K)`; the hypothesis is the universally quantified formula).
-/

namespace LeanProofs.IPRA.Foundations.CrtLcm

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP prime_of_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcm_pos val_lcm)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationAdd (val_gcd_le val_gcd_ge)
open LeanProofs.IPRA.Foundations.CrtCoprime (mS mS_at m_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias mul_one_r := Common.mul_one_right

/-! ## Two moduli -/

theorem lcm_crt {A B : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) :
    Γ ⊢[PRAAx] lcm A B ≐ A * quo B (gcd A B) := by
  have hg := gcd_pos (B := B) hA
  have hd := gcd_dvd' (b := B) hA
  ipra_lc natEq (lcm_eq hA hB) - 𝔞 (quo B (gcd A B)) * natEq (eq_of_dvd' hg (Prf.andE₁ hd))

theorem lcm_cong {A B x z : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (h1 : Γ ⊢[PRAAx] rem x A ≐ rem z A) (h2 : Γ ⊢[PRAAx] rem x B ≐ rem z B) :
    Γ ⊢[PRAAx] rem x (lcm A B) ≐ rem z (lcm A B) := by
  have e := lcm_crt hA hB
  exact (congrAp2 remF (.eqRefl _) e).eqTrans ((crt_unique_at hA hB h1 h2).eqTrans
    (congrAp2 remF (.eqRefl _) e.eqSymm))

theorem lcm_dvd_of {A B z : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (h1 : Γ ⊢[PRAAx] dvd A z) (h2 : Γ ⊢[PRAAx] dvd B z) : Γ ⊢[PRAAx] dvd (lcm A B) z :=
  (lcm_cong (x := z) (z := zero) hA hB (h1.eqTrans (rem_zero A).eqSymm) (h2.eqTrans (rem_zero B).eqSymm)).eqTrans
    (rem_zero _)

theorem dvd_lcm_left {A B : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) :
    Γ ⊢[PRAAx] dvd A (lcm A B) := dvd_of_eq' hA (lcm_crt hA hB)

theorem dvd_lcm_right {A B : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) :
    Γ ⊢[PRAAx] dvd B (lcm A B) := by
  have hg := gcd_pos (B := B) hA
  have hd := gcd_dvd' (b := B) hA
  refine dvd_of_eq' hB (w := quo A (gcd A B)) ?_
  ipra_lc natEq (lcm_eq hA hB) - 𝔞 (quo A (gcd A B)) * natEq (eq_of_dvd' hg (Prf.andE₂ hd))

/-- `d ∣ e` gives `lcm(d, c) ∣ lcm(e, c)`. -/
theorem lcm_mono {d e c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (he : Γ ⊢[PRAAx] e ≐ succ (pred e))
    (hc : Γ ⊢[PRAAx] c ≐ succ (pred c)) (h : Γ ⊢[PRAAx] dvd d e) : Γ ⊢[PRAAx] dvd (lcm d c) (lcm e c) :=
  lcm_dvd_of hd hc (dvd_trans' hd he h (dvd_lcm_left he hc)) (dvd_lcm_right he hc)

/-! ## Distributivity, one way -/

theorem le_max_right (a b : PTm n) : Γ ⊢[PRAAx] le b (a + monus b a) := by
  refine .orE (lt_or_le b a) ?_ ?_
  · exact le_trans (le_trans (le_succ_self b) Prf.hyp0) (le_add_right a _)
  · exact le_congr (.eqRefl _) (eq_add_of_le Prf.hyp0) (le_refl b)

/-- `v_p(gcd(lcm(A, B), C)) ≤ v_p(lcm(gcd(A, C), gcd(B, C)))` for a prime `p`. -/
theorem dist_val {p A B C : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hC : Γ ⊢[PRAAx] C ≐ succ (pred C)) :
    Γ ⊢[PRAAx] le (val p (gcd (lcm A B) C)) (val p (lcm (gcd A C) (gcd B C))) := by
  have h2 := prime_two hp
  have Lp := lcm_pos hA hB
  have gx := val_gcd_le h2 Lp hC
  have vL := val_lcm hp hA hB
  have g1p := gcd_pos (B := C) hA
  have g2p := gcd_pos (B := C) hB
  have vR := val_lcm hp g1p g2p
  refine le_congr (.eqRefl _) vR.eqSymm ?_
  refine .orE (lt_or_le (val p A) (val p B)) ?_ ?_
  · -- `a < b`: the lcm has valuation `b`
    have hab : (lt (val p A) (val p B) :: Γ) ⊢[PRAAx] le (val p A) (val p B) :=
      le_trans (le_succ_self _) Prf.hyp0
    have vb : (lt (val p A) (val p B) :: Γ) ⊢[PRAAx] val p (lcm A B) ≐ val p B :=
      vL.wk.eqTrans (eq_add_of_le hab).eqSymm
    have xb := le_congr (.eqRefl _) vb (Prf.andE₁ gx.wk)
    have x2 := val_gcd_ge h2.wk hB.wk xb (Prf.andE₂ gx.wk)
    exact le_trans x2 (le_max_right _ _)
  · -- `b ≤ a`: the lcm has valuation `a`
    have hba : (le (val p B) (val p A) :: Γ) ⊢[PRAAx] monus (val p B) (val p A) ≐ zero := Prf.hyp0
    have va : (le (val p B) (val p A) :: Γ) ⊢[PRAAx] val p (lcm A B) ≐ val p A :=
      vL.wk.eqTrans ((congrAdd (.eqRefl _) hba).eqTrans (add_zero _))
    have xa := le_congr (.eqRefl _) va (Prf.andE₁ gx.wk)
    have x1 := val_gcd_ge h2.wk hA.wk xa (Prf.andE₂ gx.wk)
    exact le_trans x1 (le_add_right _ _)

/-- **`gcd(lcm(A, B), C) ∣ lcm(gcd(A, C), gcd(B, C))`** for `A, B, C ≥ 1`. -/
theorem dist_dvd {A B C : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hC : Γ ⊢[PRAAx] C ≐ succ (pred C)) :
    Γ ⊢[PRAAx] dvd (gcd (lcm A B) C) (lcm (gcd A C) (gcd B C)) := by
  have ap := gcd_pos (B := C) (lcm_pos hA hB)
  have bp := lcm_pos (gcd_pos (B := C) hA) (gcd_pos (B := C) hB)
  have la : Γ ⊢[PRAAx] lt (gcd (lcm A B) C) (succ (gcd (lcm A B) C + lcm (gcd A C) (gcd B C))) :=
    Order.lt_succ_of_le (le_add_right _ _)
  have lb : Γ ⊢[PRAAx] lt (lcm (gcd A C) (gcd B C)) (succ (gcd (lcm A B) C + lcm (gcd A C) (gcd B C))) :=
    Order.lt_succ_of_le (le_add_left _ _)
  refine dvd_of_val_le ap bp la lb (.allI (.impI (.impI ?_)))
  have sA := shift_pos hA; have sB := shift_pos hB; have sC := shift_pos hC
  have s1 : Syn.shift (gcd (lcm A B) C) = gcd (lcm (Syn.shift A) (Syn.shift B)) (Syn.shift C) := by
    simp only [Syn.shift, lcm, subst_ex2, subst_ap2, PTm.subst_mul, ConciseIPRA.PTm.subst_succ]
  have s2 : Syn.shift (lcm (gcd A C) (gcd B C)) =
      lcm (gcd (Syn.shift A) (Syn.shift C)) (gcd (Syn.shift B) (Syn.shift C)) := by
    simp only [Syn.shift, lcm, subst_ex2, subst_ap2, PTm.subst_mul, ConciseIPRA.PTm.subst_succ]
  rw [s1, s2]
  exact dist_val (prime_of_isP Prf.hyp0) sA.wk.wk sB.wk.wk sC.wk.wk

/-! ## The lcm of a family -/

section Family

variable (mB : PTm 2)

/-- The step `lcm(prev, m_K)`, over `0 = K`, `1 = prev`, `2 = y`. -/
def stepB : PTm 3 := lcm (var 1) (Syn.subst ![var 0, var 2] (mS mB))

/-- `Lc K y = lcm(m_0, …, m_{K−1})`, `Lc 0 y = 1`. -/
abbrev Lc (K y : PTm n) : PTm n := ap2 (rec2 (succ zero) (stepB mB)) K y

theorem Lc_zero (y : PTm n) : Γ ⊢[PRAAx] Lc mB zero y ≐ one := by
  have h := rec2_zero (Γ := Γ) (succ zero) (stepB mB) y
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem sub02 (σ : Fin 3 → PTm n) :
    Syn.subst σ (Syn.subst ![var 0, var 2] mB) = inst2 mB (σ 0) (σ 2) := by
  simp [subst_reindex2]

theorem Lc_succ (K y : PTm n) : Γ ⊢[PRAAx] Lc mB (succ K) y ≐ lcm (Lc mB K y) (inst2 (mS mB) K y) := by
  have h := rec2_succ (Γ := Γ) (succ zero) (stepB mB) K y
  have e : Syn.subst ![K, ap2 (rec2 (succ zero) (stepB mB)) K y, y] (stepB mB) =
      lcm (Lc mB K y) (inst2 (mS mB) K y) := by
    rw [mS_at]
    simp only [stepB, lcm, Lc, mS, subst_ap2, PTm.subst_mul, subst_ex2, Syn.subst_var, sub02,
      ConciseIPRA.PTm.subst_succ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  rw [e] at h; exact h

theorem Lc_pos (K y : PTm n) : Γ ⊢[PRAAx] Lc mB K y ≐ succ (pred (Lc mB K y)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Lc mB (var 0) (Syn.shift y) ≐ succ (pred (Lc mB (var 0) (Syn.shift y)))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact (Lc_zero mB y).eqTrans (congrSucc ((pred_succ zero).eqSymm.eqTrans (congrPred (Lc_zero mB y).eqSymm)))
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have e := Lc_succ (Γ := (Lc mB (var 0) (Syn.shift y) ≐ succ (pred (Lc mB (var 0) (Syn.shift y)))) ::
        Γ.map Fm.shift) mB (var 0) (Syn.shift y)
      exact e.eqTrans ((lcm_pos Prf.hyp0 (m_pos mB _ _)).eqTrans (congrSucc (congrPred e.eqSymm)))
  have h2 := Prf.allE K hall
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_pred, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact h2

theorem Lc_step_dvd (K y : PTm n) : Γ ⊢[PRAAx] dvd (Lc mB K y) (Lc mB (succ K) y) :=
  dvd_congr (Lc_succ mB K y).eqSymm (dvd_lcm_left (Lc_pos mB K y) (m_pos mB K y))

/-- **`m_i ∣ Lc K` for `i < K`.** -/
theorem m_dvd_Lc {i K y : PTm n} (hi : Γ ⊢[PRAAx] lt i K) : Γ ⊢[PRAAx] dvd (inst2 (mS mB) i y) (Lc mB K y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (lt (Syn.shift i) (var 0) ⟶
      dvd (inst2 (mS mB) (Syn.shift i) (Syn.shift y)) (Lc mB (var 0) (Syn.shift y))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_lt, subst_dvd, Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [Fm.subst_imp, subst_lt, subst_dvd, Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI (.orE (lt_succ_cases Prf.hyp0) ?_ ?_)
      · exact dvd_trans' (m_pos mB _ _) (Lc_pos mB _ _) (.impE hyp2 Prf.hyp0) (Lc_step_dvd mB _ _)
      · have e : ((Syn.shift i ≐ var 0) :: lt (Syn.shift i) (succ (var 0)) ::
            (lt (Syn.shift i) (var 0) ⟶ dvd (inst2 (mS mB) (Syn.shift i) (Syn.shift y))
              (Lc mB (var 0) (Syn.shift y))) :: Γ.map Fm.shift) ⊢[PRAAx]
            inst2 (mS mB) (Syn.shift i) (Syn.shift y) ≐ inst2 (mS mB) (var 0) (Syn.shift y) :=
          congrInst2 (mS mB) Prf.hyp0 (.eqRefl _)
        exact dvd_congr (Lc_succ mB _ _).eqSymm
          (dvd_trans' (m_pos mB _ _) (m_pos mB _ _) (dvd_of_eq' (m_pos mB _ _) (w := one)
            ((mul_one_r _).eqSymm.eqTrans (congrMul e.eqSymm (.eqRefl _))))
            (dvd_lcm_right (Lc_pos mB _ _) (m_pos mB _ _)))
  have h2 := Prf.allE K hall
  simp only [Fm.subst_imp, subst_lt, subst_dvd, Fm.subst_eq, subst_ap2, subst_inst2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 hi

/-- **Congruence modulo every `m_i`, `i < K`, gives congruence modulo `Lc K`.** -/
theorem Lc_cong {x z K y : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift K) ⟶
      (rem (Syn.shift x) (inst2 (mS mB) (var 0) (Syn.shift y)) ≐
        rem (Syn.shift z) (inst2 (mS mB) (var 0) (Syn.shift y))))) :
    Γ ⊢[PRAAx] rem x (Lc mB K y) ≐ rem z (Lc mB K y) := by
  let P : Fm PTm (n + 1) :=
    rem (Syn.shift x) (Lc mB (var 0) (Syn.shift y)) ≐ rem (Syn.shift z) (Lc mB (var 0) (Syn.shift y))
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst K) := by
    refine qfIndUpTo K trivial ?_ ?_
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have L0 := Lc_zero (Γ := Γ) mB y
      exact (congrAp2 remF (.eqRefl _) L0).eqTrans ((AnalyticNumberTheory.Euler.rem_one _).eqTrans
        ((AnalyticNumberTheory.Euler.rem_one _).eqSymm.eqTrans (congrAp2 remF (.eqRefl _) L0.eqSymm)))
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let C := lt (var 0) (Syn.shift K) :: P :: Γ.map Fm.shift
      have hk := Prf.impE (h.allOpen.wk.wk : C ⊢[PRAAx] _) Prf.hyp0
      have e := Lc_succ (Γ := C) mB (var 0) (Syn.shift y)
      exact (congrAp2 remF (.eqRefl _) e).eqTrans
        ((lcm_cong (Lc_pos mB _ _) (m_pos mB _ _) (Prf.hyp1 : C ⊢[PRAAx] P) hk).eqTrans
          (congrAp2 remF (.eqRefl _) e.eqSymm))
  simpa [P] using atBound

end Family

end LeanProofs.IPRA.Foundations.CrtLcm

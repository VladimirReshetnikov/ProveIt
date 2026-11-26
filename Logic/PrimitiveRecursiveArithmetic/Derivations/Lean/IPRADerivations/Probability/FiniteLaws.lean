import IPRADerivations.Probability.ExpectationCorollaries

/-!
# Conditional cells, Bernoulli, balance point and finite Fatou

Packet: `probability/expected_value_ipra_2026-11-16` (cross-multiplied finite kernel):

* `cell_zero`, `cell_char` (`thm:cell-characterization`): for a partition map `c` and a cell `j`, with
  `M_j = ∑ w_i [c(i) = j]` and `S_j = ∑ w_i X_i [c(i) = j]`, a zero mass forces `S_j = 0`, so the cell
  value `h_j = S_j/D_j` with the positive denominator `D_j = M_j + [M_j = 0]` satisfies
  `h_j M_j = S_j`, i.e. `S_j M_j = S_j D_j`;
* `bernoulli` (`prop:bernoulli`): on two outcomes with the indicator of outcome `1`,
  `Ew(X) = w_1` and `W = w_0 + w_1`, i.e. `E[X] = p`;
* `center_mass` (`thm:center-mass`): for `c = p/q`, the torque `∑ m_i (q x_i) = ∑ m_i p` vanishes
  exactly when `q S = p M`, i.e. `c = S/M`;
* a running minimum `m(K) = min_{t ≤ K} Y(t)` (`mn_le`), and `fatou` (`lem:finite-fatou`):
  `E[min_{N ≤ n ≤ N+L} X_n] ≤ E[X_n]` for every `n` in the range.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.FiniteLaws

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul')
open LeanProofs.IPRA.Probability.ExpectationCorollaries (zml cst exp_scale exp_const)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias congrEqb' := Common.congrEqb

/-- `f(i, snd z)`. -/
abbrev sb (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_sb (f : PTm 2) (i z : PTm n) : Syn.subst ![i, z] (sb f) = inst2 f i (sndT z) := by
  simp only [inst2, sb, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-! ## Conditional cells -/

section Cells

variable (w X c : PTm 2)

/-- `w_i [c(i) = j]`, over `0 = i`, `1 = ⟨j, x⟩`. -/
abbrev mB : PTm 2 := sb w * eqb (sb c) (fstT (var 1))
/-- `w_i X_i [c(i) = j]`. -/
abbrev sB : PTm 2 := sb w * (sb X * eqb (sb c) (fstT (var 1)))

theorem mB_at (i j x : PTm n) : Γ ⊢[PRAAx] inst2 (mB w c) i (pairT j x) ≐ inst2 w i x * eqb (inst2 c i x) j := by
  have e : inst2 (mB w c) i (pairT j x) = inst2 w i (sndT (pairT j x)) *
      eqb (inst2 c i (sndT (pairT j x))) (fstT (pairT j x)) := by
    simp only [inst2, mB, PTm.subst_mul, subst_eqb, inst2_sb, subst_fstT]; simp
  rw [e]
  exact congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _)) (congrEqb' (congrInst2 c (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))

theorem sB_at (i j x : PTm n) : Γ ⊢[PRAAx] inst2 (sB w X c) i (pairT j x) ≐
    inst2 w i x * (inst2 X i x * eqb (inst2 c i x) j) := by
  have e : inst2 (sB w X c) i (pairT j x) = inst2 w i (sndT (pairT j x)) *
      (inst2 X i (sndT (pairT j x)) * eqb (inst2 c i (sndT (pairT j x))) (fstT (pairT j x))) := by
    simp only [inst2, sB, PTm.subst_mul, subst_eqb, inst2_sb, subst_fstT]; simp
  rw [e]
  exact congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _)) (congrMul (congrInst2 X (.eqRefl _) (snd_pair _ _))
    (congrEqb' (congrInst2 c (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)))

/-- A cell of zero mass has zero weighted sum. -/
theorem cell_zero {N j x : PTm n} (h : Γ ⊢[PRAAx] ap2 (sumF (mB w c)) N (pairT j x) ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (sB w X c)) N (pairT j x) ≐ zero := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF (mB w c)) (Syn.shift N) (pairT (Syn.shift j) (Syn.shift x)) ≐ zero := by
    have e := h.shift
    simp only [Fm.shift, Fm.subst_eq] at e
    simpa [Syn.shift] using e
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  let D : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hz : D ⊢[PRAAx] inst2 (mB w c) (var 0) (pairT (Syn.shift j) (Syn.shift x)) ≐ zero :=
    sum_zero_elim (mB w c) h'.wk Prf.hyp0
  have m0 := (mB_at (Γ := D) w c _ _ _).eqSymm.eqTrans hz
  refine (sB_at w X c _ _ _).eqTrans ?_
  refine .orE (zero_or_zero_of_mul m0) (zml Prf.hyp0 _) ?_
  exact (congrMul (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))).eqTrans (mul_zero _)

/-- `thm:cell-characterization`: with `D_j = M_j + [M_j = 0] ≥ 1` and `h_j = S_j / D_j`,
`h_j M_j = S_j`, i.e. `S_j M_j = S_j D_j`. -/
theorem cell_char (N j x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (sB w X c)) N (pairT j x) * ap2 (sumF (mB w c)) N (pairT j x) ≐
      ap2 (sumF (sB w X c)) N (pairT j x) *
        (ap2 (sumF (mB w c)) N (pairT j x) + eqb (ap2 (sumF (mB w c)) N (pairT j x)) zero) := by
  refine .orE (zero_or_succ (ap2 (sumF (mB w c)) N (pairT j x))) ?_ ?_
  · have s0 := cell_zero w X c (Prf.hyp0 : ((ap2 (sumF (mB w c)) N (pairT j x) ≐ zero) :: Γ) ⊢[PRAAx] _)
    exact (zml s0 _).eqTrans (zml s0 _).eqSymm
  · have ne : ((ap2 (sumF (mB w c)) N (pairT j x) ≐ succ (pred (ap2 (sumF (mB w c)) N (pairT j x)))) :: Γ) ⊢[PRAAx]
        neg (ap2 (sumF (mB w c)) N (pairT j x) ≐ zero) :=
      .impI (succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))
    exact congrMul (.eqRefl _) ((congrAdd (.eqRefl _) (eqb_of_ne ne)).eqTrans (add_zero _)).eqSymm

end Cells

/-! ## Bernoulli and the balance point -/

theorem inst2_ind1 (i x : PTm n) : inst2 (eqb (var 0) one : PTm 2) i x = eqb i one := by simp [inst2]

/-- `prop:bernoulli`: on outcomes `0, 1` with `X = [i = 1]`, `Ew(X) = w_1` and `W = w_0 + w_1`. -/
theorem bernoulli (w : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] (Ew w (eqb (var 0) one) two x ≐ inst2 w one x) ⋏ (Wt w two x ≐ inst2 w zero x + inst2 w one x) := by
  have e0 : Γ ⊢[PRAAx] eqb (zero : PTm n) one ≐ zero := eqb_of_ne (.impI (succ_ne_zero' _ Prf.hyp0.eqSymm))
  have e1 : Γ ⊢[PRAAx] eqb (one : PTm n) one ≐ one := eqb_of_eq (.eqRefl _)
  have t0 : Γ ⊢[PRAAx] inst2 (w * eqb (var 0) one) zero x ≐ zero := by
    rw [inst2_mul', inst2_ind1]; exact (congrMul (.eqRefl _) e0).eqTrans (mul_zero _)
  have t1 : Γ ⊢[PRAAx] inst2 (w * eqb (var 0) one) one x ≐ inst2 w one x := by
    rw [inst2_mul', inst2_ind1]; exact (congrMul (.eqRefl _) e1).eqTrans (Expectation.mul_one' _)
  have a := natEq t0; have b := natEq t1
  refine .andI ?_ ?_
  · ipra_lc natEq (sum_succ' (Γ := Γ) (w * eqb (var 0) one) one x) +
      natEq (sum_succ' (Γ := Γ) (w * eqb (var 0) one) zero x) + natEq (sum_zero (Γ := Γ) (w * eqb (var 0) one) x) +
      a + b
  · ipra_lc natEq (sum_succ' (Γ := Γ) w one x) + natEq (sum_succ' (Γ := Γ) w zero x) + natEq (sum_zero (Γ := Γ) w x)

/-- `thm:center-mass`: for `c = p/q`, the cleared torque `∑ m_i (q x_i) − ∑ m_i p` vanishes exactly when
`q S = p M`. -/
theorem center_mass (p q : PTm 1) (m X : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ((Ew m (cst q * X) N x ≐ Ew m (cst p) N x) ⟶
        (Syn.subst ![x] q * Ew m X N x ≐ Syn.subst ![x] p * Wt m N x)) ⋏
      ((Syn.subst ![x] q * Ew m X N x ≐ Syn.subst ![x] p * Wt m N x) ⟶
        (Ew m (cst q * X) N x ≐ Ew m (cst p) N x)) := by
  have a := exp_scale (Γ := Γ) q m X N x
  have b := exp_const (Γ := Γ) p m N x
  exact .andI (.impI (a.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans b.wk)))
    (.impI (a.wk.eqTrans (Prf.hyp0.eqTrans b.wk.eqSymm)))

/-! ## Finite Fatou -/

theorem min_le_left (a b : PTm n) : Γ ⊢[PRAAx] le (monus a (monus a b)) a := by
  refine .orE (le_total a (monus a b)) (le_zero_of' Prf.hyp0) ?_
  exact le_of_eq_add (d := monus a b) ((eq_add_of_le Prf.hyp0).eqTrans (add_comm _ _))
where
  le_zero_of' {Δ : List (Fm PTm n)} {u v : PTm n} (h : Δ ⊢[PRAAx] le u v) : Δ ⊢[PRAAx] le (monus u v) u :=
    le_congr h.eqSymm (.eqRefl _) (zero_le _)

theorem min_le_right (a b : PTm n) : Γ ⊢[PRAAx] le (monus a (monus a b)) b := by
  refine .orE (le_total a b) ?_ ?_
  · exact le_congr ((monus_zero _).eqSymm.eqTrans (congrMonus (.eqRefl _) Prf.hyp0.eqSymm)) (.eqRefl _) Prf.hyp0
  · have e : (le b a :: Γ) ⊢[PRAAx] monus a (monus a b) ≐ b :=
      (congrMonus (eq_add_of_le Prf.hyp0) (.eqRefl _)).eqTrans (add_monus _ _)
    exact le_congr e.eqSymm (.eqRefl _) (le_refl _)

section Fatou

variable (Y : PTm 2)

/-- The running-minimum step, over `0 = k`, `1 = m(k)`, `2 = x`. -/
def mnStep : PTm 3 := monus (var 1) (monus (var 1) (Syn.subst ![succ (var 0), var 2] Y))
abbrev mnF : PR 2 := rec2 (Syn.subst ![zero, var 0] Y) (mnStep Y)
/-- `m(K, x) = min_{t ≤ K} Y(t, x)`. -/
abbrev Mn (K x : PTm n) : PTm n := ap2 (mnF Y) K x

theorem mn_zero (x : PTm n) : Γ ⊢[PRAAx] Mn Y zero x ≐ inst2 Y zero x := by
  have h := rec2_zero (Γ := Γ) (Syn.subst ![zero, var 0] Y) (mnStep Y) x
  have e : Syn.subst ![x] (Syn.subst ![zero, var 0] Y) = inst2 Y zero x := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e] at h; exact h

theorem mn_succ (k x : PTm n) :
    Γ ⊢[PRAAx] Mn Y (succ k) x ≐ monus (Mn Y k x) (monus (Mn Y k x) (inst2 Y (succ k) x)) := by
  have h := rec2_succ (Γ := Γ) (Syn.subst ![zero, var 0] Y) (mnStep Y) k x
  have e1 : Syn.subst ![k, ap2 (mnF Y) k x, x] (Syn.subst ![succ (var 0), var 2] Y) = inst2 Y (succ k) x := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp
  have e : Syn.subst ![k, ap2 (mnF Y) k x, x] (mnStep Y) = monus (Mn Y k x) (monus (Mn Y k x) (inst2 Y (succ k) x)) := by
    simp only [mnStep, PTm.subst_monus, e1]; simp
  rw [e] at h; exact h

/-- Variables `0 = K`, `1 = t`, `2 = x`. -/
private abbrev mlF : Fm PTm 3 := le (var 1) (var 0) ⟶ le (Mn Y (var 0) (var 2)) (inst2 Y (var 1) (var 2))

private theorem ml₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] mlF Y := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [mlF, subst_le, subst_ap2, subst_inst2]
  · refine .impI ?_
    have t0 : (le (var 0) zero :: ([] : List (Fm PTm 2))) ⊢[PRAAx] var 0 ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
    exact le_congr (mn_zero Y _).eqSymm (congrInst2 Y t0.eqSymm (.eqRefl _)) (le_refl _)
  · refine .impI ?_
    refine le_congr (mn_succ Y _ _).eqSymm (.eqRefl _) ?_
    refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have h : (lt (var 1) (succ (var 0)) :: le (var 1) (succ (var 0)) :: [mlF Y]) ⊢[PRAAx] le (var 1 : PTm 3) (var 0) :=
        (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
      exact le_trans (min_le_left _ _) (.impE hyp2 h)
    · exact le_congr (.eqRefl _) (congrInst2 Y Prf.hyp0.eqSymm (.eqRefl _)) (min_le_right _ _)

/-- `min_{t ≤ K} Y(t) ≤ Y(t)` for `t ≤ K`. -/
theorem mn_le {K t x : PTm n} (h : Γ ⊢[PRAAx] le t K) : Γ ⊢[PRAAx] le (Mn Y K x) (inst2 Y t x) := by
  have i := inst (Γ := Γ) (ml₀ Y) (![K, t, x] : Fin 3 → PTm n)
  simp only [mlF, Fm.subst_imp, subst_le, subst_ap2, subst_inst2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_zero] at i
  exact .impE i h

end Fatou

section Fatou2

variable (w : PTm 2) (X : PTm 3)

/-- `X(N + t, i, x)`, over `0 = t`, `1 = ⟨i, ⟨N, x⟩⟩`. -/
abbrev YB : PTm 2 := Syn.subst ![fstT (sndT (var 1)) + var 0, fstT (var 1), sndT (sndT (var 1))] X
/-- `w(i, x) · min_{t ≤ L} X(N + t, i, x)`, over `0 = i`, `1 = ⟨L, ⟨N, x⟩⟩`. -/
abbrev wmB : PTm 2 := Syn.subst ![var 0, sndT (sndT (var 1))] w *
  ap2 (mnF (YB X)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))
/-- `w(i, x) X(n, i, x)`, over `0 = i`, `1 = ⟨n, x⟩`. -/
abbrev rB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] w * Syn.subst ![fstT (var 1), var 0, sndT (var 1)] X

theorem YB_at (t i N x : PTm n) : Γ ⊢[PRAAx] inst2 (YB X) t (pairT i (pairT N x)) ≐ inst3 X (N + t) i x := by
  have e : inst2 (YB X) t (pairT i (pairT N x)) = inst3 X (fstT (sndT (pairT i (pairT N x))) + t)
      (fstT (pairT i (pairT N x))) (sndT (sndT (pairT i (pairT N x)))) := by
    simp only [inst2, inst3, YB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]
  exact congrInst3 X (congrAdd (snd_pair _ _).fstE (.eqRefl _)) (fst_pair _ _)
    (snd_pair _ _).sndE

theorem wmB_at (i L N x : PTm n) : Γ ⊢[PRAAx] inst2 (wmB w X) i (pairT L (pairT N x)) ≐
    inst2 w i x * Mn (YB X) L (pairT i (pairT N x)) := by
  have e : inst2 (wmB w X) i (pairT L (pairT N x)) = inst2 w i (sndT (sndT (pairT L (pairT N x)))) *
      ap2 (mnF (YB X)) (fstT (pairT L (pairT N x))) (pairT i (sndT (pairT L (pairT N x)))) := by
    have hf : Syn.subst ![i, pairT L (pairT N x)] (Syn.subst ![var 0, sndT (sndT (var 1))] w) =
        inst2 w i (sndT (sndT (pairT L (pairT N x)))) := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
    simp only [inst2, wmB, PTm.subst_mul, hf]; simp
  rw [e]
  exact congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _).sndE)
    (congrAp2 (mnF (YB X)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _)))

theorem rB_at (i m x : PTm n) : Γ ⊢[PRAAx] inst2 (rB w X) i (pairT m x) ≐ inst2 w i x * inst3 X m i x := by
  have e : inst2 (rB w X) i (pairT m x) = inst2 w i (sndT (pairT m x)) * inst3 X (fstT (pairT m x)) i (sndT (pairT m x)) := by
    have hf : Syn.subst ![i, pairT m x] (Syn.subst ![var 0, sndT (var 1)] w) = inst2 w i (sndT (pairT m x)) := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
    have hg : Syn.subst ![i, pairT m x] (Syn.subst ![fstT (var 1), var 0, sndT (var 1)] X) =
        inst3 X (fstT (pairT m x)) i (sndT (pairT m x)) := by
      simp only [inst3, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
    simp only [inst2, rB, PTm.subst_mul] at hf hg ⊢
    rw [hf, hg]
  rw [e]
  exact congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _)) (congrInst3 X (fst_pair _ _) (.eqRefl _) (snd_pair _ _))

/-- `lem:finite-fatou`: `E[min_{N ≤ n ≤ N+L} X_n] ≤ E[X_{N+t}]` for every `t ≤ L`. -/
theorem fatou {M L N t x : PTm n} (ht : Γ ⊢[PRAAx] le t L) :
    Γ ⊢[PRAAx] le (ap2 (sumF (wmB w X)) M (pairT L (pairT N x))) (ap2 (sumF (rB w X)) M (pairT (N + t) x)) := by
  have ht' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift L) := by
    have e := ht.shift
    simp only [Fm.shift, subst_le] at e
    simpa [Syn.shift] using e
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, shift_pairT, show Syn.shift (N + t) = Syn.shift N + Syn.shift t by simp [Syn.shift]]
  refine le_congr (wmB_at w X _ _ _ _).eqSymm (rB_at w X _ _ _).eqSymm ?_
  exact le_mul_mono (le_refl _) (le_congr (.eqRefl _) (YB_at X _ _ _ _) (mn_le (YB X) ht'.wk))

end Fatou2

end LeanProofs.IPRA.Probability.FiniteLaws

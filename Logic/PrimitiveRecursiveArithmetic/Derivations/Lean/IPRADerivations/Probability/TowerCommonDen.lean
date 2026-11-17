import IPRADerivations.Probability.FiniteLaws
import IPRADerivations.Probability.ProductReplacement

/-!
# Common denominators and the tower property

Packet: `probability/expected_value_ipra_2026-11-16`.

* `dvd_prod_term`: every factor of a product of positive factors divides it (reusable);
* `common_den` (`lem:common-den`): for rationals `a_i / b_i` (`b_i ≥ 1`) the common denominator
  `D = ∏_{i<m} b_i` and numerators `a_i (D / b_i)` present the same rationals:
  `a_i (D / b_i) · b_i = a_i D`;
* `regroup` (`thm:tower`): if `d` refines `c = q ∘ d` (with `d(i) < s`), the fine cell sums
  `S^d_j = ∑_i w_i X_i [d(i) = j]` regroup into the coarse ones:
  `∑_{j<s} [q(j) = k] S^d_j = S^c_k`. With the cell characterization `h_j M_j = S_j`
  (`FiniteLaws.cell_char`) the `c`-conditional numerator of `E[X | d]` on cell `k` is
  `∑_{q(j)=k} h_j M_j = S^c_k`, i.e. `E[E[X | d] | c] = E[X | c]` on positive-mass cells.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.TowerCommonDen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.FiniteLaws (sb sB sB_at congrEqb')
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_mul')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Common denominators -/

theorem shift_inst2'' (g : PTm 2) (a b : PTm n) : Syn.shift (inst2 g a b) = inst2 g (Syn.shift a) (Syn.shift b) := by
  simp only [inst2, Syn.shift, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem subst_dvd' {m : ℕ} (σ : Fin n → PTm m) (d y : PTm n) :
    (dvd d y).subst σ = dvd (Syn.subst σ d) (Syn.subst σ y) := by
  simp [dvd]

/-- Every factor of a product of positive factors divides it: `b_i ∣ ∏_{j<M} b_j` for `i < M`, when
`b(j, x) ≥ 1` for every `j` (an open hypothesis in the fresh variable). -/
theorem dvd_prod_term (b : PTm 2) {M i x : PTm n}
    (hb : Γ.map Fm.shift ⊢[PRAAx] inst2 b (var 0) (Syn.shift x) ≐ succ (pred (inst2 b (var 0) (Syn.shift x))))
    (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx] dvd (inst2 b i x) (ap2 (prodF b) M x) := by
  have pos_at : ∀ (t : PTm n), Γ ⊢[PRAAx] inst2 b t x ≐ succ (pred (inst2 b t x)) := fun t => by
    have e := Prf.allE t (Prf.allI hb)
    simp only [Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_succ, PTm.subst_pred] at e
    exact e
  have hall : Γ ⊢[PRAAx] Fm.all (lt (Syn.shift i) (var 0) ⟶
      dvd (inst2 b (Syn.shift i) (Syn.shift x)) (ap2 (prodF b) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_lt, subst_dvd', subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [Fm.subst_imp, subst_lt, subst_dvd', subst_ap2, subst_inst2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := (lt (Syn.shift i) (var 0) ⟶
        dvd (inst2 b (Syn.shift i) (Syn.shift x)) (ap2 (prodF b) (var 0) (Syn.shift x))) :: Γ.map Fm.shift
      refine .impI ?_
      let C : List (Fm PTm (n + 1)) := lt (Syn.shift i) (succ (var 0)) :: D
      have bv : C ⊢[PRAAx] inst2 b (var 0) (Syn.shift x) ≐ succ (pred (inst2 b (var 0) (Syn.shift x))) := hb.wk.wk
      have hi' : Γ.map Fm.shift ⊢[PRAAx] inst2 b (Syn.shift i) (Syn.shift x) ≐ succ (pred (inst2 b (Syn.shift i) (Syn.shift x))) := by
        have e := (pos_at i).shift
        simp only [Fm.shift, Fm.subst_eq] at e
        simpa [Syn.shift, shift_inst2''] using e
      have ps := Probability.ProductReplacement.prod_succ' (Γ := C) b (var 0) (Syn.shift x)
      refine (congrAp2 remF ps (.eqRefl _)).eqTrans ?_
      refine .orE (lt_succ_cases Prf.hyp0) ?_ ?_
      · exact dvd_mul' hi'.wk.wk.wk _ (Prf.impE (Prf.hyp0 : D ⊢[PRAAx] _).wk.wk Prf.hyp0)
      · have e : ((Syn.shift i ≐ var 0) :: C) ⊢[PRAAx] inst2 b (Syn.shift i) (Syn.shift x) ≐ inst2 b (var 0) (Syn.shift x) :=
          congrInst2 b Prf.hyp0 (.eqRefl _)
        refine dvd_congr_left e.eqSymm ?_
        exact dvd_of_eq' bv.wk (w := ap2 (prodF b) (var 0) (Syn.shift x)) (mul_comm _ _)
  have h := Prf.allE M hall
  simp only [Fm.subst_imp, subst_lt, subst_dvd', subst_ap2, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact .impE h hi

/-- `lem:common-den`: with `D = ∏_{j<m} b_j`, `a_i (D / b_i) · b_i = a_i D`, i.e. `a_i / b_i = a_i (D/b_i) / D`. -/
theorem common_den (a b : PTm 2) {M i x : PTm n}
    (hb : Γ.map Fm.shift ⊢[PRAAx] inst2 b (var 0) (Syn.shift x) ≐ succ (pred (inst2 b (var 0) (Syn.shift x))))
    (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] (inst2 a i x * quo (ap2 (prodF b) M x) (inst2 b i x)) * inst2 b i x ≐ inst2 a i x * ap2 (prodF b) M x := by
  have hp : Γ ⊢[PRAAx] inst2 b i x ≐ succ (pred (inst2 b i x)) := by
    have e := Prf.allE i (Prf.allI hb)
    simp only [Fm.subst_eq, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
      ConciseIPRA.PTm.subst_succ, PTm.subst_pred] at e
    exact e
  have e := natEq (eq_of_dvd' hp (dvd_prod_term b hb hi))
  apply deriveNat; ipra_simps
  linear_combination -(Groth.ι (IPRA.Q.mk Γ (inst2 a i x))) * e

/-! ## The tower property -/

section Tower

variable (w X d q : PTm 2)

/-- `q(d(i, x), x)`. -/
abbrev qd : PTm 2 := Syn.subst ![d, var 1] q

theorem inst2_qd (i x : PTm n) : inst2 (qd d q) i x = inst2 q (inst2 d i x) x := by
  simp only [inst2, qd, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- `[q(j, x) = k] w(i, x) X(i, x) [d(i, x) = j]`, over `0 = j`, `1 = i`, `2 = ⟨k, x⟩`. -/
abbrev tA : PTm 3 := eqb (Syn.subst ![var 0, sndT (var 2)] q) (fstT (var 2)) *
  (Syn.subst ![var 1, sndT (var 2)] w * (Syn.subst ![var 1, sndT (var 2)] X *
    eqb (Syn.subst ![var 1, sndT (var 2)] d) (var 0)))

theorem tA_at (j i k x : PTm n) : Γ ⊢[PRAAx] inst3 (tA w X d q) j i (pairT k x) ≐
    eqb (inst2 q j x) k * (inst2 w i x * (inst2 X i x * eqb (inst2 d i x) j)) := by
  have h0 : ∀ f : PTm 2, Syn.subst ![j, i, pairT k x] (Syn.subst ![var 0, sndT (var 2)] f) = inst2 f j (sndT (pairT k x)) := by
    intro f; simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have h1 : ∀ f : PTm 2, Syn.subst ![j, i, pairT k x] (Syn.subst ![var 1, sndT (var 2)] f) = inst2 f i (sndT (pairT k x)) := by
    intro f; simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have ee : inst3 (tA w X d q) j i (pairT k x) = eqb (inst2 q j (sndT (pairT k x))) (fstT (pairT k x)) *
      (inst2 w i (sndT (pairT k x)) * (inst2 X i (sndT (pairT k x)) * eqb (inst2 d i (sndT (pairT k x))) j)) := by
    simp only [inst3, tA, PTm.subst_mul, subst_eqb, h0, h1, subst_fstT]; simp
  rw [ee]
  have s := snd_pair (Γ := Γ) k x
  exact congrMul (congrEqb' (congrInst2 q (.eqRefl _) s) (fst_pair _ _))
    (congrMul (congrInst2 w (.eqRefl _) s) (congrMul (congrInst2 X (.eqRefl _) s)
      (congrEqb' (congrInst2 d (.eqRefl _) s) (.eqRefl _))))

/-- A row: `∑_{i<N} tA(j, i) = [q(j) = k] S^d_j`. -/
theorem row_t (j N k x : PTm n) : Γ ⊢[PRAAx] inst2 (oB (tA w X d q)) j (pairT N (pairT k x)) ≐
    eqb (inst2 q j x) k * ap2 (sumF (sB w X d)) N (pairT j x) := by
  rw [inst2_oB]
  refine (congrAp2 (sumF (rowB (tA w X d q))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  have hc : Syn.shift (eqb (inst2 q j x) k) = eqb (Syn.shift (inst2 q j x)) (Syn.shift k) := by simp [Syn.shift]
  rw [inst2_rowB, hc, shift_inst2'']
  simp only [shift_pairT]
  refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ((tA_at w X d q _ _ _ _).eqTrans ?_)
  exact congrMul (.eqRefl _) (sB_at w X d _ _ _).eqSymm

/-- `[q(c) = k]`, over `0 = c`, `1 = ⟨k, x⟩`. -/
abbrev gB : PTm 2 := eqb (Syn.subst ![var 0, sndT (var 1)] q) (fstT (var 1))

theorem gB_at (c k x : PTm n) : Γ ⊢[PRAAx] inst2 (gB q) c (pairT k x) ≐ eqb (inst2 q c x) k := by
  have e : inst2 (gB q) c (pairT k x) = eqb (inst2 q c (sndT (pairT k x))) (fstT (pairT k x)) := by
    have hf : Syn.subst ![c, pairT k x] (Syn.subst ![var 0, sndT (var 1)] q) = inst2 q c (sndT (pairT k x)) := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext m; fin_cases m <;> simp
    simp only [inst2, gB, subst_eqb, hf, subst_fstT]; simp
  rw [e]; exact congrEqb' (congrInst2 q (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)

/-- A column: `∑_{j<s} tA(j, i) = w_i X_i [q(d(i)) = k]` when `d(i) < s`. -/
theorem col_t {i s k x : PTm n} (hd : Γ ⊢[PRAAx] lt (inst2 d i x) s) :
    Γ ⊢[PRAAx] inst2 (pB (tA w X d q)) i (pairT s (pairT k x)) ≐
      (inst2 w i x * inst2 X i x) * eqb (inst2 q (inst2 d i x) x) k := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB (tA w X d q))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  refine (sum_scale (colB (tA w X d q)) (dB (gB q)) s (inst2 w i x * inst2 X i x)
    (pairT (inst2 d i x) (pairT k x)) (pairT i (pairT k x)) (.allI (.impI ?_))).eqTrans ?_
  · have hm : Syn.shift (inst2 w i x * inst2 X i x) = inst2 w (Syn.shift i) (Syn.shift x) * inst2 X (Syn.shift i) (Syn.shift x) := by
      rw [← shift_inst2'', ← shift_inst2'']; simp [Syn.shift]
    have hd' : Syn.shift (inst2 d i x) = inst2 d (Syn.shift i) (Syn.shift x) := shift_inst2'' d i x
    rw [inst2_colB, inst2_dB, hm]
    simp only [shift_pairT, hd']
    let C : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift s) :: Γ.map Fm.shift
    have r1 : C ⊢[PRAAx] inst3 (tA w X d q) (var 0) (fstT (pairT (Syn.shift i) (pairT (Syn.shift k) (Syn.shift x))))
        (sndT (pairT (Syn.shift i) (pairT (Syn.shift k) (Syn.shift x)))) ≐
        eqb (inst2 q (var 0) (Syn.shift x)) (Syn.shift k) * (inst2 w (Syn.shift i) (Syn.shift x) *
          (inst2 X (Syn.shift i) (Syn.shift x) * eqb (inst2 d (Syn.shift i) (Syn.shift x)) (var 0))) :=
      (congrInst3 (tA w X d q) (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans
        (tA_at w X d q (var 0) (Syn.shift i) (Syn.shift k) (Syn.shift x))
    have r2 : C ⊢[PRAAx] eqb (fstT (pairT (inst2 d (Syn.shift i) (Syn.shift x)) (pairT (Syn.shift k) (Syn.shift x)))) (var 0) *
        inst2 (gB q) (var 0) (sndT (pairT (inst2 d (Syn.shift i) (Syn.shift x)) (pairT (Syn.shift k) (Syn.shift x)))) ≐
        eqb (inst2 d (Syn.shift i) (Syn.shift x)) (var 0) * eqb (inst2 q (var 0) (Syn.shift x)) (Syn.shift k) :=
      congrMul (congrEqb' (fst_pair _ _) (.eqRefl _))
        ((congrInst2 (gB q) (.eqRefl _) (snd_pair _ _)).eqTrans (gB_at q _ _ _))
    refine r1.eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) r2).eqSymm)
    apply deriveNat; ipra_simps; ring
  · exact congrMul (.eqRefl _) ((sum_delta (gB q) hd).eqTrans (gB_at q _ _ _))

/-- `thm:tower`, regrouping: if `d(i) < s` for all `i`, then
`∑_{j<s} [q(j) = k] S^d_j = S^c_k` for the coarse partition `c = q ∘ d` (rows by `row_t`). -/
theorem regroup {N s k x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll d s x) :
    Γ ⊢[PRAAx] ap2 (sumF (oB (tA w X d q))) s (pairT N (pairT k x)) ≐
      ap2 (sumF (sB w X (qd d q))) N (pairT k x) := by
  refine (fubini (tA w X d q) s N (pairT k x)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  rw [shift_pairT, shift_pairT]
  have hd : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] lt (inst2 d (var 0) (Syn.shift x)) (Syn.shift s) :=
    hr.allOpen.wk
  refine (col_t w X d q hd).eqTrans (.eqTrans ?_ (sB_at w X (qd d q) _ _ _).eqSymm)
  rw [inst2_qd]
  apply deriveNat; ipra_simps; ring

end Tower

end LeanProofs.IPRA.Probability.TowerCommonDen

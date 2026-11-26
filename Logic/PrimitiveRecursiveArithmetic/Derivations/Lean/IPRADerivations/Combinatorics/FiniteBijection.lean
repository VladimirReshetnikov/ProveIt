import IPRADerivations.Probability.Lotus
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.Probability.MedianCounts

/-!
# The finite bijection principle

Packet: `catalan_numbers_ipra_2026-11-16`, `paper/01_foundations.tex`, Lemma `lem:finite-bijection`.
Two bounded predicates are given by bodies `P(z, x)` (`z < B`) and `Q(w, x)` (`w < D`), read as the
indicators `[P(z)] = sg P(z, x)` and `[Q(w)] = sg Q(w, x)`. Primitive recursive maps `F`, `G` with

  `P(z) → Q(F z) ∧ F z < D`,  `Q(w) → P(G w) ∧ G w < B`,  `P(z) → G(F z) = z`,  `Q(w) → F(G w) = w`

(bounded hypotheses `mapsAll`, `retAll'`) give `#P = #Q`, i.e.
`∑_{z<B} [P(z)] = ∑_{w<D} [Q(w)]` (`finite_bijection`).

The proof is the packet's: the double sum `∑_{z<B} ∑_{w<D} [P(z)] [F z = w]` is computed by rows
(`row_eval`: every `z` with `P(z)` has exactly one image below `D`) and by columns (`col_eval`:
every `w` with `Q(w)` has exactly one preimage, `G w`, and no other `w` has one), and the two orders
agree by `Core/Fubini`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FiniteBijection

open_ipra
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.Probability.MedianCounts (congrSg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shift_inst2' (f : PTm 2) (t p : PTm n) : Syn.shift (inst2 f t p) = inst2 f (Syn.shift t) (Syn.shift p) := by
  simp only [Syn.shift, inst2, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem shift_zero' : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]

theorem shift_one' : Syn.shift (one : PTm n) = one := by simp [Syn.shift]

theorem shift_sg (y : PTm n) : Syn.shift (sg y) = sg (Syn.shift y) := by simp [Syn.shift]

theorem shift_pairT' (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

/-! ## Bits -/

alias sg_bit := Common.sg_zero_or_one

theorem absurd_zero_one {φ : Fm PTm n} (h : Γ ⊢[PRAAx] zero ≐ one) : Γ ⊢[PRAAx] φ :=
  lt_irrefl zero φ (lt_congr (.eqRefl _) h.eqSymm (le_refl one))

/-! ## The hypotheses -/

section Hyp

variable (F G P Q : PTm 2)

/-- `∀ z < B. [P(z)] = 1 → [Q(F z)] = 1 ∧ F z < D`. -/
def mapsAll (B D x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift B) ⟶ ((sg (inst2 P (var 0) (Syn.shift x)) ≐ one) ⟶
    ((sg (inst2 Q (inst2 F (var 0) (Syn.shift x)) (Syn.shift x)) ≐ one) ⋏
      lt (inst2 F (var 0) (Syn.shift x)) (Syn.shift D))))

/-- `∀ z < B. [P(z)] = 1 → G(F z) = z`. -/
def retAll' (B x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift B) ⟶ ((sg (inst2 P (var 0) (Syn.shift x)) ≐ one) ⟶
    (inst2 G (inst2 F (var 0) (Syn.shift x)) (Syn.shift x) ≐ var 0)))

@[simp] theorem subst_mapsAll {m : ℕ} (σ : Fin n → PTm m) (B D x : PTm n) :
    (mapsAll F P Q B D x).subst σ = mapsAll F P Q (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ x) := by
  simp [mapsAll, subst_up_shift', Syn.up]

@[simp] theorem subst_retAll' {m : ℕ} (σ : Fin n → PTm m) (B x : PTm n) :
    (retAll' F G P B x).subst σ = retAll' F G P (Syn.subst σ B) (Syn.subst σ x) := by
  simp [retAll', subst_up_shift', Syn.up]

theorem shift_mapsAll {B D x : PTm n} (h : Γ ⊢[PRAAx] mapsAll F P Q B D x) :
    Γ.map Fm.shift ⊢[PRAAx] mapsAll F P Q (Syn.shift B) (Syn.shift D) (Syn.shift x) := by
  have e := h.shift
  simp only [Fm.shift, subst_mapsAll] at e
  exact e

theorem shift_retAll' {B x : PTm n} (h : Γ ⊢[PRAAx] retAll' F G P B x) :
    Γ.map Fm.shift ⊢[PRAAx] retAll' F G P (Syn.shift B) (Syn.shift x) := by
  have e := h.shift
  simp only [Fm.shift, subst_retAll'] at e
  exact e

theorem maps_at {B D x : PTm n} (h : Γ ⊢[PRAAx] mapsAll F P Q B D x) {i : PTm n} (hi : Γ ⊢[PRAAx] lt i B)
    (hp : Γ ⊢[PRAAx] sg (inst2 P i x) ≐ one) :
    Γ ⊢[PRAAx] (sg (inst2 Q (inst2 F i x) x) ≐ one) ⋏ lt (inst2 F i x) D := by
  have e := Prf.allE i h
  simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_shift, Syn.inst_succ, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact .impE (.impE (by simpa using e) hi) hp

theorem ret_at {B x : PTm n} (h : Γ ⊢[PRAAx] retAll' F G P B x) {i : PTm n} (hi : Γ ⊢[PRAAx] lt i B)
    (hp : Γ ⊢[PRAAx] sg (inst2 P i x) ≐ one) : Γ ⊢[PRAAx] inst2 G (inst2 F i x) x ≐ i := by
  have e := Prf.allE i h
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_shift, Syn.inst_succ, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact .impE (.impE (by simpa using e) hi) hp

end Hyp

/-! ## The double sum -/

section Count

variable (F G P Q : PTm 2)

/-- `[P(z)] · [F z = w]`, over `0 = z`, `1 = w`, `2 = x`. -/
def aB : PTm 3 := Syn.subst ![var 0, var 2] (sg P) * eqb (Syn.subst ![var 0, var 2] F) (var 1)

theorem inst3_aB (i j x : PTm n) : inst3 (aB F P) i j x = sg (inst2 P i x) * eqb (inst2 F i x) j := by
  have h1 : (fun k => Syn.subst ![i, j, x] ((![var 0, var 2] : Fin 2 → PTm 3) k)) = ![i, x] := by
    funext k; fin_cases k <;> rfl
  simp only [inst3, inst2, aB, PTm.subst_mul, subst_eqb, PTm.subst_monus, Syn.subst_subst,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rw [h1]
  simp

/-- `[F(fst y) = j]`, over `0 = j`, `1 = y = ⟨i, x⟩`. -/
def eB : PTm 2 := eqb (Syn.subst ![fstT (var 1), sndT (var 1)] F) (var 0)

theorem inst2_eB (j y : PTm n) : inst2 (eB F) j y = eqb (inst2 F (fstT y) (sndT y)) j := by
  simp only [inst2, eB, subst_eqb, Syn.subst_subst]
  congr 1; congr 1; funext k; fin_cases k <;> simp

/-- The row: `∑_{j<D} a(i, j) = [P(i)] · ∑_{j<D} [F i = j]`. -/
theorem row_factor (D i x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (aB F P))) D (pairT i x) ≐
      sg (inst2 P i x) * ap2 (sumF (eB F)) D (pairT i x) := by
  refine (sum_congr_bounded (rowB (aB F P)) (cmB (eB F)) (pairT i x) (pairT (sg (inst2 P i x)) (pairT i x)) D
    (.allI (.impI ?_))).eqTrans (sum_const_mul (eB F) D _ (pairT i x))
  rw [shift_pairT', shift_pairT', shift_pairT', shift_sg, shift_inst2', inst2_rowB, inst2_cmB, inst2_eB, inst3_aB]
  exact congrMul ((congrSg (congrInst2 P (fst_pair _ _) (snd_pair _ _))).eqTrans (fst_pair _ _).eqSymm)
    (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb
      ((congrInst2 F (fst_pair _ _) (snd_pair _ _)).eqTrans
        (congrInst2 F (snd_pair _ _).fstE ((congrSnd (snd_pair _ _)).eqTrans
          (snd_pair _ _))).eqSymm) (.eqRefl _))

/-- `∑_{j<D} [c = j] = 1` for `c < D`, with `c = F i`. -/
theorem delta_F {D i x : PTm n} (h : Γ ⊢[PRAAx] lt (inst2 F i x) D) :
    Γ ⊢[PRAAx] ap2 (sumF (eB F)) D (pairT i x) ≐ one := by
  have sd := sum_delta (one : PTm 2) (x := x) h
  have e2 : inst2 (one : PTm 2) (inst2 F i x) x = one := by simp [inst2]
  rw [e2] at sd
  refine (sum_congr_bounded (eB F) (dB (one : PTm 2)) (pairT i x) (pairT (inst2 F i x) x) D
    (.allI (.impI ?_))).eqTrans sd
  rw [shift_pairT', shift_pairT', shift_inst2', inst2_eB, inst2_dB]
  have e1 : inst2 (one : PTm 2) (var 0 : PTm (n + 1))
      (sndT (pairT (inst2 F (Syn.shift i) (Syn.shift x)) (Syn.shift x))) = one := by simp [inst2]
  rw [e1]
  exact (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb (congrInst2 F (fst_pair _ _) (snd_pair _ _))
    (.eqRefl _)).eqTrans ((LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb (fst_pair _ _).eqSymm
      (.eqRefl _)).eqTrans ((one_mul _).eqSymm.eqTrans (mul_comm _ _)))

/-- Rows: `∑_{j<D} a(i, j) = [P(i)]` for `i < B`. -/
theorem row_eval {B D x i : PTm n} (hF : Γ ⊢[PRAAx] mapsAll F P Q B D x) (hi : Γ ⊢[PRAAx] lt i B) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (aB F P))) D (pairT i x) ≐ sg (inst2 P i x) := by
  refine (row_factor F P D i x).eqTrans (.orE (sg_bit (inst2 P i x)) ?_ ?_)
  · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans ((zero_mul _).eqTrans Prf.hyp0.eqSymm)
  · have d := delta_F F (Prf.andE₂ (maps_at F P Q hF.wk hi.wk Prf.hyp0))
    exact (congrMul Prf.hyp0 d).eqTrans ((one_mul one).eqTrans Prf.hyp0.eqSymm)

end Count

/-! ## Columns -/

section Cols

variable (F G P Q : PTm 2)

theorem shift_eq {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ.map Fm.shift ⊢[PRAAx] Syn.shift a ≐ Syn.shift b := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq] at e
  exact e

theorem eqbF_zero_lt {i j x : PTm n} (r : Γ ⊢[PRAAx] inst2 G (inst2 F i x) x ≐ i)
    (h : Γ ⊢[PRAAx] lt i (inst2 G j x)) : Γ ⊢[PRAAx] eqb (inst2 F i x) j ≐ zero := by
  refine .orE (lt_or_le (inst2 F i x) j) (eqb_zero_of_lt Prf.hyp0)
    (.orE (lt_or_eq_of_le Prf.hyp0) (eqb_zero_of_gt Prf.hyp0) ?_)
  exact lt_irrefl i _ (lt_congr (.eqRefl _) ((congrInst2 G Prf.hyp0 (.eqRefl x)).eqTrans r.wk.wk) h.wk.wk)

theorem eqbF_zero_gt {i j x : PTm n} (r : Γ ⊢[PRAAx] inst2 G (inst2 F i x) x ≐ i)
    (h : Γ ⊢[PRAAx] lt (inst2 G j x) i) : Γ ⊢[PRAAx] eqb (inst2 F i x) j ≐ zero := by
  refine .orE (lt_or_le (inst2 F i x) j) (eqb_zero_of_lt Prf.hyp0)
    (.orE (lt_or_eq_of_le Prf.hyp0) (eqb_zero_of_gt Prf.hyp0) ?_)
  exact lt_irrefl i _ (lt_congr ((congrInst2 G Prf.hyp0 (.eqRefl x)).eqTrans r.wk.wk) (.eqRefl _) h.wk.wk)

theorem lhs_zero_lt {B i j x : PTm n} (hGF : Γ ⊢[PRAAx] retAll' F G P B x) (hi : Γ ⊢[PRAAx] lt i B)
    (h : Γ ⊢[PRAAx] lt i (inst2 G j x)) : Γ ⊢[PRAAx] sg (inst2 P i x) * eqb (inst2 F i x) j ≐ zero := by
  refine .orE (sg_bit (inst2 P i x)) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) ?_
  exact (congrMul (.eqRefl _) (eqbF_zero_lt F G (ret_at F G P hGF.wk hi.wk Prf.hyp0) h.wk)).eqTrans (mul_zero _)

theorem lhs_zero_gt {B i j x : PTm n} (hGF : Γ ⊢[PRAAx] retAll' F G P B x) (hi : Γ ⊢[PRAAx] lt i B)
    (h : Γ ⊢[PRAAx] lt (inst2 G j x) i) : Γ ⊢[PRAAx] sg (inst2 P i x) * eqb (inst2 F i x) j ≐ zero := by
  refine .orE (sg_bit (inst2 P i x)) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) ?_
  exact (congrMul (.eqRefl _) (eqbF_zero_gt F G (ret_at F G P hGF.wk hi.wk Prf.hyp0) h.wk)).eqTrans (mul_zero _)

/-- The column term when `Q(j)` holds: `[P(i)] [F i = j] = [G j = i]`. -/
theorem col_pt {B i j x : PTm n} (hGF : Γ ⊢[PRAAx] retAll' F G P B x) (hi : Γ ⊢[PRAAx] lt i B)
    (hPG : Γ ⊢[PRAAx] sg (inst2 P (inst2 G j x) x) ≐ one) (hFG : Γ ⊢[PRAAx] inst2 F (inst2 G j x) x ≐ j) :
    Γ ⊢[PRAAx] sg (inst2 P i x) * eqb (inst2 F i x) j ≐ eqb (inst2 G j x) i * one := by
  refine .orE (lt_or_le i (inst2 G j x)) ?_ (.orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_)
  · exact (lhs_zero_lt F G P hGF.wk hi.wk Prf.hyp0).eqTrans
      ((congrMul (eqb_zero_of_gt Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · exact (lhs_zero_gt F G P hGF.wk.wk hi.wk.wk Prf.hyp0).eqTrans
      ((congrMul (eqb_zero_of_lt Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · have e : ((inst2 G j x ≐ i) :: le (inst2 G j x) i :: Γ) ⊢[PRAAx] inst2 G j x ≐ i := Prf.hyp0
    have p1 : ((inst2 G j x ≐ i) :: le (inst2 G j x) i :: Γ) ⊢[PRAAx] sg (inst2 P i x) ≐ one :=
      (congrSg (congrInst2 P e.eqSymm (.eqRefl x))).eqTrans hPG.wk.wk
    have f1 : ((inst2 G j x ≐ i) :: le (inst2 G j x) i :: Γ) ⊢[PRAAx] eqb (inst2 F i x) j ≐ one :=
      eqb_of_eq ((congrInst2 F e.eqSymm (.eqRefl x)).eqTrans hFG.wk.wk)
    exact (congrMul p1 f1).eqTrans ((congrMul (eqb_of_eq e) (.eqRefl _)).eqSymm)

/-- The column term when `Q(j)` fails: `[P(i)] [F i = j] = 0`. -/
theorem col_zero {B D i j x : PTm n} (hF : Γ ⊢[PRAAx] mapsAll F P Q B D x) (hi : Γ ⊢[PRAAx] lt i B)
    (hq : Γ ⊢[PRAAx] sg (inst2 Q j x) ≐ zero) : Γ ⊢[PRAAx] sg (inst2 P i x) * eqb (inst2 F i x) j ≐ zero := by
  refine .orE (sg_bit (inst2 P i x)) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) ?_
  have qF := Prf.andE₁ (maps_at F P Q hF.wk hi.wk Prf.hyp0)
  refine (congrMul (.eqRefl _) ?_).eqTrans (mul_zero _)
  refine .orE (lt_or_le (inst2 F i x) j) (eqb_zero_of_lt Prf.hyp0)
    (.orE (lt_or_eq_of_le Prf.hyp0) (eqb_zero_of_gt Prf.hyp0) ?_)
  exact absurd_zero_one (hq.wk.wk.wk.eqSymm.eqTrans ((congrSg (congrInst2 Q Prf.hyp0 (.eqRefl x))).eqTrans qF.wk.wk))

/-- Columns: `∑_{i<B} a(i, j) = [Q(j)]` for `j < D`. -/
theorem col_eval {B D x j : PTm n} (hF : Γ ⊢[PRAAx] mapsAll F P Q B D x) (hG : Γ ⊢[PRAAx] mapsAll G Q P D B x)
    (hGF : Γ ⊢[PRAAx] retAll' F G P B x) (hFG : Γ ⊢[PRAAx] retAll' G F Q D x) (hj : Γ ⊢[PRAAx] lt j D) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aB F P))) B (pairT j x) ≐ sg (inst2 Q j x) := by
  refine .orE (sg_bit (inst2 Q j x)) ?_ ?_
  · refine (sum_zero_of_bounded _ _ _ (.allI (.impI ?_))).eqTrans Prf.hyp0.eqSymm
    have hq := shift_eq (Prf.hyp0 (Γ := Γ) (φ := sg (inst2 Q j x) ≐ zero))
    rw [shift_sg, shift_inst2', shift_zero'] at hq
    rw [shift_pairT', inst2_colB, inst3_aB]
    refine (congrMul (congrSg (congrInst2 P (.eqRefl _) (snd_pair _ _)))
      (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb (congrInst2 F (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))).eqTrans ?_
    exact col_zero F P Q (shift_mapsAll F P Q hF.wk).wk Prf.hyp0 hq.wk
  · have m := maps_at G Q P hG.wk hj.wk Prf.hyp0
    have r := ret_at G F Q hFG.wk hj.wk Prf.hyp0
    have sd := sum_delta (one : PTm 2) (x := x) (Prf.andE₂ m)
    have e2 : inst2 (one : PTm 2) (inst2 G j x) x = one := by simp [inst2]
    rw [e2] at sd
    refine (sum_congr_bounded _ (dB (one : PTm 2)) _ (pairT (inst2 G j x) x) B (.allI (.impI ?_))).eqTrans
      (sd.eqTrans Prf.hyp0.eqSymm)
    have hp := shift_eq (Prf.andE₁ m); have hr := shift_eq r
    rw [shift_sg, shift_inst2', shift_inst2', shift_one'] at hp
    rw [shift_inst2', shift_inst2'] at hr
    rw [shift_pairT', shift_pairT', shift_inst2', inst2_colB, inst3_aB, inst2_dB]
    have e1 : inst2 (one : PTm 2) (var 0 : PTm (n + 1))
        (sndT (pairT (inst2 G (Syn.shift j) (Syn.shift x)) (Syn.shift x))) = one := by simp [inst2]
    rw [e1]
    refine (congrMul (congrSg (congrInst2 P (.eqRefl _) (snd_pair _ _)))
      (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb (congrInst2 F (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))).eqTrans
        ((col_pt F G P (shift_retAll' F G P hGF.wk).wk Prf.hyp0 hp.wk hr.wk).eqTrans ?_)
    exact congrMul (LeanProofs.IPRA.AnalyticNumberTheory.Euler.congrEqb (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)

end Cols

/-! ## The principle -/

theorem pB_at (a : PTm 3) (N M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB a) N (pairT M x) ≐ ap2 (sumF (colB a)) M (pairT N x) := by
  rw [inst2_pB]
  exact congrAp2 (sumF (colB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))

theorem inst2_sgB (P : PTm 2) (i x : PTm n) : inst2 (sg P) i x = sg (inst2 P i x) := by simp [inst2]

/-- `lem:finite-bijection`: `#{z < B : P(z)} = #{w < D : Q(w)}`. -/
theorem finite_bijection (F G P Q : PTm 2) {B D x : PTm n} (hF : Γ ⊢[PRAAx] mapsAll F P Q B D x)
    (hG : Γ ⊢[PRAAx] mapsAll G Q P D B x) (hGF : Γ ⊢[PRAAx] retAll' F G P B x) (hFG : Γ ⊢[PRAAx] retAll' G F Q D x) :
    Γ ⊢[PRAAx] ap2 (sumF (sg P)) B x ≐ ap2 (sumF (sg Q)) D x := by
  have left : Γ ⊢[PRAAx] ap2 (sumF (sg P)) B x ≐ ap2 (sumF (oB (aB F P))) B (pairT D x) := by
    refine sum_congr_bounded _ _ _ _ B (.allI (.impI ?_))
    rw [inst2_sgB, shift_pairT']
    exact (row_eval F P Q (shift_mapsAll F P Q hF).wk Prf.hyp0).eqSymm.eqTrans (oB_at _ _ _ _).eqSymm
  have right : Γ ⊢[PRAAx] ap2 (sumF (pB (aB F P))) D (pairT B x) ≐ ap2 (sumF (sg Q)) D x := by
    refine sum_congr_bounded _ _ _ _ D (.allI (.impI ?_))
    rw [inst2_sgB, shift_pairT']
    exact (pB_at _ _ _ _).eqTrans (col_eval F G P Q (shift_mapsAll F P Q hF).wk (shift_mapsAll G Q P hG).wk
      (shift_retAll' F G P hGF).wk (shift_retAll' G F Q hFG).wk Prf.hyp0)
  exact left.eqTrans ((fubini (aB F P) B D x).eqTrans right)

end LeanProofs.IPRA.Combinatorics.FiniteBijection

import ZFCinPA.LevelDerivation
import ZFCinPA.SetCongruence

/-!
# Bounded equality replacement for model-coded `ℒₛₑₜ` formulas

`SetCongruence.replace_aux` proves equality replacement for an internal
(possibly nonstandard) formula by a `𝚺₁` structural induction, but only as a
`Provable` statement: the internal derivation it yields has a code chosen by
`Classical.choose`. This module builds the derivation explicitly on the level
scale of `LevelDerivation`.

The generalized statement (`Cseq`): for a semiformula `χ` with `n` bound
variables and two closed substitution vectors `w₁`, `w₂` that agree
coordinatewise up to hypothesized equalities in a context `E` (`Paired`),
the sequent `¬χ[w₁], χ[w₂], E` is derivable. The induction measure is
Foundation's `formulaComplexity`, which shifts, substitutions and negations
preserve; this matters in the quantifier case, whose premise is about the
*shifted* body `shift p` (the formula may carry free variables). The
formula's code level `v` therefore stays fixed, while the level `c` of the
substituted variables and of `E` grows by one per quantifier.

Atoms are a parameter here (`AtomOK`); `SizedCongruenceAtoms` discharges it
from fixed `𝗭𝗙` theorems.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedCongruence

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation LeanProofs.BoundedPAConsistency.ShiftBound
open LeanProofs.BoundedPAConsistency.SubstBound
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Closed terms and the quantifier identity -/

theorem closed_fvar {t : V} (ht : IsSemiterm ℒₛₑₜ 0 t) : ∃ x, t = ^&x := by
  rcases term_var ht.isUTerm with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · simp at ht
  · exact ⟨x, rfl⟩

theorem closed_isVar {t : V} (ht : IsSemiterm ℒₛₑₜ 0 t) : IsVarTerm t := by
  obtain ⟨x, rfl⟩ := closed_fvar ht
  exact ⟨x, by simp [qqFvar, lt_succ_iff_le, le_pair_right], Or.inr rfl⟩

theorem termSubst_closed {w t : V} (ht : IsSemiterm ℒₛₑₜ 0 t) : termSubst ℒₛₑₜ w t = t := by
  obtain ⟨x, rfl⟩ := closed_fvar ht
  simp

theorem termSubst_closed_semiterm {n w t : V} (hw : IsSemitermVec ℒₛₑₜ n 0 w)
    (ht : IsSemiterm ℒₛₑₜ n t) : IsSemiterm ℒₛₑₜ 0 (termSubst ℒₛₑₜ w t) := by
  rcases term_var ht.isUTerm with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · rw [termSubst_bvar]
    exact hw.nth (by simpa using ht)
  · simp

/-- `^&0 ∷ shift w`, the substitution vector under one more binder. -/
def qFree (n w : V) : V := ^&0 ∷ termShiftVec ℒₛₑₜ n w

theorem qFree_semitermVec {n w : V} (hw : IsSemitermVec ℒₛₑₜ n 0 w) :
    IsSemitermVec ℒₛₑₜ (n + 1) 0 (qFree n w) :=
  hw.termShiftVec.adjoin (by simp)

theorem termSubstVec_qVec_free {n w : V} (hw : IsSemitermVec ℒₛₑₜ n 0 w) :
    termSubstVec ℒₛₑₜ (n + 1) (^&0 ∷ 0) (qVec ℒₛₑₜ w) = ^&0 ∷ w := by
  have hl : len w = n := hw.lh
  unfold qVec
  rw [hl, termSubstVec_cons (by simp) hw.termBShiftVec.isUTerm, termSubst_bvar, nth_adjoin_zero]
  congr 1
  apply nth_ext' n (by rw [len_termSubstVec hw.termBShiftVec.isUTerm]) hl
  intro i hi
  rw [nth_termSubstVec hw.termBShiftVec.isUTerm hi, nth_termBShiftVec hw.isUTerm hi,
    substs_cons_bShift (hw.nth hi), termSubst_closed (hw.nth hi)]

/-- Opening a substituted binder: `free (p[q w]) = (shift p)[&0 ∷ shift w]`. -/
theorem free_subst_qVec {n w p : V} (hp : IsSemiformula ℒₛₑₜ (n + 1) p)
    (hw : IsSemitermVec ℒₛₑₜ n 0 w) :
    free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w) p) = subst ℒₛₑₜ (qFree n w) (shift ℒₛₑₜ p) := by
  unfold free substs1 qFree
  rw [Bootstrapping.shift_substs hp hw.qVec, termShift_qVec hw,
    Bootstrapping.substs_substs hp.shift (by simp : IsSemitermVec ℒₛₑₜ 1 0 (^&0 ∷ 0 : V))
      (by simpa using hw.termShiftVec.qVec),
    termSubstVec_qVec_free hw.termShiftVec]

theorem free_neg {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) :
    free ℒₛₑₜ (neg ℒₛₑₜ p) = neg ℒₛₑₜ (free ℒₛₑₜ p) := by
  unfold free substs1
  rw [Bootstrapping.shift_neg hp,
    Bootstrapping.substs_neg hp.shift (by simp : IsSemitermVec ℒₛₑₜ 1 0 (^&0 ∷ 0 : V))]

theorem isFormula_free {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) : IsFormula ℒₛₑₜ (free ℒₛₑₜ p) := by
  unfold free substs1
  exact hp.shift.subst (by simp)

/-! ## Contexts -/

/-- The internal disequality atom `a ≠ b`. -/
def neR (a b : V) : V := ^nrel 2 (0 : V) (a ∷ b ∷ 0)

/-- `a` and `b` are the same term, or `E` hypothesizes `a = b` both ways. -/
def Pair1 (E a b : V) : Prop := a = b ∨ (neR a b ∈ E ∧ neR b a ∈ E)

def Paired (E n w₁ w₂ : V) : Prop := ∀ i < n, Pair1 E w₁.[i] w₂.[i]

/-- The replacement sequent `¬χ[w₁], χ[w₂], E`. -/
def Cseq (w₁ w₂ χ E : V) : V :=
  insert (neg ℒₛₑₜ (subst ℒₛₑₜ w₁ χ)) (insert (subst ℒₛₑₜ w₂ χ) E)

/-- The side conditions on the substitution vectors and the context. -/
def Inp (n w₁ w₂ E c : V) : Prop :=
  IsSemitermVec ℒₛₑₜ n 0 w₁ ∧ IsSemitermVec ℒₛₑₜ n 0 w₂ ∧ 1 ≤ c ∧
    (∀ i < n, w₁.[i] ≤ lvB c) ∧ (∀ i < n, w₂.[i] ≤ lvB c) ∧
    IsFormulaSet ℒₛₑₜ E ∧ (∀ y ∈ E, y ≤ lvB c) ∧ Paired E n w₁ w₂

/-- The level bound for the members of a replacement sequent. -/
def mB (v c : V) : V := 10 * (10 * (v + 1) + c + 1)

theorem isRel_R {R : V} (hR : R = 0 ∨ R = 1) : (ℒₛₑₜ).IsRel 2 R := by
  rw [SetCongruence.isRel_iff_Set, SetCongruence.coe_setEqIndex_eq, SetCongruence.coe_setMemIndex_eq]
  rcases hR with rfl | rfl <;> simp

theorem neR_shift (a b : V) (ha : IsUTerm ℒₛₑₜ a) (hb : IsUTerm ℒₛₑₜ b) :
    shift ℒₛₑₜ (neR a b) = neR (termShift ℒₛₑₜ a) (termShift ℒₛₑₜ b) := by
  unfold neR
  rw [Bootstrapping.shift_nrel (isRel_R (Or.inl rfl)) (by simp [ha, hb]), termShiftVec_cons₂ ha hb]

/-! ## Member bounds -/

/-- Every member of `s` is at level `m`. -/
def SeqLe (s m : V) : Prop := ∀ y ∈ s, y ≤ lvB m

theorem lt_lvB_succ {x m : V} (hx : x ≤ lvB m) : x < lvB (m + 1) := by
  rw [lvB_succ]
  have h2 : 2 ≤ lvB m := by
    have := lvB_mono (Arithmetic.zero_le m); rwa [lvB_zero] at this
  calc x ≤ lvB m := hx
    _ < lvB m * 2 := lt_mul_of_one_lt_right (lt_of_lt_of_le (by norm_num) h2) (by norm_num)
    _ ≤ lvB m * lvB m := mul_le_mul_of_nonneg_left h2 (Arithmetic.zero_le _)

theorem SeqLe.toLt {s m W : V} (h : SeqLe s m) (hW : m + 1 ≤ W) : SeqLt s W :=
  fun y hy => lt_of_lt_of_le (lt_lvB_succ (h y hy)) (lvB_mono hW)

theorem SeqLe.mono {s m m' : V} (h : SeqLe s m) (hm : m ≤ m') : SeqLe s m' :=
  fun y hy => lift_lvB (h y hy) hm

theorem SeqLe.insert {x s m : V} (hx : x ≤ lvB m) (h : SeqLe s m) : SeqLe (insert x s) m := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hx
  · exact h y hy

theorem SeqLe.setShift {s m : V} (h : SeqLe s m) : SeqLe (setShift ℒₛₑₜ s) (m + 1) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_setShift_iff.mp hy
  exact shift_level (h x hx)

theorem le_mB_left (v c : V) : 10 * (v + 1) + c ≤ mB v c :=
  le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))

theorem c_le_mB (v c : V) : c ≤ mB v c := le_trans le_add_self (le_mB_left v c)

theorem mB_succ (v c : V) : mB v (c + 1) = mB v c + 10 := by unfold mB; ring

theorem subst_mem_le {n w χ c v : V} (hχ : IsSemiformula ℒₛₑₜ n χ) (hv : χ ≤ lvB v)
    (hc : 1 ≤ c) (hw : IsSemitermVec ℒₛₑₜ n 0 w) (hb : ∀ i < n, w.[i] ≤ lvB c) :
    subst ℒₛₑₜ w χ ≤ lvB (mB v c) :=
  lift_lvB (subst_level v χ hv hχ.isUFormula c n 0 w hc hw hb
    (fun _ hi => closed_isVar (hw.nth hi))) (le_mB_left v c)

theorem neg_subst_mem_le {n w χ c v : V} (hχ : IsSemiformula ℒₛₑₜ n χ) (hv : χ ≤ lvB v)
    (hc : 1 ≤ c) (hw : IsSemitermVec ℒₛₑₜ n 0 w) (hb : ∀ i < n, w.[i] ≤ lvB c) :
    neg ℒₛₑₜ (subst ℒₛₑₜ w χ) ≤ lvB (mB v c) :=
  neg_level _ _ (subst_level v χ hv hχ.isUFormula c n 0 w hc hw hb
    (fun _ hi => closed_isVar (hw.nth hi))) (hχ.subst hw).isUFormula

theorem cseq_le {n w₁ w₂ χ E c v : V} (hχ : IsSemiformula ℒₛₑₜ n χ) (hv : χ ≤ lvB v)
    (inp : Inp n w₁ w₂ E c) : SeqLe (Cseq w₁ w₂ χ E) (mB v c) := by
  obtain ⟨hw₁, hw₂, hc, hb₁, hb₂, -, hEb, -⟩ := inp
  exact SeqLe.insert (neg_subst_mem_le hχ hv hc hw₁ hb₁)
    (SeqLe.insert (subst_mem_le hχ hv hc hw₂ hb₂)
      (fun y hy => lift_lvB (hEb y hy) (c_le_mB v c)))

theorem cseq_formulaSet {n w₁ w₂ χ E c : V} (hχ : IsSemiformula ℒₛₑₜ n χ)
    (inp : Inp n w₁ w₂ E c) : IsFormulaSet ℒₛₑₜ (Cseq w₁ w₂ χ E) := by
  obtain ⟨hw₁, hw₂, -, -, -, hE, -, -⟩ := inp
  unfold Cseq
  simp [hE, (hχ.subst hw₁).neg, hχ.subst hw₂]

/-! ## One more binder -/

theorem fvar0_le (c : V) (hc : 1 ≤ c) : (^&0 : V) ≤ lvB c :=
  le_trans (show (^&0 : V) ≤ 4 by simp [qqFvar, pair]; norm_num) (four_le_lvB hc)

theorem fvar0_lt {m : V} (hm : 1 ≤ m) : (^&0 : V) < lvB (m + 1) := lt_lvB_succ (fvar0_le m hm)

theorem mB_step (v c : V) : mB v c + 1 ≤ mB v (c + 1) + 1 := by
  rw [mB_succ]
  exact _root_.add_le_add le_self_add le_rfl

theorem qFree_nth_succ {n w i : V} (hw : IsSemitermVec ℒₛₑₜ n 0 w) (hi : i < n) :
    (qFree n w).[i + 1] = termShift ℒₛₑₜ w.[i] := by
  simp [qFree, nth_termShiftVec hw.isUTerm hi]

theorem qFree_entries {n w c : V} (hc : 1 ≤ c) (hw : IsSemitermVec ℒₛₑₜ n 0 w)
    (hb : ∀ i < n, w.[i] ≤ lvB c) : ∀ i < n + 1, (qFree n w).[i] ≤ lvB (c + 1) := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simpa [qFree] using fvar0_le (c + 1) (le_trans hc le_self_add)
  · have hj : j < n := by simpa using hi
    rw [qFree_nth_succ hw hj, lvB_succ]
    exact le_trans (termShift_le_sq _ (hw.nth hj).isUTerm) (mul_le_mul (hb j hj) (hb j hj) (Arithmetic.zero_le _)
      (Arithmetic.zero_le _))

theorem pair1_shift {E a b : V} (ha : IsUTerm ℒₛₑₜ a) (hb : IsUTerm ℒₛₑₜ b) (h : Pair1 E a b) :
    Pair1 (setShift ℒₛₑₜ E) (termShift ℒₛₑₜ a) (termShift ℒₛₑₜ b) := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · exact Or.inl rfl
  · right
    rw [← neR_shift a b ha hb, ← neR_shift b a hb ha]
    exact ⟨shift_mem_setShift h₁, shift_mem_setShift h₂⟩

theorem inp_succ {n w₁ w₂ E c : V} (inp : Inp n w₁ w₂ E c) :
    Inp (n + 1) (qFree n w₁) (qFree n w₂) (setShift ℒₛₑₜ E) (c + 1) := by
  obtain ⟨hw₁, hw₂, hc, hb₁, hb₂, hE, hEb, hP⟩ := inp
  refine ⟨qFree_semitermVec hw₁, qFree_semitermVec hw₂, le_trans hc le_self_add,
    qFree_entries hc hw₁ hb₁, qFree_entries hc hw₂ hb₂, hE.setShift,
    SeqLe.setShift hEb, ?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · exact Or.inl (by simp [qFree])
  · have hj : j < n := by simpa using hi
    rw [qFree_nth_succ hw₁ hj, qFree_nth_succ hw₂ hj]
    exact pair1_shift (hw₁.nth hj).isUTerm (hw₂.nth hj).isUTerm (hP j hj)

/-! ## The quantifier steps -/

theorem setShift_mono {s t : V} (h : s ⊆ t) : setShift ℒₛₑₜ s ⊆ setShift ℒₛₑₜ t := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_setShift_iff.mp hy
  exact shift_mem_setShift (h hx)

theorem subset_insert_insert {x y s : V} : s ⊆ insert x (insert y s) := by
  intro z hz
  simp [hz]

private theorem cseq_parts {n w₁ w₂ E c v p : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (hv : p ≤ lvB v) (inp : Inp n w₁ w₂ E c) :
    neg ℒₛₑₜ (subst ℒₛₑₜ w₁ p) ≤ lvB (mB v c) ∧ subst ℒₛₑₜ w₂ p ≤ lvB (mB v c) ∧
      IsFormula ℒₛₑₜ (neg ℒₛₑₜ (subst ℒₛₑₜ w₁ p)) ∧ IsFormula ℒₛₑₜ (subst ℒₛₑₜ w₂ p) := by
  have hb := cseq_le hp hv inp
  have hf := cseq_formulaSet hp inp
  exact ⟨hb _ (by simp [Cseq]), hb _ (by simp [Cseq]),
    hf _ (by simp [Cseq]), hf _ (by simp [Cseq])⟩


/-- The two level facts of the quantifier steps. -/
theorem quant_levels {S v c W : V} (hS0 : SeqLe S (mB v c)) (hW : mB v (c + 1) + 1 ≤ W) :
    SeqLe (setShift ℒₛₑₜ S) (mB v (c + 1)) ∧ mB v c + 1 ≤ W + 1 + 1 :=
  ⟨by rw [mB_succ]; exact (SeqLe.setShift hS0).mono (_root_.add_le_add le_rfl (by norm_num)),
    le_trans (mB_step v c) (le_trans hW (le_trans le_self_add le_self_add))⟩

theorem step_all {n w₁ w₂ E c v p W : V} (hp : IsSemiformula ℒₛₑₜ (n + 1) p)
    (inp : Inp n w₁ w₂ E c) (hpv : ^∀ p ≤ lvB v) (hspv : shift ℒₛₑₜ p ≤ lvB v)
    (hW : mB v (c + 1) + 1 ≤ W) (hW4 : 4 ≤ W)
    (ih : DLv 𝗭𝗙 (Cseq (qFree n w₁) (qFree n w₂) (shift ℒₛₑₜ p) (setShift ℒₛₑₜ E)) W) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ (^∀ p) E) (W + 1 + 1 + 1) := by
  have hall : IsSemiformula ℒₛₑₜ n (^∀ p) := by simpa using hp
  have hS0 := cseq_le hall hpv inp
  have hSf := cseq_formulaSet hall inp
  have inp' := inp_succ inp
  obtain ⟨hw₁, hw₂, -⟩ := inp
  have hP₁ : IsSemiformula ℒₛₑₜ 1 (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p) := by simpa using hp.subst hw₁.qVec
  have hP₂ : IsSemiformula ℒₛₑₜ 1 (subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) := by simpa using hp.subst hw₂.qVec
  have hS : Cseq w₁ w₂ (^∀ p) E = insert (^∃ neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p))
      (insert (^∀ subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) E) := by
    unfold Cseq
    rw [substs_all hp.isUFormula, substs_all hp.isUFormula, neg_all hP₁.isUFormula]
  rw [hS] at hS0 hSf ⊢
  set S := insert (^∃ neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p))
      (insert (^∀ subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) E) with hSdef
  obtain ⟨hF₁, hF₂, hFf₁, hFf₂⟩ := cseq_parts hp.shift hspv inp'
  set F₁ := subst ℒₛₑₜ (qFree n w₁) (shift ℒₛₑₜ p)
  set F₂ := subst ℒₛₑₜ (qFree n w₂) (shift ℒₛₑₜ p)
  have hf₂ : free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) = F₂ := free_subst_qVec hp hw₂
  have hf₁ : substs1 ℒₛₑₜ ^&0 (shift ℒₛₑₜ (neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p))) = neg ℒₛₑₜ F₁ := by
    rw [show F₁ = free ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p) from (free_subst_qVec hp hw₁).symm,
      ← free_neg hP₁]
    rfl
  have hsh : ^∃ shift ℒₛₑₜ (neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p)) ∈ setShift ℒₛₑₜ S := by
    have := shift_mem_setShift (L := ℒₛₑₜ) (show ^∃ neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p) ∈ S by simp [hSdef])
    rwa [Bootstrapping.shift_exs hP₁.neg.isUFormula] at this
  have hsub : setShift ℒₛₑₜ E ⊆ setShift ℒₛₑₜ S := setShift_mono subset_insert_insert
  obtain ⟨hSS, hc10⟩ := quant_levels hS0 hW
  -- weakening of the induction hypothesis
  have d1 : DLv 𝗭𝗙 (insert (neg ℒₛₑₜ F₁) (insert F₂ (setShift ℒₛₑₜ S))) (W + 1) := by
    refine DLv.wk hW4 ((hSS.insert hF₂).insert hF₁ |>.toLt hW)
      (by simp [hFf₁, hFf₂, hSf.setShift]) ?_ ih
    intro z hz
    simp only [Cseq, mem_bitInsert_iff] at hz ⊢
    rcases hz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hsub h))
  -- the existential side at `&0`
  have d2 : DLv 𝗭𝗙 (insert F₂ (setShift ℒₛₑₜ S)) (W + 1 + 1) := by
    refine DLv.ex_m (le_trans hW4 le_self_add) ((hSS.insert hF₂).toLt (le_trans hW le_self_add))
      (p := shift ℒₛₑₜ (neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p)))
      (fvar0_lt (le_trans (by norm_num) hW4)) (mem_bitInsert_iff.mpr (Or.inr hsh)) (by simp) ?_
    rwa [hf₁]
  refine DLv.all_m (le_trans hW4 (le_trans le_self_add le_self_add)) (hS0.toLt hc10)
    (p := subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) (by simp [hSdef]) ?_
  rwa [hf₂]

theorem step_ex {n w₁ w₂ E c v p W : V} (hp : IsSemiformula ℒₛₑₜ (n + 1) p)
    (inp : Inp n w₁ w₂ E c) (hpv : ^∃ p ≤ lvB v) (hspv : shift ℒₛₑₜ p ≤ lvB v)
    (hW : mB v (c + 1) + 1 ≤ W) (hW4 : 4 ≤ W)
    (ih : DLv 𝗭𝗙 (Cseq (qFree n w₁) (qFree n w₂) (shift ℒₛₑₜ p) (setShift ℒₛₑₜ E)) W) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ (^∃ p) E) (W + 1 + 1 + 1) := by
  have hex : IsSemiformula ℒₛₑₜ n (^∃ p) := by simpa using hp
  have hS0 := cseq_le hex hpv inp
  have hSf := cseq_formulaSet hex inp
  have inp' := inp_succ inp
  obtain ⟨hw₁, hw₂, -⟩ := inp
  have hP₁ : IsSemiformula ℒₛₑₜ 1 (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p) := by simpa using hp.subst hw₁.qVec
  have hP₂ : IsSemiformula ℒₛₑₜ 1 (subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) := by simpa using hp.subst hw₂.qVec
  have hS : Cseq w₁ w₂ (^∃ p) E = insert (^∀ neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p))
      (insert (^∃ subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) E) := by
    unfold Cseq
    rw [substs_ex hp.isUFormula, substs_ex hp.isUFormula, neg_ex hP₁.isUFormula]
  rw [hS] at hS0 hSf ⊢
  set S := insert (^∀ neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p))
      (insert (^∃ subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) E) with hSdef
  obtain ⟨hF₁, hF₂, hFf₁, hFf₂⟩ := cseq_parts hp.shift hspv inp'
  set F₁ := subst ℒₛₑₜ (qFree n w₁) (shift ℒₛₑₜ p)
  set F₂ := subst ℒₛₑₜ (qFree n w₂) (shift ℒₛₑₜ p)
  have hf₁ : free ℒₛₑₜ (neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p)) = neg ℒₛₑₜ F₁ := by
    rw [free_neg hP₁, free_subst_qVec hp hw₁]
  have hf₂ : substs1 ℒₛₑₜ ^&0 (shift ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p)) = F₂ :=
    free_subst_qVec hp hw₂
  have hsh : ^∃ shift ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p) ∈ setShift ℒₛₑₜ S := by
    have := shift_mem_setShift (L := ℒₛₑₜ) (show ^∃ subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p ∈ S by simp [hSdef])
    rwa [Bootstrapping.shift_exs hP₂.isUFormula] at this
  have hsub : setShift ℒₛₑₜ E ⊆ setShift ℒₛₑₜ S := setShift_mono subset_insert_insert
  obtain ⟨hSS, hc10⟩ := quant_levels hS0 hW
  have d1 : DLv 𝗭𝗙 (insert F₂ (insert (neg ℒₛₑₜ F₁) (setShift ℒₛₑₜ S))) (W + 1) := by
    refine DLv.wk hW4 ((hSS.insert hF₁).insert hF₂ |>.toLt hW)
      (by simp [hFf₁, hFf₂, hSf.setShift]) ?_ ih
    intro z hz
    simp only [Cseq, mem_bitInsert_iff] at hz ⊢
    rcases hz with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (hsub h))
  have d2 : DLv 𝗭𝗙 (insert (neg ℒₛₑₜ F₁) (setShift ℒₛₑₜ S)) (W + 1 + 1) := by
    refine DLv.ex_m (le_trans hW4 le_self_add) ((hSS.insert hF₁).toLt (le_trans hW le_self_add))
      (p := shift ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₂) p))
      (fvar0_lt (le_trans (by norm_num) hW4)) (mem_bitInsert_iff.mpr (Or.inr hsh)) (by simp) ?_
    rwa [hf₂]
  refine DLv.all_m (le_trans hW4 (le_trans le_self_add le_self_add)) (hS0.toLt hc10)
    (p := neg ℒₛₑₜ (subst ℒₛₑₜ (qVec ℒₛₑₜ w₁) p)) (by simp [hSdef]) ?_
  rwa [hf₁]

/-! ## The propositional steps -/


theorem step_and {n w₁ w₂ E c v p q W : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (hq : IsSemiformula ℒₛₑₜ n q) (inp : Inp n w₁ w₂ E c) (hpqv : p ^⋏ q ≤ lvB v)
    (hW : mB v c + 1 ≤ W) (hW4 : 4 ≤ W)
    (ihp : DLv 𝗭𝗙 (Cseq w₁ w₂ p E) W) (ihq : DLv 𝗭𝗙 (Cseq w₁ w₂ q E) W) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ (p ^⋏ q) E) (W + 1 + 1 + 1) := by
  have hpq : IsSemiformula ℒₛₑₜ n (p ^⋏ q) := by simp [hp, hq]
  have hS0 := cseq_le hpq hpqv inp
  have hSf := cseq_formulaSet hpq inp
  have hw₁ := inp.1
  have hw₂ := inp.2.1
  obtain ⟨mA₁, mA₂, fA₁, fA₂⟩ := cseq_parts hp (le_trans (le_of_lt (lt_K!_left p q)) hpqv) inp
  obtain ⟨mB₁, mB₂, fB₁, fB₂⟩ := cseq_parts hq (le_trans (le_of_lt (lt_K!_right p q)) hpqv) inp
  set A₁ := subst ℒₛₑₜ w₁ p
  set B₁ := subst ℒₛₑₜ w₁ q
  set A₂ := subst ℒₛₑₜ w₂ p
  set B₂ := subst ℒₛₑₜ w₂ q
  have hS : Cseq w₁ w₂ (p ^⋏ q) E = insert (neg ℒₛₑₜ A₁ ^⋎ neg ℒₛₑₜ B₁) (insert (A₂ ^⋏ B₂) E) := by
    unfold Cseq
    rw [substs_and hp.isUFormula hq.isUFormula, substs_and hp.isUFormula hq.isUFormula,
      neg_and (hp.subst hw₁).isUFormula (hq.subst hw₁).isUFormula]
  rw [hS] at hS0 hSf ⊢
  set S := insert (neg ℒₛₑₜ A₁ ^⋎ neg ℒₛₑₜ B₁) (insert (A₂ ^⋏ B₂) E) with hSdef
  have hW1 : mB v c + 1 ≤ W + 1 := le_trans hW le_self_add
  have hW2 : mB v c + 1 ≤ W + 1 + 1 := le_trans hW1 le_self_add
  have side : ∀ (X Y : V), X ≤ lvB (mB v c) → IsFormula ℒₛₑₜ X →
      DLv 𝗭𝗙 (insert Y (insert X E)) W → Y = neg ℒₛₑₜ A₁ ∨ Y = neg ℒₛₑₜ B₁ →
      DLv 𝗭𝗙 (insert X S) (W + 1 + 1) := by
    intro X Y hX hXf hd hY
    have hXS := hS0.insert hX
    refine DLv.or_m (le_trans hW4 le_self_add) (hXS.toLt hW1) (p := neg ℒₛₑₜ A₁)
      (q := neg ℒₛₑₜ B₁) (by simp [hSdef]) ?_
    refine DLv.wk hW4 ((hXS.insert mB₁).insert mA₁ |>.toLt hW)
      (by simp [fA₁, fB₁, hXf, hSf]) ?_ hd
    intro z hz
    simp only [mem_bitInsert_iff] at hz ⊢
    rcases hz with rfl | rfl | h
    · rcases hY with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (by simp [hSdef, h])))
  have dA := side A₂ (neg ℒₛₑₜ A₁) mA₂ fA₂ ihp (Or.inl rfl)
  have dB := side B₂ (neg ℒₛₑₜ B₁) mB₂ fB₂ ihq (Or.inr rfl)
  exact DLv.and_m (le_trans hW4 (le_trans le_self_add le_self_add)) (hS0.toLt hW2)
    (p := A₂) (q := B₂) (by simp [hSdef]) dA dB

theorem step_or {n w₁ w₂ E c v p q W : V} (hp : IsSemiformula ℒₛₑₜ n p)
    (hq : IsSemiformula ℒₛₑₜ n q) (inp : Inp n w₁ w₂ E c) (hpqv : p ^⋎ q ≤ lvB v)
    (hW : mB v c + 1 ≤ W) (hW4 : 4 ≤ W)
    (ihp : DLv 𝗭𝗙 (Cseq w₁ w₂ p E) W) (ihq : DLv 𝗭𝗙 (Cseq w₁ w₂ q E) W) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ (p ^⋎ q) E) (W + 1 + 1 + 1) := by
  have hpq : IsSemiformula ℒₛₑₜ n (p ^⋎ q) := by simp [hp, hq]
  have hS0 := cseq_le hpq hpqv inp
  have hSf := cseq_formulaSet hpq inp
  have hw₁ := inp.1
  have hw₂ := inp.2.1
  obtain ⟨mA₁, mA₂, fA₁, fA₂⟩ := cseq_parts hp (le_trans (le_of_lt (lt_or_left p q)) hpqv) inp
  obtain ⟨mB₁, mB₂, fB₁, fB₂⟩ := cseq_parts hq (le_trans (le_of_lt (lt_or_right p q)) hpqv) inp
  set A₁ := subst ℒₛₑₜ w₁ p
  set B₁ := subst ℒₛₑₜ w₁ q
  set A₂ := subst ℒₛₑₜ w₂ p
  set B₂ := subst ℒₛₑₜ w₂ q
  have hS : Cseq w₁ w₂ (p ^⋎ q) E = insert (neg ℒₛₑₜ A₁ ^⋏ neg ℒₛₑₜ B₁) (insert (A₂ ^⋎ B₂) E) := by
    unfold Cseq
    rw [substs_or hp.isUFormula hq.isUFormula, substs_or hp.isUFormula hq.isUFormula,
      neg_or (hp.subst hw₁).isUFormula (hq.subst hw₁).isUFormula]
  rw [hS] at hS0 hSf ⊢
  set S := insert (neg ℒₛₑₜ A₁ ^⋏ neg ℒₛₑₜ B₁) (insert (A₂ ^⋎ B₂) E) with hSdef
  have hW1 : mB v c + 1 ≤ W + 1 := le_trans hW le_self_add
  have hW2 : mB v c + 1 ≤ W + 1 + 1 := le_trans hW1 le_self_add
  set S₂ := insert A₂ (insert B₂ S) with hS₂
  have hS₂l : SeqLe S₂ (mB v c) := (hS0.insert mB₂).insert mA₂
  have hS₂f : IsFormulaSet ℒₛₑₜ S₂ := by simp [hS₂, fA₂, fB₂, hSf]
  have side : ∀ (Y X : V), Y ≤ lvB (mB v c) → IsFormula ℒₛₑₜ Y → (X = A₂ ∨ X = B₂) →
      DLv 𝗭𝗙 (insert Y (insert X E)) W → DLv 𝗭𝗙 (insert Y S₂) (W + 1) := by
    intro Y X hY hYf hX hd
    refine DLv.wk hW4 ((hS₂l.insert hY).toLt hW) (by simp [hYf, hS₂f]) ?_ hd
    intro z hz
    simp only [hS₂, mem_bitInsert_iff] at hz ⊢
    rcases hz with rfl | rfl | h
    · exact Or.inl rfl
    · rcases hX with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inr h))))))
  have dA := side (neg ℒₛₑₜ A₁) A₂ mA₁ fA₁ (Or.inl rfl) ihp
  have dB := side (neg ℒₛₑₜ B₁) B₂ mB₁ fB₁ (Or.inr rfl) ihq
  have dAnd : DLv 𝗭𝗙 S₂ (W + 1 + 1) :=
    DLv.and_m (le_trans hW4 le_self_add) (hS₂l.toLt hW1) (p := neg ℒₛₑₜ A₁) (q := neg ℒₛₑₜ B₁)
      (by simp [hS₂, hSdef]) dA dB
  exact DLv.or_m (le_trans hW4 (le_trans le_self_add le_self_add)) (hS0.toLt hW2)
    (p := A₂) (q := B₂) (by simp [hSdef]) dAnd

/-! ## Constants -/

private theorem step_const {n w₁ w₂ E c v W z : V} (inp : Inp n w₁ w₂ E c)
    (hz : IsSemiformula ℒₛₑₜ n z) (hv : z ≤ lvB v)
    (hW : mB v c + 1 ≤ W) (hW4 : 4 ≤ W) (hmem : (^⊤ : V) ∈ Cseq w₁ w₂ z E) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ z E) (W + 1) :=
  DLv.verum hW4 ((cseq_le hz hv inp).toLt hW) (cseq_formulaSet hz inp) hmem

theorem step_verum {n w₁ w₂ E c v W : V} (inp : Inp n w₁ w₂ E c) (hv : (^⊤ : V) ≤ lvB v)
    (hW : mB v c + 1 ≤ W) (hW4 : 4 ≤ W) : DLv 𝗭𝗙 (Cseq w₁ w₂ ^⊤ E) (W + 1) :=
  step_const inp (by simp) hv hW hW4 (by simp [Cseq])

theorem step_falsum {n w₁ w₂ E c v W : V} (inp : Inp n w₁ w₂ E c) (hv : (^⊥ : V) ≤ lvB v)
    (hW : mB v c + 1 ≤ W) (hW4 : 4 ≤ W) : DLv 𝗭𝗙 (Cseq w₁ w₂ ^⊥ E) (W + 1) :=
  step_const inp (by simp) hv hW hW4 (by simp [Cseq])

/-! ## Atoms -/

/-- The atom oracle: replacement in a single atom, at level `A + 10·c`. -/
def AtomOK (A : V) : Prop := ∀ R a₁ a₂ b₁ b₂ E c : V, (R = 0 ∨ R = 1) → 1 ≤ c →
    IsSemiterm ℒₛₑₜ 0 a₁ → IsSemiterm ℒₛₑₜ 0 a₂ → IsSemiterm ℒₛₑₜ 0 b₁ → IsSemiterm ℒₛₑₜ 0 b₂ →
    a₁ ≤ lvB c → a₂ ≤ lvB c → b₁ ≤ lvB c → b₂ ≤ lvB c →
    IsFormulaSet ℒₛₑₜ E → SeqLe E c → Pair1 E a₁ b₁ → Pair1 E a₂ b₂ →
    DLv 𝗭𝗙 (insert (^nrel 2 R (a₁ ∷ a₂ ∷ 0)) (insert (^rel 2 R (b₁ ∷ b₂ ∷ 0)) E)) (A + 10 * c)

theorem pair1_symm {E a b : V} (h : Pair1 E a b) : Pair1 E b a := by
  rcases h with rfl | ⟨h₁, h₂⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h₂, h₁⟩

theorem atom_terms (x R t₁ t₂ : V) :
    t₁ ≤ ⟪x, 2, R, t₁ ∷ t₂ ∷ 0⟫ + 1 ∧ t₂ ≤ ⟪x, 2, R, t₁ ∷ t₂ ∷ 0⟫ + 1 := by
  have hv : t₁ ∷ t₂ ∷ 0 ≤ ⟪x, 2, R, t₁ ∷ t₂ ∷ 0⟫ + 1 :=
    le_trans (le_pair_right R _) (le_trans (le_pair_right 2 _) (le_trans (le_pair_right x _) le_self_add))
  exact ⟨le_trans (le_of_lt (lt_adjoin _ _)) hv,
    le_trans (le_of_lt (lt_trans (lt_adjoin _ _) (lt_adjoin' _ _))) hv⟩

theorem term_pair {n w₁ w₂ E t : V} (hP : Paired E n w₁ w₂) (ht : IsSemiterm ℒₛₑₜ n t) :
    Pair1 E (termSubst ℒₛₑₜ w₁ t) (termSubst ℒₛₑₜ w₂ t) := by
  rcases term_var ht.isUTerm with ⟨z, rfl⟩ | ⟨x, rfl⟩
  · simp only [termSubst_bvar]
    exact hP z (by simpa using ht)
  · simp only [termSubst_fvar]
    exact Or.inl rfl

theorem atom_vec {n R t₁ t₂ : V} (h : IsSemiformula ℒₛₑₜ n (^rel 2 R (t₁ ∷ t₂ ∷ 0)) ∨
    IsSemiformula ℒₛₑₜ n (^nrel 2 R (t₁ ∷ t₂ ∷ 0))) :
    IsSemitermVec ℒₛₑₜ 2 n (t₁ ∷ t₂ ∷ 0) ∧ IsSemiterm ℒₛₑₜ n t₁ ∧ IsSemiterm ℒₛₑₜ n t₂ := by
  have hvec : IsSemitermVec ℒₛₑₜ 2 n (t₁ ∷ t₂ ∷ 0) := by
    rcases h with h | h
    · exact (IsSemiformula.rel.mp h).2
    · exact (IsSemiformula.nrel.mp h).2
  exact ⟨hvec, by simpa using hvec.nth (i := 0) (by simp), by simpa using hvec.nth (i := 1) (by simp)⟩

private theorem inp_swap {n w₁ w₂ E c : V} (inp : Inp n w₁ w₂ E c) : Inp n w₂ w₁ E c := by
  obtain ⟨hw₁, hw₂, hc, hb₁, hb₂, hE, hEb, hP⟩ := inp
  exact ⟨hw₂, hw₁, hc, hb₂, hb₁, hE, hEb, fun i hi => pair1_symm (hP i hi)⟩

private theorem atom_subst {A : V} (hA : AtomOK A) {n w₁ w₂ E c v R t₁ t₂ : V}
    (hR : R = 0 ∨ R = 1) (ht₁ : IsSemiterm ℒₛₑₜ n t₁) (ht₂ : IsSemiterm ℒₛₑₜ n t₂)
    (hl₁ : t₁ ≤ lvB v) (hl₂ : t₂ ≤ lvB v) (inp : Inp n w₁ w₂ E c) :
    DLv 𝗭𝗙 (insert (^nrel 2 R (termSubst ℒₛₑₜ w₁ t₁ ∷ termSubst ℒₛₑₜ w₁ t₂ ∷ 0))
      (insert (^rel 2 R (termSubst ℒₛₑₜ w₂ t₁ ∷ termSubst ℒₛₑₜ w₂ t₂ ∷ 0)) E)) (A + 10 * (v + c)) := by
  obtain ⟨hw₁, hw₂, hc, hb₁, hb₂, hE, hEb, hP⟩ := inp
  exact hA R _ _ _ _ E (v + c) hR (le_trans hc le_add_self)
    (termSubst_closed_semiterm hw₁ ht₁) (termSubst_closed_semiterm hw₁ ht₂)
    (termSubst_closed_semiterm hw₂ ht₁) (termSubst_closed_semiterm hw₂ ht₂)
    (termSubst_var_le hw₁.lh hb₁ ht₁.isUTerm hl₁)
    (termSubst_var_le hw₁.lh hb₁ ht₂.isUTerm hl₂)
    (termSubst_var_le hw₂.lh hb₂ ht₁.isUTerm hl₁)
    (termSubst_var_le hw₂.lh hb₂ ht₂.isUTerm hl₂)
    hE (fun y hy => lift_lvB (hEb y hy) le_add_self) (term_pair hP ht₁) (term_pair hP ht₂)

theorem step_rel {A : V} (hA : AtomOK A) {n w₁ w₂ E c v R t₁ t₂ : V} (hR : R = 0 ∨ R = 1)
    (hχ : IsSemiformula ℒₛₑₜ n (^rel 2 R (t₁ ∷ t₂ ∷ 0))) (hv : ^rel 2 R (t₁ ∷ t₂ ∷ 0) ≤ lvB v)
    (inp : Inp n w₁ w₂ E c) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ (^rel 2 R (t₁ ∷ t₂ ∷ 0)) E) (A + 10 * (v + c)) := by
  have hw₁ := inp.1
  obtain ⟨hvec, ht₁, ht₂⟩ := atom_vec (Or.inl hχ)
  obtain ⟨hl₁, hl₂⟩ := atom_terms 0 R t₁ t₂
  unfold Cseq
  rw [substs_rel (isRel_R hR) hvec.isUTerm, substs_rel (isRel_R hR) hvec.isUTerm,
    neg_rel (isRel_R hR) (hw₁.termSubstVec hvec).isUTerm,
    termSubstVec_cons₂ ht₁.isUTerm ht₂.isUTerm, termSubstVec_cons₂ ht₁.isUTerm ht₂.isUTerm]
  exact atom_subst hA hR ht₁ ht₂ (le_trans hl₁ hv) (le_trans hl₂ hv) inp

theorem step_nrel {A : V} (hA : AtomOK A) {n w₁ w₂ E c v R t₁ t₂ : V} (hR : R = 0 ∨ R = 1)
    (hχ : IsSemiformula ℒₛₑₜ n (^nrel 2 R (t₁ ∷ t₂ ∷ 0))) (hv : ^nrel 2 R (t₁ ∷ t₂ ∷ 0) ≤ lvB v)
    (inp : Inp n w₁ w₂ E c) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ (^nrel 2 R (t₁ ∷ t₂ ∷ 0)) E) (A + 10 * (v + c)) := by
  have hw₁ := inp.1
  obtain ⟨hvec, ht₁, ht₂⟩ := atom_vec (Or.inr hχ)
  obtain ⟨hl₁, hl₂⟩ := atom_terms 1 R t₁ t₂
  unfold Cseq
  rw [substs_nrel (isRel_R hR) hvec.isUTerm, substs_nrel (isRel_R hR) hvec.isUTerm,
    neg_nrel (isRel_R hR) (hw₁.termSubstVec hvec).isUTerm,
    termSubstVec_cons₂ ht₁.isUTerm ht₂.isUTerm, termSubstVec_cons₂ ht₁.isUTerm ht₂.isUTerm]
  exact DLv.ofSetEq (fun x => by simp only [mem_bitInsert_iff]; tauto)
    (atom_subst hA hR ht₁ ht₂ (le_trans hl₁ hv) (le_trans hl₂ hv) (inp_swap inp))

/-! ## The induction on formula complexity -/

/-- The level of the replacement derivation. -/
def cW (A v h c : V) : V := 30 * h + 10 * c + 100 * v + A + 200

theorem le_of_add_eq {x y z : V} (h : x + y = z) : x ≤ z := h ▸ le_self_add

theorem cW_atom (A v h c : V) : A + 10 * (v + c) ≤ cW A v h c :=
  le_of_add_eq (y := 30 * h + 90 * v + 200) (by unfold cW; ring)

theorem cW_const (A v h c : V) : mB v c + 1 + 1 ≤ cW A v h c :=
  le_of_add_eq (y := 30 * h + A + 88) (by unfold cW mB; ring)

theorem cW_four (A v h c : V) : 4 ≤ cW A v h c :=
  le_of_add_eq (y := 30 * h + 10 * c + 100 * v + A + 196) (by unfold cW; ring)

theorem four_le_mB (v c : V) : 4 ≤ mB v c + 1 :=
  le_of_add_eq (y := 100 * v + 10 * c + 107) (by unfold mB; ring)

theorem cW_mB (A v h c : V) : mB v c + 1 ≤ cW A v h c :=
  le_trans le_self_add (cW_const A v h c)

theorem cW_quant (A v h c : V) : cW A v h (c + 1) + 1 + 1 + 1 ≤ cW A v (h + 1) c :=
  le_of_add_eq (y := 17) (by unfold cW; ring)

theorem cW_mB_succ (A v h c : V) : mB v (c + 1) + 1 ≤ cW A v h (c + 1) := cW_mB A v h (c + 1)

theorem cW_prop (A v h c : V) : cW A v h c + 1 + 1 + 1 ≤ cW A v (h + 1) c :=
  le_of_add_eq (y := 27) (by unfold cW; ring)

theorem cW_mono (A v h c : V) : cW A v h c ≤ cW A v (h + 1) c :=
  le_of_add_eq (y := 30) (by unfold cW; ring)

theorem le_of_succ_le_succ' {x h : V} (hx : x + 1 ≤ h + 1) : x ≤ h :=
  (add_le_add_iff_right 1).mp hx

/-- Atoms and constants, at every height. -/
theorem core_base {A : V} (hA : AtomOK A) {v h χ n w₁ w₂ E c : V}
    (hχ : IsSemiformula ℒₛₑₜ n χ) (hv : χ ≤ lvB v) (inp : Inp n w₁ w₂ E c)
    (hcase : (∃ k R u, (ℒₛₑₜ).IsRel k R ∧ IsUTermVec ℒₛₑₜ k u ∧ χ = ^rel k R u) ∨
      (∃ k R u, (ℒₛₑₜ).IsRel k R ∧ IsUTermVec ℒₛₑₜ k u ∧ χ = ^nrel k R u) ∨ χ = ^⊤ ∨ χ = ^⊥) :
    DLv 𝗭𝗙 (Cseq w₁ w₂ χ E) (cW A v h c) := by
  rcases hcase with ⟨k, R, u, hR, hu, rfl⟩ | ⟨k, R, u, hR, hu, rfl⟩ | rfl | rfl
  · obtain ⟨rfl, hR01⟩ := isRel_set hR
    obtain ⟨t₁, t₂, rfl, -, -⟩ := vec_two hu
    exact (step_rel hA hR01 hχ hv inp).mono (cW_atom A v h c)
  · obtain ⟨rfl, hR01⟩ := isRel_set hR
    obtain ⟨t₁, t₂, rfl, -, -⟩ := vec_two hu
    exact (step_nrel hA hR01 hχ hv inp).mono (cW_atom A v h c)
  · exact (step_verum inp hv le_rfl (four_le_mB v c)).mono (cW_const A v h c)
  · exact (step_falsum inp hv le_rfl (four_le_mB v c)).mono (cW_const A v h c)

theorem quant_child {p v : V} (_hp : IsUFormula ℒₛₑₜ p) {tag : V}
    (hv : ⟪tag, p⟫ + 1 ≤ lvB v) (hF : IsUFormula ℒₛₑₜ (⟪tag, p⟫ + 1)) :
    shift ℒₛₑₜ p ≤ lvB v := by
  rcases zero_or_succ v with rfl | ⟨v', rfl⟩
  · exact absurd rfl (formula_level_pos hv hF)
  · exact shift_level (pair_children hv).2

theorem or4_left {A B C D R : Prop} (h : A ∨ B ∨ C ∨ D ∨ R) : (A ∨ B ∨ C ∨ D) ∨ R := by
  tauto

set_option maxHeartbeats 4000000 in
/-- **Bounded equality replacement.** -/
theorem core {A : V} (hA : AtomOK A) (v : V) : ∀ h : V, ∀ χ n w₁ w₂ E c : V,
    formulaComplexity ℒₛₑₜ χ ≤ h → IsSemiformula ℒₛₑₜ n χ → χ ≤ lvB v → Inp n w₁ w₂ E c →
    DLv 𝗭𝗙 (Cseq w₁ w₂ χ E) (cW A v h c) := by
  intro h
  induction h using ISigma1.pi1_succ_induction
  · simp only [DLv, DerivableLe, Cseq, Inp, Paired, Pair1, neR, lvB, cW]
    definability
  · intro χ n w₁ w₂ E c hcx hχ hv inp
    rcases or4_left hχ.isUFormula.case with hb | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ |
        ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact core_base hA hχ hv inp hb
    all_goals simp [formulaComplexity_and, formulaComplexity_or, formulaComplexity_all,
      formulaComplexity_ex, *] at hcx
  · case succ h ih =>
    intro χ n w₁ w₂ E c hcx hχ hv inp
    rcases or4_left hχ.isUFormula.case with hb | ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ |
        ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact core_base hA hχ hv inp hb
    · rw [formulaComplexity_and hp hq] at hcx
      have hm := le_of_succ_le_succ' hcx
      obtain ⟨hp', hq'⟩ := IsSemiformula.and.mp hχ
      have hpv := le_trans (le_of_lt (lt_K!_left p q)) hv
      have hqv := le_trans (le_of_lt (lt_K!_right p q)) hv
      exact (step_and hp' hq' inp hv (cW_mB A v h c) (cW_four A v h c)
        (ih p n w₁ w₂ E c (le_trans (le_max_left _ _) hm) hp' hpv inp)
        (ih q n w₁ w₂ E c (le_trans (le_max_right _ _) hm) hq' hqv inp)).mono (cW_prop A v h c)
    · rw [formulaComplexity_or hp hq] at hcx
      have hm := le_of_succ_le_succ' hcx
      obtain ⟨hp', hq'⟩ := IsSemiformula.or.mp hχ
      have hpv := le_trans (le_of_lt (lt_or_left p q)) hv
      have hqv := le_trans (le_of_lt (lt_or_right p q)) hv
      exact (step_or hp' hq' inp hv (cW_mB A v h c) (cW_four A v h c)
        (ih p n w₁ w₂ E c (le_trans (le_max_left _ _) hm) hp' hpv inp)
        (ih q n w₁ w₂ E c (le_trans (le_max_right _ _) hm) hq' hqv inp)).mono (cW_prop A v h c)
    · rw [formulaComplexity_all hp] at hcx
      have hm := le_of_succ_le_succ' hcx
      have hp' : IsSemiformula ℒₛₑₜ (n + 1) p := IsSemiformula.all.mp hχ
      have hspv := quant_child (tag := 6) hp hv hχ.isUFormula
      have ih' := ih (shift ℒₛₑₜ p) (n + 1) (qFree n w₁) (qFree n w₂) (setShift ℒₛₑₜ E) (c + 1)
        (by rw [formulaComplexity_shift hp]; exact hm) hp'.shift hspv (inp_succ inp)
      exact (step_all hp' inp hv hspv (cW_mB_succ A v h c) (cW_four A v h (c + 1)) ih').mono
        (cW_quant A v h c)
    · rw [formulaComplexity_ex hp] at hcx
      have hm := le_of_succ_le_succ' hcx
      have hp' : IsSemiformula ℒₛₑₜ (n + 1) p := IsSemiformula.exs.mp hχ
      have hspv := quant_child (tag := 7) hp hv hχ.isUFormula
      have ih' := ih (shift ℒₛₑₜ p) (n + 1) (qFree n w₁) (qFree n w₂) (setShift ℒₛₑₜ E) (c + 1)
        (by rw [formulaComplexity_shift hp]; exact hm) hp'.shift hspv (inp_succ inp)
      exact (step_ex hp' inp hv hspv (cW_mB_succ A v h c) (cW_four A v h (c + 1)) ih').mono
        (cW_quant A v h c)

end LeanProofs.ZFCinPA.SizedCongruence

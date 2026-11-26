import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumSegments
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale

/-!
# Actual finite Gaussian-rational sums

A fixed two-variable body supplies the original entries and numerical data.
The program builds the actual finite list and evaluates it at one. Every
count, scalar and datum remains internal. Genuine prefix inductions prove
the recurrence, first-term split, additivity and multiplication transport.
Generic congruence requires only bounded individual entry-code equations,
never a desired sum identity. Raw first entries stay under qadd, so no
canonical code is falsely equated with an arbitrary original code.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSumSegments
  (partialSum prefix_zero prefix_succ prefix_canonical prefix_entries_congr entriesEqual)
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence sequence_decode subst_sequence)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sum (t : PTm 2) (m x : PTm n) : PTm n := partialSum (sequence t m x) m

ipra_subst sum

theorem sum_canonical (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx] canonical (sum t m x) :=
  prefix_canonical _ _

theorem sum_zero (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] sum t zero x ≐ qzero := prefix_zero _

/-- Different stored lengths have the same actual original entries on
their common prefix; no outer list-code equality is asserted. -/
theorem generated_prefix_entries (t : PTm 2) (m l x r : PTm n)
    (hm : Γ ⊢[PRAAx] le r m) (hl : Γ ⊢[PRAAx] le r l) : Γ ⊢[PRAAx]
    entriesEqual (sequence t m x) (sequence t l x) r := by
  refine .allI (.impI ?_)
  have mh : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift r) (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hm.shift
  have lh : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift r) (Syn.shift l) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using hl.shift
  have im : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift m) :=
    le_trans Prf.hyp0 mh.wk
  have il : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift l) :=
    le_trans Prf.hyp0 lh.wk
  simpa only [Syn.shift,subst_sequence] using
    (sequence_decode t (x := Syn.shift x) im).eqTrans
      (sequence_decode t (x := Syn.shift x) il).eqSymm

theorem generated_prefix_congr (t : PTm 2) (m l x r : PTm n)
    (hm : Γ ⊢[PRAAx] le r m) (hl : Γ ⊢[PRAAx] le r l) : Γ ⊢[PRAAx]
    partialSum (sequence t m x) r ≐ partialSum (sequence t l x) r :=
  prefix_entries_congr _ _ r r (generated_prefix_entries t m l x r hm hl) (le_refl _)

theorem sum_succ (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx]
    sum t (succ m) x ≐ qadd (sum t m x) (inst2 t m x) :=
  (prefix_succ (sequence t (succ m) x) m).eqTrans
    (qadd_congr (generated_prefix_congr t (succ m) m x m (le_succ_self _) (le_refl _))
      (sequence_decode t (le_refl (succ m))))

def termsEqual (t u : PTm 2) (m x y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ inst2 t (var 0) (Syn.shift x) ≐ inst2 u (var 0) (Syn.shift y))

ipra_subst termsEqual [Syn.subst_shift, Syn.shift_subst]

theorem term_equal_at (t u : PTm 2) (m x y i : PTm n)
    (h : Γ ⊢[PRAAx] termsEqual t u m x y) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    inst2 t i x ≐ inst2 u i y := by
  have rule : Γ ⊢[PRAAx] lt i m ⟶ inst2 t i x ≐ inst2 u i y := by simpa [termsEqual] using h.allE i
  exact .impE rule hi

/-- Equality of the actual bounded entries suffices, without equality of
the original data or generated list codes. -/
theorem sum_congr_bounded (t u : PTm 2) (m x y : PTm n)
    (h : Γ ⊢[PRAAx] termsEqual t u m x y) : Γ ⊢[PRAAx] sum t m x ≐ sum u m y := by
  apply prefix_entries_congr _ _ m m (hr := le_refl _)
  refine .allI (.impI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] termsEqual t u (Syn.shift m) (Syn.shift x) (Syn.shift y) := by
    simpa only [Fm.shift,subst_termsEqual,Syn.shift] using h.shift
  simpa only [Syn.shift,subst_sequence] using
    (sequence_decode t (x := Syn.shift x) Prf.hyp0).eqTrans
      ((term_equal_at t u _ _ _ (var 0) hs.wk Prf.hyp0).eqTrans
        (sequence_decode u (x := Syn.shift y) Prf.hyp0).eqSymm)

theorem sum_index_congr (t : PTm 2) {m l x y : PTm n}
    (hm : Γ ⊢[PRAAx] m ≐ l) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] sum t m x ≐ sum t l y := by
  ipra_congr (sum t (var 0) (var 1) : PTm 2) with [hm, hx]

def shiftLaw (t : PTm 2) (m x : PTm n) : Fm PTm n :=
  sum t (succ m) x ≐ qadd (inst2 t zero x) (sum (shiftBody t) m x)

ipra_subst shiftLaw

theorem shift_zero (t : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] shiftLaw t zero x :=
  (sum_succ t zero x).eqTrans ((qadd_congr (sum_zero t x) (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
      (qadd_congr (.eqRefl _) (sum_zero (shiftBody t) x).eqSymm)))

theorem shift_step (t : PTm 2) (m x : PTm n) (h : Γ ⊢[PRAAx] shiftLaw t m x) :
    Γ ⊢[PRAAx] shiftLaw t (succ m) x := by
  have tail : Γ ⊢[PRAAx] qadd (sum (shiftBody t) m x) (inst2 t (succ m) x) ≐
      sum (shiftBody t) (succ m) x := by
    simpa only [inst2_shiftBody] using (sum_succ (shiftBody t) m x).eqSymm
  exact (sum_succ t (succ m) x).eqTrans ((qadd_congr h (.eqRefl _)).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqTrans (qadd_congr (.eqRefl _) tail)))

/-- The original first term stays under actual qadd even when its stored
code is not canonical. -/
theorem sum_shift_first (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx]
    sum t (succ m) x ≐ qadd (inst2 t zero x) (sum (shiftBody t) m x) := by
  have all : Γ ⊢[PRAAx] .all (shiftLaw t (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_shiftLaw]
    · exact shift_zero t x
    · exact shift_step t _ _ Prf.hyp0
  change Γ ⊢[PRAAx] shiftLaw t m x
  simpa only [subst_shiftLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

def addBody (t u : PTm 2) : PTm 2 := qadd t u
@[simp] theorem inst2_addBody (t u : PTm 2) (i x : PTm n) :
    inst2 (addBody t u) i x = qadd (inst2 t i x) (inst2 u i x) := by simp [inst2,addBody]

theorem add_shuffle (a b c d : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd a b) (qadd c d) ≐ qadd (qadd a c) (qadd b d) :=
  (GaussianRationalSumAlgebra.qadd_associative (qadd a b) c d).eqSymm.eqTrans
    (GaussianRationalSumAlgebra.shuffle_four a b c d)

def addLaw (t u : PTm 2) (m x : PTm n) : Fm PTm n :=
  sum (addBody t u) m x ≐ qadd (sum t m x) (sum u m x)
ipra_subst addLaw

theorem add_zero (t u : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] addLaw t u zero x :=
  (sum_zero _ _).eqTrans ((qadd_congr (sum_zero t x) (sum_zero u x)).eqTrans
    (GaussianRationalSyntheticDivision.qzero_add qzero qzero_canonical)).eqSymm

theorem add_step (t u : PTm 2) (m x : PTm n) (h : Γ ⊢[PRAAx] addLaw t u m x) :
    Γ ⊢[PRAAx] addLaw t u (succ m) x := by
  have actual := sum_succ (Γ := Γ) (addBody t u) m x
  rw [inst2_addBody] at actual
  exact actual.eqTrans ((qadd_congr h (.eqRefl _)).eqTrans
    ((add_shuffle _ _ _ _).eqTrans (qadd_congr (sum_succ t m x).eqSymm (sum_succ u m x).eqSymm)))

theorem sum_add (t u : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx]
    sum (addBody t u) m x ≐ qadd (sum t m x) (sum u m x) := by
  have all : Γ ⊢[PRAAx] .all (addLaw t u (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_addLaw]
    · exact add_zero t u x
    · exact add_step t u _ _ Prf.hyp0
  change Γ ⊢[PRAAx] addLaw t u m x
  simpa only [subst_addLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

def multiplyBody (t : PTm 2) : PTm 2 := qmul (fstT (var 1)) (inst2 t (var 0) (sndT (var 1)))

theorem multiply_body_at (t : PTm 2) (a i x : PTm n) : Γ ⊢[PRAAx]
    inst2 (multiplyBody t) i (pairT a x) ≐ qmul a (inst2 t i x) := by
  have e : Syn.subst ![i,pairT a x] (Syn.subst ![var 0,sndT (var 1)] t) =
      inst2 t i (sndT (pairT a x)) := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  simp only [multiplyBody,inst2,GaussianRationalHorner.subst_qmul,subst_fstT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,e]
  exact qmul_congr (fst_pair _ _) (congrInst2 t (.eqRefl _) (snd_pair _ _))

def multiplyLaw (t : PTm 2) (a m x : PTm n) : Fm PTm n :=
  sum (multiplyBody t) m (pairT a x) ≐ qmul a (sum t m x)
ipra_subst multiplyLaw

theorem multiply_zero (t : PTm 2) (a x : PTm n) : Γ ⊢[PRAAx] multiplyLaw t a zero x :=
  (sum_zero _ _).eqTrans ((qmul_congr (.eqRefl _) (sum_zero t x)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right a)).eqSymm

theorem multiply_step (t : PTm 2) (a m x : PTm n) (h : Γ ⊢[PRAAx] multiplyLaw t a m x) :
    Γ ⊢[PRAAx] multiplyLaw t a (succ m) x :=
  (sum_succ (multiplyBody t) m (pairT a x)).eqTrans
    ((qadd_congr h (multiply_body_at t a m x)).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqSymm.eqTrans
        (qmul_congr (.eqRefl _) (sum_succ t m x).eqSymm)))

theorem sum_multiply (t : PTm 2) (a m x : PTm n) : Γ ⊢[PRAAx]
    sum (multiplyBody t) m (pairT a x) ≐ qmul a (sum t m x) := by
  have all : Γ ⊢[PRAAx] .all (multiplyLaw t (Syn.shift a) (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_multiplyLaw]
    · exact multiply_zero t a x
    · exact multiply_step t _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] multiplyLaw t a m x
  simpa only [subst_multiplyLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE m

def sumF (t : PTm 2) : PR 2 := PTm.toPR (sum t (var 0) (var 1))
theorem program_at (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF t) m x ≐ sum t m x := by
  simpa [sumF,ap2] using toPR_eq (Γ := Γ) (sum t (var 0) (var 1) : PTm 2) ![m,x]

theorem finite_sum_recurrence_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum t (succ (var 0)) (var 1) ≐ qadd (sum t (var 0) (var 1)) (inst2 t (var 0) (var 1))) :=
  closeUniv 2 (sum_succ _ _ _)
theorem finite_sum_shift_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum t (succ (var 0)) (var 1) ≐ qadd (inst2 t zero (var 1)) (sum (shiftBody t) (var 0) (var 1))) :=
  closeUniv 2 (sum_shift_first _ _ _)
theorem finite_sum_add_closed (t u : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sum (addBody t u) (var 0) (var 1) ≐ qadd (sum t (var 0) (var 1)) (sum u (var 0) (var 1))) :=
  closeUniv 2 (sum_add _ _ _ _)
theorem finite_sum_multiply_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sum (multiplyBody t) (var 1) (pairT (var 0) (var 2)) ≐ qmul (var 0) (sum t (var 1) (var 2))) :=
  closeUniv 3 (sum_multiply _ _ _ _)
theorem finite_sum_congruence_closed (t u : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termsEqual t u (var 0) (var 1) (var 2) ⟶ sum t (var 0) (var 1) ≐ sum u (var 0) (var 2)) :=
  closeUniv 3 (.impI (sum_congr_bounded _ _ _ _ _ Prf.hyp0))
theorem finite_sum_program_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 (sumF t) (var 0) (var 1) ≐ sum t (var 0) (var 1)) ⋏ canonical (ap2 (sumF t) (var 0) (var 1))) :=
  closeUniv 2 (.andI (program_at _ _ _) (GaussianRationalHorner.canonical_congr (program_at _ _ _) (sum_canonical _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianRationalFiniteSum

import IPRADerivations.Analysis.Polynomials.Determinants.RationalEmbedding.RationalPolynomialDeterminantTermsGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminant

/-!
# Coefficientwise congruence for the stored polynomial determinant

The original retained words select the same positions in both matrices.
Their coefficient lists need only agree at protected indices. A bounded
induction compares the actual word-product stages, then the original
coefficient sum compares the two determinants.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantCongruence

open_ipra
open GaussianPolynomialDeterminantTerms (cell factor stage term stage_zero stage_coefficient_succ term_coefficient)
open RationalPolynomialDeterminantTermsGaussianEmbedding (entriesEqual entry_equal_at coefficient_left_entries)
open GaussianRationalMonicReconstruction (paddedEqual coefficient_padded_ext)
open GaussianRationalLinearProduct (padded padded_inside padded_outside)
open GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowEntries (M P m L r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  entriesEqual (cell (Syn.shift M) (Syn.shift r) (var 0)) (cell (Syn.shift P) (Syn.shift r) (var 0)) (succ (Syn.shift L)))
def matrixEntries (M P m L : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ rowEntries (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) (var 0))

ipra_subst rowEntries [Syn.subst_shift, Syn.shift_subst]
ipra_subst matrixEntries [Syn.subst_shift, Syn.shift_subst]

theorem matrix_entries_at (M P m L r j : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] entriesEqual (cell M r j) (cell P r j) (succ L) := by
  have rows : Γ ⊢[PRAAx] lt r m ⟶ rowEntries M P m L r := by simpa [matrixEntries] using h.allE r
  have cells : Γ ⊢[PRAAx] lt j m ⟶ entriesEqual (cell M r j) (cell P r j) (succ L) := by
    simpa [rowEntries] using (Prf.impE rows hr).allE j
  exact .impE cells hj

theorem factor_entries (M P m L w j : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] entriesEqual (factor M m w j) (factor P m w j) (succ L) :=
  matrix_entries_at M P m L _ j h (Foundations.RuntimePermutationWords.digit_bound m w j hj) hj

private theorem padded_at {C D L i : PTm n} (h : Γ ⊢[PRAAx] entriesEqual C D (succ L)) :
    Γ ⊢[PRAAx] padded C (succ L) i ≐ padded D (succ L) i := by
  refine .orE (lt_or_le i (succ L)) ?_ ?_
  · exact (padded_inside _ _ _ Prf.hyp0).eqTrans
      ((entry_equal_at _ _ _ _ h.wk Prf.hyp0).eqTrans (padded_inside _ _ _ Prf.hyp0).eqSymm)
  · exact (padded_outside _ _ _ Prf.hyp0).eqTrans (padded_outside _ _ _ Prf.hyp0).eqSymm

theorem padded_entries (C D L k : PTm n) (h : Γ ⊢[PRAAx] entriesEqual C D (succ L)) :
    Γ ⊢[PRAAx] paddedEqual C D L L k := by
  refine .allI (.impI ?_)
  have sh : Γ.map Fm.shift ⊢[PRAAx] entriesEqual (Syn.shift C) (Syn.shift D) (succ (Syn.shift L)) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [Syn.shift] using padded_at (i := var 0) sh.wk

def stageEntries (M P m L w j : PTm n) : Fm PTm n :=
  entriesEqual (stage M m L w j) (stage P m L w j) (succ (j*L))
def stageLaw (M P m L w j : PTm n) : Fm PTm n := le j m ⟶ stageEntries M P m L w j

ipra_subst stageEntries
ipra_subst stageLaw

theorem stage_base (M P m L w : PTm n) : Γ ⊢[PRAAx] stageEntries M P m L w zero := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianPolynomialDeterminantTerms.subst_stage,ConciseIPRA.PTm.subst_zero] using
    entry_congr ((stage_zero (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w)).eqTrans
      (stage_zero (Syn.shift P) (Syn.shift m) (Syn.shift L) (Syn.shift w)).eqSymm) (.eqRefl (var 0))

theorem stage_step_at (M P m L w j s : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L) (hj : Γ ⊢[PRAAx] lt j m)
    (ih : Γ ⊢[PRAAx] stageEntries M P m L w j) (hs : Γ ⊢[PRAAx] le s (succ j*L)) :
    Γ ⊢[PRAAx] entry (stage M m L w (succ j)) s ≐ entry (stage P m L w (succ j)) s := by
  let A := stage M m L w j
  let B := stage P m L w j
  let C := factor M m w j
  let D := factor P m w j
  let H := succ (j*L)
  have left := coefficient_left_entries A B C L H H s ih (le_refl _)
  have right := coefficient_padded_ext B C D L L H s (padded_entries _ _ _ _ (factor_entries M P m L w j h hj))
  exact (stage_coefficient_succ M m L w j s hs).eqTrans
    (left.eqTrans (right.eqTrans (stage_coefficient_succ P m L w j s hs).eqSymm))

theorem stage_step (M P m L w j : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L) (hj : Γ ⊢[PRAAx] lt j m)
    (ih : Γ ⊢[PRAAx] stageEntries M P m L w j) : Γ ⊢[PRAAx] stageEntries M P m L w (succ j) := by
  refine .allI (.impI ?_)
  have hj' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hj.shift
  have h' : Γ.map Fm.shift ⊢[PRAAx] matrixEntries (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have ih' : Γ.map Fm.shift ⊢[PRAAx] stageEntries (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L)
      (Syn.shift w) (Syn.shift j) := by simpa [Fm.shift,Syn.shift] using ih.shift
  have hs : lt (var 0) (succ (succ (Syn.shift j)*Syn.shift L)) :: Γ.map Fm.shift ⊢[PRAAx]
      le (var 0) (succ (Syn.shift j)*Syn.shift L) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [Syn.shift,GaussianPolynomialDeterminantTerms.subst_stage,ConciseIPRA.PTm.subst_succ,PTm.subst_mul] using
    stage_step_at (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift j) (var 0) h'.wk hj'.wk ih'.wk hs

def stageSyntax (M P m L w j : PTm n) : BFm n := .imp (.le j m) (.all (succ (j*L)) (.eq
  (entry (Syn.shift (stage M m L w j)) (var 0)) (entry (Syn.shift (stage P m L w j)) (var 0))))
theorem stage_formula (M P m L w j : PTm n) : formula (stageSyntax M P m L w j) = stageLaw M P m L w j := rfl

theorem stage_congruence (M P m L w j : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L)
    (hj : Γ ⊢[PRAAx] le j m) : Γ ⊢[PRAAx] stageEntries M P m L w j := by
  let S := stageSyntax (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)
  have h' : Γ.map Fm.shift ⊢[PRAAx] matrixEntries (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (stageLaw (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) (Syn.shift w) (var 0)) := by
    change Γ ⊢[PRAAx] .all (formula S)
    apply Foundations.BoundedSyntaxInduction.induction S
    · simp only [S,stage_formula,subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (stage_base M P m L w).wk
    · simp only [S,stage_formula,subst_stageLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (stage_step _ _ _ _ _ _ h'.wk.wk Prf.hyp0 (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have gate : Γ ⊢[PRAAx] stageLaw M P m L w j := by
    simpa only [subst_stageLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE gate hj

theorem term_congruence (M P m L w s : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L)
    (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx] entry (term M m L w) s ≐ entry (term P m L w) s :=
  (term_coefficient M m L w s hs).eqTrans ((qmul_congr (.eqRefl _)
    (entry_equal_at _ _ _ _ (stage_congruence M P m L w m h (le_refl _)) ((succ_monus_succ _ _).eqTrans hs))).eqTrans
      (term_coefficient P m L w s hs).eqSymm)

theorem sum_congruence (M P m L t s : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L)
    (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminant.coefficientSum M m L t s ≐ GaussianPolynomialDeterminant.coefficientSum P m L t s := by
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ t _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] matrixEntries (Syn.shift M) (Syn.shift P) (Syn.shift m) (Syn.shift L) := by
    simpa [Δ,Fm.shift,Syn.shift] using h.shift.wk
  have hs' : Δ ⊢[PRAAx] le (Syn.shift s) (Syn.shift m*Syn.shift L) := by
    simpa [Δ,Fm.shift,Syn.shift] using hs.shift.wk
  have left := GaussianPolynomialDeterminant.coefficient_body_at (Γ := Δ)
    (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift s)
  have right := GaussianPolynomialDeterminant.coefficient_body_at (Γ := Δ)
    (Syn.shift P) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift s)
  let w := GaussianPolynomialDeterminant.wordCode (Syn.shift m) (var 0)
  have sameEntries := stage_congruence _ _ _ _ w (Syn.shift m) h' (le_refl _)
  have same : Δ ⊢[PRAAx]
      GaussianPolynomialDeterminant.coefficientTerm (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift s) ≐
      GaussianPolynomialDeterminant.coefficientTerm (Syn.shift P) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift s) :=
    qmul_congr (.eqRefl _) (entry_equal_at _ _ _ _ sameEntries ((succ_monus_succ _ _).eqTrans hs'))
  simpa [Δ,Syn.shift] using left.eqTrans (same.eqTrans right.eqSymm)

theorem determinant_coefficient (M P m L s : PTm n) (h : Γ ⊢[PRAAx] matrixEntries M P m L)
    (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (GaussianPolynomialDeterminant.determinant M m L) s ≐ entry (GaussianPolynomialDeterminant.determinant P m L) s :=
  (GaussianPolynomialDeterminant.coefficient_leibniz M m L s hs).eqTrans
    ((sum_congruence M P m L _ s h hs).eqTrans (GaussianPolynomialDeterminant.coefficient_leibniz P m L s hs).eqSymm)

theorem actual_determinant_coefficient_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (matrixEntries (var 0) (var 1) (var 2) (var 3) ⟶ le (var 4) (var 2*var 3) ⟶
      entry (GaussianPolynomialDeterminant.determinant (var 0) (var 2) (var 3)) (var 4) ≐
        entry (GaussianPolynomialDeterminant.determinant (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (determinant_coefficient _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantCongruence

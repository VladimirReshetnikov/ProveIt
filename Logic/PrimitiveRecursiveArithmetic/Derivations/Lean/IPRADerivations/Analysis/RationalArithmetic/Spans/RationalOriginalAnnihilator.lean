import IPRADerivations.Analysis.RationalArithmetic.Spans.RationalRowSpanGaussianEmbedding
import IPRADerivations.Analysis.LinearAlgebra.Cofactors.GaussianRationalAnnihilatorVector
import IPRADerivations.Analysis.RationalArithmetic.Spans.GaussianRationalRankNullityCriterion

/-!
# The computed annihilator of the original rational rows

Take the real coordinates of the computed Gaussian annihilator of the
embedded matrix. Its free coordinate is the original rational unit. Each
finite dot product uses the original rational row and the returned real
coefficients, and agrees with the real part of the corresponding Gaussian
dot product.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalOriginalAnnihilator

open_ipra
open RationalRowSpanGaussianEmbedding (matrix matrix_shape matrix_lookup realVector real_vector_lookup real_vector_length)
open RationalGaussianEmbedding (embed scalarOne scalarZero)
open RationalArgmin (rationalEq rationalEq_congr)
open GaussianRationalRankNullityCriterion (rank)
open GaussianRationalRowElimination (dotData)
open GaussianPolynomialDeterminantTerms (cell subst_cell)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def dotBody : PTm 2 := RationalArithmetic.multiply (entry (fstT (sndT (var 1))) (var 0))
  (cell (fstT (var 1)) (sndT (sndT (var 1))) (var 0))

def rowDot (A N v r : PTm n) : PTm n := RationalFiniteSum.sum dotBody N (dotData A v r)

def nullRows (A R N v : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift R) ⟶
  rowDot (Syn.shift A) (Syn.shift N) (Syn.shift v) (var 0) ≐ scalarZero)

def free (A R N : PTm n) : PTm n := GaussianRationalAnnihilatorVector.freeColumn (matrix A R N) R N

def vector (A R N : PTm n) : PTm n := realVector (GaussianRationalAnnihilatorVector.vector (matrix A R N) R N) N

def deficit (A R N : PTm n) : Fm PTm n := lt (rank (matrix A R N) R N) N

def certificate (A R N v s : PTm n) : Fm PTm n := length v ≐ N ⋏ (lt s N ⋏ (entry v s ≐ scalarOne ⋏ nullRows A R N v))

ipra_subst rowDot

ipra_subst free

ipra_subst vector

theorem dot_body_at (A v r j : PTm n) : Γ ⊢[PRAAx]
    inst2 dotBody j (dotData A v r) ≐ RationalArithmetic.multiply (entry v j) (cell A r j) := by
  have payload := snd_pair (Γ := Γ) A (pairT v r)
  have hv := (congrFst payload).eqTrans (fst_pair v r)
  have hr := (congrSnd payload).eqTrans (snd_pair v r)
  have ha := fst_pair (Γ := Γ) A (pairT v r)
  simp only [dotBody,dotData,inst2,RationalArithmetic.subst_multiply,subst_entry,subst_cell,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact RationalAlgebra.multiply_congr (entry_congr hv (.eqRefl j)) (entry_congr (entry_congr ha hr) (.eqRefl j))

theorem row_dot_real_part (A R N w r : PTm n) (hr : Γ ⊢[PRAAx] lt r R) : Γ ⊢[PRAAx]
    fstT (GaussianRationalRowElimination.rowDot (matrix A R N) N w r) ≐ rowDot A N (realVector w N) r := by
  refine (RationalGaussianRealPart.real_sum GaussianRationalRowElimination.dotBody N (dotData (matrix A R N) w r)).eqTrans
    (RationalFiniteSum.sum_ext _ _ N _ _ ?_)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  let A' := Syn.shift A
  let R' := Syn.shift R
  let N' := Syn.shift N
  let w' := Syn.shift w
  let r' := Syn.shift r
  have hr' : Δ ⊢[PRAAx] lt r' R' := by simpa only [Δ,r',R',Fm.shift,subst_lt,Syn.shift] using hr.shift.wk
  have hj : Δ ⊢[PRAAx] lt (var 0) N' := Prf.hyp0
  let a := cell A' r' (var 0)
  let z := entry w' (var 0)
  have g := (GaussianRationalRowElimination.dot_body_at (Γ := Δ) (matrix A' R' N') w' r' (var 0)).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (matrix_lookup _ _ _ _ _ hr' hj) (.eqRefl z)).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative (embed a) z))
  have h := (congrFst g).eqTrans (RationalGaussianRealPart.real_product z a)
  have k := (dot_body_at (Γ := Δ) A' (realVector w' N') r' (var 0)).eqTrans
    (RationalAlgebra.multiply_congr (real_vector_lookup w' N' (var 0) hj) (.eqRefl a))
  have val := rationalEq_congr (.eqRefl _) (h.eqTrans k.eqSymm) (.eqRefl _)
  simpa only [Δ,A',R',N',w',r',Syn.shift,RationalFiniteSum.term,RationalGaussianRealPart.realBody,
    inst2,subst_fstT,GaussianRationalRowElimination.subst_dotData,RationalRowSpanGaussianEmbedding.subst_matrix,
    RationalRowSpanGaussianEmbedding.subst_realVector] using val

theorem projected_null_rows (A R N w : PTm n) (h : Γ ⊢[PRAAx]
    GaussianRationalRowElimination.nullRows (matrix A R N) R N w) : Γ ⊢[PRAAx] nullRows A R N (realVector w N) := by
  have h' : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalRowElimination.nullRows
      (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R) (Syn.shift N) (Syn.shift w) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (Syn.shift R) := Prf.hyp0
  have g := GaussianRationalRowElimination.null_at (matrix (Syn.shift A) (Syn.shift R) (Syn.shift N)) (Syn.shift R)
    (Syn.shift N) (Syn.shift w) (var 0) h'.wk hr
  simpa only [Δ,Syn.shift,subst_rowDot,RationalRowSpanGaussianEmbedding.subst_realVector] using
    (row_dot_real_part (Syn.shift A) (Syn.shift R) (Syn.shift N) (Syn.shift w) (var 0) hr).eqSymm.eqTrans
      ((congrFst g).eqTrans RationalGaussianRealPart.real_zero)

theorem certificate_of_deficit (A R N : PTm n) (h : Γ ⊢[PRAAx] deficit A R N) : Γ ⊢[PRAAx]
    certificate A R N (vector A R N) (free A R N) := by
  let M := matrix A R N
  let w := GaussianRationalAnnihilatorVector.vector M R N
  let s := free A R N
  have inp : Γ ⊢[PRAAx] GaussianRationalAnnihilatorVector.input M R N := .andI (matrix_shape A R N) h
  have hs : Γ ⊢[PRAAx] lt s N := .andE₁ (GaussianRationalAnnihilatorVector.free_correct M R N inp)
  have realOne : Γ ⊢[PRAAx] fstT (GaussianRationalReciprocal.qone : PTm n) ≐ scalarOne :=
    ((congrFst RationalGaussianEmbedding.embed_one).eqSymm.eqTrans (fst_pair _ _)).eqTrans
      (RationalNormalForm.normalize_fixed_point _ (RationalNormalForm.normalize_well_formed _ _ (le_refl one)))
  have hit := (real_vector_lookup w N s hs).eqTrans ((congrFst (GaussianRationalAnnihilatorVector.selected_one M R N inp)).eqTrans realOne)
  exact .andI (real_vector_length w N) (.andI hs (.andI hit
    (projected_null_rows A R N w (GaussianRationalAnnihilatorVector.original_null_rows M R N inp))))

def vectorF : PR 3 := PTm.toPR (vector (var 0) (var 1) (var 2))

theorem vector_at (A R N : PTm n) : Γ ⊢[PRAAx] app vectorF ![A,R,N] ≐ vector A R N := by
  simpa [vectorF] using toPR_eq (Γ := Γ) (vector (var 0) (var 1) (var 2) : PTm 3) ![A,R,N]

theorem actual_rational_annihilator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (deficit (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (vector (var 0) (var 1) (var 2))
      (free (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (certificate_of_deficit _ _ _ Prf.hyp0))

theorem actual_rational_annihilator_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (app vectorF ![var 0,var 1,var 2] ≐ vector (var 0) (var 1) (var 2)) := closeUniv 3 (vector_at _ _ _)

end LeanProofs.IPRA.Analysis.RationalOriginalAnnihilator

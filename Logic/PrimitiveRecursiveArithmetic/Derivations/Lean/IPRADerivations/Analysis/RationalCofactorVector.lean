import IPRADerivations.Analysis.RationalCofactorMinorBounds
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual bounded signed cofactor vector

The support is the augmented column mask. On this support take the signed
numerator of the determinant omitting that column. The sign is relative to
the free column's position, so the free entry is the original determinant.
The vector uses the signed-integer sequence encoding of the source matrix
construction. The row expansion which proves annihilation is separate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorVector

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode sequence_length)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg)
open RationalSupMetric (coordinate numeratorOf denominatorOf)
open RationalSelectedMinors (count normalized)
open RationalSubtupleSpan (bit)
open RationalMinorFreeColumn (free free_column_spec bit_cases)
open RationalMinorAugmentation (extendedColumn)
open RationalMinorMaskExtension (new_bit)
open RationalCofactorMinorBounds (bound minorValue cofactor_minor_bound free_minor_nonzero columnMask)
open RationalMaximalMinors (rank bestColumn bestRow)
open RationalArithmetic (select select_zero select_one)
open RationalMatrixClearingBounds (inputMatrix)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def integerPair (x : ZT n) : PTm n := pairT x.pos x.neg
def unpack (x : PTm n) : ZT n := ⟨fstT x,sndT x⟩
def unsignedEntry (P d j : PTm n) : ZT n := numeratorOf (minorValue P d j)
def positionParity (P d j : PTm n) : PTm n := rem (free P d+count j (extendedColumn P d)) two
def signedCode (P d j : PTm n) : PTm n :=
  let a := unsignedEntry P d j
  select (eqb j (free P d))
    (select (eqb (positionParity P d j) zero) (pairT a.neg a.pos) (integerPair a)) (integerPair a)
def coefficientCode (P d j : PTm n) : PTm n :=
  select (bit (extendedColumn P d) j) (pairT zero zero) (signedCode P d j)
def coefficient (P d j : PTm n) : ZT n := unpack (coefficientCode P d j)
def coefficientBody : PTm 2 := coefficientCode (fstT (var 1)) (sndT (var 1)) (var 0)
def vector (P d : PTm n) : PTm n := sequence coefficientBody d (pairT P d)
def vectorF : PR 2 := PTm.toPR (vector (var 0) (var 1))
def run (P d : PTm n) : PTm n := ap2 vectorF P d

@[simp] theorem subst_coefficientCode {k : ℕ} (σ : Fin n → PTm k) (P d j : PTm n) :
    Syn.subst σ (coefficientCode P d j) = coefficientCode (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ j) := by
  simp [coefficientCode,signedCode,integerPair,unsignedEntry,positionParity,minorValue,RationalSupMetric.numeratorOf,rem,two,one]

@[simp] theorem subst_vector {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (vector P d) = vector (Syn.subst σ P) (Syn.subst σ d) := by simp [vector]

theorem unpack_congr {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] ZT.eq (unpack a) (unpack b) := by
  apply ZT.derive
  simp only [unpack,ZT.toZ,natEq (congrFst e),natEq (congrSnd e)]

theorem unpack_pair (a : ZT n) : Γ ⊢[PRAAx] ZT.eq (unpack (integerPair a)) a := by
  apply ZT.derive
  simp only [unpack,integerPair,ZT.toZ,natEq (fst_pair a.pos a.neg),natEq (snd_pair a.pos a.neg)]

theorem code_of_free (P d j : PTm n) (h : Γ ⊢[PRAAx] j ≐ free P d) :
    Γ ⊢[PRAAx] signedCode P d j ≐ integerPair (unsignedEntry P d j) :=
  select_one _ _ _ (eqb_of_eq h)

theorem code_off_free (P d j : PTm n) (h : Γ ⊢[PRAAx] neg (j ≐ free P d)) :
    Γ ⊢[PRAAx] signedCode P d j ≐
      select (eqb (positionParity P d j) zero) (integerPair (-(unsignedEntry P d j))) (integerPair (unsignedEntry P d j)) :=
  select_zero _ _ _ (eqb_of_ne h)

theorem signed_code_abs (P d j : PTm n) : Γ ⊢[PRAAx] zabs (unpack (signedCode P d j)) ≐ zabs (unsignedEntry P d j) := by
  refine .orE (eq_or_ne j (free P d)) ?_ ?_
  · exact (zabs_congr (ZT.toZ_eq (unpack_congr (code_of_free P d j Prf.hyp0)))).eqTrans
      (zabs_congr (ZT.toZ_eq (unpack_pair (unsignedEntry P d j))))
  · have reduced := code_off_free P d j (Prf.hyp0 : neg (j ≐ free P d) :: Γ ⊢[PRAAx] neg (j ≐ free P d))
    refine .orE (eq_or_ne (positionParity P d j) zero) ?_ ?_
    · exact (zabs_congr (ZT.toZ_eq (unpack_congr (reduced.wk.eqTrans (select_one _ _ _ (eqb_of_eq Prf.hyp0)))))).eqTrans
        (zabs_congr (ZT.toZ_eq (unpack_pair (unsignedEntry P d j))))
    · exact ((zabs_congr (ZT.toZ_eq (unpack_congr (reduced.wk.eqTrans (select_zero _ _ _ (eqb_of_ne Prf.hyp0)))))).eqTrans
        (zabs_congr (ZT.toZ_eq (unpack_pair (-(unsignedEntry P d j)))))).eqTrans (zabs_neg _)

theorem coefficient_bound (P d H j : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hH : Γ ⊢[PRAAx] le one H) (hP : Γ ⊢[PRAAx] inputMatrix P d H) :
    Γ ⊢[PRAAx] le (zabs (coefficient P d j)) (bound P d H) := by
  refine .orE (bit_cases j (extendedColumn P d)) ?_ ?_
  · have z : (bit (extendedColumn P d) j ≐ zero) :: Γ ⊢[PRAAx] coefficientCode P d j ≐ integerPair (ZT.ofNat zero) :=
      select_zero _ _ _ Prf.hyp0
    have e := (zabs_congr (ZT.toZ_eq (unpack_congr z))).eqTrans
      ((zabs_congr (ZT.toZ_eq (unpack_pair (ZT.ofNat zero)))).eqTrans (GaussianL1.abs_ofNat zero))
    exact le_congr e.eqSymm (.eqRefl _) (zero_le _)
  · have a : (bit (extendedColumn P d) j ≐ one) :: Γ ⊢[PRAAx] coefficientCode P d j ≐ signedCode P d j :=
      select_one _ _ _ Prf.hyp0
    have e := (zabs_congr (ZT.toZ_eq (unpack_congr a))).eqTrans (signed_code_abs P d j)
    exact le_congr e.eqSymm (.eqRefl _) (cofactor_minor_bound P d j H hr.wk hj.wk Prf.hyp0 hH.wk hP.wk).andE₂

theorem free_coefficient (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] ZT.eq (coefficient P d (free P d)) (unsignedEntry P d (free P d)) := by
  have bitOne := new_bit d (bestColumn P d) (free P d) (free_column_spec P d h).andE₁
  have e : Γ ⊢[PRAAx] coefficientCode P d (free P d) ≐ integerPair (unsignedEntry P d (free P d)) :=
    (select_one _ _ _ bitOne).eqTrans (code_of_free _ _ _ (.eqRefl _))
  exact ZT.derive ((ZT.toZ_eq (unpack_congr e)).trans (ZT.toZ_eq (unpack_pair _)))

theorem vector_length (P d : PTm n) : Γ ⊢[PRAAx] length (vector P d) ≐ d := sequence_length _ _ _

theorem vector_lookup (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) :
    Γ ⊢[PRAAx] entry (vector P d) j ≐ coefficientCode P d j := by
  refine (sequence_decode coefficientBody (x := pairT P d) hj).eqTrans ?_
  ipra_congr (coefficientCode (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl j] using [coefficientBody, inst2]

theorem vector_coordinate (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) :
    Γ ⊢[PRAAx] ZT.eq (coordinate (vector P d) j) (coefficient P d j) :=
  unpack_congr (vector_lookup P d j hj)

theorem vector_bound (P d H j : PTm n) (hr : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hH : Γ ⊢[PRAAx] le one H) (hP : Γ ⊢[PRAAx] inputMatrix P d H) :
    Γ ⊢[PRAAx] le (zabs (coordinate (vector P d) j)) (bound P d H) :=
  le_congr (zabs_congr (ZT.toZ_eq (vector_coordinate P d j hj))).eqSymm (.eqRefl _) (coefficient_bound P d H j hr hj hH hP)

theorem vector_zero (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) (b : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ zero) :
    Γ ⊢[PRAAx] ZT.eq (coordinate (vector P d) j) (ZT.ofNat zero) := by
  have code : Γ ⊢[PRAAx] coefficientCode P d j ≐ integerPair (ZT.ofNat zero) := select_zero _ _ _ b
  have eq := unpack_congr ((vector_lookup P d j hj).eqTrans code)
  exact ZT.derive ((ZT.toZ_eq eq).trans (ZT.toZ_eq (unpack_pair _)))

theorem vector_free (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] ZT.eq (coordinate (vector P d) (free P d)) (unsignedEntry P d (free P d)) := by
  have atFree := vector_coordinate P d (free P d) (free_column_spec P d h).andE₁
  exact ZT.derive ((ZT.toZ_eq atFree).trans (ZT.toZ_eq (free_coefficient P d h)))

theorem vector_nonzero (P d : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) :
    Γ ⊢[PRAAx] neg (ZT.eq (coordinate (vector P d) (free P d)) (ZT.ofNat zero)) := by
  refine .impI (.impE (free_minor_nonzero P d).wk ?_)
  let a := minorValue P d (free P d)
  let Δ := ZT.eq (coordinate (vector P d) (free P d)) (ZT.ofNat zero) :: Γ
  have freeEntry : Δ ⊢[PRAAx] ZT.eq (coordinate (vector P d) (free P d)) (numeratorOf a) := (vector_free P d h).wk
  have zeroEntry := (ZT.toZ_eq freeEntry).symm.trans (ZT.toZ_eq (Prf.hyp0 : Δ ⊢[PRAAx] ZT.eq (coordinate (vector P d) (free P d)) (ZT.ofNat zero)))
  apply RationalFiniteSum.canonical_equal a RationalGaussianEmbedding.scalarZero (numeratorOf a) (ZT.ofNat zero) (denominatorOf a) one
    (RationalScalarDeterminantGaussianEmbedding.determinant_well_formed _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) (RationalRepresentations.represents_self a)
    (RationalGaussianEmbedding.scalar_zero_represents one) (RationalArgmin.denominator_positive a) (le_refl one)
  apply ZT.derive
  change ZT.toZ Δ (numeratorOf a * ZT.ofNat one) = ZT.toZ Δ (ZT.ofNat zero * ZT.ofNat (denominatorOf a))
  rw [ZT.toZ_mul,ZT.toZ_mul,zeroEntry]
  simp

theorem program_at (P d : PTm n) : Γ ⊢[PRAAx] run P d ≐ vector P d := by
  simpa [run,vectorF,ap2] using toPR_eq (Γ := Γ) (vector (var 0) (var 1) : PTm 2) ![P,d]

theorem actual_cofactor_vector_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ vector (var 0) (var 1)) := closeUniv 2 (program_at _ _)

theorem actual_cofactor_vector_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 3) (var 1) ⟶ le one (var 2) ⟶ inputMatrix (var 0) (var 1) (var 2) ⟶
      le (zabs (coordinate (vector (var 0) (var 1)) (var 3))) (bound (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (vector_bound _ _ _ _ (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

theorem actual_cofactor_vector_free_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (rank (var 0) (var 1)) (var 1) ⟶ ZT.eq (coordinate (vector (var 0) (var 1)) (free (var 0) (var 1)))
      (unsignedEntry (var 0) (var 1) (free (var 0) (var 1)))) := closeUniv 2 (.impI (vector_free _ _ Prf.hyp0))

theorem actual_cofactor_vector_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (rank (var 0) (var 1)) (var 1) ⟶ neg (ZT.eq (coordinate (vector (var 0) (var 1)) (free (var 0) (var 1))) (ZT.ofNat zero))) :=
  closeUniv 2 (.impI (vector_nonzero _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalCofactorVector

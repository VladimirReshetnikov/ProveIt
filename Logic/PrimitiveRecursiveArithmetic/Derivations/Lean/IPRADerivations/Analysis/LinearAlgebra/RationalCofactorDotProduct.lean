import IPRADerivations.Analysis.LinearAlgebra.RationalCofactorBorderedMinors
import IPRADerivations.Analysis.Polynomials.RationalCofactorCoefficientValues
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual cofactor vector annihilates the cleared rows

The ordered supported terms are the terms of the bordered last-row
expansion up to a common unit. Filtering preserves the full dot product
because the actual returned vector is zero away from the enlarged mask.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorDotProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open RationalMaximalMinors (rank)
open RationalMinorFreeColumn (free bit_cases)
open RationalMinorAugmentation (extendedColumn extended_column_size)
open RationalCofactorSupport (supportedColumn common_unit)
open RationalCofactorCoefficientValues (coefficientValue subst_coefficientValue cofactor_embedded_at zero_value)
open RationalCofactorBorderedRows (bordered clearedCell data subst_clearedCell subst_data bordered_determinant_zero)
open RationalCofactorBorderedMinors (minor_determinant last_supported_cell)
open RationalSelectedMinors (count)
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalGaussianEmbedding (embed embed_zero)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianRationalHorner (qmul qzero subst_qmul)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qmul_zero_left qmul_zero_right)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalFiniteSum (sum termsEqual sum_index_congr sum_multiply multiplyBody multiply_body_at)
open GaussianRationalBlockSums (selectedBody maskBody filteredData filtered_sum selected_list_at mask_zero mask_kept)
open GaussianScalarDeterminantLaplace (unitSign sign_bit_even sign_bit_odd summand rowWeight expansion expansionBody
  expansion_body_at last_row_expansion)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clearedTerm (P d i j : PTm n) : PTm n :=
  qmul (embed (coefficientValue P d j)) (clearedCell P d i j)

def clearedBody : PTm 2 :=
  clearedTerm (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

def clearedDot (P d i : PTm n) : PTm n := sum clearedBody d (data P d i)

def supportDot (P d i : PTm n) : PTm n :=
  sum (selectedBody bitBody clearedBody) (count d (extendedColumn P d))
    (filteredData d (extendedColumn P d) (data P d i))

@[simp] theorem subst_clearedTerm {k : ℕ} (σ : Fin n → PTm k) (P d i j : PTm n) :
    Syn.subst σ (clearedTerm P d i j) =
      clearedTerm (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ j) := by
  simp [clearedTerm]

@[simp] theorem subst_clearedDot {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (clearedDot P d i) = clearedDot (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by
  simp [clearedDot]

theorem cleared_term_congr {P Q d e i k j l : PTm n} (hP : Γ ⊢[PRAAx] P ≐ Q)
    (hd : Γ ⊢[PRAAx] d ≐ e) (hi : Γ ⊢[PRAAx] i ≐ k) (hj : Γ ⊢[PRAAx] j ≐ l) :
    Γ ⊢[PRAAx] clearedTerm P d i j ≐ clearedTerm Q e k l := by
  ipra_congr (clearedTerm (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hP, hd, hi, hj]

theorem cleared_body_at (P d i j : PTm n) :
    Γ ⊢[PRAAx] inst2 clearedBody j (data P d i) ≐ clearedTerm P d i j := by
  simp only [clearedBody,inst2,subst_clearedTerm,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact cleared_term_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _)

theorem supported_body_at (P d i r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count d (extendedColumn P d))) :
    Γ ⊢[PRAAx] inst2 (selectedBody bitBody clearedBody) r (filteredData d (extendedColumn P d) (data P d i)) ≐
      clearedTerm P d i (supportedColumn P d r) :=
  (selected_list_at bitBody clearedBody d (extendedColumn P d) (data P d i) r hr).eqTrans
    (cleared_body_at P d i (supportedColumn P d r))

private theorem masked_term (P d i j : PTm n) (hj : Γ ⊢[PRAAx] lt j d) : Γ ⊢[PRAAx]
    inst2 (maskBody bitBody clearedBody) j (pairT (extendedColumn P d) (data P d i)) ≐
      inst2 clearedBody j (data P d i) := by
  let C := extendedColumn P d
  refine .orE (bit_cases j C) ?_ ?_
  · have hz : (bit C j ≐ zero) :: Γ ⊢[PRAAx] inst2 bitBody j C ≐ zero := by
      rw [bit_body_at]
      exact Prf.hyp0
    have hterm := (qmul_congr ((embed_congr (zero_value P d j hj.wk Prf.hyp0)).eqTrans embed_zero)
      (.eqRefl (clearedCell P d i j))).eqTrans (qmul_zero_left _)
    exact (mask_zero bitBody clearedBody C (data P d i) j hz).eqTrans
      ((cleared_body_at P d i j).eqTrans hterm).eqSymm
  · apply mask_kept
    rw [bit_body_at]
    exact .impI (succ_ne_zero (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))

theorem support_eq_full (P d i : PTm n) : Γ ⊢[PRAAx] supportDot P d i ≐ clearedDot P d i := by
  let C := extendedColumn P d
  let x := data P d i
  have ht : Γ ⊢[PRAAx] termsEqual (maskBody bitBody clearedBody) clearedBody d (pairT C x) x := by
    refine .allI (.impI ?_)
    simpa only [C,x,Syn.shift,subst_pairT,RationalMinorAugmentation.subst_extendedColumn,subst_data] using
      masked_term (Syn.shift P) (Syn.shift d) (Syn.shift i) (var 0) Prf.hyp0
  exact (filtered_sum bitBody clearedBody d C x).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded (maskBody bitBody clearedBody) clearedBody d (pairT C x) x ht)

private theorem rearrange_sign (u v a b : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul (qmul u v) a) b ≐ qmul u (qmul (qmul v b) a) :=
  (qmul_associative (qmul u v) a b).eqTrans
    ((qmul_associative u v (qmul a b)).eqTrans
      ((qmul_congr (.eqRefl u) (qmul_congr (.eqRefl v) (qmul_commutative a b))).eqTrans
        (qmul_congr (.eqRefl u) (qmul_associative v b a).eqSymm)))

theorem laplace_term (P d i r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) : Γ ⊢[PRAAx]
    summand (bordered P d i) (rank P d) r ≐
      qmul (unitSign (rank P d+free P d)) (clearedTerm P d i (supportedColumn P d r)) := by
  let m := rank P d
  let c := free P d
  let j := supportedColumn P d r
  let a := clearedCell P d i j
  let b := embed (RationalCofactorMinorBounds.minorValue P d j)
  have hs : Γ ⊢[PRAAx] lt r (count d (extendedColumn P d)) :=
    lt_congr (.eqRefl _) (extended_column_size P d h).eqSymm hr
  exact (qmul_congr (qmul_congr (common_unit m c r) (last_supported_cell P d i r hr))
    (minor_determinant P d i r h hr)).eqTrans
    ((rearrange_sign (unitSign (m+c)) (unitSign (c+r)) a b).eqTrans
      (qmul_congr (.eqRefl _) (qmul_congr (cofactor_embedded_at P d r h hs).eqSymm (.eqRefl _))))

private theorem expansion_term (P d i r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hr : Γ ⊢[PRAAx] lt r (count d (extendedColumn P d))) : Γ ⊢[PRAAx]
    inst2 expansionBody r (pairT (bordered P d i) (rank P d)) ≐
      inst2 (multiplyBody (selectedBody bitBody clearedBody)) r
        (pairT (unitSign (rank P d+free P d)) (filteredData d (extendedColumn P d) (data P d i))) :=
  (expansion_body_at _ _ _).eqTrans
    ((laplace_term P d i r h (lt_congr (.eqRefl _) (extended_column_size P d h) hr)).eqTrans
      ((multiply_body_at _ _ _ _).eqTrans
        (qmul_congr (.eqRefl _) (supported_body_at P d i r hr))).eqSymm)

theorem expansion_eq_signed_dot (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) : Γ ⊢[PRAAx]
    expansion (bordered P d i) (rank P d) ≐ qmul (unitSign (rank P d+free P d)) (clearedDot P d i) := by
  let C := extendedColumn P d
  let L := count d C
  let U := unitSign (rank P d+free P d)
  let X := filteredData d C (data P d i)
  have hh : Γ.map Fm.shift ⊢[PRAAx] lt (rank (Syn.shift P) (Syn.shift d)) (Syn.shift d) := by
    simpa only [Fm.shift,subst_lt,RationalMaximalMinors.subst_rank,Syn.shift] using h.shift
  let Y := pairT (bordered P d i) (rank P d)
  let B := selectedBody bitBody clearedBody
  have ht : Γ ⊢[PRAAx] termsEqual expansionBody (multiplyBody B) L Y (pairT U X) := by
    refine .allI (.impI ?_)
    simpa only [Y,U,X,L,C,Syn.shift,subst_pairT,PTm.subst_add,RationalSelectedMinors.subst_count,RationalMaximalMinors.subst_rank,
      RationalMinorFreeColumn.subst_free,RationalCofactorBorderedRows.subst_bordered,
      GaussianScalarDeterminantLaplace.subst_unitSign,GaussianRationalBlockSums.filteredData,
      RationalMinorAugmentation.subst_extendedColumn,subst_data] using
      expansion_term (Syn.shift P) (Syn.shift d) (Syn.shift i) (var 0) hh.wk Prf.hyp0
  exact (sum_index_congr expansionBody (extended_column_size P d h).eqSymm (.eqRefl Y)).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded expansionBody (multiplyBody B) L Y (pairT U X) ht).eqTrans
      ((sum_multiply B U L X).eqTrans (qmul_congr (.eqRefl U) (support_eq_full P d i))))

private theorem unit_square (k : PTm n) : Γ ⊢[PRAAx] qmul (unitSign k) (unitSign k) ≐ qone := by
  refine .orE (par_cases k) ?_ ?_
  · have e := sign_bit_even (par k) (Γ := (par k ≐ zero) :: Γ) Prf.hyp0
    exact (qmul_congr e e).eqTrans (qmul_one_right _ qone_canonical)
  · have e := sign_bit_odd (par k) (Γ := (par k ≐ one) :: Γ) Prf.hyp0
    exact (qmul_congr e e).eqTrans ((GaussianScalarColumnSelection.negative_both_product _ _).eqTrans
      (qmul_one_right _ qone_canonical))

theorem cleared_dot_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx] clearedDot P d i ≐ qzero := by
  let U := unitSign (rank P d+free P d)
  let z := clearedDot P d i
  have hu : Γ ⊢[PRAAx] qmul U z ≐ qzero := (expansion_eq_signed_dot P d i h).eqSymm.eqTrans
    ((last_row_expansion (bordered P d i) (rank P d)).eqSymm.eqTrans (bordered_determinant_zero P d i h hi))
  have hz : Γ ⊢[PRAAx] GaussianRationalHorner.canonical z := GaussianRationalFiniteSum.sum_canonical clearedBody d (data P d i)
  exact ((qmul_commutative qone z).eqTrans (qmul_one_right z hz)).eqSymm.eqTrans
    ((qmul_congr (unit_square (rank P d+free P d)).eqSymm (.eqRefl z)).eqTrans
      ((qmul_associative U U z).eqTrans
        ((qmul_congr (.eqRefl U) hu).eqTrans (qmul_zero_right U))))

theorem actual_cleared_cofactor_dot_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶
      lt (var 2) (length (var 0)) ⟶ clearedDot (var 0) (var 1) (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (cleared_dot_zero _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCofactorDotProduct

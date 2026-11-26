import IPRADerivations.Analysis.LinearAlgebra.RationalMatrixClearingBounds
import IPRADerivations.Analysis.RationalArithmetic.RationalSubtupleSpan
import IPRADerivations.Analysis.LinearAlgebra.RationalScalarDeterminantGaussianEmbedding
import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarDiagonalDeterminant
import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarDeterminantMultiplication
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerNonzero
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.LinearCombination

/-!
# Actual rational minors and their denominator-cleared counterparts

The original row and column masks select the same increasing indices in
both matrices. The cleared minor reads the actual integer entries from
the single global denominator-clearing program before presenting them as
denominator-one rationals for the existing determinant.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSelectedMinors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalSubtupleSpan (bit bitBody bit_body_at)
open RationalMatrixClearingBounds (cleared_representation)
open RationalSupMetric (coordinate commonDenominator normalizedList)
open RationalIntegerNormalization (normalize)
open RationalGaussianEmbedding (embed embed_multiply scalarZero)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalFiberVandermonde (table table_lookup table_length table_row_length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def count (N mask : PTm n) : PTm n := Foundations.FilteredEnumerationCode.count bitBody N mask
def indices (N mask : PTm n) : PTm n := Foundations.FilteredEnumerationCode.list bitBody N mask
def index (N mask i : PTm n) : PTm n := entry (indices N mask) i

@[simp] theorem subst_count {k : ℕ} (σ : Fin n → PTm k) (N mask : PTm n) :
    Syn.subst σ (count N mask) = count (Syn.subst σ N) (Syn.subst σ mask) := by simp [count]
@[simp] theorem subst_indices {k : ℕ} (σ : Fin n → PTm k) (N mask : PTm n) :
    Syn.subst σ (indices N mask) = indices (Syn.subst σ N) (Syn.subst σ mask) := by simp [indices]
@[simp] theorem subst_index {k : ℕ} (σ : Fin n → PTm k) (N mask i : PTm n) :
    Syn.subst σ (index N mask i) = index (Syn.subst σ N) (Syn.subst σ mask) (Syn.subst σ i) := by simp [index]

theorem count_bound (N mask : PTm n) : Γ ⊢[PRAAx] le (count N mask) N := Foundations.FilteredEnumerationCode.count_le _ _ _
theorem indices_length (N mask : PTm n) : Γ ⊢[PRAAx] length (indices N mask) ≐ count N mask :=
  Foundations.FilteredEnumerationCode.list_length _ _ _
theorem index_bound (N mask i : PTm n) (hi : Γ ⊢[PRAAx] lt i (count N mask)) :
    Γ ⊢[PRAAx] lt (index N mask i) N := Foundations.FilteredEnumerationCode.entry_bound _ _ _ _ hi
theorem index_increasing (N mask i j : PTm n) (hij : Γ ⊢[PRAAx] lt i j) (hj : Γ ⊢[PRAAx] lt j (count N mask)) :
    Γ ⊢[PRAAx] lt (index N mask i) (index N mask j) := Foundations.FilteredEnumerationCode.increasing _ _ _ _ _ hij hj
theorem index_selected (N mask i : PTm n) (hi : Γ ⊢[PRAAx] lt i (count N mask)) :
    Γ ⊢[PRAAx] neg (bit mask (index N mask i) ≐ zero) := by
  simpa only [index,indices,bit_body_at] using
    Foundations.FilteredEnumerationCode.entry_valid (Γ := Γ) bitBody N mask i hi

theorem selected_listed (N mask i : PTm n) (hi : Γ ⊢[PRAAx] lt i N)
    (hb : Γ ⊢[PRAAx] neg (bit mask i ≐ zero)) : Γ ⊢[PRAAx]
    lt (Foundations.FilteredEnumeration.rank bitBody i mask) (count N mask) ⋏
      index N mask (Foundations.FilteredEnumeration.rank bitBody i mask) ≐ i :=
  Foundations.FilteredEnumerationCode.listed bitBody N mask i hi (by simpa only [bit_body_at] using hb)

def selectedBody : PTm 3 := cell (fstT (var 2)) (entry (fstT (sndT (var 2))) (var 0))
  (entry (sndT (sndT (var 2))) (var 1))
def selectedData (A M N R C : PTm n) : PTm n := pairT A (pairT (indices M R) (indices N C))
def selected (A M N R C : PTm n) : PTm n :=
  table selectedBody (count M R) (count N C) (selectedData A M N R C)

@[simp] theorem subst_selectedData {k : ℕ} (σ : Fin n → PTm k) (A M N R C : PTm n) :
    Syn.subst σ (selectedData A M N R C) =
      selectedData (Syn.subst σ A) (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ C) := by
  simp [selectedData]
@[simp] theorem subst_selected {k : ℕ} (σ : Fin n → PTm k) (A M N R C : PTm n) :
    Syn.subst σ (selected A M N R C) =
      selected (Syn.subst σ A) (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ C) := by simp [selected]

theorem selected_length (A M N R C : PTm n) : Γ ⊢[PRAAx] length (selected A M N R C) ≐ count M R :=
  table_length _ _ _ _
theorem selected_row_length (A M N R C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (count M R)) :
    Γ ⊢[PRAAx] length (entry (selected A M N R C) i) ≐ count N C := table_row_length _ _ _ _ _ hi

theorem selected_lookup (A M N R C i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (count M R))
    (hj : Γ ⊢[PRAAx] lt j (count N C)) : Γ ⊢[PRAAx]
    cell (selected A M N R C) i j ≐ cell A (index M R i) (index N C j) := by
  refine (table_lookup _ _ _ _ _ _ hi hj).eqTrans ?_
  simp only [selectedBody,GaussianPolynomialDeterminantTerms.subst_cell,Foundations.MasterCertificate.subst_entry,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact entry_congr (entry_congr (fst_pair _ _) (entry_congr ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _)))
    (entry_congr ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _))

def fromInteger (a : PTm n) : PTm n := normalize (⟨fstT a,sndT a⟩ : ZT n) one
def integerBody : PTm 3 := fromInteger (cell (var 2) (var 0) (var 1))
def presentIntegers (S I J : PTm n) : PTm n := table integerBody I J S
def original (P d R C : PTm n) : PTm n := selected P (length P) d R C
def normalized (P d R C : PTm n) : PTm n := presentIntegers
  (selected (normalizedList P d) (length P) d R C) (count (length P) R) (count d C)

@[simp] theorem subst_fromInteger {k : ℕ} (σ : Fin n → PTm k) (a : PTm n) :
    Syn.subst σ (fromInteger a) = fromInteger (Syn.subst σ a) := by simp [fromInteger,ZT.subst]
@[simp] theorem subst_original {k : ℕ} (σ : Fin n → PTm k) (P d R C : PTm n) :
    Syn.subst σ (original P d R C) = original (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ R) (Syn.subst σ C) := by
  simp [original]
@[simp] theorem subst_normalized {k : ℕ} (σ : Fin n → PTm k) (P d R C : PTm n) :
    Syn.subst σ (normalized P d R C) = normalized (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ R) (Syn.subst σ C) := by
  simp [normalized,presentIntegers]

theorem from_integer_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] fromInteger a ≐ fromInteger b := by
  ipra_congr (fromInteger (var 0) : PTm 1) with [h]

theorem normalized_lookup (P d R C i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (count (length P) R))
    (hj : Γ ⊢[PRAAx] lt j (count d C)) : Γ ⊢[PRAAx]
    cell (normalized P d R C) i j ≐ normalize
      (coordinate (entry (normalizedList P d) (index (length P) R i)) (index d C j)) one := by
  have e : Γ ⊢[PRAAx] cell (normalized P d R C) i j ≐
      fromInteger (cell (selected (normalizedList P d) (length P) d R C) i j) := by
    simpa [normalized,presentIntegers,integerBody] using
      table_lookup (Γ := Γ) integerBody (count (length P) R) (count d C)
        (selected (normalizedList P d) (length P) d R C) i j hi hj
  exact e.eqTrans (from_integer_congr (selected_lookup _ _ _ _ _ _ _ hi hj))

theorem normalized_cell_scale (P d R C i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (count (length P) R))
    (hj : Γ ⊢[PRAAx] lt j (count d C)) : Γ ⊢[PRAAx]
    embed (cell (normalized P d R C) i j) ≐
      GaussianRationalHorner.qmul (embed (GaussianRationalSyntheticBounds.natCode (commonDenominator P d)))
        (embed (cell (original P d R C) i j)) := by
  let D := commonDenominator P d
  let r := index (length P) R i
  let c := index d C j
  let q := cell P r c
  let a := coordinate (entry (normalizedList P d) r) c
  let s := GaussianRationalSyntheticBounds.natCode D
  have hD : Γ ⊢[PRAAx] le one D := RationalSupMetric.commonDenominator_one_le P d
  have scaled := RationalRepresentations.represents_multiply (Γ := Γ) s q (ZT.ofNat D) a one D
    (GaussianRationalSyntheticBounds.natCode_represents D) (cleared_representation P d r c (index_bound _ _ _ hi) (index_bound _ _ _ hj))
  have value : Γ ⊢[PRAAx] RationalArithmetic.multiply s q ≐ normalize a one := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
      (RationalNormalForm.normalize_well_formed a one (le_refl one)) scaled
      (RationalIntegerNormalization.normalize_preserves_value a one (le_refl one))
      (GaussianRationalHorner.positive_product _ _ (le_refl one) hD) (le_refl one)
    ipra_lc
  exact (embed_congr ((normalized_lookup P d R C i j hi hj).eqTrans value.eqSymm)).eqTrans
    ((embed_multiply _ _).eqTrans (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (embed_congr (selected_lookup P (length P) d R C i j hi hj)).eqSymm))

open RationalScalarDeterminantGaussianEmbedding (determinant determinant_embedding)
open RationalRowSpanGaussianEmbedding (matrix matrix_lookup)
open GaussianScalarDiagonalDeterminant (diagonal diagonal_left_action diagonal_det weight_upper)
open GaussianRationalMatrixFiniteSums (matrixProduct)
open GaussianScalarDeterminant (scalarDet scalarCellsEqual scalar_det_congr)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianRationalReciprocal (power)

def scale (P d : PTm n) : PTm n := embed (GaussianRationalSyntheticBounds.natCode (commonDenominator P d))

@[simp] theorem subst_scale {k : ℕ} (σ : Fin n → PTm k) (P d : PTm n) :
    Syn.subst σ (scale P d) = scale (Syn.subst σ P) (Syn.subst σ d) := by simp [scale]

theorem normalized_embedded_cell (P d R C k i j : PTm n) (hR : Γ ⊢[PRAAx] k ≐ count (length P) R)
    (hC : Γ ⊢[PRAAx] k ≐ count d C) (hi : Γ ⊢[PRAAx] lt i k) (hj : Γ ⊢[PRAAx] lt j k) : Γ ⊢[PRAAx]
    cell (matrix (normalized P d R C) k k) i j ≐
      cell (matrixProduct (diagonal (scale P d) k k) (matrix (original P d R C) k k) k) i j := by
  have l := (matrix_lookup (normalized P d R C) k k i j hi hj).eqTrans
    (normalized_cell_scale P d R C i j (lt_congr (.eqRefl _) hR hi) (lt_congr (.eqRefl _) hC hj))
  have r := (diagonal_left_action (scale P d) k k (matrix (original P d R C) k k) i j hi hj).eqTrans
    (qmul_congr (weight_upper _ _ _ hi) (matrix_lookup (original P d R C) k k i j hi hj))
  exact l.eqTrans r.eqSymm

theorem normalized_embedded_cells (P d R C k : PTm n) (hR : Γ ⊢[PRAAx] k ≐ count (length P) R)
    (hC : Γ ⊢[PRAAx] k ≐ count d C) : Γ ⊢[PRAAx]
    scalarCellsEqual (matrix (normalized P d R C) k k)
      (matrixProduct (diagonal (scale P d) k k) (matrix (original P d R C) k k) k) k := by
  refine .allI (.impI (.allI (.impI ?_)))
  let shift2 (a : PTm n) := Syn.shift (Syn.shift a)
  let K := shift2 k
  let Δ := lt (var 0) K :: lt (var 1) K :: (Γ.map Fm.shift).map Fm.shift
  have r : Δ ⊢[PRAAx] K ≐ count (length (shift2 P)) (shift2 R) := by
    simpa only [Δ,K,shift2,Fm.shift,Fm.subst_eq,subst_count,Foundations.SequenceComposition.subst_length,Syn.shift] using
      hR.shift.shift.wk.wk
  have c : Δ ⊢[PRAAx] K ≐ count (shift2 d) (shift2 C) := by
    simpa only [Δ,K,shift2,Fm.shift,Fm.subst_eq,subst_count,Syn.shift] using hC.shift.shift.wk.wk
  have values := GaussianRationalValueEquality.value_equal_of_code
    (normalized_embedded_cell (shift2 P) (shift2 d) (shift2 R) (shift2 C) K (var 1) (var 0) r c Prf.hyp1 Prf.hyp0)
  simpa [Δ,K,shift2,Fm.shift,Syn.shift] using values

theorem normalized_determinant_scale (P d R C k : PTm n) (hR : Γ ⊢[PRAAx] k ≐ count (length P) R)
    (hC : Γ ⊢[PRAAx] k ≐ count d C) : Γ ⊢[PRAAx]
    embed (determinant (normalized P d R C) k) ≐ qmul (power (scale P d) k)
      (embed (determinant (original P d R C) k)) := by
  let A := matrix (original P d R C) k k
  let D := diagonal (scale P d) k k
  exact (determinant_embedding _ _).eqTrans ((scalar_det_congr _ _ _ (normalized_embedded_cells P d R C k hR hC)).eqTrans
    ((GaussianScalarDeterminantMultiplication.scalar_det_multiply D A k).eqTrans
      (qmul_congr (diagonal_det _ _ _ (le_refl _)) (determinant_embedding _ _).eqSymm)))

theorem positive_scale_nonzero (P d : PTm n) : Γ ⊢[PRAAx] neg (scale P d ≐ qzero) := by
  refine .impI ?_
  let D := commonDenominator P d
  let s := GaussianRationalSyntheticBounds.natCode D
  let Δ := (scale P d ≐ qzero) :: Γ
  have eq : Δ ⊢[PRAAx] embed s ≐ embed scalarZero := Prf.hyp0.eqTrans RationalGaussianEmbedding.embed_zero.eqSymm
  have original : Δ ⊢[PRAAx] s ≐ scalarZero :=
    RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding s scalarZero
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
      (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) eq
  have zeroValue := GaussianRationalHorner.scalar_congr original.eqSymm (ZT.derive rfl) (.eqRefl one)
    (RationalGaussianEmbedding.scalar_zero_represents one)
  have cross := GaussianDominantPairAlgebra.scalar_representation_cross s (ZT.ofNat D) (ZT.ofNat zero) one one
    (GaussianRationalSyntheticBounds.natCode_represents D) zeroValue
  have hz : Δ ⊢[PRAAx] D ≐ zero := by
    apply deriveNat
    simpa only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_one,map_one,mul_one] using ZT.toZ_eq cross
  exact le_lt_absurd _ ((le_congr (.eqRefl _) hz (RationalSupMetric.commonDenominator_one_le _ _)) : Δ ⊢[PRAAx] le one zero)
    (zero_lt_succ zero)

theorem normalized_determinant_zero_iff (P d R C k : PTm n) (hR : Γ ⊢[PRAAx] k ≐ count (length P) R)
    (hC : Γ ⊢[PRAAx] k ≐ count d C) : Γ ⊢[PRAAx]
    Fm.iff (embed (determinant (normalized P d R C) k) ≐ qzero) (embed (determinant (original P d R C) k) ≐ qzero) := by
  let a := embed (determinant (original P d R C) k)
  let u := power (scale P d) k
  have equation := normalized_determinant_scale P d R C k hR hC
  have hc := RationalGaussianEmbedding.embed_canonical (Γ := Γ) (determinant (original P d R C) k)
  have hu := GaussianRationalReciprocal.power_canonical (Γ := Γ) (scale P d) k
  have hn : Γ ⊢[PRAAx] neg (u ≐ qzero) := GaussianRationalPowerNonzero.power_nonzero _ _
    (RationalGaussianEmbedding.embed_canonical _) (positive_scale_nonzero _ _)
  refine .andI (.impI (.orE (eq_or_ne a qzero) Prf.hyp0 ?_)) (.impI ?_)
  · let Δ := neg (a ≐ qzero) :: (embed (determinant (normalized P d R C) k) ≐ qzero) :: Γ
    have nz : Δ ⊢[PRAAx] neg (qmul u a ≐ qzero) :=
      GaussianRationalPolynomialProductDegree.multiply_nonzero u a hu.wk.wk hc.wk.wk hn.wk.wk Prf.hyp0
    exact .botE _ (.impE nz (equation.wk.wk.eqSymm.eqTrans Prf.hyp1))
  · exact equation.wk.eqTrans ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans (qmul_zero_right _))

theorem actual_minor_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 5) (count (var 1) (var 3)) ⟶ lt (var 6) (count (var 2) (var 4)) ⟶
      cell (selected (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) (var 6) ≐
        cell (var 0) (index (var 1) (var 3) (var 5)) (index (var 2) (var 4) (var 6))) :=
  closeUniv 7 (.impI (.impI (selected_lookup (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) Prf.hyp1 Prf.hyp0)))

theorem actual_cleared_minor_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (var 4 ≐ count (length (var 0)) (var 2) ⟶ var 4 ≐ count (var 1) (var 3) ⟶
      embed (determinant (normalized (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐
        qmul (power (scale (var 0) (var 1)) (var 4)) (embed (determinant (original (var 0) (var 1) (var 2) (var 3)) (var 4)))) :=
  closeUniv 5 (.impI (.impI (normalized_determinant_scale (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1 Prf.hyp0)))

theorem actual_cleared_minor_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (var 4 ≐ count (length (var 0)) (var 2) ⟶ var 4 ≐ count (var 1) (var 3) ⟶
      Fm.iff (embed (determinant (normalized (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐ qzero)
        (embed (determinant (original (var 0) (var 1) (var 2) (var 3)) (var 4)) ≐ qzero)) :=
  closeUniv 5 (.impI (.impI (normalized_determinant_zero_iff (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalSelectedMinors

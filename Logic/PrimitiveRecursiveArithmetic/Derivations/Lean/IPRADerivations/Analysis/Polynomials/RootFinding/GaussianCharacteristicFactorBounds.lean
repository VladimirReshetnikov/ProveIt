import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianCharacteristicEntryNorm
import IPRADerivations.Analysis.Polynomials.Elimination.GaussianRationalRowElimination

/-!
# Original matrix-entry bounds for actual characteristic word factors

Every bounded original row/column is read at the actual runtime word digit.
The characteristic table, polynomial factor and coefficient subtraction are
the existing programs. No successful-word, table norm or determinant law is
an input. The original square shapes are retained in the source bundle.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicFactorBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalCharacteristicPolynomial (characteristicTable cellPolynomial table_shape table_lookup_at)
open GaussianPolynomialDeterminantTerms (cell factor tableShape)
open GaussianCoefficientL1 (coefficientNorm subCoefficients)
open GaussianCoefficientNormOrder (coefficientNorm_congr subCoefficients_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticBounds (natCode)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (digit digit_bound)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBounds (A N B r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  bounded (cell (Syn.shift A) (Syn.shift r) (var 0)) (Syn.shift B) one)
def entryBounds (A N B : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  rowBounds (Syn.shift A) (Syn.shift N) (Syn.shift B) (var 0))
def rowDistances (A C N P Q r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  distanceBounded (cell (Syn.shift A) (Syn.shift r) (var 0)) (cell (Syn.shift C) (Syn.shift r) (var 0))
    (Syn.shift P) (Syn.shift Q))
def entryDistances (A C N P Q : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift N) ⟶
  rowDistances (Syn.shift A) (Syn.shift C) (Syn.shift N) (Syn.shift P) (Syn.shift Q) (var 0))
def input (A C N B P Q : PTm n) : Fm PTm n := GaussianRationalRowElimination.shape A N N ⋏
  (GaussianRationalRowElimination.shape C N N ⋏ (entryBounds A N B ⋏
    (entryBounds C N B ⋏ (le one Q ⋏ entryDistances A C N P Q))))
@[simp] theorem subst_rowBounds {l : ℕ} (σ : Fin n → PTm l) (A N B r : PTm n) :
    (rowBounds A N B r).subst σ = rowBounds (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ B) (Syn.subst σ r) := by
  simp [rowBounds,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_entryBounds {l : ℕ} (σ : Fin n → PTm l) (A N B : PTm n) :
    (entryBounds A N B).subst σ = entryBounds (Syn.subst σ A) (Syn.subst σ N) (Syn.subst σ B) := by
  simp [entryBounds,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_rowDistances {l : ℕ} (σ : Fin n → PTm l) (A C N P Q r : PTm n) :
    (rowDistances A C N P Q r).subst σ = rowDistances (Syn.subst σ A) (Syn.subst σ C)
      (Syn.subst σ N) (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ r) := by
  simp [rowDistances,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_entryDistances {l : ℕ} (σ : Fin n → PTm l) (A C N P Q : PTm n) :
    (entryDistances A C N P Q).subst σ = entryDistances (Syn.subst σ A) (Syn.subst σ C)
      (Syn.subst σ N) (Syn.subst σ P) (Syn.subst σ Q) := by simp [entryDistances,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (A C N B P Q : PTm n) :
    (input A C N B P Q).subst σ = input (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ B) (Syn.subst σ P) (Syn.subst σ Q) := by simp [input]

theorem entry_bound_at (A N B r j : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B)
    (hr : Γ ⊢[PRAAx] lt r N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] bounded (cell A r j) B one := by
  have row : Γ ⊢[PRAAx] lt r N ⟶ rowBounds A N B r := by simpa [entryBounds] using h.allE r
  have col : Γ ⊢[PRAAx] lt j N ⟶ bounded (cell A r j) B one := by simpa [rowBounds] using (Prf.impE row hr).allE j
  exact .impE col hj

theorem entry_distance_at (A C N P Q r j : PTm n) (h : Γ ⊢[PRAAx] entryDistances A C N P Q)
    (hr : Γ ⊢[PRAAx] lt r N) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] distanceBounded (cell A r j) (cell C r j) P Q := by
  have row : Γ ⊢[PRAAx] lt r N ⟶ rowDistances A C N P Q r := by simpa [entryDistances] using h.allE r
  have col : Γ ⊢[PRAAx] lt j N ⟶ distanceBounded (cell A r j) (cell C r j) P Q := by
    simpa [rowDistances] using (Prf.impE row hr).allE j
  exact .impE col hj

theorem factor_at (A N w j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    factor (characteristicTable A N) N w j ≐ cellPolynomial A (digit N w j) j :=
  table_lookup_at A N (digit N w j) j (digit_bound N w j hj) hj

theorem factor_length (A N w j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    Foundations.SequenceComposition.length (factor (characteristicTable A N) N w j) ≐ two :=
  (congrFst (factor_at A N w j hj)).eqTrans (GaussianRationalCharacteristicPolynomial.cell_length _ _ _)

theorem factor_norm (A N B w j : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B)
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (factor (characteristicTable A N) N w j)) (natCode (two*(B+one))) :=
  rationalLE_congr (coefficientNorm_congr (factor_at A N w j hj)).eqSymm (.eqRefl _)
    (GaussianCharacteristicEntryNorm.entry_relaxed_norm_bound A (digit N w j) j B
      (entry_bound_at A N B _ j h (digit_bound N w j hj) hj))

theorem factor_difference_norm (A C N P Q w j : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] entryDistances A C N P Q) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (subCoefficients (factor (characteristicTable A N) N w j)
      (factor (characteristicTable C N) N w j) two))
      (RationalIntegerNormalization.normalize (ZT.ofNat (two*P)) Q) :=
  rationalLE_congr (coefficientNorm_congr
    (subCoefficients_congr (factor_at A N w j hj) (factor_at C N w j hj) (.eqRefl _))).eqSymm (.eqRefl _)
      (GaussianCharacteristicEntryNorm.entry_difference_bound A C (digit N w j) j P Q hQ
        (entry_distance_at A C N P Q _ j h (digit_bound N w j hj) hj))

theorem source_tables (A C N B P Q : PTm n) (_h : Γ ⊢[PRAAx] input A C N B P Q) : Γ ⊢[PRAAx]
    tableShape (characteristicTable A N) N one ⋏ tableShape (characteristicTable C N) N one :=
  .andI (table_shape A N) (table_shape C N)

theorem factor_bounds (A N B w : PTm n) (h : Γ ⊢[PRAAx] entryBounds A N B) : Γ ⊢[PRAAx]
    .all (lt (var 0) (Syn.shift N) ⟶ rationalLE
      (coefficientNorm (factor (characteristicTable (Syn.shift A) (Syn.shift N)) (Syn.shift N) (Syn.shift w) (var 0)))
        (natCode (two*(Syn.shift B+one)))) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] entryBounds (Syn.shift A) (Syn.shift N) (Syn.shift B) := by
    simpa only [Fm.shift,subst_entryBounds,Syn.shift] using h.shift
  exact .allI (.impI (factor_norm _ _ _ _ _ hs.wk Prf.hyp0))

theorem factor_difference_bounds (A C N P Q w : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] entryDistances A C N P Q) : Γ ⊢[PRAAx]
    .all (lt (var 0) (Syn.shift N) ⟶ rationalLE
      (coefficientNorm (subCoefficients
        (factor (characteristicTable (Syn.shift A) (Syn.shift N)) (Syn.shift N) (Syn.shift w) (var 0))
        (factor (characteristicTable (Syn.shift C) (Syn.shift N)) (Syn.shift N) (Syn.shift w) (var 0)) two))
      (RationalIntegerNormalization.normalize (ZT.ofNat (two*Syn.shift P)) (Syn.shift Q))) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] entryDistances (Syn.shift A) (Syn.shift C) (Syn.shift N) (Syn.shift P) (Syn.shift Q) := by
    simpa only [Fm.shift,subst_entryDistances,Syn.shift] using h.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift,one] using hQ.shift
  exact .allI (.impI (factor_difference_norm _ _ _ _ _ _ _ qs.wk hs.wk Prf.hyp0))

theorem actual_characteristic_word_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (var 1) ⟶ factor (characteristicTable (var 0) (var 1)) (var 1) (var 2) (var 3) ≐
      cellPolynomial (var 0) (digit (var 1) (var 2) (var 3)) (var 3)) := closeUniv 4 (.impI (factor_at _ _ _ _ Prf.hyp0))
theorem actual_characteristic_factor_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (entryBounds (var 0) (var 1) (var 2) ⟶ lt (var 4) (var 1) ⟶
      rationalLE (coefficientNorm (factor (characteristicTable (var 0) (var 1)) (var 1) (var 3) (var 4)))
        (natCode (two*(var 2+one)))) := closeUniv 5 (.impI (.impI (factor_norm _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_characteristic_factor_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 4) ⟶ entryDistances (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 6) (var 2) ⟶
      rationalLE (coefficientNorm (subCoefficients
        (factor (characteristicTable (var 0) (var 2)) (var 2) (var 5) (var 6))
        (factor (characteristicTable (var 1) (var 2)) (var 2) (var 5) (var 6)) two))
        (RationalIntegerNormalization.normalize (ZT.ofNat (two*var 3)) (var 4))) :=
  closeUniv 7 (.impI (.impI (.impI (factor_difference_norm _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_source_characteristic_tables_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      (tableShape (characteristicTable (var 0) (var 2)) (var 2) one ⋏ tableShape (characteristicTable (var 1) (var 2)) (var 2) one)) :=
  closeUniv 6 (.impI (source_tables _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCharacteristicFactorBounds

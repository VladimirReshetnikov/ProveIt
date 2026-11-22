import IPRADerivations.Analysis.GaussianGammaEulerHeadNewton
import IPRADerivations.Analysis.GaussianRationalParityPower
import IPRADerivations.Analysis.GaussianGammaHarmonicPowerPoints

/-!
# The original head Newton sum in the source harmonic-power form

The SAME actual double Newton convolution is interchanged by the proved
finite Gaussian Fubini program. Its actual signed power cells separate
into the original reciprocal-power partial sums. The resulting genuine
single sum is exactly sum(j=0..s) (-1)^j H_N^(j+1) A_N(s-j), equal to
s A_N(s+1) at every internal N,s. No interchange, harmonic kernel or
Newton identity is assumed as an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadHarmonicNewton

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianGammaEulerHeadGeometricStep (term value)
open GaussianGammaEulerHeadExponentStep (reader)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianGammaHarmonicPowerPoints (point)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalFiniteSum (sum)
open GaussianGammaReciprocalDegreeCells (embeddedBody)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N s : PTm n) : PTm n := pairT N s
def matrix : PTm 3 := term (reciprocalPoint (var 0)) (fstT (var 2)) (sndT (var 2)) (var 1)
def weight (N s j : PTm n) : PTm n := qmul (parityPoint j) (reader N (monus s j))
def powerTerm (N s j : PTm n) : PTm n := qmul (qmul (parityPoint j) (point (succ j) N)) (reader N (monus s j))
def powerBody : PTm 2 := powerTerm (fstT (var 1)) (sndT (var 1)) (var 0)
def powerSum (N s : PTm n) : PTm n := sum powerBody (succ s) (data N s)
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (N s : PTm n) :
    Syn.subst σ (data N s) = data (Syn.subst σ N) (Syn.subst σ s) := by simp [data]
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (N s j : PTm n) :
    Syn.subst σ (weight N s j) = weight (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ j) := by simp [weight]
@[simp] theorem subst_powerTerm {l : ℕ} (σ : Fin n → PTm l) (N s j : PTm n) :
    Syn.subst σ (powerTerm N s j) = powerTerm (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ j) := by simp [powerTerm]
@[simp] theorem subst_powerSum {l : ℕ} (σ : Fin n → PTm l) (N s : PTm n) :
    Syn.subst σ (powerSum N s) = powerSum (Syn.subst σ N) (Syn.subst σ s) := by simp [powerSum]

theorem term_congr {a b N M s t j k : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b)
    (hN : Γ ⊢[PRAAx] N ≐ M) (hs : Γ ⊢[PRAAx] s ≐ t) (hj : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] term a N s j ≐ term b M t k := by
  simpa only [GaussianGammaEulerHeadGeometricStep.subst_term,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (term (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![a,N,s,j]) (σ' := ![b,M,t,k]) (fun i => by fin_cases i; exact ha; exact hN; exact hs; exact hj)

theorem power_term_congr {N M s t j k : PTm n} (hN : Γ ⊢[PRAAx] N ≐ M)
    (hs : Γ ⊢[PRAAx] s ≐ t) (hj : Γ ⊢[PRAAx] j ≐ k) : Γ ⊢[PRAAx] powerTerm N s j ≐ powerTerm M t k := by
  simpa only [subst_powerTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (powerTerm (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![N,s,j]) (σ' := ![M,t,k]) (fun i => by fin_cases i; exact hN; exact hs; exact hj)

theorem matrix_at (N s k j : PTm n) : Γ ⊢[PRAAx] inst3 matrix k j (data N s) ≐ term (reciprocalPoint k) N s j := by
  simp only [matrix,inst3,GaussianGammaEulerHeadGeometricStep.subst_term,
    GaussianGammaHarmonicIncrement.subst_reciprocalPoint,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  exact term_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

theorem power_term_at (N s j : PTm n) : Γ ⊢[PRAAx] inst2 powerBody j (data N s) ≐ powerTerm N s j := by
  simp only [powerBody,inst2,subst_powerTerm,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  exact power_term_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _)

theorem row_as_original (N s k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.row matrix k (succ s) (data N s) ≐ value (reciprocalPoint k) N s := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have h := (GaussianRationalFubini.row_entry (Γ := lt (var 0) (succ (Syn.shift s)) :: Γ.map Fm.shift)
    matrix (Syn.shift k) (var 0) (data (Syn.shift N) (Syn.shift s))).eqTrans
      ((matrix_at _ _ _ _).eqTrans (GaussianGammaEulerHeadGeometricStep.term_at _ _ _ _).eqSymm)
  simpa only [Syn.shift,subst_data,GaussianGammaEulerHeadGeometricStep.data,
    GaussianCoefficientGeometricCancellation.subst_data,GaussianGammaEulerHeadPolynomial.subst_polynomial,
    GaussianGammaHarmonicIncrement.subst_reciprocalPoint,subst_pairT,PTm.subst_succ] using h

theorem original_rows (N s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.rowFirst matrix N (succ s) (data N s) ≐ GaussianGammaEulerHeadNewton.newtonSum N s := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have h := (GaussianRationalFubini.row_sum_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    matrix (var 0) (succ (Syn.shift s)) (data (Syn.shift N) (Syn.shift s))).eqTrans
      ((row_as_original _ _ _).eqTrans (GaussianGammaEulerHeadNewton.term_at _ _ _).eqSymm)
  simpa only [Syn.shift,subst_data,GaussianGammaEulerHeadNewton.subst_data,subst_pairT,PTm.subst_succ] using h

theorem separated_cell (N s k j : PTm n) : Γ ⊢[PRAAx] inst3 matrix k j (data N s) ≐
    qmul (weight N s j) (RationalGaussianEmbedding.embed (RationalReciprocalPowerTail.reciprocalPower (succ j) (succ k))) :=
  (matrix_at N s k j).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (GaussianRationalParityPower.weighted_negative_power _ _) (.eqRefl _)).eqTrans
        ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
          ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
            ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
              (qmul_congr (.eqRefl _) (GaussianGammaHarmonicPowerPoints.reciprocal_power (succ j) k)))))))

theorem embedded_term (m k : PTm n) : Γ ⊢[PRAAx]
    inst2 embeddedBody k (RationalReciprocalPowerTail.data m zero) ≐
      RationalGaussianEmbedding.embed (RationalReciprocalPowerTail.reciprocalPower m (succ k)) :=
  (GaussianGammaReciprocalDegreeCells.embedded_term_at m zero k).eqTrans
    (RationalGaussianRealPart.embed_congr
      (RationalReciprocalPowerTail.reciprocal_congr (.eqRefl m) (congrSucc (zero_add k))))

theorem column_alignment (N s j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column matrix j N (data N s) ≐ sum (GaussianRationalFiniteSum.multiplyBody embeddedBody)
      N (pairT (weight N s j) (RationalReciprocalPowerTail.data (succ j) zero)) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have left := (GaussianRationalFubini.column_entry (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    matrix (var 0) (Syn.shift j) (data (Syn.shift N) (Syn.shift s))).eqTrans (separated_cell _ _ _ _)
  have right := (GaussianRationalFiniteSum.multiply_body_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift)
    embeddedBody (weight (Syn.shift N) (Syn.shift s) (Syn.shift j)) (var 0)
      (RationalReciprocalPowerTail.data (succ (Syn.shift j)) zero)).eqTrans
        (qmul_congr (.eqRefl _) (embedded_term _ _))
  simpa only [Syn.shift,subst_data,subst_weight,RationalReciprocalPowerTail.subst_data,
    subst_pairT,PTm.subst_succ,PTm.subst_zero] using left.eqTrans right.eqSymm

theorem original_column (N s j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.column matrix j N (data N s) ≐ powerTerm N s j :=
  (column_alignment N s j).eqTrans
    ((GaussianRationalFiniteSum.sum_multiply embeddedBody (weight N s j) N
      (RationalReciprocalPowerTail.data (succ j) zero)).eqTrans
        ((qmul_congr (.eqRefl _) (RationalGaussianRealPart.embed_sum RationalReciprocalPowerTail.body N
          (RationalReciprocalPowerTail.data (succ j) zero)).eqSymm).eqTrans
            ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
              ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
                (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm))))

theorem original_columns (N s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFubini.columnFirst matrix N (succ s) (data N s) ≐ powerSum N s := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have h := (GaussianRationalFubini.column_sum_at (Γ := lt (var 0) (succ (Syn.shift s)) :: Γ.map Fm.shift)
    matrix (var 0) (Syn.shift N) (data (Syn.shift N) (Syn.shift s))).eqTrans
      ((original_column _ _ _).eqTrans (power_term_at _ _ _).eqSymm)
  simpa only [Syn.shift,subst_data,subst_pairT,PTm.subst_succ] using h

theorem original_interchange (N s : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaEulerHeadNewton.newtonSum N s ≐ powerSum N s :=
  (original_rows N s).eqSymm.eqTrans
    ((GaussianRationalFubini.fubini matrix N (succ s) (data N s)).eqTrans (original_columns N s))

theorem original_harmonic_Newton (N s : PTm n) : Γ ⊢[PRAAx]
    powerSum N s ≐ GaussianRationalNaturalScale.natScale s (reader N (succ s)) :=
  (original_interchange N s).eqSymm.eqTrans (GaussianGammaEulerHeadNewton.original_finite_head_Newton N s)

theorem original_Euler_head_Newton_sum_actual_signed_harmonic_interchange_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (GaussianGammaEulerHeadNewton.newtonSum (var 0) (var 1) ≐ powerSum (var 0) (var 1)) :=
  closeUniv 2 (original_interchange _ _)

theorem original_Euler_head_signed_harmonic_power_Newton_identity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (powerSum (var 0) (var 1) ≐ GaussianRationalNaturalScale.natScale (var 1) (reader (var 0) (succ (var 1)))) :=
  closeUniv 2 (original_harmonic_Newton _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadHarmonicNewton

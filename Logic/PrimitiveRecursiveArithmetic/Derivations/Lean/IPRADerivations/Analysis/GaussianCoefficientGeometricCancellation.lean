import IPRADerivations.Analysis.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.GaussianRationalPolynomialExponentialStability

/-!
# Actual finite geometric coefficient cancellation

The original Gaussian finite-sum program computes the alternating
coefficient convolution sum(j=0..s) (-a)^j a C_(s-j). Its original
first-term split and actual power successor show that its next sum,
plus a times its preceding sum, is exactly a C_(s+1). The input buffer
and all degree indices are arbitrary internal codes; zero extension
uses the actual original exponent reader. No convolution, polynomial
inverse or recurrence identity is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCoefficientGeometricCancellation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalMetric (qnegative qsub)
open GaussianInverseBinomialRows (negative_congr negative_product)
open GaussianRationalReciprocal (power)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalFiniteSum (sum multiplyBody)
open GaussianRationalMatrixFiniteSums (negativeBody)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (a C D s : PTm n) : PTm n := pairT a (pairT C (pairT D s))
def getA (x : PTm n) : PTm n := fstT x
def getC (x : PTm n) : PTm n := fstT (sndT x)
def getD (x : PTm n) : PTm n := fstT (sndT (sndT x))
def getS (x : PTm n) : PTm n := sndT (sndT (sndT x))
def term (a C D s j : PTm n) : PTm n :=
  qmul (power (qnegative a) j) (qmul a (exponentCoefficient C D (monus s j)))
def body : PTm 2 := term (getA (var 1)) (getC (var 1)) (getD (var 1)) (getS (var 1)) (var 0)
def geometricSum (a C D s : PTm n) : PTm n := sum body (succ s) (data a C D s)
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (a C D s : PTm n) :
    Syn.subst σ (data a C D s) = data (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ s) := by simp [data]
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (a C D s j : PTm n) :
    Syn.subst σ (term a C D s j) =
      term (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ s) (Syn.subst σ j) := by simp [term]
@[simp] theorem subst_geometricSum {l : ℕ} (σ : Fin n → PTm l) (a C D s : PTm n) :
    Syn.subst σ (geometricSum a C D s) =
      geometricSum (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ s) := by simp [geometricSum]

theorem term_at (a C D s j : PTm n) : Γ ⊢[PRAAx] inst2 body j (data a C D s) ≐ term a C D s j := by
  have b := snd_pair (Γ := Γ) a (pairT C (pairT D s))
  have c := (congrSnd b).eqTrans (snd_pair C (pairT D s))
  simp only [body,inst2,subst_term,getA,getC,getD,getS,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  apply qmul_congr
  · exact congrAp2 GaussianRationalReciprocal.powerF (.eqRefl _) (negative_congr (fst_pair _ _))
  · exact qmul_congr (fst_pair _ _)
      (GaussianRationalPolynomialExponentialStability.exponent_congr
        ((congrFst b).eqTrans (fst_pair _ _)) ((congrFst c).eqTrans (fst_pair _ _))
        (congrMonus ((congrSnd c).eqTrans (snd_pair _ _)) (.eqRefl _)))

theorem first_term (a C D s : PTm n) : Γ ⊢[PRAAx]
    term a C D s zero ≐ qmul a (exponentCoefficient C D s) :=
  (qmul_congr (GaussianRationalReciprocal.power_zero _) (qmul_congr (.eqRefl _)
    (GaussianRationalPolynomialExponentialStability.exponent_congr (.eqRefl _) (.eqRefl _) (monus_zero s)))).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianRationalHorner.qmul_canonical _ _))

theorem shifted_term (a C D s j : PTm n) : Γ ⊢[PRAAx]
    term a C D (succ s) (succ j) ≐ qnegative (qmul a (term a C D s j)) :=
  (qmul_congr (GaussianRationalReciprocal.power_succ _ _)
    (qmul_congr (.eqRefl _) (GaussianRationalPolynomialExponentialStability.exponent_congr
      (.eqRefl _) (.eqRefl _) (succ_monus_succ s j)))).eqTrans
        ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
          ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans (negative_product _ _).eqSymm))

theorem shifted_sum (a C D s : PTm n) : Γ ⊢[PRAAx]
    sum (shiftBody body) (succ s) (data a C D (succ s)) ≐ qnegative (qmul a (geometricSum a C D s)) := by
  have eqs : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (shiftBody body)
      (negativeBody (multiplyBody body)) (succ s) (data a C D (succ s)) (pairT a (data a C D s)) := by
    refine .allI (.impI ?_)
    rw [inst2_shiftBody,GaussianRationalMatrixFiniteSums.negative_body_at,shift_pairT]
    have h := (term_at (Γ := lt (var 0) (succ (Syn.shift s)) :: Γ.map Fm.shift)
      (Syn.shift a) (Syn.shift C) (Syn.shift D) (succ (Syn.shift s)) (succ (var 0))).eqTrans
        ((shifted_term _ _ _ _ _).eqTrans (negative_congr
          ((qmul_congr (.eqRefl _) (term_at _ _ _ _ _).eqSymm).eqTrans
            (GaussianRationalFiniteSum.multiply_body_at body _ _ _).eqSymm)))
    simpa only [Syn.shift,subst_data,PTm.subst_succ] using h
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ eqs).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_negative _ _ _).eqTrans
      (negative_congr (GaussianRationalFiniteSum.sum_multiply body a (succ s) (data a C D s))))

theorem exact_difference (a C D s : PTm n) : Γ ⊢[PRAAx]
    geometricSum a C D (succ s) ≐
      qsub (qmul a (exponentCoefficient C D (succ s))) (qmul a (geometricSum a C D s)) :=
  (GaussianRationalFiniteSum.sum_shift_first body (succ s) (data a C D (succ s))).eqTrans
    (qadd_congr ((term_at _ _ _ _ _).eqTrans (first_term _ _ _ _)) (shifted_sum a C D s))

theorem exact_cancellation (a C D s : PTm n) : Γ ⊢[PRAAx]
    qadd (geometricSum a C D (succ s)) (qmul a (geometricSum a C D s)) ≐
      qmul a (exponentCoefficient C D (succ s)) :=
  (qadd_congr (exact_difference a C D s) (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans
      (GaussianRationalLinearProduct.add_sub_right _ _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem actual_alternating_geometric_coefficient_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (qadd (geometricSum (var 0) (var 1) (var 2) (succ (var 3)))
      (qmul (var 0) (geometricSum (var 0) (var 1) (var 2) (var 3))) ≐
        qmul (var 0) (exponentCoefficient (var 1) (var 2) (succ (var 3)))) :=
  closeUniv 4 (exact_cancellation _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCoefficientGeometricCancellation

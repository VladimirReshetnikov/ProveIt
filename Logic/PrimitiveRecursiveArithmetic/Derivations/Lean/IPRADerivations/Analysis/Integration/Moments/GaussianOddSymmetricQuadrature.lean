import IPRADerivations.Analysis.Integration.Moments.GaussianMomentReflection

/-!
# Exact finite symmetric odd Gaussian quadratures

Both actual PR3 clients use the SAME original decay sampler at the
squared time and the same odd internal monomial degree. The reflected
client negates the rational argument inside the actual power loop.
Original finite sums and the actual quadrature weight therefore cancel
both symmetric halves exactly, including zero cell count/width. This
finite statement does not supply an improper-convergence premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianOddSymmetricQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianMomentReflection (row)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalMetric (qnegative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalFiniteSum (sum)
open GaussianCompactRiemannName (grid sampleBody sampleData quadrature)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fixedData (N c d : PTm n) : PTm n := pairT N (pairT c d)
def positiveTerm (p t x : PTm n) : PTm n := row p (succ (two*fstT x)) (fraction (fstT t) (sndT t))
  (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x))
def negativeTerm (p t x : PTm n) : PTm n := row p (succ (two*fstT x)) (qnegative (fraction (fstT t) (sndT t)))
  (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x))
def positiveF : PR 3 := PTm.toPR (positiveTerm (var 0) (var 1) (var 2))
def negativeF : PR 3 := PTm.toPR (negativeTerm (var 0) (var 1) (var 2))
@[simp] theorem subst_fixedData {m : ℕ} (σ : Fin n → PTm m) (N c d : PTm n) :
    Syn.subst σ (fixedData N c d) = fixedData (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ d) := by simp [fixedData]
@[simp] theorem subst_positiveTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (positiveTerm p t x) = positiveTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [positiveTerm]
@[simp] theorem subst_negativeTerm {m : ℕ} (σ : Fin n → PTm m) (p t x : PTm n) :
    Syn.subst σ (negativeTerm p t x) = negativeTerm (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ x) := by simp [negativeTerm]

theorem positive_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 positiveF p t x ≐ positiveTerm p t x := by
  simpa [positiveF,ap3] using toPR_eq (Γ := Γ) (positiveTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
theorem negative_at (p t x : PTm n) : Γ ⊢[PRAAx] ap3 negativeF p t x ≐ negativeTerm p t x := by
  simpa [negativeF,ap3] using toPR_eq (Γ := Γ) (negativeTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]

theorem reflected_row (p t x : PTm n) : Γ ⊢[PRAAx]
    ap3 negativeF p t x ≐ qnegative (ap3 positiveF p t x) :=
  (negative_at p t x).eqTrans ((GaussianMomentReflection.odd_row p (fstT x) (fstT t) (sndT t)
    (fstT (sndT x)) (sndT (sndT x))).eqTrans (GaussianInverseBinomialRows.negative_congr (positive_at p t x).eqSymm))

theorem reflected_cell (i p M a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 (sampleBody negativeF) i (sampleData p M a C E x) ≐
      qnegative (inst2 (sampleBody positiveF) i (sampleData p M a C E x)) :=
  (GaussianCompactRiemannName.sample_body_at negativeF i p M a C E x).eqTrans
    ((reflected_row p (grid i M a C E) x).eqTrans (GaussianInverseBinomialRows.negative_congr
      (GaussianCompactRiemannName.sample_body_at positiveF i p M a C E x).eqSymm))

theorem reflected_sum (p M a C E x : PTm n) : Γ ⊢[PRAAx]
    sum (sampleBody negativeF) M (sampleData p M a C E x) ≐
      qnegative (sum (sampleBody positiveF) M (sampleData p M a C E x)) := by
  have cells : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual (sampleBody negativeF)
      (GaussianRationalMatrixFiniteSums.negativeBody (sampleBody positiveF)) M (sampleData p M a C E x) (sampleData p M a C E x) := by
    refine .allI (.impI ?_)
    simpa only [GaussianRationalFiniteSum.termsEqual,GaussianRationalMatrixFiniteSums.negative_body_at,
      GaussianCompactRiemannName.subst_sampleData,Syn.shift] using
      reflected_cell (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x)
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ cells).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_negative (sampleBody positiveF) M (sampleData p M a C E x))

theorem reflected_quadrature (p M a C E x : PTm n) : Γ ⊢[PRAAx]
    quadrature negativeF p M a C E x ≐ qnegative (quadrature positiveF p M a C E x) :=
  (qmul_congr (.eqRefl _) (reflected_sum p M a C E x)).eqTrans (GaussianMomentReflection.negative_right_product _ _)

theorem symmetric_quadrature_zero (p M a C E x : PTm n) : Γ ⊢[PRAAx]
    qadd (quadrature positiveF p M a C E x) (quadrature negativeF p M a C E x) ≐ qzero :=
  (qadd_congr (.eqRefl _) (reflected_quadrature p M a C E x)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

theorem actual_original_odd_Gaussian_symmetric_quadrature_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (qadd (quadrature positiveF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (quadrature negativeF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐ qzero) :=
  closeUniv 6 (symmetric_quadrature_zero _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianOddSymmetricQuadrature

import IPRADerivations.Analysis.RationalPolynomialMonicHornerReductionGaussianEmbedding
import IPRADerivations.Analysis.RationalPolynomialMonicNorm

/-!
# The original rational norm bound for arbitrary input Y degree

The determinant consumes the actual returned rational remainder. Its
proved evaluator law transfers every original common zero to that same
remainder, retaining the stored point list and its original distinctness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalHighYNormBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalPolynomialMonicHornerReductionGaussianEmbedding (input width originalValue returned_evaluation)
open RationalCurvePointsGaussianEmbedding (distinct curveZeros functionZeros curve_at function_at)
open RationalPolynomialMonicNorm (norm finite_zero_bound_of_nonzero)
open RationalPolynomialNonvanishing (nonzeroCoefficients)
open GaussianPolynomialMonicNorm (degreeBound)
open GaussianRationalFiberGrouping (abscissa ordinate)
open RationalGaussianEmbedding (scalarZero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reduced (F H m a c N : PTm n) : PTm n :=
  RationalPolynomialMonicHornerReductionGaussianEmbedding.run F H m a c N
def normPolynomial (F H m a c N : PTm n) : PTm n :=
  norm F (reduced F H m a c N) m (width a c (succ N)) c
def degree (F H m a c N : PTm n) : PTm n :=
  RationalPolynomialDegreeGaussianEmbedding.degree (normPolynomial F H m a c N) (degreeBound m (width a c (succ N)) c)
def points (F H m L : PTm n) : Fm PTm n := distinct L ⋏ (curveZeros F m L ⋏ functionZeros H (length H) L)

@[simp] theorem subst_reduced {l : ℕ} (σ : Fin n → PTm l) (F H m a c N : PTm n) :
    Syn.subst σ (reduced F H m a c N) =
      reduced (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by
  simp [reduced]
@[simp] theorem subst_normPolynomial {l : ℕ} (σ : Fin n → PTm l) (F H m a c N : PTm n) :
    Syn.subst σ (normPolynomial F H m a c N) =
      normPolynomial (Syn.subst σ F) (Syn.subst σ H) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ N) := by
  simp [normPolynomial]

theorem monic_input (F H m a c N : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N) :
    Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F (reduced F H m a c N) m (width a c (succ N)) c :=
  .andI (.andE₁ h) (.andI (.andE₁ (.andE₂ (.andE₂ h)))
    (RationalPolynomialMonicHornerReductionGaussianEmbedding.returned_shape F H m a c N))

theorem reduced_zero_at (F H m a c N L i : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hp : Γ ⊢[PRAAx] points F H m L) (hi : Γ ⊢[PRAAx] lt i (length L)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalEq
      (RationalBivariateGaussianEmbedding.bivariate (reduced F H m a c N) m (abscissa L i) (ordinate L i)) scalarZero := by
  let x := abscissa L i
  let y := ordinate L i
  have curve := curve_at F m L i (.andE₁ (.andE₂ hp)) hi
  have original := function_at H (length H) L i (.andE₂ (.andE₂ hp)) hi
  have eval := returned_evaluation F H m a c N x y h curve
  exact RationalArgmin.rationalEq_congr eval.eqSymm (.eqRefl _) original

theorem reduced_points (F H m a c N L : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hp : Γ ⊢[PRAAx] points F H m L) : Γ ⊢[PRAAx]
    RationalCurvePointsGaussianEmbedding.sourceInput F (reduced F H m a c N) m L := by
  refine .andI (.andE₁ hp) (.andI (.andE₁ (.andE₂ hp)) (.allI (.impI ?_)))
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] input (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) (Syn.shift N) := by
    simpa [Δ, Fm.shift,Syn.shift] using h.shift
  have hp' : Δ ⊢[PRAAx] points (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift L) := by
    simpa [Δ,points,Fm.shift,Syn.shift] using hp.shift
  simpa [Δ,Syn.shift] using reduced_zero_at (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c)
    (Syn.shift N) (Syn.shift L) (var 0) h'.wk hp'.wk Prf.hyp0

theorem finite_zero_bound (F H m a c N L : PTm n) (h : Γ ⊢[PRAAx] input F H m a c N)
    (hp : Γ ⊢[PRAAx] points F H m L)
    (hn : Γ ⊢[PRAAx] nonzeroCoefficients (normPolynomial F H m a c N) (degreeBound m (width a c (succ N)) c)) :
    Γ ⊢[PRAAx] le (length L) (degree F H m a c N) :=
  finite_zero_bound_of_nonzero F (reduced F H m a c N) m (width a c (succ N)) c L
    (monic_input F H m a c N h) (reduced_points F H m a c N L h hp) hn

def normF : PR 6 := PTm.toPR (normPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
theorem program_at (F H m a c N : PTm n) : Γ ⊢[PRAAx] PTm.app normF ![F,H,m,a,c,N] ≐ normPolynomial F H m a c N := by
  simpa [normF] using toPR_eq (Γ := Γ) (normPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![F,H,m,a,c,N]

theorem actual_rational_high_y_norm_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (PTm.app normF ![var 0,var 1,var 2,var 3,var 4,var 5] ≐ normPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

theorem actual_rational_high_y_norm_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ points (var 0) (var 1) (var 2) (var 6) ⟶
      nonzeroCoefficients (normPolynomial (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (degreeBound (var 2) (width (var 3) (var 4) (succ (var 5))) (var 4)) ⟶
      le (length (var 6)) (degree (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (finite_zero_bound _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalHighYNormBound

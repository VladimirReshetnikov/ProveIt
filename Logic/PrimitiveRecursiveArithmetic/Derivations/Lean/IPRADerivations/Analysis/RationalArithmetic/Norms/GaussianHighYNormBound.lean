import IPRADerivations.Analysis.Polynomials.Horner.GaussianPolynomialMonicHornerReduction
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianNormFiniteZeroBound

/-!
# The monic norm bound for arbitrary input Y degree

The norm uses the actual bounded remainder of the input polynomial.
Every original common zero is a zero of that computed remainder.
The hypothesis on the norm is its actual nonzero coefficient flag.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianHighYNormBound

open_ipra
open GaussianPolynomialMonicCompanion (rowShape values values_length)
open GaussianPolynomialMonicHornerReduction (stage stage_shape width prefix_evaluation)
open GaussianNormFiberDivisibility (sourceOriginal)
open GaussianPolynomialMonicNorm (degreeBound)
open GaussianRationalCurveFibers (curveZeros functionZeros pointDistinct curve_at function_at)
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalPolynomialDegree (flag degree)
open GaussianRationalHorner (evaluate hornerF qzero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def remainder (F H m a c : PTm n) : PTm n := stage F H m a c (length H)
def norm (F H m a c : PTm n) : PTm n := sourceOriginal F (remainder F H m a c) m (width a c (length H)) c
def normWidth (H m a c : PTm n) : PTm n := degreeBound m (width a c (length H)) c

def input (F H m a c : PTm n) : Fm PTm n :=
  le one m ⋏ (rowShape F m c ⋏ rowShape H (length H) a)
def points (F H m P : PTm n) : Fm PTm n :=
  pointDistinct P ⋏ (curveZeros F m P ⋏ functionZeros H (length H) P)

ipra_subst remainder
ipra_subst input
ipra_subst points

theorem remainder_zero_at (F H m a c P i : PTm n) (h : Γ ⊢[PRAAx] input F H m a c)
    (hP : Γ ⊢[PRAAx] points F H m P) (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    evaluate (values (remainder F H m a c) m (abscissa P i)) (ordinate P i) ≐ qzero := by
  let x := abscissa P i
  let y := ordinate P i
  have curve := curve_at F m P i (.andE₁ (.andE₂ hP)) hi
  have original := function_at H (length H) P i (.andE₂ (.andE₂ hP)) hi
  exact (prefix_evaluation F H m a c (length H) x y (length H) (.andE₁ h) (.andE₁ (.andE₂ h))
    (.andE₂ (.andE₂ h)) curve (le_refl _)).eqTrans
      ((congrAp3 hornerF (values_length H (length H) x).eqSymm (.eqRefl _) (.eqRefl y)).eqTrans original)

theorem reduced_points (F H m a c P : PTm n) (h : Γ ⊢[PRAAx] input F H m a c) (hP : Γ ⊢[PRAAx] points F H m P) :
    Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F (remainder F H m a c) m P := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] points (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift P) := by
    simpa [Fm.shift,Syn.shift] using hP.shift
  refine .andI (.andE₁ hP) (.andI (.andE₁ (.andE₂ hP)) (.allI (.impI ?_)))
  simpa [Syn.shift] using remainder_zero_at (Syn.shift F) (Syn.shift H) (Syn.shift m) (Syn.shift a) (Syn.shift c)
    (Syn.shift P) (var 0) hs.wk ps.wk Prf.hyp0

theorem original_point_bound (F H m a c P : PTm n) (h : Γ ⊢[PRAAx] input F H m a c) (hP : Γ ⊢[PRAAx] points F H m P)
    (hn : Γ ⊢[PRAAx] flag (norm F H m a c) (normWidth H m a c) ≐ one) : Γ ⊢[PRAAx]
    le (length P) (degree (norm F H m a c) (normWidth H m a c)) :=
  GaussianNormFiniteZeroBound.finite_norm_zero_bound F (remainder F H m a c) m (width a c (length H)) c P zero
    (.andI (.andI (.andE₁ h) (.andI (.andE₁ (.andE₂ h)) (stage_shape F H m a c (length H))))
      (.andI (reduced_points F H m a c P h hP) hn))

theorem actual_high_y_norm_zero_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ points (var 0) (var 1) (var 2) (var 5) ⟶
      flag (norm (var 0) (var 1) (var 2) (var 3) (var 4)) (normWidth (var 1) (var 2) (var 3) (var 4)) ≐ one ⟶
      le (length (var 5)) (degree (norm (var 0) (var 1) (var 2) (var 3) (var 4))
        (normWidth (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (original_point_bound _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianHighYNormBound

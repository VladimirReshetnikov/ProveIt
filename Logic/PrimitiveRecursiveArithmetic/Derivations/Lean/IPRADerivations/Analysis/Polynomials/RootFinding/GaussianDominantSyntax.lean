import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianBalancedRadiusValues

/-!
# Actual squared scores at the successive descent radii

At scale h the radius is 2^j/2^(E+2h), with no clipped subtraction of
exponents. Positive-degree scores are the original squared Gaussian norms
times the actual rational radius powers. Their natural numerator is
independent of h; their actual positive denominator contains that scale.
All polynomial codes, degrees, scales and coefficient indices are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantSyntax

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def four : PTm n := two*two
def exponent (E h : PTm n) : PTm n := E+two*h
def score (C N E j h i : PTm n) : PTm n := GaussianBalancedRadiusValues.scaledNorm C N (exponent E h) j i
def numerator (C N j i : PTm n) : PTm n := GaussianBalancedRadiusValues.scaledNumerator C N j i
def denominator (C N E h i : PTm n) : PTm n := GaussianBalancedRadiusValues.scaledDenominator C N (exponent E h) i

@[simp] theorem subst_four {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (four : PTm n) = (four : PTm m) := by simp [four]
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (E h : PTm n) :
    Syn.subst σ (exponent E h) = exponent (Syn.subst σ E) (Syn.subst σ h) := by simp [exponent]
@[simp] theorem subst_score {m : ℕ} (σ : Fin n → PTm m) (C N E j h i : PTm n) :
    Syn.subst σ (score C N E j h i) = score (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ E)
      (Syn.subst σ j) (Syn.subst σ h) (Syn.subst σ i) := by simp [score]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (C N j i : PTm n) :
    Syn.subst σ (numerator C N j i) = numerator (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ j) (Syn.subst σ i) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (C N E h i : PTm n) :
    Syn.subst σ (denominator C N E h i) = denominator (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ E) (Syn.subst σ h) (Syn.subst σ i) := by simp [denominator]

theorem denominator_positive (C N E h i : PTm n) : Γ ⊢[PRAAx] le one (denominator C N E h i) :=
  GaussianBalancedRadiusValues.scaled_denominator_positive _ _ _ _

theorem score_represents (C N E j h i : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (score C N E j h i) (ZT.ofNat (numerator C N j i)) (denominator C N E h i) :=
  GaussianBalancedRadiusValues.scaledNorm_represents _ _ _ _ _

theorem score_canonical (C N E j h i : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (score C N E j h i) :=
  GaussianBalancedRadiusValues.scaledNorm_canonical _ _ _ _ _

theorem score_nonnegative (C N E j h i : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (GaussianEuclideanDistanceName.fraction zero one) (score C N E j h i) :=
  GaussianBalancedRadiusValues.scaledNorm_nonnegative _ _ _ _ _

theorem numerator_positive (C N j i : PTm n)
    (h : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N i)) :
    Γ ⊢[PRAAx] le one (numerator C N j i) :=
  GaussianRationalHorner.positive_product _ _ h (unit_positive _)

theorem score_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (denominator (var 0) (var 1) (var 2) (var 4) (var 5)) ⋏
      RationalArithmetic.represents (score (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (ZT.ofNat (numerator (var 0) (var 1) (var 3) (var 5))) (denominator (var 0) (var 1) (var 2) (var 4) (var 5))) :=
  closeUniv 6 (.andI (denominator_positive _ _ _ _ _) (score_represents _ _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianDominantSyntax

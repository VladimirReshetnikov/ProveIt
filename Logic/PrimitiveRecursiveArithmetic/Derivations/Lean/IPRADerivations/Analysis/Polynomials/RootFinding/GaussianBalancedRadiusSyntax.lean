import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalL1
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootSchedule

/-!
# Actual squared comparisons for a balanced dyadic radius

The coefficient list uses the existing descending Horner order. Its
coefficient of W^i is entry N-i, so index zero denotes the constant term.
The original rational Gaussian components retain their independent decoded
denominators. The finite scan uses only natural squared-norm comparisons;
its exponent j denotes the actual positive radius 2^j/2^E.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def unit (t : PTm n) : PTm n := pw two t
def three : PTm n := succ two
def coefficient (C N i : PTm n) : PTm n := entry C (PTm.monus N i)
def numerator (C N i : PTm n) : PTm n := normSq (rawGaussian (coefficient C N i))
def denominator (C N i : PTm n) : PTm n := rawDen (coefficient C N i)*rawDen (coefficient C N i)
def score (C N _E j i : PTm n) : PTm n := numerator C N i*denominator C N zero*unit (two*j*i)
def cap (C N E i : PTm n) : PTm n := numerator C N zero*denominator C N i*unit (two*E*i)
def fitAt (C N E j i : PTm n) : Fm PTm n := le (score C N E j i) (cap C N E i)
def nonconstant (C N : PTm n) : Fm PTm n := .ex
  (le one (var 0) ⋏ (le (var 0) (Syn.shift N) ⋏ le one (numerator (Syn.shift C) (Syn.shift N) (var 0))))
def input (C N : PTm n) : Fm PTm n :=
  Foundations.SequenceComposition.length C ≐ succ N ⋏
    (le one N ⋏ (le one (numerator C N zero) ⋏ nonconstant C N))

@[simp] theorem subst_unit {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst σ (unit t) = unit (Syn.subst σ t) := by simp [unit]
@[simp] theorem subst_three {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (three : PTm n) = (three : PTm m) := by
  simp [three]
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (C N i : PTm n) :
    Syn.subst σ (coefficient C N i) = coefficient (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ i) := by
  simp [coefficient]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (C N i : PTm n) :
    Syn.subst σ (numerator C N i) = numerator (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ i) := by
  simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (C N i : PTm n) :
    Syn.subst σ (denominator C N i) = denominator (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ i) := by
  simp [denominator]
@[simp] theorem subst_score {m : ℕ} (σ : Fin n → PTm m) (C N E j i : PTm n) :
    Syn.subst σ (score C N E j i) = score (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ E)
      (Syn.subst σ j) (Syn.subst σ i) := by simp [score]
@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (C N E i : PTm n) :
    Syn.subst σ (cap C N E i) = cap (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ E) (Syn.subst σ i) := by
  simp [cap]
@[simp] theorem subst_fitAt {m : ℕ} (σ : Fin n → PTm m) (C N E j i : PTm n) :
    (fitAt C N E j i).subst σ = fitAt (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ E)
      (Syn.subst σ j) (Syn.subst σ i) := by simp [fitAt]
@[simp] theorem subst_nonconstant {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (nonconstant C N).subst σ = nonconstant (Syn.subst σ C) (Syn.subst σ N) := by
  simp [nonconstant,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (input C N).subst σ = input (Syn.subst σ C) (Syn.subst σ N) := by simp [input]

theorem unit_positive (t : PTm n) : Γ ⊢[PRAAx] le one (unit t) :=
  GaussianFactorBudget.power_positive two t (le_succ_self one)

theorem denominator_positive (C N i : PTm n) : Γ ⊢[PRAAx] le one (denominator C N i) :=
  positive_product _ _ (raw_den_positive _) (raw_den_positive _)

theorem coefficient_norm_represents (C N i : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (GaussianRationalMetric.qnormSq (coefficient C N i))
      (ZT.ofNat (numerator C N i)) (denominator C N i) :=
  GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive _) (raw_represents _)

theorem coefficient_norm_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (denominator (var 0) (var 1) (var 2)) ⋏
      RationalArithmetic.represents (GaussianRationalMetric.qnormSq (coefficient (var 0) (var 1) (var 2)))
        (ZT.ofNat (numerator (var 0) (var 1) (var 2))) (denominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (denominator_positive _ _ _) (coefficient_norm_represents _ _ _))

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax

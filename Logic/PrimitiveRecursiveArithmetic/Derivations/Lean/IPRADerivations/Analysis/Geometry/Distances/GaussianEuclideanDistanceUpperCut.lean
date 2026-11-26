import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName

/-!
# Actual rational upper cuts for Euclidean distance names

The natural numerator and positive denominator are computed by the literal
finite Euclidean argmin and square-root programs. A genuine point CN law
and a nonempty original finite list derive an upper cut at each actual
sample plus its dyadic error, including square-root and point-name errors.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceUpperCut

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianEuclideanPointDistance (unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName
  (shifted pointCN distanceSample distanceLE fraction finite_hit_to_cut two_units_le_shift)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (point : PR 2) (T x m : PTm n) : PTm n :=
  GaussianEuclideanPointDistance.root (ap2 point (shifted m) x) T (shifted m)
def denominator (point : PR 2) (T x m : PTm n) : PTm n :=
  GaussianEuclideanPointDistance.denominator (ap2 point (shifted m) x) T*unit (shifted m)
def upperNumerator (point : PR 2) (T x m : PTm n) : PTm n := numerator point T x m*unit m+denominator point T x m
def upperDenominator (point : PR 2) (T x m : PTm n) : PTm n := denominator point T x m*unit m

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x m : PTm n) :
    Syn.subst σ (numerator point T x m) = numerator point (Syn.subst σ T) (Syn.subst σ x) (Syn.subst σ m) := by simp [numerator]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x m : PTm n) :
    Syn.subst σ (denominator point T x m) = denominator point (Syn.subst σ T) (Syn.subst σ x) (Syn.subst σ m) := by simp [denominator]
@[simp] theorem subst_upperNumerator {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x m : PTm n) :
    Syn.subst σ (upperNumerator point T x m) = upperNumerator point (Syn.subst σ T) (Syn.subst σ x) (Syn.subst σ m) := by simp [upperNumerator]
@[simp] theorem subst_upperDenominator {l : ℕ} (σ : Fin n → PTm l) (point : PR 2) (T x m : PTm n) :
    Syn.subst σ (upperDenominator point T x m) = upperDenominator point (Syn.subst σ T) (Syn.subst σ x) (Syn.subst σ m) := by simp [upperDenominator]

theorem denominator_positive (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx] le one (denominator point T x m) :=
  positive_product _ _ (GaussianEuclideanPointDistance.denominator_positive _ _) (unit_positive _)
theorem upper_denominator_positive (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx] le one (upperDenominator point T x m) :=
  positive_product _ _ (denominator_positive point T x m) (unit_positive _)

theorem sample_represents (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (distanceSample point T x m) (ZT.ofNat (numerator point T x m)) (denominator point T x m) :=
  GaussianEuclideanPointDistance.lower_represents _ _ _

theorem sample_fraction (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    distanceSample point T x m ≐ fraction (numerator point T x m) (denominator point T x m) := .eqRefl _

theorem upper_fraction (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.cutRadius (numerator point T x m) (denominator point T x m) m ≐
      fraction (upperNumerator point T x m) (upperDenominator point T x m) :=
  GaussianEuclideanDistanceName.cut_fraction _ _ _ (denominator_positive point T x m)

/-- Both finite errors are included: the selected square-root sample and
its original point sample each contribute at most 2^-(m+2). -/
theorem sample_upper_cut (point : PR 2) (T x m : PTm n)
    (hCN : Γ ⊢[PRAAx] pointCN point x) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx]
    distanceLE point T x (upperNumerator point T x m) (upperDenominator point T x m) := by
  have dp := denominator_positive (Γ := Γ) point T x m
  have sp := unit_positive (Γ := Γ) (shifted m)
  have actual := GaussianEuclideanPointDistance.lower_bound_to_hit
    (ap2 point (shifted m) x) T (shifted m) (numerator point T x m) (denominator point T x m)
    hT dp (RationalArgmin.rationalLE_congr (.eqRefl _) (sample_fraction point T x m) (RationalArgmin.reflexive _))
  have scaled := le_mul_mono (two_units_le_shift (Γ := Γ) m)
    (le_refl (denominator point T x m*denominator point T x m*unit (shifted m)))
  have budget : Γ ⊢[PRAAx] le
      (((numerator point T x m*unit (shifted m)+denominator point T x m)*unit (shifted m)+
        denominator point T x m*unit (shifted m))*upperDenominator point T x m)
      (upperNumerator point T x m*((denominator point T x m*unit (shifted m))*unit (shifted m))) :=
    le_congr (by unfold upperDenominator; ipra_ring) (by unfold upperNumerator; ipra_ring)
      (add_le_add_right (numerator point T x m*unit (shifted m)*unit (shifted m)*denominator point T x m*unit m) scaled)
  exact finite_hit_to_cut point T x (shifted m) _ _ _ _ hCN (positive_product _ _ dp sp)
    (upper_denominator_positive point T x m) actual budget

/-! Actual PR3 metadata returns the original scalar sample and all four
natural fields; no represented minimizing-index selection is an input. -/
def output (point : PR 2) (T x m : PTm n) : PTm n := pairT (distanceSample point T x m)
  (pairT (numerator point T x m) (pairT (denominator point T x m)
    (pairT (upperNumerator point T x m) (upperDenominator point T x m))))
def outputF (point : PR 2) : PR 3 := PTm.toPR (output point (var 0) (var 1) (var 2))

theorem program_at (point : PR 2) (T x m : PTm n) : Γ ⊢[PRAAx]
    ap3 (outputF point) T x m ≐ output point T x m := by
  simpa [outputF,output,ap3] using toPR_eq (Γ := Γ) (output point (var 0) (var 1) (var 2) : PTm 3) ![T,x,m]

theorem distance_sample_upper_cut_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (pointCN point (var 1) ⟶ le one (length (var 0)) ⟶
      distanceLE point (var 0) (var 1) (upperNumerator point (var 0) (var 1) (var 2))
        (upperDenominator point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (sample_upper_cut _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem distance_sample_fraction_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (denominator point (var 0) (var 1) (var 2))) ⋏
      distanceSample point (var 0) (var 1) (var 2) ≐ fraction (numerator point (var 0) (var 1) (var 2))
        (denominator point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (denominator_positive _ _ _ _) (sample_fraction _ _ _ _))

theorem distance_sample_upper_program_closed (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (outputF point) (var 0) (var 1) (var 2) ≐ output point (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceUpperCut

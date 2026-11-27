import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantSelector
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadius

/-!
# Literal descent radii and actual dominant Gaussian scores

The source radius at scale h is the actual normalized fraction
2^j0/2^(E+2h), with E and j0 computed by the checked radius producer.
Its quarter-step identity is proved using the original scalar operations.
Actual selector maximality gives every positive-degree coefficient bound,
rather than accepting a dominance predicate as a source assumption.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantRadiusValues

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive input)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax (exponent four)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianDominantSelector (index)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaleExponent (C N h : PTm n) : PTm n := exponent (GaussianBalancedRadiusHeight.E C N) h
def radius (C N h : PTm n) : PTm n :=
  GaussianBalancedRadiusValues.radius (scaleExponent C N h) (GaussianBalancedRadiusSearch.radiusIndex C N)
def score (C N h i : PTm n) : PTm n := GaussianDominantSyntax.score C N
  (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) h i

ipra_subst scaleExponent
ipra_subst radius
ipra_subst score

theorem radius_represents (C N h : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (radius C N h)
      (ZT.ofNat (unit (GaussianBalancedRadiusSearch.radiusIndex C N))) (unit (scaleExponent C N h)) :=
  GaussianBalancedRadiusValues.radius_represents _ _

theorem radius_canonical (C N h : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (radius C N h) :=
  GaussianBalancedRadiusValues.radius_canonical _ _

theorem radius_positive (C N h : PTm n) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (radius C N h) (fraction zero one)) :=
  GaussianBalancedRadiusValues.radius_positive _ _

theorem denominator_quarter_step (C N h : PTm n) : Γ ⊢[PRAAx]
    unit (scaleExponent C N (succ h)) ≐ four*unit (scaleExponent C N h) := by
  have shift : Γ ⊢[PRAAx] scaleExponent C N (succ h) ≐ scaleExponent C N h+two := by
    unfold scaleExponent exponent
    ipra_ring
  exact (congrAp2 powF shift (.eqRefl two)).eqTrans
    ((GaussianEuclideanDistanceName.unit_shift (scaleExponent C N h)).eqTrans (by
      unfold four unit GaussianEuclideanPointDistance.unit
      ipra_ring))

/-- The actual next radius multiplied by four is the current one. This
preserves negative source exponents by increasing the denominator. -/
theorem quarter_radius (C N h : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (radius C N (succ h)) (fraction four one) ≐ radius C N h := by
  have nextPos := unit_positive (Γ := Γ) (scaleExponent C N (succ h))
  have currentPos := unit_positive (Γ := Γ) (scaleExponent C N h)
  have productPos := positive_product (Γ := Γ) _ _ nextPos (le_refl one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (radius_canonical C N h)
    (RationalRepresentations.represents_multiply _ _ _ _ _ _
      (radius_represents C N (succ h)) (fraction_represents four one (le_refl one)))
    (radius_represents C N h) productPos currentPos
  apply ZT.derive
  have step := natEq (denominator_quarter_step (Γ := Γ) C N h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  rw [step]
  ring

theorem initial_radius (C N : PTm n) (h : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    radius C N zero ≐ GaussianBalancedRadius.radius C N := by
  have shift : Γ ⊢[PRAAx] scaleExponent C N zero ≐ GaussianBalancedRadiusHeight.E C N := by
    unfold scaleExponent exponent
    ipra_ring
  have same := RationalNonnegativePowers.fraction_congr (.eqRefl (unit (GaussianBalancedRadiusSearch.radiusIndex C N)))
    (congrAp2 powF shift (.eqRefl two))
  exact same.eqTrans (GaussianBalancedRadius.positive_radius C N (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))).eqSymm

def dominates (C N h k : PTm n) : Fm PTm n := .all
  (le one (var 0) ⟶ le (var 0) (Syn.shift N) ⟶
    RationalArgmin.rationalLE (score (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0))
      (score (Syn.shift C) (Syn.shift N) (Syn.shift h) (Syn.shift k)))

ipra_subst dominates [Syn.subst_shift, Syn.shift_subst]

theorem dominates_at (C N h k i : PTm n) (hDom : Γ ⊢[PRAAx] dominates C N h k)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (score C N h i) (score C N h k) := by
  have rule : Γ ⊢[PRAAx] le one i ⟶ le i N ⟶ RationalArgmin.rationalLE (score C N h i) (score C N h k) := by
    simpa [dominates] using hDom.allE i
  exact .impE (.impE rule hi) hiN

theorem selected_dominates (C N h : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    dominates C N h (index C N h) := by
  refine .allI (.impI (.impI ?_))
  have shifted : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianBalancedRadiusSyntax.subst_input,Syn.shift] using hInput.shift
  simpa only [score,Syn.shift,GaussianDominantSelector.subst_index] using
    GaussianDominantSelector.index_maximal (Syn.shift C) (Syn.shift N) (Syn.shift h) (var 0) shifted.wk.wk Prf.hyp1 Prf.hyp0

theorem dominates_congr (C N h : PTm n) {k l : PTm n} (hk : Γ ⊢[PRAAx] k ≐ l)
    (hDom : Γ ⊢[PRAAx] dominates C N h k) : Γ ⊢[PRAAx] dominates C N h l := by
  refine .allI (.impI (.impI ?_))
  have shifted : Γ.map Fm.shift ⊢[PRAAx] dominates (Syn.shift C) (Syn.shift N) (Syn.shift h) (Syn.shift k) := by
    simpa only [Fm.shift,subst_dominates,Syn.shift] using hDom.shift
  have indexEq : Γ.map Fm.shift ⊢[PRAAx] Syn.shift k ≐ Syn.shift l := by simpa only [Fm.shift,Fm.subst_eq,Syn.shift] using hk.shift
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (GaussianDominantSelector.score_index_congr (Syn.shift C) (Syn.shift N)
      (GaussianBalancedRadiusHeight.E (Syn.shift C) (Syn.shift N))
      (GaussianBalancedRadiusSearch.radiusIndex (Syn.shift C) (Syn.shift N)) (Syn.shift h) indexEq.wk.wk)
    (dominates_at (Syn.shift C) (Syn.shift N) (Syn.shift h) (Syn.shift k) (var 0) shifted.wk.wk Prf.hyp1 Prf.hyp0)

def radiusF : PR 3 := PTm.toPR (radius (var 0) (var 1) (var 2))
theorem radius_program (C N h : PTm n) : Γ ⊢[PRAAx] ap3 radiusF C N h ≐ radius C N h := by
  simpa [radiusF,ap3] using toPR_eq (Γ := Γ) (radius (var 0) (var 1) (var 2) : PTm 3) ![C,N,h]

theorem actual_quarter_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArithmetic.multiply (radius (var 0) (var 1) (succ (var 2))) (fraction four one) ≐ radius (var 0) (var 1) (var 2)) :=
  closeUniv 3 (quarter_radius _ _ _)

theorem actual_selected_dominance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) ⟶ dominates (var 0) (var 1) (var 2) (index (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (selected_dominates _ _ _ Prf.hyp0))

theorem actual_radius_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 radiusF (var 0) (var 1) (var 2) ≐ radius (var 0) (var 1) (var 2)) := closeUniv 3 (radius_program _ _ _)

end LeanProofs.IPRA.Analysis.GaussianDominantRadiusValues

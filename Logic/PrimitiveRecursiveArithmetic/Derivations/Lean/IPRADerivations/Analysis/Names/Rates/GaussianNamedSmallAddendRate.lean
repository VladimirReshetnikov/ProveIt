import IPRADerivations.Analysis.Names.GaussianNameRingLaws
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Exact independent rate after removing a small named addend

The original normalized sum is retained. A genuine bound on each
canonical small-addend observation and the exact named decomposition
give A/B plus the two requested observation allowances. Only the
auxiliary six-dyadic diagonal envelope is removed by the finite gap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedSmallAddendRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNameArithmetic (addF addData)
open GaussianRationalHorner (canonical qadd positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tailSamples (U : PR 2) (z A B : PTm n) : Fm PTm n := .all
  (canonical (ap2 U (var 0) (Syn.shift z)) ⋏ bounded (ap2 U (var 0) (Syn.shift z))
    (Syn.shift A*unit (var 0)+Syn.shift B) (Syn.shift B*unit (var 0)))
def source (C L U : PR 2) (x y z A B : PTm n) : Fm PTm n := le one B ⋏
  ((pointCN C x ⋏ pointCN L y) ⋏ (pointCN U z ⋏
    (crossEquivalent L (addF C U) y (addData x z) ⋏ tailSamples U z A B)))

@[simp] theorem subst_tailSamples {m : ℕ} (σ : Fin n → PTm m) (U : PR 2) (z A B : PTm n) :
    (tailSamples U z A B).subst σ = tailSamples U (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [tailSamples,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (C L U : PR 2) (x y z A B : PTm n) :
    (source C L U x y z A B).subst σ = source C L U (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [source]

theorem tail_at (U : PR 2) (z A B t : PTm n) (h : Γ ⊢[PRAAx] tailSamples U z A B) : Γ ⊢[PRAAx]
    canonical (ap2 U t z) ⋏ bounded (ap2 U t z) (A*unit t+B) (B*unit t) := by
  simpa only [tailSamples,Fm.subst_and,GaussianRationalHorner.subst_canonical,GaussianRationalMetric.subst_bounded,
    subst_ap2,PTm.subst_add,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE t

theorem original_diagonal (C L U : PR 2) (t x y z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] pointCN C x) (hU : Γ ⊢[PRAAx] pointCN U z)
    (he : Γ ⊢[PRAAx] crossEquivalent L (addF C U) y (addData x z))
    (ht : Γ ⊢[PRAAx] tailSamples U z A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 C t x) (ap2 L t y) (diagonalNumerator A B (num 6) t) (diagonalDenominator B t) := by
  let P := unit t
  let D := B*P
  let S := ap2 (addF C U) t (addData x z)
  let W := qadd (ap2 C t x) (ap2 U t z)
  have hp := unit_positive (Γ := Γ) t
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hp
  have sample := tail_at U z A B t ht
  have raw : Γ ⊢[PRAAx] distanceBounded W (ap2 C t x) (A*P+B) D :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ sample.andE₁).eqSymm (.eqRefl _) (.eqRefl _) sample.andE₂
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 C t x) W (A*P+B) D := distance_symmetric _ _ _ _ hd raw
  have second : Γ ⊢[PRAAx] distanceBounded W S (num 3*B) D :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by dsimp only [D]; unfold GaussianNameRingLaws.three; ipra_ring))
      (distance_symmetric _ _ _ _ hp (GaussianNameRingLaws.add_sample_error C U x z t hC hU))
  have third : Γ ⊢[PRAAx] distanceBounded S (ap2 L t y) (two*B) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hd
      (le_of_eq_add (d := zero) (by dsimp only [D,P]; ipra_ring))
      (distance_symmetric _ _ _ _ (positive_product _ _ hp hp) (cross_at _ _ _ _ t t he))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ W _ _ _ D hd first (distance_triangle_same _ S _ _ _ D hd second third))

theorem independent_rate (C L U : PR 2) (x y z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] pointCN C x) (hL : Γ ⊢[PRAAx] pointCN L y) (hU : Γ ⊢[PRAAx] pointCN U z)
    (he : Γ ⊢[PRAAx] crossEquivalent L (addF C U) y (addData x z))
    (ht : Γ ⊢[PRAAx] tailSamples U z A B) : Γ ⊢[PRAAx] independentRate C L x y A B := by
  apply GaussianNamedLipschitzRate.independent_rate C L x y A B (num 6) hB hC hL
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] pointCN C (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hC.shift
  have us : Γ.map Fm.shift ⊢[PRAAx] pointCN U (Syn.shift z) := by simpa [Fm.shift,Syn.shift] using hU.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent L (addF C U) (Syn.shift y) (addData (Syn.shift x) (Syn.shift z)) := by simpa [Fm.shift,Syn.shift] using he.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] tailSamples U (Syn.shift z) (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using ht.shift
  refine .allI ?_
  simpa only [diagonalEnvelope,PTm.subst_num,Syn.shift] using original_diagonal C L U (var 0) (Syn.shift x) (Syn.shift y) (Syn.shift z)
    (Syn.shift A) (Syn.shift B) bs cs us es ts

theorem rate_of_source (C L U : PR 2) (x y z A B : PTm n) (h : Γ ⊢[PRAAx] source C L U x y z A B) : Γ ⊢[PRAAx]
    independentRate C L x y A B :=
  independent_rate C L U x y z A B h.andE₁ h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂

theorem original_observations (C L U : PR 2) (p q x y z A B : PTm n) (h : Γ ⊢[PRAAx] source C L U x y z A B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 C p x) (ap2 L q y) (rateNumerator A B p q) (rateDenominator B p q) :=
  rate_at _ _ _ _ _ _ p q (rate_of_source C L U x y z A B h)

theorem actual_named_small_addend_rate_closed (C L U : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source C L U (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ independentRate C L (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (rate_of_source C L U _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedSmallAddendRate

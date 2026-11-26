import IPRADerivations.Analysis.Names.GaussianNameReciprocal
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# Tightness of the finite apartness predicate for regular names

An excluded apartness certificate bounds the corresponding observation
by the opposite rational norm comparison. Regularity and finite rational
slack removal carry these bounds to all observation indices. The proof
also applies to the original named difference of two regular names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedApartnessTightness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans point_at)
open GaussianNameReciprocal (apart anchor)
open GaussianNameRingLaws (zeroF zero_at zero_fast add_associative add_commutative add_negative add_zero_left
  negativeF negativeData negative_fast)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qnormSq squaredTolerance)
open GaussianRationalSlackRemoval (slack precision slack_removal_at)
open GaussianReconstructionRoots (norm_from_distance distance_zero_iff)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "D" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

def noApart (f : PR 2) (x : PTm n) : Fm PTm n := .all (neg (apart f (var 0) (Syn.shift x)))

@[simp] theorem subst_noApart {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    (noApart f x).subst σ = noApart f (Syn.subst σ x) := by
  simp [noApart, neg, Syn.subst_shift, Syn.shift_subst]

theorem anchor_bound (f : PR 2) (h x : PTm n) (ha : Γ ⊢[PRAAx] neg (apart f h x)) :
    Γ ⊢[PRAAx] bounded (ap2 f (anchor h) x) one (unit h) := by
  let q := ap2 f (anchor h) x
  exact .orE (RationalArgmin.total (qnormSq q) (squaredTolerance one (unit h))) Prf.hyp0
    (.botE _ (ha.wk.impE Prf.hyp0))

private theorem observation_slack (f : PR 2) (x p h : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (ha : Γ ⊢[PRAAx] noApart f x) : Γ ⊢[PRAAx] slack (ap2 f p x) one (unit p) two h := by
  let P := unit p
  let H := unit h
  let V := unit (anchor h)
  have hP := unit_positive (Γ := Γ) p
  have hH := unit_positive (Γ := Γ) h
  have hV := unit_positive (Γ := Γ) (anchor h)
  have hPV := positive_product _ _ hP hV
  have ha' : Γ ⊢[PRAAx] neg (apart f h x) := by simpa [noApart, neg] using ha.allE h
  have base := anchor_bound f h x ha'
  have near := norm_from_distance _ _ _ _ _ _ hPV hH (point_at f x p (anchor h) hf) base
  have late : Γ ⊢[PRAAx] le H V := unit_monotone (le_add_right _ _)
  change Γ ⊢[PRAAx] bounded (ap2 f p x) (one*H+two*P) (P*H)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hPV hH) (positive_product _ _ hP hH)
    (by ipra_le 𝔞(P)^2*𝔞(H)*sl late) near

theorem sample_bound (f : PR 2) (x p : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] noApart f x) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) one (unit p) :=
  slack_removal_at _ _ _ two (unit_positive p) (observation_slack f x p (precision _ one (unit p) two) hf ha)

private theorem zero_comparison_at (f : PR 2) (x z p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (ha : Γ ⊢[PRAAx] noApart f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 zeroF q z) (unit p+unit q) (unit p*unit q) := by
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have near := (distance_zero_iff (ap2 f p x) one (unit p) hp).iffMpr (sample_bound f x p hf ha)
  exact distance_congr (.eqRefl _) (zero_at q z).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hp (positive_product _ _ hp hq) (by ipra_le 𝔞(unit p)^2) near)

/-- The zero program accepts arbitrary data, including the literal term zero. -/
theorem of_no_apart_at_zero_data (f : PR 2) (x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (ha : Γ ⊢[PRAAx] noApart f x) : Γ ⊢[PRAAx] crossEquivalent f zeroF x z := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let y := Syn.shift (Syn.shift x)
  have hs : Δ ⊢[PRAAx] pointCN f y := by simpa [Δ, y, Fm.shift, Syn.shift] using hf.shift.shift
  have as_ : Δ ⊢[PRAAx] noApart f y := by simpa [Δ, y, Fm.shift, Syn.shift] using ha.shift.shift
  exact .allI (.allI (zero_comparison_at f y (Syn.shift (Syn.shift z)) (var 1) (var 0) hs as_))

theorem of_no_apart (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (ha : Γ ⊢[PRAAx] noApart f x) : Γ ⊢[PRAAx] crossEquivalent f zeroF x zero :=
  of_no_apart_at_zero_data f x zero hf ha

private theorem zero_data_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast x) (zero_fast y)
  refine .allI ?_
  exact (zero_at _ (Syn.shift x)).eqTrans (zero_at _ (Syn.shift y)).eqSymm

theorem names_equivalent_of_no_difference_apart (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] noApart (D f g) (dd x y)) : Γ ⊢[PRAAx] crossEquivalent f g x y := by
  let M := negativeF g
  let z := negativeData y
  let d := dd x y
  have hn := negative_fast g y hg
  have hD := GaussianNamedDifference.name_regular f g x y hf hg
  have hzero := of_no_apart_at_zero_data _ _ y hD ha
  have removed := add_cross (D f g) zeroF g g d y y y hD (zero_fast y) hg hg hzero (cross_refl _ _ hg)
  have swapped := add_commutative M g z y hn hg
  have cancel := cross_trans _ _ _ _ _ _ swapped
    (cross_trans _ _ _ _ _ _ (add_negative g y hg) (zero_data_cross y x))
  have restored := cross_trans _ _ _ _ _ _ (add_associative f M g x z y hf hn hg)
    (cross_trans _ _ _ _ _ _ (add_cross f f (addF M g) zeroF x x (addData z y) x hf hf
      (add_fast _ _ _ _ hn hg) (zero_fast x) (cross_refl _ _ hf) cancel) (GaussianNameRingLaws.add_zero f x hf))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ restored)
    (cross_trans _ _ _ _ _ _ removed (add_zero_left g y hg))

theorem actual_named_apartness_tightness_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((pointCN f (var 0) ⋏ noApart f (var 0)) ⟶ crossEquivalent f zeroF (var 0) zero) :=
  closeUniv 1 (.impI (of_no_apart f _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedApartnessTightness

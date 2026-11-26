import IPRADerivations.Analysis.Exponential.Names.GaussianFiniteExponentialLocalUniqueness
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialDifferenceIdentity
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealNameExponentialUnitReflection

/-!
# Local uniqueness of the original complex exponential

Late centered samples of radius at most three quarters suffice. Read the
original exponential at its computed later clock, contract its finite
argument, and transfer the resulting bound back to the requested sample.
For comparing two exponential values, apply the estimate to the actual
difference name.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialLocalUniqueness

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianExponentialRadiusIndependence (independent_radii_proper input_widen)
open GaussianFastValueCut (exponent query_budget)
open GaussianFiniteExponentialLocalUniqueness (tolerance contraction)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_symm cross_refl point_at)
open GaussianNameRingLaws (oneF one_at)
open GaussianRadiusExponentialName (input sample_at data nameF inputPrecision index value)
open GaussianRationalHorner (canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data

def lateSmall (f : PR 2) (x C : PTm n) : Fm PTm n := .all
  (le (Syn.shift C) (var 0) ⟶
    (canonical (ap2 f (var 0) (Syn.shift x)) ⋏ bounded (ap2 f (var 0) (Syn.shift x)) (num 3) (num 4)))

ipra_subst lateSmall [Syn.subst_shift, Syn.shift_subst]

theorem late_at (f : PR 2) (x C t : PTm n) (h : Γ ⊢[PRAAx] lateSmall f x C)
    (ht : Γ ⊢[PRAAx] le C t) :
    Γ ⊢[PRAAx] canonical (ap2 f t x) ⋏ bounded (ap2 f t x) (num 3) (num 4) := by
  have rule : Γ ⊢[PRAAx] le C t ⟶
      (canonical (ap2 f t x) ⋏ bounded (ap2 f t x) (num 3) (num 4)) := by
    simpa [lateSmall] using h.allE t
  exact .impE rule ht

private theorem index_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (index R p) := by
  let K := index R p
  let k := GaussianRationalExponentialTail.cutoff R (p+num 4)
  have e : Γ ⊢[PRAAx] succ K ≐ k := GaussianRationalExponentialTail.last_successor R (p+num 4)
  have h : Γ ⊢[PRAAx] le two k := by
    unfold k GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞 R+𝔞 R+𝔞 R*𝔞(R+R)+𝔞 p+6
  exact (succ_monus_succ one K).eqSymm.eqTrans (le_congr (.eqRefl two) e.eqSymm h)

theorem sample_zero (f : PR 2) (R x C anchor p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hs : Γ ⊢[PRAAx] lateSmall f x C)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) (num 3) (unit p) := by
  let r := exponent (num 32) (p+C)
  let t := inputPrecision R r
  let U := unit p
  let V := unit r
  let T := unit t
  let q := ap2 f t x
  have hp : Γ ⊢[PRAAx] le p (p+C) := le_add_right _ _
  have hc : Γ ⊢[PRAAx] le C (p+C) := le_add_left _ _
  have late : Γ ⊢[PRAAx] le (p+C) r := le_add_right _ _
  have rt : Γ ⊢[PRAAx] le r t := by
    unfold t inputPrecision
    exact le_trans (le_add_right _ _) (le_add_right _ _)
  have ht := late_at f x C t hs (le_trans hc (le_trans late rt))
  have budget : Γ ⊢[PRAAx] le (num 32*U) V :=
    le_trans
      (mul_le_mul_left (num 32) (unit_monotone hp))
      (query_budget _ _)
  have out := cross_at _ _ _ _ r r he
  have valueError : Γ ⊢[PRAAx] distanceBounded (value f R r x) qone (V+V) (V*V) :=
    distance_congr (sample_at f R r x) (one_at r anchor) (.eqRefl _) (.eqRefl _) out
  have den := positive_product _ _ (by ipra_le 15 : Γ ⊢[PRAAx] le one (num 16)) (unit_positive p)
  have smaller : Γ ⊢[PRAAx] distanceBounded (value f R r x) qone one (tolerance p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive r)) den
      (by unfold tolerance; ipra_le 𝔞 V*sl budget) valueError
  have bound : Γ ⊢[PRAAx] bounded q one U := contraction q (index R r) p ht.andE₁ (index_positive R r) ht.andE₂ smaller
  have lateT : Γ ⊢[PRAAx] le U T := unit_monotone (le_trans hp (le_trans late rt))
  have dist : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) q two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive t)) (unit_positive p)
      (by ipra_le 𝔞 U*sl lateT) (point_at f x p t hf.andE₁)
  have qZero := (GaussianReconstructionRoots.distance_zero_iff q one U (unit_positive p)).iffMpr bound
  have joined := distance_triangle_same _ _ _ _ _ _ (unit_positive p) dist qZero
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive p)).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) joined)

theorem unit_reflection (f : PR 2) (R x C anchor : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hs : Γ ⊢[PRAAx] lateSmall f x C)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor) :
    Γ ⊢[PRAAx] crossEquivalent f GaussianNameRingLaws.zeroF x anchor := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 3) hf.andE₁ (GaussianNameRingLaws.zero_fast _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (u : PTm n) := Syn.shift u
  have i : Δ ⊢[PRAAx] input f (sh R) (sh x) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hf.shift
  have s : Δ ⊢[PRAAx] lateSmall f (sh x) (sh C) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hs.shift
  have e : Δ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data (sh R) (sh x)) (sh anchor) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using he.shift
  let p : PTm (n+1) := var 0
  have b := sample_zero f (sh R) (sh x) (sh C) (sh anchor) p i s e
  have d := distance_congr (.eqRefl _) (GaussianNameRingLaws.zero_at p (sh anchor)).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive p)).iffMpr b)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,LeanProofs.IPRA.PTm.subst_num,sh,p,Δ] using d

theorem difference_diagonal (f g : PR 2) (R x y C p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (hs : Γ ⊢[PRAAx] lateSmall (F f g) (X x y) C)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) (num 9) (unit p) := by
  let a := GaussianRationalMetric.qsub (ap2 f p x) (ap2 g p y)
  let b := ap2 (F f g) p (X x y)
  let U := unit p
  have d := GaussianNamedExponentialDifferenceIdentity.difference_input f g R x y hf hg
  have e := GaussianNamedExponentialDifferenceIdentity.difference_exponential_one f g R x y hf hg he
  have bZero := sample_zero (F f g) (R+R) (X x y) C y p d hs e
  have raw := GaussianNamedDifference.sample_error f g x y p hf.andE₁ hg.andE₁
  have near := distance_triangle_same a b GaussianRationalHorner.qzero (num 6) (num 3) U (unit_positive p)
    (distance_symmetric _ _ _ _ (unit_positive p) raw)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive p)).iffMpr bZero)
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (unit_positive p)).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) near)

theorem local_injective (f g : PR 2) (R S x y C : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (hs : Γ ⊢[PRAAx] lateSmall (F f g) (X x y) C)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data S y)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 9) hf.andE₁ hg.andE₁
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  let W := sh R+sh S
  have i : Δ ⊢[PRAAx] input f (sh R) (sh x) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hf.shift
  have j : Δ ⊢[PRAAx] input g (sh S) (sh y) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hg.shift
  have iw := input_widen f (sh R) W (sh x) i (le_add_right _ _)
  have jw := input_widen g (sh S) W (sh y) j (le_add_left _ _)
  have s : Δ ⊢[PRAAx] lateSmall (F f g) (X (sh x) (sh y)) (sh C) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hs.shift
  have e : Δ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data (sh R) (sh x)) (data (sh S) (sh y)) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using he.shift
  have join := cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross f W (sh R) (sh x) iw i)
    (cross_trans _ _ _ _ _ _ e (GaussianExponentialRadiusIndependence.same_input_cross g (sh S) W (sh y) j jw))
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,LeanProofs.IPRA.PTm.subst_num,sh,Δ]
    using difference_diagonal f g W (sh x) (sh y) (sh C) (var 0) iw jw s join

theorem actual_named_complex_exponential_locally_injective_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((input f (var 0) (var 2) ⋏ input g (var 1) (var 3)) ⟶
        lateSmall (F f g) (X (var 2) (var 3)) (var 4) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3)) ⟶
        crossEquivalent f g (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (local_injective f g _ _ _ _ _ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialLocalUniqueness

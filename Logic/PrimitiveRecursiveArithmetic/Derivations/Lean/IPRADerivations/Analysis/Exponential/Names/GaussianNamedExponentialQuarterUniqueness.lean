import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.GaussianRationalFourthRootBranch
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialLocalUniqueness
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNamedHalf

/-!
# Complex exponential uniqueness for late differences of radius three

Two exact named halvings put the quarter argument in the existing
three-quarter disk. Its exponential stays within 21/16 of one. A finite
fourth-root estimate selects the branch at one, after which local
exponential reflection and the two doubling identities recover the
original argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialQuarterUniqueness

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast addF addData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_symm cross_to_diagonal point_at)
open GaussianNameRingLaws (oneF one_at one_fast zeroF zero_at zero_fast multiply_sample_error)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianNamedExponentialLocalUniqueness (lateSmall)
open GaussianRadiusExponentialName (input data inputPrecision index)
open GaussianRationalHorner (qadd qmul qzero canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalReciprocal (bounded_product bound_congr qone)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalPolynomialExponential (scalarSum)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "H" => GaussianNamedHalf.nameF
local notation "hd" => GaussianNamedHalf.data
local notation "halfPoint" => GaussianEulerSquareFactorInverse.half

def lateRadius (f : PR 2) (x C : PTm n) : Fm PTm n := .all
  (le (Syn.shift C) (var 0) ⟶ bounded (ap2 f (var 0) (Syn.shift x)) (num 3) one)

ipra_subst lateRadius [Syn.subst_shift, Syn.shift_subst, one]

private theorem late_at (f : PR 2) (x C p : PTm n) (h : Γ ⊢[PRAAx] lateRadius f x C)
    (hp : Γ ⊢[PRAAx] le C p) : Γ ⊢[PRAAx] bounded (ap2 f p x) (num 3) one := by
  exact .impE (by simpa [lateRadius,one] using h.allE p) hp

private theorem half_bound : Γ ⊢[PRAAx] bounded (halfPoint : PTm n) one two := by
  let z : PTm n := ComplexLogarithmRemainder.scale one ComplexLogarithmRemainder.oneCode
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hn : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq z ≐ one :=
    (ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  apply GaussianRationalMetric.bounded_of_cleared _ z two one two ht ht (GaussianRationalHorner.ofGaussian_represents z two ht)
  exact le_congr
    ((by ipra_ring : Γ ⊢[PRAAx] two*two ≐ (two*two)*one).eqTrans (congrMul (.eqRefl _) hn.eqSymm))
    (by ipra_ring) (le_refl (two*two))

private theorem half_at (f : PR 2) (x p : PTm n) :
    Γ ⊢[PRAAx] ap2 (H f) p (hd f x) ≐
      qmul halfPoint (ap2 f (GaussianNamedSmallPerturbationTransport.productClock constantF f halfPoint x p) x) := by
  let k := GaussianNamedSmallPerturbationTransport.productClock constantF f halfPoint x p
  exact (GaussianNamedSmallPerturbationTransport.product_at constantF f halfPoint x p).eqTrans
    (qmul_congr (constant_at k halfPoint) (.eqRefl _))

private theorem quarter_at (f : PR 2) (x C p : PTm n) (h : Γ ⊢[PRAAx] lateRadius f x C)
    (hp : Γ ⊢[PRAAx] le C p) :
    Γ ⊢[PRAAx] canonical (ap2 (H (H f)) p (hd (H f) (hd f x))) ⋏
      bounded (ap2 (H (H f)) p (hd (H f) (hd f x))) (num 3) (num 4) := by
  let a := hd f x
  let b := ap2 (H f) (GaussianNamedSmallPerturbationTransport.productClock constantF (H f) halfPoint a p) a
  let k := GaussianNamedSmallPerturbationTransport.productClock constantF (H f) halfPoint a p
  let j := GaussianNamedSmallPerturbationTransport.productClock constantF f halfPoint x k
  have hk : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have hj : Γ ⊢[PRAAx] le k j := le_add_right _ _
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have inner : Γ ⊢[PRAAx] bounded b (num 3) two :=
    bound_congr (half_at f x k).eqSymm (one_mul _) (by ipra_ring)
    (bounded_product halfPoint (ap2 f j x) one two (num 3) one ht (le_refl one) half_bound
      (late_at f x C j h (le_trans hp (le_trans hk hj))))
  have outer : Γ ⊢[PRAAx] bounded (ap2 (H (H f)) p (hd (H f) a)) (num 3) (num 4) :=
    bound_congr (half_at (H f) a p).eqSymm (one_mul _) (by ipra_ring)
    (bounded_product halfPoint b one two (num 3) two ht ht half_bound inner)
  exact .andI (GaussianNameArithmetic.multiply_canonical constantF (H f) halfPoint a p) outer

private theorem late_quarter (f : PR 2) (x C : PTm n) (h : Γ ⊢[PRAAx] lateRadius f x C) :
    Γ ⊢[PRAAx] lateSmall (H (H f)) (hd (H f) (hd f x)) C := by
  refine .allI (.impI ?_)
  let Δ := le (Syn.shift C) (var 0) :: Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] lateRadius f (Syn.shift x) (Syn.shift C) := by
    simpa only [Fm.shift,Syn.shift,subst_lateRadius,Δ] using h.shift.wk
  simpa only [lateSmall,Syn.shift,GaussianNamedHalf.subst_data,LeanProofs.IPRA.PTm.subst_num,Δ] using
    quarter_at f (Syn.shift x) (Syn.shift C) (var 0) h' Prf.hyp0

private theorem index_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (index R p) := by
  let K := index R p
  let k := GaussianRationalExponentialTail.cutoff R (p+num 4)
  have e : Γ ⊢[PRAAx] succ K ≐ k := GaussianRationalExponentialTail.last_successor R (p+num 4)
  have h : Γ ⊢[PRAAx] le two k := by
    unfold k GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le (Groth.ι (IPRA.Q.mk Γ R))*2+(Groth.ι (IPRA.Q.mk Γ R))^2*2+(Groth.ι (IPRA.Q.mk Γ p))+6
  exact (succ_monus_succ one K).eqSymm.eqTrans (le_congr (.eqRefl two) e.eqSymm h)

private theorem near_one (f : PR 2) (R x C p : PTm n) (hs : Γ ⊢[PRAAx] lateSmall f x C)
    (hp : Γ ⊢[PRAAx] le C p) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (E f) p (data R x)) qone (num 21) (num 16) := by
  let j := inputPrecision R p
  let q := ap2 f j x
  let K := index R p
  have hj : Γ ⊢[PRAAx] le p j := le_trans (le_add_right _ _) (le_add_right _ _)
  have hq := GaussianNamedExponentialLocalUniqueness.late_at f x C j hs (le_trans hp hj)
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have h16 : Γ ⊢[PRAAx] le one (num 16 : PTm n) := by ipra_le 15
  have tail := GaussianExponentialLinearRemainder.original_finite_linear_remainder q (num 3) (num 4) K h4
    (by ipra_le 1) hq.andE₂ hq.andE₁ (index_positive R p)
  have raw : Γ ⊢[PRAAx] distanceBounded (scalarSum q K) (qadd qone q) (num 9) (num 16) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) tail
  have linear : Γ ⊢[PRAAx] distanceBounded (qadd qone q) qone (num 12) (num 16) := by
    have e := (qsub_congr (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) qone q) (.eqRefl qone)).eqTrans
      (GaussianReciprocalHorner.qsub_add_cancel q qone hq.andE₁)
    exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ h4 h16 (le_of_eq_add (d := zero) (by ipra_ring)) hq.andE₂)
  exact distance_congr (GaussianRadiusExponentialName.sample_at f R p x).eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ h16 raw linear)

private def squareF (g : PR 2) : PR 2 := multiplyF g g
private def squareData (g : PR 2) (x : PTm n) : PTm n := multiplyData g g x x
private def fourthBudget (g : PR 2) (x : PTm n) : PTm n :=
  (multiplyModulus g g x x+one)*(U (squareF g) (squareData g x)+U g x*U g x)+
    (multiplyModulus (squareF g) (squareF g) (squareData g x) (squareData g x)+one)+two

private theorem fourth_at (g : PR 2) (x anchor p : PTm n) (hg : Γ ⊢[PRAAx] pointCN g x)
    (he : Γ ⊢[PRAAx] crossEquivalent (squareF (squareF g)) oneF (squareData (squareF g) (squareData g x)) anchor) :
    Γ ⊢[PRAAx] distanceBounded (qmul (qmul (ap2 g p x) (ap2 g p x)) (qmul (ap2 g p x) (ap2 g p x)))
      qone (fourthBudget g x) (unit p) := by
  let h := squareF g
  let y := squareData g x
  let u := ap2 g p x
  let v := qmul u u
  let w := ap2 h p y
  let M := multiplyModulus g g x x+one
  have hp := unit_positive (Γ := Γ) p
  have hw := multiply_fast g g x x hg hg
  have small := distance_symmetric _ _ _ _ hp (multiply_sample_error g g x x p hg hg)
  have ub := GaussianNameBounds.sample_bound g x p hg
  have vb : Γ ⊢[PRAAx] bounded v (U g x*U g x) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
      (bounded_product u u _ one _ one (le_refl _) (le_refl _) ub ub)
  have wb := GaussianNameBounds.sample_bound h y p hw
  have a := GaussianNameArithmetic.product_distance v w v w M M (unit p) (U g x*U g x) (U h y) hp small small vb wb
  have b := distance_symmetric _ _ _ _ hp (multiply_sample_error h h y y p hw hw)
  have c := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at _ _ _ _ p p he)
  exact distance_congr (.eqRefl _) (one_at p anchor) (by dsimp only [fourthBudget,M,h,y]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp a b) c)

private theorem fourth_reflection (f : PR 2) (R x C anchor : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hs : Γ ⊢[PRAAx] lateSmall f x C)
    (he : Γ ⊢[PRAAx] crossEquivalent (squareF (squareF (E f))) oneF
      (squareData (squareF (E f)) (squareData (E f) (data R x))) anchor) :
    Γ ⊢[PRAAx] crossEquivalent (E f) oneF (data R x) anchor := by
  let g := E f
  let y := data R x
  let K := two+num 4096*fourthBudget g y
  have hg := GaussianRadiusExponentialName.name_regular f R x hf
  refine cross_of_diagonal_rate _ _ _ _ K hg (one_fast anchor) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (s : PTm n) := Syn.shift s
  let p : PTm (n+1) := var 0
  let k := p+sh C
  have hf' : Δ ⊢[PRAAx] input f (sh R) (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift
  have hs' : Δ ⊢[PRAAx] lateSmall f (sh x) (sh C) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift
  have he' : Δ ⊢[PRAAx] crossEquivalent (squareF (squareF g)) oneF
      (squareData (squareF g) (squareData g (data (sh R) (sh x)))) (sh anchor) := by
    simpa [Fm.shift,Syn.shift,sh,Δ,squareData,y] using he.shift
  have hg' := GaussianRadiusExponentialName.name_regular f (sh R) (sh x) hf'
  have hp := unit_positive (Γ := Δ) p
  have hk := unit_positive (Γ := Δ) k
  have later := GaussianExponentialReference.unit_monotone (Γ := Δ) (le_add_right p (sh C))
  have q := GaussianRationalFourthRootBranch.cancel_fourth _ _ _ hk
    (near_one f (sh R) (sh x) (sh C) k hs' (le_add_left _ _)) (fourth_at g (data (sh R) (sh x)) (sh anchor) k hg' he')
  have step := distance_radius_mono _ _ _ _ _ (unit p) hk hp
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) later) q
  have earliest := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hk) hp
    (by
      ipra_le (Groth.ι (IPRA.Q.mk Δ (unit p)))*sl later)
    (point_at g (data (sh R) (sh x)) p k hg')
  simpa [diagonalRate,Syn.shift,sh,p,Δ,K,g,y,fourthBudget,squareData,two,one] using
    distance_congr (.eqRefl _) (one_at p (sh anchor)).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hp earliest step)

private theorem double_zero (f : PR 2) (x a : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (h : Γ ⊢[PRAAx] crossEquivalent (H f) zeroF (hd f x) a) :
    Γ ⊢[PRAAx] crossEquivalent f zeroF x a := by
  have hh := GaussianNamedHalf.regular f x hf
  have hz := zero_fast (Γ := Γ) a
  have d := cross_to_diagonal _ _ _ _ h
  have a := GaussianNameArithmetic.add_equivalent (H f) zeroF (H f) zeroF (hd f x) a (hd f x) a hh hz hh hz d d
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNamedHalf.double f x hf))
    (cross_trans _ _ _ _ _ _ a (GaussianNameRingLaws.add_zero zeroF _ hz))

/-- At any late observation radius three, the original exponential has
a unique inverse branch at one. -/
theorem unit_reflection (f : PR 2) (R x C a : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (hs : Γ ⊢[PRAAx] lateRadius f x C)
    (he : Γ ⊢[PRAAx] crossEquivalent (E f) oneF (data R x) a) :
    Γ ⊢[PRAAx] crossEquivalent f zeroF x a := by
  let h := H f
  let q := H h
  let u := hd f x
  let v := hd h u
  let e := exponentialInputData h u
  let c := exponentialInputData q v
  have hh := GaussianNamedHalf.regular f x hf.andE₁
  have hq := GaussianNamedHalf.regular h u hh
  have hi := exponential_input h u hh
  have qi := exponential_input q v hq
  have eh := GaussianRadiusExponentialName.name_regular _ _ _ hi
  have eq := GaussianRadiusExponentialName.name_regular _ _ _ qi
  have a₁ := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent q q h
    _ _ _ v v u qi qi hi (GaussianNamedHalf.double h u hh)
  have a₂ := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent h h f
    _ _ _ u u x hi hi hf (GaussianNamedHalf.double f x hf.andE₁)
  have sq := multiply_fast (E q) (E q) c c eq eq
  have rep := GaussianGammaAdjacentCutoff.multiply_cross (squareF (E q)) (E h) (squareF (E q)) (E h)
    (squareData (E q) c) e (squareData (E q) c) e sq eh sq eh a₁ a₁
  have fourth := cross_trans _ _ _ _ _ _ rep (cross_trans _ _ _ _ _ _ a₂ he)
  have small := late_quarter f x C hs
  have quarterExp := fourth_reflection q _ v C a qi small fourth
  have qZero := GaussianNamedExponentialLocalUniqueness.unit_reflection q _ v C a qi small quarterExp
  exact double_zero f x a hf.andE₁ (double_zero h u a hh qZero)

theorem actual_named_exponential_radius_three_unit_reflection_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (input f (var 0) (var 1) ⟶ lateRadius f (var 1) (var 2) ⟶
        crossEquivalent (E f) oneF (data (var 0) (var 1)) (var 3) ⟶ crossEquivalent f zeroF (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (unit_reflection f _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

private theorem difference_zero_at (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF f g) zeroF
      (GaussianNamedDifference.data x y) y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) (num 8) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have sub := distance_symmetric _ _ _ _ hp (GaussianNamedDifference.sample_error f g x y p hf hg)
  have close := distance_congr (.eqRefl _) (zero_at p y) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
      (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at _ _ _ _ p p he))
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hp).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hp sub close))

/-- Independently bounded original exponentials are injective when the
actual difference name eventually lies in the radius-three disk. -/
theorem injective (f g : PR 2) (R S x y C : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (hs : Γ ⊢[PRAAx] lateRadius (GaussianNamedDifference.nameF f g) (GaussianNamedDifference.data x y) C)
    (he : Γ ⊢[PRAAx] crossEquivalent (E f) (E g) (data R x) (data S y)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  let W := R+S
  have iw := GaussianExponentialRadiusIndependence.input_widen f R W x hf (le_add_right _ _)
  have jw := GaussianExponentialRadiusIndependence.input_widen g S W y hg (le_add_left _ _)
  have ex := cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross f W R x iw hf)
    (cross_trans _ _ _ _ _ _ he (GaussianExponentialRadiusIndependence.same_input_cross g S W y hg jw))
  have dif := GaussianNamedExponentialDifferenceIdentity.difference_input f g W x y iw jw
  have one := GaussianNamedExponentialDifferenceIdentity.difference_exponential_one f g W x y iw jw ex
  have eq := unit_reflection (GaussianNamedDifference.nameF f g) (W+W) (GaussianNamedDifference.data x y) C y dif hs one
  refine cross_of_diagonal_rate _ _ _ _ (num 8) hf.andE₁ hg.andE₁ (.allI ?_)
  let Δ := Γ.map Fm.shift
  let a := Syn.shift x
  let b := Syn.shift y
  have a' : Δ ⊢[PRAAx] pointCN f a := by simpa [Fm.shift,Syn.shift,Δ,a] using hf.andE₁.shift
  have b' : Δ ⊢[PRAAx] pointCN g b := by simpa [Fm.shift,Syn.shift,Δ,b] using hg.andE₁.shift
  have e' : Δ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF f g) zeroF (GaussianNamedDifference.data a b) b := by
    simpa [Fm.shift,Syn.shift,Δ,a,b] using eq.shift
  simpa [diagonalRate,Syn.shift,Δ,a,b] using difference_zero_at f g a b (var 0) a' b' e'

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialQuarterUniqueness

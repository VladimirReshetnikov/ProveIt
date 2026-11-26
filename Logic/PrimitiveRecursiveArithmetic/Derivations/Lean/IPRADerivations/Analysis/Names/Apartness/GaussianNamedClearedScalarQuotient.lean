import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialDifferenceIdentity
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaWeierstrassApproximant

/-!
# Solving a cleared scalar quotient with actual named arithmetic

From an original equality `L = S (1+a K)`, the actual named quotient
`a⁻¹ (L−S) S⁻¹` agrees with `K`. The reciprocal is the original
regular-name inverse with its stated apartness witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianNamedClearedScalarQuotient

open_ipra
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_product_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative add_commutative add_negative distributive
  multiply_associative multiply_commutative multiply_one multiply_one_left negativeF negativeData negative_fast
  oneF one_at one_fast zeroF zero_at zero_fast)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "difference" => GaussianNamedDifference.data
local notation "Inv" => GaussianNameReciprocal.nameF
local notation "inverse" => GaussianNameReciprocal.nameData

def weightedF (K : PR 2) : PR 2 := multiplyF constantF K
def weightedData (K : PR 2) (a k : PTm n) : PTm n := multiplyData constantF K a k
def factorF (K : PR 2) : PR 2 := addF oneF (weightedF K)
def factorData (K : PR 2) (b a k : PTm n) : PTm n := addData b (weightedData K a k)
def quotientF (L S : PR 2) : PR 2 := multiplyF constantF (multiplyF (Diff L S) (Inv S))
def quotientData (L S : PR 2) (l s c h : PTm n) : PTm n :=
  multiplyData constantF (multiplyF (Diff L S) (Inv S)) c
    (multiplyData (Diff L S) (Inv S) (difference l s) (inverse h s))

private theorem zero_cross (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent zeroF zeroF x y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (zero_fast x) (zero_fast y)
  exact .allI ((zero_at (var 0) (Syn.shift x)).eqTrans (zero_at (var 0) (Syn.shift y)).eqSymm)

private theorem constant_one (c x : PTm n) (h : Γ ⊢[PRAAx] c ≐ qone) : Γ ⊢[PRAAx] crossEquivalent constantF oneF c x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular c) (one_fast x)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] Syn.shift c ≐ qone := by simpa [Fm.shift,Syn.shift] using h.shift
  exact (constant_at (var 0) (Syn.shift c)).eqTrans (hs.eqTrans (one_at (var 0) (Syn.shift x)).eqSymm)

theorem subtract_first_addend (F G : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) :
    Γ ⊢[PRAAx] crossEquivalent (Diff (addF F G) F) G (difference (addData x y) x) y := by
  let N := negativeF F
  let u := negativeData x
  have hn := negative_fast F x hf
  have swap := add_cross (addF F G) (addF G F) N N (addData x y) (addData y x) u u
    (add_fast _ _ _ _ hf hg) (add_fast _ _ _ _ hg hf) hn hn (add_commutative F G x y hf hg) (cross_refl _ _ hn)
  have group := add_associative G F N y x u hg hf hn
  have cancel := cross_trans _ _ _ _ _ _ (add_negative F x hf) (zero_cross x y)
  have z := add_cross G G (addF F N) zeroF y y (addData x u) y hg hg
    (add_fast _ _ _ _ hf hn) (zero_fast y) (cross_refl _ _ hg) cancel
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ group
    (cross_trans _ _ _ _ _ _ z (GaussianNameRingLaws.add_zero G y hg)))

private theorem remove_one (F : PR 2) (x b : PTm n) (h : Γ ⊢[PRAAx] pointCN F x) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF F oneF) F (multiplyData F oneF x b) x := by
  have move := multiply_cross F F oneF oneF x x b x h h (one_fast b) (one_fast x) (cross_refl _ _ h)
    (GaussianNamedExponentialDifferenceIdentity.ones_equivalent b x)
  exact cross_trans _ _ _ _ _ _ move (multiply_one F x h)

private theorem numerator_cross (L S K : PR 2) (l s k a b : PTm n)
    (hL : Γ ⊢[PRAAx] pointCN L l) (hS : Γ ⊢[PRAAx] pointCN S s) (hK : Γ ⊢[PRAAx] pointCN K k)
    (h : Γ ⊢[PRAAx] crossEquivalent L (multiplyF S (factorF K)) l (multiplyData S (factorF K) s (factorData K b a k))) :
    Γ ⊢[PRAAx] crossEquivalent (Diff L S) (multiplyF S (weightedF K)) (difference l s)
      (multiplyData S (weightedF K) s (weightedData K a k)) := by
  let T := weightedF K
  let t := weightedData K a k
  let M := multiplyF S T
  let m := multiplyData S T s t
  have ht : Γ ⊢[PRAAx] pointCN T t := multiply_fast _ _ _ _ (constant_regular a) hK
  have hm : Γ ⊢[PRAAx] pointCN M m := multiply_fast _ _ _ _ hS ht
  have distribute := distributive S oneF T s b t hS (one_fast b) ht
  have replace := add_cross (multiplyF S oneF) S M M (multiplyData S oneF s b) s m m
    (multiply_fast _ _ _ _ hS (one_fast b)) hS hm hm (remove_one S s b hS) (cross_refl _ _ hm)
  have rhs := cross_trans _ _ _ _ _ _ h (cross_trans _ _ _ _ _ _ distribute replace)
  have moved := difference_proper L (addF S M) S S l (addData s m) s s hL (add_fast _ _ _ _ hS hm) hS hS rhs
    (cross_refl _ _ hS)
  exact cross_trans _ _ _ _ _ _ moved (subtract_first_addend S M s m hS hm)

private theorem divide_left_factor (S T : PR 2) (s t h : PTm n)
    (hS : Γ ⊢[PRAAx] pointCN S s) (hT : Γ ⊢[PRAAx] pointCN T t)
    (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart S h s) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF S T) (Inv S)) T
      (multiplyData (multiplyF S T) (Inv S) (multiplyData S T s t) (inverse h s)) t := by
  let I := Inv S
  let i := inverse h s
  have hi := GaussianNameReciprocal.name_fast S h s hS ha
  have swap := multiply_cross (multiplyF S T) (multiplyF T S) I I _ _ i i (multiply_fast _ _ _ _ hS hT)
    (multiply_fast _ _ _ _ hT hS) hi hi (multiply_commutative S T s t hS hT) (cross_refl _ _ hi)
  have assoc := multiply_associative T S I t s i hT hS hi
  have unit := multiply_cross T T (multiplyF S I) oneF t t _ t hT hT (multiply_fast _ _ _ _ hS hi) (one_fast t)
    (cross_refl _ _ hT) (cross_trans _ _ _ _ _ _ (GaussianNameReciprocal.product_one S h s hS ha)
      (GaussianNamedExponentialDifferenceIdentity.ones_equivalent s t))
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ unit (multiply_one T t hT)))

theorem quotient_agrees (L S K : PR 2) (l s k a b c h : PTm n)
    (hL : Γ ⊢[PRAAx] pointCN L l) (hS : Γ ⊢[PRAAx] pointCN S s) (hK : Γ ⊢[PRAAx] pointCN K k)
    (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart S h s) (hc : Γ ⊢[PRAAx] qmul c a ≐ qone)
    (cleared : Γ ⊢[PRAAx] crossEquivalent L (multiplyF S (factorF K)) l
      (multiplyData S (factorF K) s (factorData K b a k))) : Γ ⊢[PRAAx]
    crossEquivalent (quotientF L S) K (quotientData L S l s c h) k := by
  let T := weightedF K
  let t := weightedData K a k
  let I := Inv S
  let i := inverse h s
  let v := difference l s
  let F := multiplyF (Diff L S) I
  let f := multiplyData (Diff L S) I v i
  have ht : Γ ⊢[PRAAx] pointCN T t := multiply_fast _ _ _ _ (constant_regular a) hK
  have hi := GaussianNameReciprocal.name_fast S h s hS ha
  have hv := GaussianNamedDifference.name_regular L S l s hL hS
  have hf : Γ ⊢[PRAAx] pointCN F f := multiply_fast _ _ _ _ hv hi
  have num := numerator_cross L S K l s k a b hL hS hK cleared
  have inv := multiply_cross (Diff L S) (multiplyF S T) I I v _ i i hv (multiply_fast _ _ _ _ hS ht) hi hi num
    (cross_refl _ _ hi)
  have ratio := cross_trans _ _ _ _ _ _ inv (divide_left_factor S T s t h hS ht ha)
  have outer := multiply_cross constantF constantF F T c c f t (constant_regular c) (constant_regular c) hf ht
    (cross_refl _ _ (constant_regular c)) ratio
  have regroup := cross_symm _ _ _ _ (multiply_associative constantF constantF K c a k (constant_regular c) (constant_regular a) hK)
  have cc := cross_trans (multiplyF constantF constantF) constantF oneF (multiplyData constantF constantF c a)
    (qmul c a) k (constant_product_cross c a) (constant_one (qmul c a) k hc)
  have one := multiply_cross (multiplyF constantF constantF) oneF K K _ k k k
    (multiply_fast _ _ _ _ (constant_regular c) (constant_regular a)) (one_fast k) hK hK cc (cross_refl _ _ hK)
  exact cross_trans _ _ _ _ _ _ outer (cross_trans _ _ _ _ _ _ regroup
    (cross_trans _ _ _ _ _ _ one (multiply_one_left K k hK)))

end LeanProofs.IPRA.Analysis.GaussianNamedClearedScalarQuotient

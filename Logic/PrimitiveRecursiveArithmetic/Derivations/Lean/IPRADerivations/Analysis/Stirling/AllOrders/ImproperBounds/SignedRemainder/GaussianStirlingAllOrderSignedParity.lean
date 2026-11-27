import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.SignedRemainder.GaussianStirlingAllOrderSignedParityAlgebra
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderLinear

/-!
# Strict bounds on the un-oriented log-Stirling error

At even truncation orders the original error lies strictly between
zero and the first omitted term. At odd orders it lies strictly
between the first omitted term and zero. The comparison uses the
actual literal truncation and its original error name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedParity

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaStrongLogConvexityAlgebra (add_negative_front)
open GaussianNameArithmetic (multiplyF multiplyData multiplyRawF multiplyModulus multiply_fast multiply_raw_at multiply_regular
  addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast negativeRawF negative_raw_at
  negative_regular oneF one_fast multiply_one_left add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (negative_order negative_constant)
open GaussianNamedRealOrderTransport (transport)
open GaussianRationalHorner (qzero qmul)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative qsub qnegative_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qzero_add)
open GaussianRationalReciprocal (qone)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianStirlingNames (source)
open GaussianStirlingAllOrderLogTruncation (errorF errorData error_regular)
open GaussianStirlingAllOrderSignedBounds (original_strict_oriented_bracket)
open GaussianStirlingAllOrderSignedBoundsTransport (orientedCap)
open GaussianStirlingAllOrderSignedLower (orientedF orientedData zeroPoint)
open GaussianStirlingAllOrderSignedLowerAlgebra (orientationPoint)
open GaussianStirlingAllOrderSignedParityAlgebra (orientation_even orientation_odd even_cap odd_cap)
open GaussianStirlingAllOrderTruncationAlgebra (correction)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF

theorem oriented_even (m : ℕ) (hm : Even m) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent orientedF errorF (orientedData m A B x) (errorData m A B x) := by
  let y := errorData m A B x
  let S := orientationPoint (n := n) m
  have hy := error_regular m A B x hs
  have h := cross_trans C C oneF S qone y (constant_equal_cross (Γ := Γ) S _ (orientation_even m hm))
    (GaussianArctangentExponentialPeriod.constant_one_cross y)
  exact GaussianNameRingLaws.multiply_unit_left C errorF S y y (constant_regular S) hy h

theorem even_bracket (m : ℕ) (hm : Even m) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder C errorF zeroPoint (errorData m A B x) ⋏
      strictOrder errorF C (errorData m A B x) (correction m A B) := by
  have b := original_strict_oriented_bracket m A B x hs
  have mid := oriented_even m hm A B x hs
  have c := constant_equal_cross (Γ := Γ) _ _ (even_cap m hm A B)
  exact .andI (strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ (constant_regular _)) mid b.andE₁)
    (strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ mid) c b.andE₂)

private theorem minus_product_raw (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyRawF C f) p (GaussianNameArithmetic.data minusOne x) ≐ ap2 (negativeRawF f) p x := by
  let q := ap2 f p x
  have read := multiply_raw_at (Γ := Γ) C f p (minusOne : PTm n) x
  exact read.eqTrans ((qmul_congr (constant_at p minusOne) (.eqRefl q)).eqTrans
    ((negative_as_minusOne q).eqSymm.eqTrans
      ((qzero_add _ (qnegative_canonical q)).eqSymm.eqTrans (negative_raw_at f x p).eqSymm)))

private theorem minus_product_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C f) (negativeF f)
      (multiplyData C f minusOne x) (negativeData x) := by
  refine GaussianValueNormalizerExtensionality.normalized_names_equivalent
    (multiplyRawF C f) (negativeRawF f) (multiplyModulus C f minusOne x) (one+one)
    (GaussianNameArithmetic.data minusOne x) x zero
    (multiply_regular _ _ _ _ (constant_regular minusOne) hf)
    (negative_regular f x hf) (.allI ?_)
  let y := Syn.shift x
  let p : PTm (n+1) := var 0
  have e := minus_product_raw (Γ := Γ.map Fm.shift) f p y
  have bd := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ.map Fm.shift)
    (ap2 (negativeRawF f) p y) (unit p) (unit_positive p)
  simpa only [Syn.shift,GaussianNameArithmetic.subst_data,GaussianRationalMatrixFiniteSums.subst_minusOne,
    ConciseIPRA.PTm.subst_zero,y,p] using
    GaussianRationalDistanceOrder.distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) bd

theorem oriented_odd (m : ℕ) (hm : Odd m) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent orientedF (negativeF errorF) (orientedData m A B x)
      (negativeData (errorData m A B x)) := by
  let y := errorData m A B x
  let S := orientationPoint (n := n) m
  have hy := error_regular m A B x hs
  have mid := multiply_cross C C errorF errorF S minusOne y y (constant_regular S) (constant_regular _)
    hy hy (constant_equal_cross _ _ (orientation_odd m hm)) (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _ mid (minus_product_cross _ _ hy)

private theorem reflect_negative_order (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] realOrder (negativeF g) (negativeF f) (negativeData y) (negativeData x)) :
    Γ ⊢[PRAAx] realOrder f g x y := by
  let a := addData y x
  let b := addData x y
  let A := addF g f
  let B := addF f g
  let F := negativeF f
  let u := negativeData x
  have ha := add_fast g f y x hg hf
  have hb := add_fast f g x y hf hg
  have hu := negative_fast f x hf
  have expansion := add_order (negativeF g) F A A (negativeData y) u a a h (order_refl _ _ ha)
  have left := add_negative_front g f y x hg hf
  have right := add_cross F F A B u u a b hu hu ha hb (cross_refl _ _ hu)
    (add_commutative g f y x hg hf)
  exact transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ right (add_negative_front f g x y hf hg)) expansion

private theorem reflect_negative_strict (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] strictOrder (negativeF g) (negativeF f) (negativeData y) (negativeData x)) :
    Γ ⊢[PRAAx] strictOrder f g x y :=
  .andI (reflect_negative_order f g x y hf hg h.andE₁)
    (.impI (h.andE₂.wk.impE (negative_order g f y x hg.wk hf.wk Prf.hyp0)))

private theorem negative_zero_point :
    Γ ⊢[PRAAx] crossEquivalent (negativeF C) C (negativeData (zeroPoint : PTm n)) zeroPoint := by
  have z : Γ ⊢[PRAAx] (zeroPoint : PTm n) ≐ qzero :=
    (GaussianStirlingOddCoefficients.fraction_embed zero one (le_refl one)).eqSymm.eqTrans RationalGaussianEmbedding.embed_zero
  have q : Γ ⊢[PRAAx] qsub qzero zeroPoint ≐ zeroPoint :=
    (qsub_congr (.eqRefl _) z).eqTrans
      ((GaussianCoefficientNormOrder.qsub_self _).eqTrans z.eqSymm)
  exact cross_trans _ _ _ _ _ _ (negative_constant _) (constant_equal_cross _ _ q)

private theorem negative_correction (m : ℕ) (hm : Odd m) (A B : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF C) C (negativeData (correction m A B)) (orientedCap m A B) := by
  let z := correction m A B
  have v : Γ ⊢[PRAAx] qsub qzero z ≐ qnegative z := qzero_add _ (qnegative_canonical z)
  exact cross_trans _ _ _ _ _ _ (negative_constant z)
    (constant_equal_cross _ _ (v.eqTrans (odd_cap m hm A B).eqSymm))

theorem odd_bracket (m : ℕ) (hm : Odd m) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder C errorF (correction m A B) (errorData m A B x) ⋏
      strictOrder errorF C (errorData m A B x) zeroPoint := by
  let y := errorData m A B x
  let z := correction m A B
  have b := original_strict_oriented_bracket m A B x hs
  have o := oriented_odd m hm A B x hs
  have c := negative_correction (Γ := Γ) m hm A B
  have d := strict_transport _ _ _ _ _ _ _ _ negative_zero_point o b.andE₁
  have u := strict_transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ o) (cross_symm _ _ _ _ c) b.andE₂
  have h := error_regular m A B x hs
  exact .andI (reflect_negative_strict C errorF z y (constant_regular _) h u)
    (reflect_negative_strict errorF C y zeroPoint h (constant_regular _) d)

theorem actual_even_log_Stirling_bracket_closed (m : ℕ) (hm : Even m) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (source (var 0) (var 1) ⟶
      strictOrder C errorF zeroPoint (errorData m (var 0) (var 1) (var 2)) ⋏
        strictOrder errorF C (errorData m (var 0) (var 1) (var 2)) (correction m (var 0) (var 1))) :=
  closeUniv 3 (.impI (even_bracket m hm _ _ _ Prf.hyp0))

theorem actual_odd_log_Stirling_bracket_closed (m : ℕ) (hm : Odd m) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (source (var 0) (var 1) ⟶
      strictOrder C errorF (correction m (var 0) (var 1)) (errorData m (var 0) (var 1) (var 2)) ⋏
        strictOrder errorF C (errorData m (var 0) (var 1) (var 2)) zeroPoint) :=
  closeUniv 3 (.impI (odd_bracket m hm _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedParity

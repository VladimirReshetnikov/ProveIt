import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalProductSign
import IPRADerivations.Analysis.Gamma.GaussianGammaPoleMultiplier
import IPRADerivations.Analysis.Integration.GaussianMomentReflection
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderLinear
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsStrictOrder
import IPRADerivations.Core.ParityArith

/-!
# Sign adjustment of a named magnitude on a negative Gamma interval

The original sign factor is (-1)^(N+1) on the interval indexed by N.
Multiplying by it either preserves a magnitude name or negates that name.
This gives the corresponding weak and strict comparisons for Gamma values.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedSign

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaNegativeIntervalProductSign (signUnit)
open GaussianGammaStrongLogConvexityAlgebra (add_negative_front)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyRawF multiplyModulus
  multiply_fast multiply_raw_at multiply_regular)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left multiply_associative negativeF negativeData negativeRawF
  negative_raw_at negative_regular negative_fast add_commutative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderTransport (transport)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative_canonical)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (powerF)
open GaussianRationalSyntheticDivision (qone qmul_congr qzero_add)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def valueF (f : PR 2) : PR 2 := multiplyF constantF f
def valueData (f : PR 2) (N x : PTm n) : PTm n := multiplyData constantF f (signUnit (succ N)) x

@[simp] theorem subst_valueData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (N x : PTm n) :
    Syn.subst σ (valueData f N x) = valueData f (Syn.subst σ N) (Syn.subst σ x) := by simp [valueData]

theorem value_regular (f : PR 2) (N x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (valueF f) (valueData f N x) :=
  multiply_fast _ _ _ _ (constant_regular _) hf

theorem even_interval_sign (N : PTm n) (h : Γ ⊢[PRAAx] par N ≐ zero) : Γ ⊢[PRAAx] signUnit (succ N) ≐ minusOne :=
  (congrAp2 powerF (congrSucc (even_of h)) (.eqRefl _)).eqTrans
    ((GaussianRationalParityPower.minus_one_power _).eqTrans (GaussianMomentReflection.parity_odd (half N)))

theorem odd_interval_sign (N : PTm n) (h : Γ ⊢[PRAAx] par N ≐ one) : Γ ⊢[PRAAx] signUnit (succ N) ≐ qone := by
  have e : Γ ⊢[PRAAx] succ N ≐ two*succ (half N) := (congrSucc (odd_of h)).eqTrans (by ipra_ring)
  exact (congrAp2 powerF e (.eqRefl _)).eqTrans
    ((GaussianRationalParityPower.minus_one_power _).eqTrans (GaussianMomentReflection.parity_even (succ (half N))))

theorem sign_cases (N : PTm n) : Γ ⊢[PRAAx] (signUnit (succ N) ≐ qone) ⋎ (signUnit (succ N) ≐ minusOne) :=
  .orE (par_cases N) (.orI₂ (even_interval_sign N Prf.hyp0)) (.orI₁ (odd_interval_sign N Prf.hyp0))

private theorem minus_product_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyRawF constantF f) p (GaussianNameArithmetic.data minusOne x) ≐ ap2 (negativeRawF f) p x := by
  let q := ap2 f p x
  have read := multiply_raw_at (Γ := Γ) constantF f p (minusOne : PTm n) x
  exact read.eqTrans ((qmul_congr (constant_at p minusOne) (.eqRefl q)).eqTrans
    ((negative_as_minusOne q).eqSymm.eqTrans
      ((qzero_add _ (qnegative_canonical q)).eqSymm.eqTrans (negative_raw_at f x p).eqSymm)))

theorem minus_product_cross (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (valueF f) (negativeF f) (multiplyData constantF f minusOne x) (negativeData x) := by
  refine GaussianValueNormalizerExtensionality.normalized_names_equivalent
    (multiplyRawF constantF f) (negativeRawF f) (multiplyModulus constantF f minusOne x) (one+one)
    (GaussianNameArithmetic.data minusOne x) x zero
    (multiply_regular _ _ _ _ (constant_regular minusOne) hf) (negative_regular f x hf) (.allI ?_)
  let y := Syn.shift x
  let p : PTm (n+1) := var 0
  have eq := minus_product_at (Γ := Γ.map Fm.shift) f p y
  have bd := distance_refl_zero (Γ := Γ.map Fm.shift) (ap2 (negativeRawF f) p y) (unit p) (unit_positive p)
  simpa only [Syn.shift, GaussianNameArithmetic.subst_data, GaussianRationalMatrixFiniteSums.subst_minusOne,
    ConciseIPRA.PTm.subst_zero, y, p] using
    GaussianRationalDistanceOrder.distance_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) bd

theorem positive_cross (f : PR 2) (N x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hs : Γ ⊢[PRAAx] signUnit (succ N) ≐ qone) : Γ ⊢[PRAAx] crossEquivalent (valueF f) f (valueData f N x) x := by
  let s := signUnit (succ N)
  have e := cross_trans constantF constantF oneF s qone x (constant_data_cross _ _ hs)
    (GaussianArctangentExponentialPeriod.constant_one_cross x)
  have move := multiply_cross constantF oneF f f s x x x (constant_regular _) (one_fast x) hf hf e (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ move (multiply_one_left f x hf)

theorem negative_cross (f : PR 2) (N x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hs : Γ ⊢[PRAAx] signUnit (succ N) ≐ minusOne) :
    Γ ⊢[PRAAx] crossEquivalent (valueF f) (negativeF f) (valueData f N x) (negativeData x) :=
  cross_trans _ _ _ _ _ _ (multiply_cross constantF constantF f f (signUnit (succ N)) minusOne x x
    (constant_regular _) (constant_regular _) hf hf (constant_data_cross _ _ hs) (cross_refl _ _ hf))
    (minus_product_cross f x hf)

theorem value_involution (f : PR 2) (N x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (valueF (valueF f)) f (valueData (valueF f) N (valueData f N x)) x := by
  let s := signUnit (succ N)
  have hc := constant_regular (Γ := Γ) s
  have cc := multiply_fast constantF constantF s s hc hc
  have mulOne := cross_trans (Γ := Γ) _ _ _ _ _ _ (constant_product_cross s s)
    (cross_trans _ _ _ _ _ _ (constant_data_cross _ _ (GaussianGammaPoleMultiplier.sign_square (succ N)))
      (GaussianArctangentExponentialPeriod.constant_one_cross x))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative constantF constantF f s s x hc hc hf))
    (cross_trans _ _ _ _ _ _ (multiply_cross (multiplyF constantF constantF) oneF f f _ _ x x cc (one_fast x)
      hf hf mulOne (cross_refl _ _ hf)) (multiply_one_left f x hf))

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
  have right := add_cross F F A B u u a b hu hu ha hb (cross_refl _ _ hu) (add_commutative g f y x hg hf)
  exact transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ right (add_negative_front f g x y hf hg)) expansion

theorem positive_order (f g : PR 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] signUnit (succ N) ≐ qone) (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (valueF f) (valueF g) (valueData f N x) (valueData g N y) :=
  transport _ _ _ _ _ _ _ _ (positive_cross f N x hf hs) (cross_symm _ _ _ _ (positive_cross g N y hg hs)) h

theorem negative_order (f g : PR 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] signUnit (succ N) ≐ minusOne) (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (valueF g) (valueF f) (valueData g N y) (valueData f N x) :=
  transport _ _ _ _ _ _ _ _ (negative_cross g N y hg hs) (cross_symm _ _ _ _ (negative_cross f N x hf hs))
    (GaussianNamedRealOrderLinear.negative_order f g x y hf hg h)

theorem positive_strict_order (f g : PR 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] signUnit (succ N) ≐ qone) (h : Γ ⊢[PRAAx] strictOrder f g x y) :
    Γ ⊢[PRAAx] strictOrder (valueF f) (valueF g) (valueData f N x) (valueData g N y) :=
  strict_transport _ _ _ _ _ _ _ _ (positive_cross f N x hf hs) (cross_symm _ _ _ _ (positive_cross g N y hg hs)) h

theorem negative_strict_order (f g : PR 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hs : Γ ⊢[PRAAx] signUnit (succ N) ≐ minusOne) (h : Γ ⊢[PRAAx] strictOrder f g x y) :
    Γ ⊢[PRAAx] strictOrder (valueF g) (valueF f) (valueData g N y) (valueData f N x) := by
  have reversed : Γ ⊢[PRAAx] strictOrder (negativeF g) (negativeF f) (negativeData y) (negativeData x) :=
    .andI (GaussianNamedRealOrderLinear.negative_order f g x y hf hg h.andE₁)
      (.impI (h.andE₂.wk.impE (reflect_negative_order g f y x hg.wk hf.wk Prf.hyp0)))
  exact strict_transport _ _ _ _ _ _ _ _ (negative_cross g N y hg hs)
    (cross_symm _ _ _ _ (negative_cross f N x hf hs)) reversed

theorem actual_negative_interval_sign_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (((par (var 0) ≐ zero) ⟶ (signUnit (succ (var 0)) ≐ minusOne)) ⋏
      ((par (var 0) ≐ one) ⟶ (signUnit (succ (var 0)) ≐ qone))) :=
  closeUniv 1 (.andI (.impI (even_interval_sign _ Prf.hyp0)) (.impI (odd_interval_sign _ Prf.hyp0)))

theorem actual_negative_interval_value_strict_order_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((pointCN f (var 1) ⋏ (pointCN g (var 2) ⋏ strictOrder f g (var 1) (var 2))) ⟶
      (((par (var 0) ≐ one) ⟶ strictOrder (valueF f) (valueF g) (valueData f (var 0) (var 1)) (valueData g (var 0) (var 2))) ⋏
       ((par (var 0) ≐ zero) ⟶ strictOrder (valueF g) (valueF f) (valueData g (var 0) (var 2)) (valueData f (var 0) (var 1))))) :=
  closeUniv 3 (.impI (.andI
    (.impI (positive_strict_order f g _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁
      (odd_interval_sign _ Prf.hyp0) Prf.hyp1.andE₂.andE₂))
    (.impI (negative_strict_order f g _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁
      (even_interval_sign _ Prf.hyp0) Prf.hyp1.andE₂.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedSign

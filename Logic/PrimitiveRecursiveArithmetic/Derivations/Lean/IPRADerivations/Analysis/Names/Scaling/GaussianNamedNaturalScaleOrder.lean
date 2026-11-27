import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScaleOrder
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementObservations
import IPRADerivations.Analysis.Stirling.Bounds.Multiplicative.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# Positive natural scaling of real order on actual Gaussian names

The normalized product's dyadic observation cost is explicit. Removing
that cost preserves and reflects both weak and strict independent order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianNamedNaturalScaleOrder

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (addF addData multiply_fast multiplyModulus)
open GaussianNameRingLaws (add_sample_error multiply_sample_error sum_left_error sum_right_error three)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical qadd qmul positive_product)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalNaturalScale
  (naturalPoint natScale natScale_add natScale_as_product natScale_congr natScale_one_canonical natScale_sub)
open GaussianRationalNaturalScaleOrder (scale_upper reflect_upper)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qsub_add_cancel)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGlobalBounds (small_join)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingTailComparison (point_add_upper_same point_order_refl)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_of_radius)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF

def cost (f : PR 2) (t x : PTm n) : PTm n :=
  multiplyModulus C f (naturalPoint t) x+one

ipra_subst cost

theorem regular (f : PR 2) (t x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (productF f) (productData f t x) :=
  multiply_fast C f _ _ (constant_regular _) h

theorem sample_error (f : PR 2) (t x p : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (productF f) p (productData f t x))
      (natScale t (ap2 f p x)) (cost f t x) (unit p) :=
  distance_congr (.eqRefl _) ((qmul_congr (constant_at p (naturalPoint t)) (.eqRefl (ap2 f p x))).eqTrans
    (natScale_as_product _ _).eqSymm) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error C f (naturalPoint t) x p (constant_regular _) h)

theorem common_upper (f g : PR 2) (x y p : PTm n) (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (fstT (ap2 g p y)) two (unit p) :=
  upper_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive _) (unit_positive _))
    (real_order_at f g x y p p h) (le_of_eq_add (d := zero) (by ipra_ring))

private theorem cancel_scaled_base (W x y : PTm n) (hx : Γ ⊢[PRAAx] canonical x)
    (hy : Γ ⊢[PRAAx] canonical y) (hW : Γ ⊢[PRAAx] le one W) :
    Γ ⊢[PRAAx] qsub (qadd (natScale (pred W) x) y) (natScale W x) ≐ qsub y x := by
  let X := natScale (pred W) x
  have ew := (Common.pos_of_one_le hW).eqTrans (succ_eq_add_one (pred W))
  have split := (natScale_congr ew (.eqRefl x)).eqTrans
    ((natScale_add (pred W) one x).eqTrans (qadd_congr (.eqRefl X) (natScale_one_canonical x hx)))
  exact (qsub_congr (qadd_commutative X y) split).eqTrans
    ((subtract_sum (qadd y X) X x).eqSymm.eqTrans (qsub_congr (qsub_add_cancel y X hy) (.eqRefl x)))

private theorem translate_chord (m W X Y Z A P : PTm n)
    (hW : Γ ⊢[PRAAx] le one W) (hP : Γ ⊢[PRAAx] le one P)
    (hx : Γ ⊢[PRAAx] canonical X) (hy : Γ ⊢[PRAAx] canonical Y)
    (h : Γ ⊢[PRAAx] upper (fstT (qadd m (natScale W Z)))
      (fstT (qadd (natScale (pred W) X) Y)) A P) :
    Γ ⊢[PRAAx] upper (fstT (qadd m (natScale W (qsub Z X)))) (fstT (qsub Y X)) A P := by
  let v := natScale W X
  have sub : Γ ⊢[PRAAx] upper (fstT (qnegative v)) (fstT (qnegative v)) zero P :=
    upper_of_order _ _ _ _ (point_order_refl _)
  have together := point_add_upper_same _ _ _ _ _ _ _ hP h sub
  have left : Γ ⊢[PRAAx] qsub (qadd m (natScale W Z)) v ≐ qadd m (natScale W (qsub Z X)) :=
    (qadd_associative m (natScale W Z) (qnegative v)).eqTrans (qadd_congr (.eqRefl _) (natScale_sub W Z X))
  exact upper_congr (congrFst left) (congrFst (cancel_scaled_base W X Y hx hy hW))
    (LeanProofs.IPRA.add_zero A) (.eqRefl _) together

/-- Read a weighted chord at a single precision and subtract its full base
weight. The error is determined by the two scaling programs and the addition and order costs. -/
theorem weighted_chord_difference_at (G : PR 2) (p m W x y z : PTm n)
    (hW : Γ ⊢[PRAAx] le one W)
    (hx : Γ ⊢[PRAAx] pointCN G x) (hy : Γ ⊢[PRAAx] pointCN G y) (hz : Γ ⊢[PRAAx] pointCN G z)
    (canX : Γ ⊢[PRAAx] canonical (ap2 G p x)) (canY : Γ ⊢[PRAAx] canonical (ap2 G p y))
    (h : Γ ⊢[PRAAx] realOrder (addF C (productF G)) (addF (productF G) G)
      (addData m (productData G W z)) (addData (productData G (pred W) x) y)) :
    Γ ⊢[PRAAx] upper (fstT (qadd m (natScale W (qsub (ap2 G p z) (ap2 G p x)))))
      (fstT (qsub (ap2 G p y) (ap2 G p x))) (cost G W z+cost G (pred W) x+num 8) (unit p) := by
  let P := unit p
  let leftData := addData m (productData G W z)
  let rightData := addData (productData G (pred W) x) y
  let left := ap2 (addF C (productF G)) p leftData
  let right := ap2 (addF (productF G) G) p rightData
  let leftRaw := qadd m (natScale W (ap2 G p z))
  let rightRaw := qadd (natScale (pred W) (ap2 G p x)) (ap2 G p y)
  have hP := unit_positive (Γ := Γ) p
  have leftAdd : Γ ⊢[PRAAx] distanceBounded left (qadd m (ap2 (productF G) p (productData G W z))) three P :=
    distance_congr (.eqRefl _) (qadd_congr (constant_at p m) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
      (add_sample_error C (productF G) m (productData G W z) p (constant_regular m) (regular G W z hz))
  have rightAdd :=
    add_sample_error (productF G) G (productData G (pred W) x) y p (regular G (pred W) x hx) hy
  have leftErr : Γ ⊢[PRAAx] distanceBounded left leftRaw (three+cost G W z) P :=
    distance_triangle_same _ _ _ _ _ _ hP leftAdd (sum_right_error m _ _ _ _ hP (sample_error G W z p hz))
  have rightErr : Γ ⊢[PRAAx] distanceBounded right rightRaw (three+cost G (pred W) x) P :=
    distance_triangle_same _ _ _ _ _ _ hP rightAdd (sum_left_error _ _ _ _ _ hP (sample_error G (pred W) x p hx))
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP (distance_symmetric _ _ _ _ hP leftErr))
  have after := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hP rightErr)
  have middle := common_upper _ _ leftData rightData p h
  have together : Γ ⊢[PRAAx] upper (fstT leftRaw) (fstT rightRaw) (cost G W z+cost G (pred W) x+num 8) P :=
    upper_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
      (small_join _ _ _ _ _ p (small_join _ _ _ _ _ p before middle) after)
  exact translate_chord m W _ _ _ _ P hW hP canX canY together

theorem preserve_at (f g : PR 2) (t x y p : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (productF f) p (productData f t x))) (fstT (ap2 (productF g) p (productData g t y)))
      (cost f t x+t*two+cost g t y) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have l := scalar_upper _ _ _ _ hp (sample_error f t x p hf)
  have m := scale_upper t (ap2 f p x) (ap2 g p y) two (unit p) (common_upper f g x y p h)
  have r := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (sample_error g t y p hg))
  exact small_join _ _ _ _ _ p (small_join _ _ _ _ _ p l m) r

theorem reflect_at (f g : PR 2) (t x y p : PTm n) (ht : Γ ⊢[PRAAx] le one t)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] realOrder (productF f) (productF g) (productData f t x) (productData g t y)) :
    Γ ⊢[PRAAx] upper (fstT (ap2 f p x)) (fstT (ap2 g p y)) (cost f t x+two+cost g t y) (unit p) := by
  let A := cost f t x+two+cost g t y
  have hp := unit_positive (Γ := Γ) p
  have l := scalar_upper _ _ _ _ hp (distance_symmetric _ _ _ _ hp (sample_error f t x p hf))
  have m := common_upper (productF f) (productF g) (productData f t x) (productData g t y) p h
  have r := scalar_upper _ _ _ _ hp (sample_error g t y p hg)
  have joined := small_join _ _ _ _ _ p (small_join _ _ _ _ _ p l m) r
  have raw := reflect_upper t (ap2 f p x) (ap2 g p y) A (unit p) joined
  have leU : Γ ⊢[PRAAx] le (unit p) (t*unit p) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right (unit p) ht)
  exact upper_mono _ _ _ _ A (unit p) (positive_product _ _ ht hp) raw (le_mul_mono (le_refl A) leU)

theorem preserve_order (f g : PR 2) (t x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hg : Γ ⊢[PRAAx] pointCN g y) (h : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (productF f) (productF g) (productData f t x) (productData g t y) := by
  apply GaussianNamedRealOrderEnvelope.order_from_envelope (productF f) (productF g) (productData f t x)
    (productData g t y) (cost f t x+t*two+cost g t y) (regular f t x hf) (regular g t y hg)
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have hF : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have hG : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  have hO : Δ ⊢[PRAAx] realOrder f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  simpa [GaussianNamedRealOrderEnvelope.envelope,Δ,sh,Syn.shift] using
    preserve_at f g (sh t) (sh x) (sh y) (var 0) hF hG hO

theorem reflect_order (f g : PR 2) (t x y : PTm n) (ht : Γ ⊢[PRAAx] le one t)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] realOrder (productF f) (productF g) (productData f t x) (productData g t y)) :
    Γ ⊢[PRAAx] realOrder f g x y := by
  apply GaussianNamedRealOrderEnvelope.order_from_envelope f g x y (cost f t x+two+cost g t y) hf hg
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have hT : Δ ⊢[PRAAx] le one (sh t) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ht.shift
  have hF : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have hG : Δ ⊢[PRAAx] pointCN g (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift
  have hO : Δ ⊢[PRAAx] realOrder (productF f) (productF g) (productData f (sh t) (sh x)) (productData g (sh t) (sh y)) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  simpa [GaussianNamedRealOrderEnvelope.envelope,Δ,sh,Syn.shift] using
    reflect_at f g (sh t) (sh x) (sh y) (var 0) hT hF hG hO

theorem reflect_strict (f g : PR 2) (t x y : PTm n) (ht : Γ ⊢[PRAAx] le one t)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] strictOrder (productF f) (productF g) (productData f t x) (productData g t y)) :
    Γ ⊢[PRAAx] strictOrder f g x y :=
  .andI (reflect_order f g t x y ht hf hg h.andE₁)
    (.impI (h.andE₂.wk.impE (preserve_order g f t y x hg.wk hf.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedNaturalScaleOrder

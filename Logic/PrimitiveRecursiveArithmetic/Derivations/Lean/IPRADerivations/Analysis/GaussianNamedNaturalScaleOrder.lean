import IPRADerivations.Analysis.GaussianRationalNaturalScaleOrder
import IPRADerivations.Analysis.GaussianStirlingGammaFractionalIncrementObservations
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# Positive natural scaling of real order on actual Gaussian names

The normalized product's dyadic observation cost is explicit. Removing
that cost preserves and reflects both weak and strict independent order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianNamedNaturalScaleOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (multiply_fast multiplyModulus)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product)
open GaussianRationalNaturalScaleOrder (scale_upper reflect_upper)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingGlobalBounds (small_join)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open RationalValueBounds (upper upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF

def cost (f : PR 2) (t x : PTm n) : PTm n :=
  multiplyModulus C f (naturalPoint t) x+one

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (t x : PTm n) :
    Syn.subst σ (cost f t x) = cost f (Syn.subst σ t) (Syn.subst σ x) := by simp [cost]

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

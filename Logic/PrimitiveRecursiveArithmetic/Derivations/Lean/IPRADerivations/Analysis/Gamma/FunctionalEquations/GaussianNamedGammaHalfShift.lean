import IPRADerivations.Analysis.Euler.GaussianEulerNamedShiftInput
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealExponentialPositiveIncrement
import IPRADerivations.Analysis.RationalArithmetic.RationalUpperAddition

/-!
# Exact half shifts for named Gamma

The source certifies a real name above one half by an explicit positive
margin. The translated margin supplies the original Gamma source for
both half shifts using a single common certificate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaHalfShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_at add_fast add_equivalent)
open GaussianNameRingLaws (add_associative add_zero additive_inverse_value)
open GaussianRationalHorner (ofGaussian canonical canonical_unique represents_congr qadd qadd_canonical qzero)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qadd_congr qone_canonical)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_of_order upper_mono upper_congr)
open RationalGaussianEmbedding (embed axis)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def half : PTm n := embed (fraction one two)
def negativeHalf : PTm n := qsub qzero half
def threeHalves : PTm n := qadd qone half

def minusF (f : PR 2) : PR 2 := addF f constantF
def minusData (x : PTm n) : PTm n := addData x negativeHalf
def plusF (f : PR 2) : PR 2 := GaussianEulerNamedShiftInput.shiftF (minusF f)
def plusData (x : PTm n) : PTm n := GaussianEulerNamedShiftInput.shiftData (minusData x)
def floorPoint (A : PTm n) : PTm n := qadd (marginPoint A) half
def source (f : PR 2) (x A : PTm n) : Fm PTm n :=
  pointCN f x ⋏ (realSamples f x ⋏ (le one A ⋏ realOrder constantF f (floorPoint A) x))

@[simp] theorem subst_minusData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (minusData x) = minusData (Syn.subst σ x) := by simp [minusData,negativeHalf,half]
@[simp] theorem subst_plusData {m : ℕ} (σ : Fin n → PTm m) (x : PTm n) :
    Syn.subst σ (plusData x) = plusData (Syn.subst σ x) := by simp [plusData]
@[simp] theorem subst_floorPoint {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (floorPoint A) = floorPoint (Syn.subst σ A) := by simp [floorPoint,half]

theorem half_exact : Γ ⊢[PRAAx] (half : PTm n) ≐ ofGaussian oneCode two := by
  apply canonical_unique _ _ oneCode two (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ RationalAlgebra.two_positive) RationalAlgebra.two_positive
    (hrv := GaussianRationalHorner.ofGaussian_represents _ _ RationalAlgebra.two_positive)
  apply represents_congr (.eqRefl _) _ (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation _ _ _
      (fraction_represents _ _ RationalAlgebra.two_positive))
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat]
    ipra_simps <;> ring

theorem three_halves_exact : Γ ⊢[PRAAx] (threeHalves : PTm n) ≐ ofGaussian (scale (num 3) oneCode) two := by
  have hD := RationalAlgebra.two_positive (Γ := Γ)
  have hv := represents_congr half_exact.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents oneCode two hD)
  have rep := GaussianRationalHorner.qadd_represents qone half (scale two oneCode) oneCode two hD
    (qone_represents_scaled two) hv
  apply canonical_unique _ _ _ two (qadd_canonical _ _) (GaussianRationalHorner.ofGaussian_canonical _ _ hD)
    hD (hrv := GaussianRationalHorner.ofGaussian_represents _ _ hD)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rep
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat] <;> ipra_simps <;> ring

theorem negative_half_real : Γ ⊢[PRAAx] realSamples constantF (negativeHalf : PTm n) := by
  refine .allI ?_
  have can := GaussianRationalMetric.qsub_canonical (Γ := Γ.map Fm.shift) qzero half
  have ax : Γ.map Fm.shift ⊢[PRAAx] axis (negativeHalf : PTm (n+1)) :=
    RationalGaussianEmbedding.axis_add _ _ RationalGaussianEmbedding.axis_zero
      (RationalGaussianEmbedding.axis_negative _ (RationalGaussianEmbedding.embed_axis _))
  simpa only [realSamples,Syn.shift,negativeHalf,half,GaussianRationalMetric.subst_qsub,
    GaussianRationalHorner.subst_qzero,RationalGaussianEmbedding.subst_embed,
    GaussianEuclideanDistanceName.subst_fraction,PTm.subst_succ,PTm.subst_zero] using
    Prf.andI (GaussianRationalHorner.canonical_congr (constant_at (var 0) (negativeHalf : PTm (n+1))) can)
      (RationalGaussianEmbedding.axis_congr (constant_at (var 0) (negativeHalf : PTm (n+1))).eqSymm ax)

theorem add_constant_at (f : PR 2) (x c p : PTm n) : Γ ⊢[PRAAx]
    ap2 (addF f constantF) p (addData x c) ≐ qadd (ap2 f (GaussianEulerNamedShiftInput.clock p) x) c :=
  (add_at f constantF x c p).eqTrans
    ((GaussianNameArithmetic.recode_congr (qadd_congr (.eqRefl _) (constant_at _ c))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _)))

theorem minus_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (minusF f) (minusData x) :=
  add_fast f constantF x negativeHalf h (constant_regular _)

theorem minus_real (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] realSamples (minusF f) (minusData x) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have observation : Γ.map Fm.shift ⊢[PRAAx]
      (canonical (ap2 (minusF f) (var 0) (minusData (Syn.shift x))) ⋏
        axis (ap2 (minusF f) (var 0) (minusData (Syn.shift x)))) :=
    GaussianRealExponentialPositiveIncrement.sum_real_at f constantF (var 0) (Syn.shift x) negativeHalf hs negative_half_real
  simpa only [realSamples,subst_minusData,Syn.shift] using observation

theorem add_subtract_half (c : PTm n) (hc : Γ ⊢[PRAAx] canonical c) : Γ ⊢[PRAAx]
    qadd (qadd c half) negativeHalf ≐ c :=
  (qadd_associative _ _ _).eqTrans
    ((qadd_congr (.eqRefl _) (additive_inverse_value half)).eqTrans (qadd_zero_right _ hc))

theorem add_cross (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v)
    (ha : Γ ⊢[PRAAx] crossEquivalent f g x y) (hb : Γ ⊢[PRAAx] crossEquivalent h k u v) :
    Γ ⊢[PRAAx] crossEquivalent (addF f h) (addF g k) (addData x u) (addData y v) :=
  add_equivalent f g h k x y u v hf hg hh hk (cross_to_diagonal _ _ _ _ ha) (cross_to_diagonal _ _ _ _ hb)

theorem constant_sum (a b c : PTm n) (he : Γ ⊢[PRAAx] qadd a b ≐ c) :
    Γ ⊢[PRAAx] crossEquivalent (addF constantF constantF) constantF (addData a b) c := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (add_fast _ _ _ _ (constant_regular _) (constant_regular _))
    (constant_regular _)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] qadd (sh a) (sh b) ≐ sh c := by simpa [Fm.shift,Syn.shift,sh] using he.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianNameArithmetic.subst_addData,sh] using
    (add_constant_at constantF (sh a) (sh b) (var 0)).eqTrans
      ((qadd_congr (constant_at _ _) (.eqRefl _)).eqTrans (hs.eqTrans (constant_at _ _).eqSymm))

private theorem two_halves : Γ ⊢[PRAAx] qadd (half : PTm n) half ≐ qone := by
  have hD := RationalAlgebra.two_positive (Γ := Γ)
  have hv := represents_congr half_exact.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents oneCode two hD)
  have rep := GaussianRationalHorner.qadd_represents half half oneCode oneCode two hD hv hv
  apply canonical_unique _ _ _ two (qadd_canonical _ _) qone_canonical hD (hrv := qone_represents_scaled two)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) rep
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

private theorem negative_half_plus_one : Γ ⊢[PRAAx] qadd (negativeHalf : PTm n) qone ≐ half :=
  (qadd_congr (.eqRefl _) two_halves.eqSymm).eqTrans
    ((qadd_associative negativeHalf half half).eqSymm.eqTrans
      ((qadd_congr ((qadd_commutative _ _).eqTrans (additive_inverse_value half)) (.eqRefl _)).eqTrans
        (GaussianRationalSyntheticDivision.qzero_add _ (RationalGaussianEmbedding.embed_canonical _))))

/-- The recurrence input is a name for the ordinary positive half shift. -/
theorem plus_associated (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (plusF f) (addF f constantF) (plusData x) (addData x half) := by
  have hn := constant_regular (Γ := Γ) (negativeHalf : PTm n)
  have h1 := constant_regular (Γ := Γ) (qone : PTm n)
  have assoc := add_associative f constantF constantF x negativeHalf qone h hn h1
  have exactHalf := constant_sum negativeHalf qone (half : PTm n) (negative_half_plus_one (Γ := Γ))
  have add := add_cross f f (addF constantF constantF) constantF x x (addData negativeHalf qone) half h h
    (add_fast _ _ _ _ hn h1) (constant_regular _) (cross_refl _ _ h) exactHalf
  exact cross_trans _ _ _ _ _ _ assoc add

private theorem minus_certificate_at (f : PR 2) (p q x A : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (h : Γ ⊢[PRAAx] realOrder constantF f (floorPoint A) x) : Γ ⊢[PRAAx]
    upper (fstT (ap2 constantF p (marginPoint A))) (fstT (ap2 (minusF f) q (minusData x)))
      (unit p+unit q) (unit p*unit q) := by
  let r := GaussianEulerNamedShiftInput.clock q
  let z := ap2 f r x
  let b := fstT (negativeHalf : PTm n)
  have obs := real_order_at constantF f (floorPoint A) x p r h
  have old := upper_congr (congrFst (constant_at p (floorPoint A))) (.eqRefl _) (.eqRefl _) (.eqRefl _) obs
  have self : Γ ⊢[PRAAx] upper b b zero one :=
    upper_of_order _ _ _ _ (le_refl _)
  have temp := RationalUpperAddition.add_upper _ _ _ _ _ _ _ _ old self
  have left := (RationalGaussianRealPart.real_add (floorPoint A) negativeHalf).eqSymm.eqTrans
    (congrFst (add_subtract_half (marginPoint A) (GaussianRationalHorner.ofGaussian_canonical _ _ hA)))
  have right := (RationalGaussianRealPart.real_add (Γ := Γ) z negativeHalf).eqSymm.eqTrans
    (congrFst (add_constant_at f x negativeHalf q)).eqSymm
  have bound : Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (marginPoint A)))
      (fstT (ap2 (minusF f) q (minusData x))) (unit p+unit r) (unit p*unit r) :=
    upper_congr (left.eqTrans (congrFst (constant_at p (marginPoint A))).eqSymm) right
      (by ipra_ring) (by ipra_ring) temp
  have grow := GaussianExponentialReference.unit_monotone (GaussianEulerNamedShiftInput.clock_later (Γ := Γ) q)
  exact upper_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive r)) bound
    (by ipra_le 𝔞(unit p*unit p)*sl grow)

theorem minus_source (f : PR 2) (x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedGammaPositiveLower.source (minusF f) (minusData x) A := by
  refine .andI (.andI (minus_regular f x hs.andE₁) (.andI hs.andE₂.andE₂.andE₁ (.allI (.allI ?_))))
    (minus_real f x hs.andE₂.andE₁)
  let sh (w : PTm n) := Syn.shift (Syn.shift w)
  have hA : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh A) :=
    by simpa [Fm.shift,Syn.shift,sh] using hs.andE₂.andE₂.andE₁.shift.shift
  have old : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realOrder constantF f (floorPoint (sh A)) (sh x) :=
    by simpa [Fm.shift,Syn.shift,sh] using hs.andE₂.andE₂.andE₂.shift.shift
  simpa only [GaussianNamedRightHalfPlane.certificate,realOrder,Syn.shift,sh,subst_minusData,
    GaussianNamedRightHalfPlane.subst_marginPoint] using minus_certificate_at f (var 1) (var 0) (sh x) (sh A) hA old

theorem plus_source (f : PR 2) (x A : PTm n) (hs : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    GaussianNamedRightHalfPlane.source (plusF f) (plusData x) A :=
  GaussianEulerNamedShiftInput.original_source _ _ _ (minus_source f x A hs).andE₁

private theorem constant_zero (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent constantF GaussianNameRingLaws.zeroF qzero x := by
  apply GaussianNameConjugation.equal_samples_cross constantF GaussianNameRingLaws.zeroF qzero x
    (constant_regular qzero) (GaussianNameRingLaws.zero_fast x)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianRationalHorner.subst_qzero] using
    (constant_at (Γ := Γ.map Fm.shift) (var 0) qzero).eqTrans (GaussianNameRingLaws.zero_at (var 0) (Syn.shift x)).eqSymm

theorem minus_half_reflects_one (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (he : Γ ⊢[PRAAx] crossEquivalent (minusF f) constantF (minusData x) qone) :
    Γ ⊢[PRAAx] crossEquivalent f constantF x threeHalves := by
  let S := addF (minusF f) constantF
  let C := addF constantF constantF
  let P := addF f C
  let Z := GaussianNameRingLaws.zeroF
  let a := addData (minusData x) half
  let b : PTm n := addData negativeHalf half
  let c : PTm n := addData qone half
  have hf' := minus_regular f x hf
  have hc := constant_regular (Γ := Γ) (half : PTm n)
  have lifted : Γ ⊢[PRAAx] crossEquivalent S C a c :=
    add_cross (minusF f) constantF constantF constantF (minusData x) qone half half
      hf' (constant_regular _) hc hc he (cross_refl _ _ hc)
  have middle := add_associative f constantF constantF x negativeHalf half hf (constant_regular _) hc
  have cancelled := constant_sum (Γ := Γ) (negativeHalf : PTm n) half qzero
    ((qadd_commutative negativeHalf half).eqTrans (additive_inverse_value half))
  have to_zero := cross_trans C constantF Z b qzero x cancelled (constant_zero x)
  have lifted_zero := add_cross f f C Z x x b x hf hf
    (add_fast _ _ _ _ (constant_regular _) hc) (GaussianNameRingLaws.zero_fast x)
    (cross_refl _ _ hf) to_zero
  have id := cross_trans P (addF f Z) f (addData x b) (addData x x) x lifted_zero
    (GaussianNameRingLaws.add_zero f x hf)
  have right := cross_trans S C constantF a c threeHalves lifted (constant_sum qone half threeHalves (.eqRefl _))
  have left := cross_trans S P f a (addData x b) x middle id
  exact cross_trans f S constantF x a threeHalves (cross_symm S f a x left) right

theorem three_halves_gives_minus_one (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (he : Γ ⊢[PRAAx] crossEquivalent f constantF x threeHalves) :
    Γ ⊢[PRAAx] crossEquivalent (minusF f) constantF (minusData x) qone := by
  have c := constant_regular (Γ := Γ) (negativeHalf : PTm n)
  have h := add_cross f constantF constantF constantF x threeHalves negativeHalf negativeHalf hf
    (constant_regular _) c c he (cross_refl _ _ c)
  exact cross_trans (minusF f) (addF constantF constantF) constantF
    (minusData x) (addData threeHalves negativeHalf) qone h
    (constant_sum threeHalves negativeHalf qone (add_subtract_half _ qone_canonical))

end LeanProofs.IPRA.Analysis.GaussianNamedGammaHalfShift

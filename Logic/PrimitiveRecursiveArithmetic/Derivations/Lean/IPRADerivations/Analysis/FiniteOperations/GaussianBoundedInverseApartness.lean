import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialSmallPerturbation

/-!
# Constructive apartness from a bounded inverse name

The actual multiplication program for two regular names is assumed
equivalent to the constant one. A bound on the inverse gives a finite
binary-length demand for the original reciprocal program's anchor.
The resulting reciprocal agrees with the bounded inverse supplied in
the hypothesis, including when its bound is a nonintegral rational.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedInverseApartness

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation lower_to_cleared)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open ComplexLogarithmRemainder (scale oneCode normSq)
open GaussianRationalReciprocal (qone bound_congr bounded_sum qone_represents_scaled)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast multiply_equivalent)
open GaussianNameRingLaws (oneF one_at one_fast multiply_sample_error)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal cross_symm cross_trans diagonal_at diagonal_refl)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem lower_near_one (q : PTm n) (h : Γ ⊢[PRAAx] distanceBounded q qone one two) :
    Γ ⊢[PRAAx] lower q one two := by
  let D := rawDen q
  let r := scale D oneCode
  let t := rawGaussian q
  have d := raw_den_positive (Γ := Γ) q
  have hp : Γ ⊢[PRAAx] le one two := le_succ_self one
  have rr : Γ ⊢[PRAAx] GaussianRationalHorner.represents qone r D := qone_represents_scaled D
  have tt : Γ ⊢[PRAAx] GaussianRationalHorner.represents q t D := raw_represents q
  have main := (GaussianRationalMetric.bounded_difference_iff qone q r t D one two d hp rr tt).iffMp
    (distance_symmetric _ _ _ _ hp h)
  have norm : Γ ⊢[PRAAx] normSq r ≐ D*D :=
    (ComplexLogarithmRemainder.normSq_scale D oneCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  have ref : Γ ⊢[PRAAx] le (two*two*(D*D)) (two*two*normSq r) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) norm).eqSymm (le_refl _)
  exact lower_from_representation q t D one two d hp tt
    (le_congr (by ipra_ring) (.eqRefl _)
      (GaussianGeneralCoefficientNames.native_apart_tail r t D two ref
        (le_congr (.eqRefl _) (by ipra_ring) main)))

theorem factor_lower (q r A B M : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hP : Γ ⊢[PRAAx] lower (qmul q r) A B) (hr : Γ ⊢[PRAAx] bounded r M one) :
    Γ ⊢[PRAAx] lower q A (B*M) := by
  let D := rawDen q
  let E := rawDen r
  let u := rawGaussian q
  let v := rawGaussian r
  have d := raw_den_positive (Γ := Γ) q
  have e := raw_den_positive (Γ := Γ) r
  have mul := GaussianRationalHorner.qmul_represents q r u v D E d e (raw_represents q) (raw_represents r)
  have lp := lower_to_cleared _ _ _ _ _ (positive_product D E d e) hB mul hP
  have norm := natEq (ComplexLogarithmRemainder.normSq_mul (Γ := Γ) u v)
  have rb := GaussianRationalMetric.bounded_to_cleared r v E M one e (le_refl _) (raw_represents r) hr
  have rb' : Γ ⊢[PRAAx] le (normSq v) (M*M*(E*E)) :=
    le_congr (by ipra_ring) (.eqRefl _) rb
  have sq : Γ ⊢[PRAAx] le ((E*E)*(A*A*(D*D))) ((B*B*normSq u)*normSq v) :=
    le_congr (by ipra_ring) (by apply deriveNat; ipra_simps; rw [norm]; ring) lp
  have h : Γ ⊢[PRAAx] le ((E*E)*(A*A*(D*D))) ((E*E)*((B*M)*(B*M)*normSq u)) :=
    le_trans sq (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_refl (B*B*normSq u)) rb'))
  exact lower_from_representation q u D A (B*M) d (positive_product _ _ hB hM)
    (raw_represents q) (RationalValueBounds.positive_cancel (positive_product _ _ e e) h)

theorem weaken_denominator (q A B D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hBD : Γ ⊢[PRAAx] le B D) (h : Γ ⊢[PRAAx] lower q A B) : Γ ⊢[PRAAx] lower q A D := by
  let E := rawDen q
  let u := rawGaussian q
  have e := raw_den_positive (Γ := Γ) q
  have rep := raw_represents (Γ := Γ) q
  exact lower_from_representation q u E A D e (le_trans hB hBD) rep
    (le_trans (lower_to_cleared q u E A B e hB rep h)
      (le_mul_mono (le_mul_mono hBD hBD) (le_refl (normSq u))))

def productError (f g : PR 2) (x y : PTm n) : PTm n := (multiplyModulus f g x y+one)+two

def height (f g : PR 2) (x y M : PTm n) : PTm n :=
  GaussianRootSchedule.binaryLength (two*productError f g x y+two*M)

ipra_subst productError

ipra_subst height

theorem raw_product_at (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) oneF (multiplyData f g x y) x) :
    Γ ⊢[PRAAx] distanceBounded (qmul (ap2 f p x) (ap2 g p y)) qone (productError f g x y) (unit p) := by
  have u := unit_positive (Γ := Γ) p
  have close := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ he)
  exact distance_triangle_same _ _ _ _ _ _ u
    (distance_symmetric _ _ _ _ u (multiply_sample_error f g x y p hf hg))
    (distance_congr (.eqRefl _) (one_at p x) (.eqRefl _) (.eqRefl _) close)

theorem anchor_apart (f g : PR 2) (x y M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hb : Γ ⊢[PRAAx] smallSamples g y M one)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) oneF (multiplyData f g x y) x) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart f (height f g x y M) x := by
  let h := height f g x y M
  let p := GaussianNameReciprocal.anchor h
  let K := productError f g x y
  have large : Γ ⊢[PRAAx] le (two*K+two*M) (unit h) :=
    (GaussianRootSchedule.binary_length_correct (two*K+two*M)).andE₁
  have hp : Γ ⊢[PRAAx] le h p := le_add_right _ _
  have hK := le_trans (le_add_right (two*K) (two*M))
    (le_trans large (GaussianBalancedRadiusArithmetic.unit_monotone h p hp))
  have hden : Γ ⊢[PRAAx] le (two*M) (unit h) :=
    le_trans (le_congr (.eqRefl _) (add_comm _ _) (le_add_right (two*M) (two*K))) large
  have close : Γ ⊢[PRAAx] distanceBounded (qmul (ap2 f p x) (ap2 g p y)) qone one two :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive p) (le_succ_self one)
      (le_congr (mul_comm _ _) (one_mul _).eqSymm hK) (raw_product_at f g x y p hf hg he)
  exact weaken_denominator _ one (two*M) (unit h) (positive_product _ _ (le_succ_self one) hM) hden
    (factor_lower _ _ _ _ _ (le_succ_self one) hM (lower_near_one _ close)
      (small_samples_at g y M one p hb))

theorem bounded_inverse_input (f g : PR 2) (x y A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hb : Γ ⊢[PRAAx] smallSamples g y A B)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) oneF (multiplyData f g x y) x) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input f (height f g x y A) x := by
  refine .andI hf (anchor_apart f g x y A hA hf hg ?_ he)
  refine .allI ?_
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift, Syn.shift] using hB.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] smallSamples g (Syn.shift y) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift, Syn.shift, GaussianExponentialSmallPerturbation.subst_smallSamples] using hb.shift
  have cmp : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A*one) (Syn.shift A*Syn.shift B) :=
    le_mul_mono (le_refl _) bs
  have b : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 g (var 0) (Syn.shift y)) (Syn.shift A) one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ bs (le_refl _) cmp
      (small_samples_at g (Syn.shift y) (Syn.shift A) (Syn.shift B) (var 0) hs)
  simpa only [smallSamples, Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using b

theorem ones_equivalent (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF oneF x y := by
  refine .allI (.allI ?_)
  have h := GaussianNameEquivalence.cross_at (Γ := (Γ.map Fm.shift).map Fm.shift) _ _ _ _ (var 1) (var 0)
    (GaussianNameEquivalence.cross_refl oneF (Syn.shift (Syn.shift x)) (one_fast _))
  exact distance_congr (.eqRefl _) ((one_at _ _).eqTrans (one_at _ (Syn.shift (Syn.shift y))).eqSymm)
    (.eqRefl _) (.eqRefl _) h

theorem reciprocal_matches_inverse (f g : PR 2) (h x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] GaussianNameReciprocal.apart f h x)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) oneF (multiplyData f g x y) x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameReciprocal.nameF f) g (GaussianNameReciprocal.nameData h x) y := by
  let I := GaussianNameReciprocal.nameF f
  let D := GaussianNameReciprocal.nameData h x
  have hi : Γ ⊢[PRAAx] pointCN I D := GaussianNameReciprocal.name_fast f h x hf ha
  have ig := multiply_fast I f D x hi hf
  have fg := multiply_fast f g x y hf hg
  have one := one_fast (Γ := Γ) D
  have oneY := one_fast (Γ := Γ) y
  have a := multiply_equivalent I I (multiplyF f g) oneF D D (multiplyData f g x y) D hi hi fg one
    (diagonal_refl I D) (cross_to_diagonal _ _ _ _ (cross_trans _ _ _ _ _ _ he (ones_equivalent x D)))
  have left := cross_trans _ _ _ _ _ _ a (GaussianNameRingLaws.multiply_one I D hi)
  have b := multiply_equivalent (multiplyF I f) oneF g g (multiplyData I f D x) y y y ig oneY hg hg
    (cross_to_diagonal _ _ _ _
      (cross_trans _ _ _ _ _ _ (GaussianNameReciprocal.product_one_left f h x hf ha) (ones_equivalent x y)))
    (diagonal_refl g y)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNameRingLaws.multiply_associative I f g D x y hi hf hg))
      (cross_trans _ _ _ _ _ _ b (GaussianNameRingLaws.multiply_one_left g y hg)))

theorem bounded_inverse_correct (f g : PR 2) (x y A B : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hb : Γ ⊢[PRAAx] smallSamples g y A B)
    (he : Γ ⊢[PRAAx] crossEquivalent (multiplyF f g) oneF (multiplyData f g x y) x) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input f (height f g x y A) x ⋏
      crossEquivalent (GaussianNameReciprocal.nameF f) g (GaussianNameReciprocal.nameData (height f g x y A) x) y := by
  have h := bounded_inverse_input f g x y A B hA hB hf hg hb he
  exact .andI h (reciprocal_matches_inverse f g _ x y hf hg h.andE₂ he)

theorem actual_named_bounded_inverse_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le one (var 3) ⟶ pointCN f (var 0) ⟶ pointCN g (var 1) ⟶
      smallSamples g (var 1) (var 2) (var 3) ⟶
      crossEquivalent (multiplyF f g) oneF (multiplyData f g (var 0) (var 1)) (var 0) ⟶
      (GaussianNameReciprocal.input f (height f g (var 0) (var 1) (var 2)) (var 0) ⋏
        crossEquivalent (GaussianNameReciprocal.nameF f) g
          (GaussianNameReciprocal.nameData (height f g (var 0) (var 1) (var 2)) (var 0)) (var 1))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI
    (bounded_inverse_correct f g _ _ _ _ hyp2.wk.wk.wk hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianBoundedInverseApartness

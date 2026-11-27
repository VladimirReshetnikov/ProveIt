import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGamma
import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFactorialValues
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# Named Gamma at positive integers

A constant positive integer has the same decoded Gaussian value as the
original factorial input. Exact rational readback and radius overlap
transport the factorial theorem to the Gamma program on regular names.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace LeanProofs.IPRA.Analysis.GaussianNamedGammaFactorial

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFactorialValues (argument factorialValue error)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNamedGamma (nameF clock data)
open GaussianNamedRightHalfPlane (marginPoint numerator denominator radius)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents represents represents_congr scalar_congr positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_represents)
open GaussianRationalMetric (distanceBounded comparison_of_cleared)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRootAlgebra (equal equal_refl re_one re_scale)
open RationalIntegerNormalization (normalize normalize_integer normalize_unit_denominator)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem margin_order (t : PTm n) (ht : Γ ⊢[PRAAx] le one t) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT (marginPoint one)) (fstT (naturalPoint t)) := by
  have base : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (marginPoint one)) (ZT.ofNat one) one := by
    refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents oneCode one (le_refl _)).andE₁
    exact ZT.derive (by simp only [re_one,ZT.toZ_ofNat]; ipra_simps; ring)
  have value : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (naturalPoint t)) (ZT.ofNat t) one := by
    refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) (natural_point_represents t).andE₁
    exact ZT.derive (by simp only [re_scale,re_one,ZT.toZ_ofNat]; ring)
  exact comparison_of_cleared _ _ _ _ one one (le_refl _) (le_refl _) base value
    (le_congr (by ipra_ring) (by ipra_ring) ht)

theorem positive_integer_source (E : PTm n) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source constantF (naturalPoint (succ E)) one := by
  refine .andI (constant_regular _) (.andI (le_refl one) (.allI (.allI ?_)))
  let t := naturalPoint (succ (Syn.shift (Syn.shift E)))
  have order := margin_order (Γ := (Γ.map Fm.shift).map Fm.shift) (succ (Syn.shift (Syn.shift E))) (zero_lt_succ _)
  have actual := RationalArgmin.rationalLE_congr
    (congrFst (constant_at (var 1) (marginPoint one))).eqSymm
    (congrFst (constant_at (var 0) t)).eqSymm order
  simpa only [GaussianNamedRightHalfPlane.certificate,GaussianNamedPositiveExponentialOrder.realOrder,
    GaussianNamedRightHalfPlane.subst_marginPoint,GaussianRationalNaturalScale.subst_naturalPoint,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,t] using
    RationalValueBounds.upper_of_order _ _ _ _ actual

private theorem natural_denominator (t : PTm n) : Γ ⊢[PRAAx] rawDen (naturalPoint t) ≐ one := by
  change Γ ⊢[PRAAx] rawDen (ofGaussian (ComplexLogarithmRemainder.scale t oneCode) one) ≐ one
  refine (congrMul ?_ ?_).eqTrans (one_mul one)
  · exact (congrSucc (congrSnd (fst_pair _ _))).eqTrans (normalize_unit_denominator _)
  · exact (congrSucc (congrSnd (snd_pair _ _))).eqTrans (normalize_unit_denominator _)

private theorem decoded_denominator (k E : PTm n) :
    Γ ⊢[PRAAx] denominator constantF k (naturalPoint (succ E)) ≐ one := by
  have e := constant_at (Γ := Γ) k (naturalPoint (succ E))
  exact (congrMul (congrSucc (congrSnd (congrFst e))) (congrSucc (congrSnd (congrSnd e)))).eqTrans
    (natural_denominator (succ E))

private theorem decoded_value (k E : PTm n) :
    Γ ⊢[PRAAx] equal (numerator constantF k (naturalPoint (succ E))) (argument E) := by
  let x := naturalPoint (succ E)
  let q := ap2 constantF k x
  have left := represents_congr (.eqRefl q) (equal_refl _) (decoded_denominator (Γ := Γ) k E) (raw_represents q)
  have right : Γ ⊢[PRAAx] represents q (argument E) one :=
    represents_congr ((GaussianGammaFactorialValues.scalar_argument (Γ := Γ) E).eqTrans
      (constant_at k x).eqSymm) (equal_refl _) (.eqRefl one) (ofGaussian_represents (argument E) one (le_refl _))
  change Γ ⊢[PRAAx] equal (rawGaussian q) (argument E)
  refine .andI ?_ ?_
  · apply RationalNormalForm.positive_integer_cancel (denominatorOf (fstT q)) _ _
      (RationalArgmin.denominator_positive _)
    apply ZT.derive
    have e := (ZT.toZ_eq left.andE₁).trans (ZT.toZ_eq right.andE₁).symm
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
    linear_combination e
  · apply RationalNormalForm.positive_integer_cancel (denominatorOf (sndT q)) _ _
      (RationalArgmin.denominator_positive _)
    apply ZT.derive
    have e := (ZT.toZ_eq left.andE₂).trans (ZT.toZ_eq right.andE₂).symm
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
    linear_combination e

private theorem gamma_source_denominator {z R B D A : PTm n}
    (h : Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R B one A) (e : Γ ⊢[PRAAx] B ≐ D) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source z R D one A := by
  simpa only [GaussianGammaReciprocalInverse.subst_source,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    Prf.eqSubst (GaussianGammaReciprocalInverse.source (var 0) (var 1) (var 2) one (var 3) : Fm PTm 4)
      ![z,R,B,A] ![z,R,D,A] (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact e; exact .eqRefl _)
      (by simpa using h)

theorem named_factorial_sample (p E : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF constantF) p (data (naturalPoint (succ E)) one))
      (factorialValue E) (two+error E) (unit p) := by
  let x := naturalPoint (succ E)
  let k := clock constantF p x one
  let z := numerator constantF k x
  let R := radius constantF x
  let B := denominator constantF k x
  let A : PTm n := two*one
  let q := succ p
  have hs := positive_integer_source (Γ := Γ) E
  have source_native := GaussianNamedRightHalfPlane.actual_late_source constantF x one k hs
    (GaussianNamedGamma.clock_margin constantF p x one)
  have native := GaussianGammaHalfPlaneInputContinuity.reciprocal_source z R B A
    (.andI source_native (GaussianNameBounds.U_positive constantF x))
  have hden : Γ ⊢[PRAAx] B ≐ one := decoded_denominator k E
  have source_unit := gamma_source_denominator native hden
  have hvalue : Γ ⊢[PRAAx] equal z (argument E) := decoded_value k E
  have source_argument := GaussianGammaInputProperness.gamma_source_equal _ _ _ _ _ _ source_unit hvalue
  have proper := GaussianGammaInputProperness.original_Gamma_proper _ _ _ _ _ _ source_unit hvalue
  have overlap := GaussianGammaRadiusOverlap.original_Gamma_overlap (argument E) R
    (GaussianGammaFactorialValues.radius E) one one A one one source_argument
    (GaussianGammaFactorialValues.integer_source E)
  have equivalent := cross_trans _ _ _ _ _ _ proper overlap
  have between := cross_at _ _ _ _ q q equivalent
  have common := distance_radius_mono _ _ _ _ two (unit q)
    (positive_product _ _ (unit_positive q) (unit_positive q)) (unit_positive q)
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) between
  have finite := distance_triangle_same _ _ _ _ _ _ (unit_positive q) common
    (GaussianGammaFactorialValues.prefix_error q E)
  have sampleEq : Γ ⊢[PRAAx] ap2 (nameF constantF) p (data x one) ≐ ap2 gammaF q (gammaData z R one A) :=
    (GaussianNamedGamma.name_at constantF p x one).eqTrans
      (congrAp2 gammaF (.eqRefl _) (GaussianGammaFactorialValues.gamma_fields_congr
        (.eqRefl z) (.eqRefl R) hden (.eqRefl A)))
  exact distance_congr sampleEq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianExponentialReference.dyadic_weaken _ _ _ p q (le_succ_self p) finite)

theorem named_factorial (E : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF) constantF (data (naturalPoint (succ E)) one) (factorialValue E) := by
  apply cross_of_diagonal_rate _ _ _ _ (two+error E)
    (GaussianNamedGamma.name_regular constantF _ _ (positive_integer_source E)) (constant_regular _)
  refine .allI ?_
  have hs := named_factorial_sample (Γ := Γ.map Fm.shift) (var 0) (Syn.shift E)
  simpa only [diagonalRate,Syn.shift,GaussianNamedGamma.subst_data,GaussianGammaFactorialValues.subst_error,
    GaussianGammaFactorialValues.subst_factorialValue,GaussianRationalNaturalScale.subst_naturalPoint,
    PTm.subst_add,PTm.subst_succ,PTm.subst_zero] using
    distance_congr (.eqRefl _) (constant_at _ _).eqSymm (.eqRefl _) (.eqRefl _) hs

theorem actual_original_named_Gamma_positive_integer_factorial_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent (nameF constantF) constantF (data (naturalPoint (succ (var 0))) one) (factorialValue (var 0))) :=
  closeUniv 1 (named_factorial _)

end LeanProofs.IPRA.Analysis.GaussianNamedGammaFactorial

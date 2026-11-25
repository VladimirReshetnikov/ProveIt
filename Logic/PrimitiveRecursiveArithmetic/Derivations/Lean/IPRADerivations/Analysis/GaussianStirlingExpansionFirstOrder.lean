import IPRADerivations.Analysis.GaussianStirlingExpansionErrorProgram
import IPRADerivations.Analysis.GaussianStirlingGammaFractionalIncrement
import IPRADerivations.Analysis.GaussianStirlingFactorialRobbinsExponential

/-!
# The first multiplicative Stirling polynomial on the original quotient

The fixed first log polynomial is exactly 1/(12x). The original
Robbins bracket gives a quadratic logarithmic error with a uniform
coefficient, which closes the error program at this order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionFirstOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BernoulliBounds (zint toZ_zint)
open BernoulliCoefficients (bc)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianNamedPositiveExponentialOrder (real_order_at scalar_coordinate_distance)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical ofGaussian ofGaussian_canonical ofGaussian_represents represents_congr
  represents_rescale canonical_unique positive_product qadd qmul qzero evaluate horner hornerF horner_zero horner_succ)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical qsub_represents)
open GaussianRationalPolynomialExponential (inverseFactorial polynomial_evaluation polynomial_length scalarSum
  scalar_sum_succ scalar_sum_zero)
open GaussianRationalPowerExpansion (power_expansion terms_length)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qmul_zero_left qzero_add qone)
open GaussianStirlingExpansionCoefficients (logCoefficient quoted logTable log_table_length log_table_entry log_table_zero expTable)
open GaussianStirlingExpansionConditionalError (logRate)
open GaussianStirlingExpansionExponentialError (logBudget)
open GaussianStirlingExpansionFiniteError (query logPolynomial query_bound approximation)
open GaussianStirlingExpansionErrorProgram (run program_at returned_approximation_bound)
open GaussianStirlingMultiplicative (quotientF quotientData)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (upperValue lowerValue upper_den_positive lower_den_positive)
open LeanProofs.IPRA.Analysis.Products (fact)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius radius_of_upper)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem log_coefficient_one : logCoefficient 1 = (1/12 : ℚ) := by
  norm_num [logCoefficient,bc,Finset.sum_range_succ]

private theorem literal_one_twelfth :
    Γ ⊢[PRAAx] quoted (1/12 : ℚ) ≐ (fraction one (num 12) : PTm n) := by
  let r : ℚ := ⟨1,12,by decide,by decide⟩
  have hr : r = (1/12 : ℚ) := by
    simpa [r] using Rat.num_div_den r |>.symm
  have nonzero : r ≠ 0 := by rw [hr]; norm_num
  rw [← hr]
  unfold quoted
  rw [if_neg nonzero]
  change Γ ⊢[PRAAx] ofGaussian (RationalGaussianEmbedding.native (zint 1)) (num 12) ≐ fraction one (num 12)
  refine GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (RationalPhiSharpQuintic.numeral_le 1 12 (by decide)) ?_
  apply GaussianRootAlgebra.equal_of_values <;>
    simp [RationalGaussianEmbedding.native,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ComplexLogarithmRemainder.eval_re_code,
      ComplexLogarithmRemainder.eval_im_code,
      toZ_zint,ZT.toZ_ofNat]

theorem first_log_polynomial (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] logPolynomial 1 a b ≐ upperValue a b := by
  let L := logTable (n := n) 1
  let Q := query a b
  let G : PTm n := fraction one (num 12)
  have hc : Γ ⊢[PRAAx] canonical G :=
    ofGaussian_canonical _ _ (RationalPhiSharpQuintic.numeral_le 1 12 (by decide))
  have top : Γ ⊢[PRAAx] entry L zero ≐ G := by
    have e := log_table_entry (Γ := Γ) 1 0 (by decide)
    simp only [Nat.sub_zero,log_coefficient_one] at e
    exact e.eqTrans literal_one_twelfth
  have early : Γ ⊢[PRAAx] horner L Q one ≐ G :=
    (horner_succ L Q zero).eqTrans
      ((qadd_congr ((qmul_congr (horner_zero L Q) (.eqRefl _)).eqTrans (qmul_zero_left _)) top).eqTrans
        (qzero_add _ hc))
  have poly : Γ ⊢[PRAAx] logPolynomial 1 a b ≐ qmul G Q :=
    (congrAp3 hornerF (log_table_length 1) (.eqRefl L) (.eqRefl Q)).eqTrans
      ((horner_succ L Q one).eqTrans
        ((qadd_congr (qmul_congr early (.eqRefl _)) (log_table_zero 1)).eqTrans
          (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _))))
  exact poly.eqTrans ((GaussianEulerDampedTimeRate.fraction_product one (num 12) b a
    (RationalPhiSharpQuintic.numeral_le 1 12 (by decide)) ha).eqTrans
      (GaussianEulerPositivePowerChartJacobian.fraction_congr (one_mul _) (.eqRefl _)))

theorem first_approximation (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] approximation 1 a b ≐ qadd qone (upperValue a b) := by
  let z := query a b
  let C := expTable (n := n) 1
  let N : PTm n := num 1*num 1
  have hN : Γ ⊢[PRAAx] N ≐ one := one_mul one
  have hLen : Γ ⊢[PRAAx] LeanProofs.IPRA.Foundations.SequenceComposition.length C ≐ succ N :=
    polynomial_length _ _ _
  have eval : Γ ⊢[PRAAx] approximation 1 a b ≐ evaluate C z :=
    (congrAp3 hornerF ((congrSucc hN).eqSymm.eqTrans (terms_length C N z).eqSymm)
      (.eqRefl _) (.eqRefl _)).eqTrans (power_expansion C N z hLen).eqSymm
  have taylor : Γ ⊢[PRAAx] evaluate C z ≐ scalarSum (logPolynomial 1 a b) one :=
    polynomial_evaluation _ _ _ _ (log_table_length 1)
  have factOne : Γ ⊢[PRAAx] fact one ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl one)).eqTrans (one_mul one))
  have inv : Γ ⊢[PRAAx] inverseFactorial one ≐ qone := by
    simpa only [inverseFactorial,GaussianRationalSyntheticDivision.qone,GaussianRationalHorner.subst_ofGaussian,
      ComplexLogarithmRemainder.subst_oneCode,Syn.subst_var] using
      (Prf.eqCongr (Γ := Γ) (ofGaussian oneCode (var 0) : PTm 1)
        (σ := fun _ => fact one) (σ' := fun _ => one) (fun _ => factOne))
  let q := logPolynomial 1 a b
  have qc : Γ ⊢[PRAAx] canonical q := GaussianRationalHorner.horner_canonical _ _ _
  have term := (qmul_congr inv (GaussianRationalPowerAlgebra.power_one q qc)).eqTrans
    ((GaussianPolynomialDeterminantTerms.one_mul_canonical q qc).eqTrans (first_log_polynomial a b ha))
  exact eval.eqTrans (taylor.eqTrans ((scalar_sum_succ q zero).eqTrans (qadd_congr (scalar_sum_zero q) term)))

private theorem bracket_gap (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] upper (fstT (upperValue a b)) (fstT (lowerValue a b)) (b*b) (a*a) := by
  let j := num 12*a
  let k := j+b
  let E := j*k
  let z := scale b oneCode
  have hj := upper_den_positive a ha
  have hk := lower_den_positive a b ha
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hj hk
  have qi : Γ ⊢[PRAAx] GaussianRationalHorner.represents (upperValue a b) (scale k z) E :=
    represents_rescale _ _ _ _ (ofGaussian_represents z j hj)
  have ti : Γ ⊢[PRAAx] GaussianRationalHorner.represents (lowerValue a b) (scale j z) E :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm k j)
      (represents_rescale _ _ _ _ (ofGaussian_represents z k hk))
  have exactValue : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (scale k z) (scale j z)) (scale (b*b) oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;> dsimp only [z,j,k] <;>
      simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
      ipra_simps <;> ring
  have difference : Γ ⊢[PRAAx] qsub (upperValue a b) (lowerValue a b) ≐ query E (b*b) :=
    canonical_unique _ _ _ _ (qsub_canonical _ _) (ofGaussian_canonical _ _ he) he
      (represents_congr (.eqRefl _) exactValue (.eqRefl _)
        (qsub_represents _ _ _ _ E he qi ti)) (ofGaussian_represents _ _ he)
  have hD := positive_product _ _ ha ha
  have ja : Γ ⊢[PRAAx] le a j := by dsimp [j]; ipra_le 11*𝔞 a
  have eGrow : Γ ⊢[PRAAx] le (a*a) E :=
    LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono ja (le_trans ja (le_add_right j b))
  have radius : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (qsub (upperValue a b) (lowerValue a b)) (b*b) (a*a) :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ he hD
    (by ipra_le 𝔞 (b*b)*sl eGrow)
    (GaussianRationalReciprocal.bound_congr difference.eqSymm (.eqRefl _) (.eqRefl _) (query_bound E (b*b) he))
  exact upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD radius)

theorem log_error_at (p q a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] distanceBounded (ap2 remainderF p (remainderData a b x)) (ap2 constantF q (logPolynomial 1 a b))
      (rateNumerator (one*pw b two) (pw a two) p q) (rateDenominator (pw a two) p q) := by
  let Q := upperValue a b
  let L := lowerValue a b
  let Z := ap2 remainderF p (remainderData a b x)
  let up := unit p
  let uq := unit q
  let M := rateNumerator (b*b) (a*a) p q
  let N := rateDenominator (a*a) p q
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hN : Γ ⊢[PRAAx] le one N := denominator_positive _ p q (positive_product _ _ hs.andE₁ hs.andE₁)
  have bounds := GaussianStirlingGammaFractionalIncrement.original_rational_robbins a b x hs hba
  have leR := (GaussianStirlingFactorialRobbinsExponential.upper_log_strict a b x hs bounds.andE₂).andE₁
  have geR := (GaussianStirlingFactorialRobbinsExponential.lower_log_strict a b x hs hba bounds.andE₁).andE₁
  have leAt := upper_congr (.eqRefl _) (congrFst (constant_at q Q)) (.eqRefl _) (.eqRefl _)
    (real_order_at _ _ _ _ p q leR)
  have loAt := upper_congr (congrFst (constant_at q L)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (real_order_at _ _ _ _ q p geR)
  have upR : Γ ⊢[PRAAx] upper (fstT Z) (fstT Q) M N :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hP hQ) leAt
      (by dsimp only [M,N,rateNumerator,rateDenominator]; ipra_le 𝔞 (b*b)*(𝔞 up*𝔞 uq)^2)
  have loR : Γ ⊢[PRAAx] upper (fstT Q) (fstT Z) M N :=
    upper_congr (.eqRefl _) (.eqRefl _) (by dsimp only [M,rateNumerator]; ipra_ring)
      (by dsimp only [N,rateDenominator]; ipra_ring)
      (upper_triangle _ _ _ _ _ _ _ (bracket_gap a b hs.andE₁) loAt)
  have exactRad := radius_of_upper _ _ _ _ upR loR
  have zReal := GaussianSignedNameExponentialOrder.real_sample_at remainderF (remainderData a b x) p
    (GaussianStirlingMultiplicativeBounds.remainder_real a b x hs)
  have qReal := GaussianStirlingNames.fraction_axis b (num 12*a) (upper_den_positive a hs.andE₁)
  have qCan : Γ ⊢[PRAAx] canonical Q := ofGaussian_canonical _ _ (upper_den_positive a hs.andE₁)
  have ba := (pw_succ (Γ := Γ) b one).eqTrans (congrMul (pw_one b) (.eqRefl b))
  have aa := (pw_succ (Γ := Γ) a one).eqTrans (congrMul (pw_one a) (.eqRefl a))
  have ps := (one_mul (pw b two)).eqTrans ba
  have eM : Γ ⊢[PRAAx] rateNumerator (one*pw b two) (pw a two) p q ≐ M :=
    congrAdd (congrMul (congrMul ps (.eqRefl up)) (.eqRefl uq)) (congrMul aa (.eqRefl _))
  have eN : Γ ⊢[PRAAx] rateDenominator (pw a two) p q ≐ N :=
    congrMul (congrMul aa (.eqRefl up)) (.eqRefl uq)
  exact GaussianRationalDistanceOrder.distance_congr
    (RationalGaussianEmbedding.canonical_axis_roundtrip Z zReal.andE₁ zReal.andE₂)
    ((RationalGaussianEmbedding.canonical_axis_roundtrip Q qCan qReal).eqTrans
      ((first_log_polynomial a b hs.andE₁).eqSymm.eqTrans (constant_at q (logPolynomial 1 a b)).eqSymm))
    eM.eqSymm eN.eqSymm
    (RationalGaussianNameEmbedding.distance_from_radius _ _ M N hN exactRad)

theorem first_log_rate (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] logRate 1 a b x one := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have p : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh a) (sh b) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift.shift
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (sh b) (sh a) := by
    simpa [Fm.shift,Syn.shift,sh] using hba.shift.shift
  simpa [logRate,independentRate,logPolynomial,query,Syn.shift,sh,two,one,num] using
    log_error_at (var 1) (var 0) (sh a) (sh b) (sh x) p h

set_option maxHeartbeats 800000 in
theorem actual_first_Stirling_multiplicative_error_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 1) (var 2) ⟶ le (var 2) (var 1) ⟶ le (two*(logBudget 1*var 2)) (var 1) ⟶
        distanceBounded (ap2 quotientF (var 0) (quotientData (var 1) (var 2) (var 3)))
          (fstT (run 1 (var 0) (var 1) (var 2) one))
          (fstT (sndT (run 1 (var 0) (var 1) (var 2) one)))
          (sndT (sndT (run 1 (var 0) (var 1) (var 2) one)))) := by
  refine closeUniv 4 (.impI (.impI (.impI ?_)))
  exact returned_approximation_bound 1 _ _ _ _ one Prf.hyp1.wk Prf.hyp1 Prf.hyp0
    (first_log_rate _ _ _ Prf.hyp1.wk Prf.hyp1)

theorem first_program_value (p a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] fstT (run 1 p a b one) ≐ qadd qone (upperValue a b) :=
  (congrFst (program_at 1 p a b one)).eqTrans
    ((fst_pair _ _).eqTrans (first_approximation a b ha))

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionFirstOrder

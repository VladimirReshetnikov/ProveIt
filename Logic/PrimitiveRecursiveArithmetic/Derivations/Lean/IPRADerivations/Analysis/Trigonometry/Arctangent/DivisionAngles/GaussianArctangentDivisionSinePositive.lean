import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionAngleGaps
import IPRADerivations.Analysis.Trigonometry.Arctangent.Comparisons.GaussianArctangentAngleChord
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# A positive lower bound for every actual divided-angle sine

The original chord estimate applies to the checked divided-angle name.
Its common quarter-turn factor has actual ordinate at least one and
can be cancelled in the signed rational comparison. Removing the
finite observation allowance gives the named lower bound 2k/m.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionSinePositive

open_ipra
open ComplexLogarithmRemainder (re scale eval_im_code eval_re_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentDivisionAngles (nameF data clock source coefficient coefficient_bound sample_at
  exponential_input interval_input imaginary_samples quarter_represents quarterDenominator quarterNumerator)
open GaussianArctangentDivisionAngleGaps (quarter_lower)
open GaussianArctangentInverseForward (imaginary_order_at)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentQuarterExponential (quarterF quarter_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianNamedSineFromExponential (sineF sineData sine_regular sine_proper)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameEquivalence (point_at cross_refl)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul qmul_represents ofGaussian_represents represents scalar_congr positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRootAlgebra (im_mul re_scale im_scale)
open GaussianApproximateInverseDistance (multiply_distance)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius upper_order_left)
open PolynomialBisection (zle_scale_cancel slack)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem scaled_ordinate (a A E p z : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] represents a A E) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (sndT (qmul a (ap2 quarterF p z))) (re A*ZT.ofNat (quarterNumerator p))
      (E*quarterDenominator p) := by
  have hF := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) (GaussianGammaHalfPiName.clearing p)
  have hp := qmul_represents _ _ _ _ E _ hE hF ha (quarter_represents p z)
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) hp.andE₂
  apply ZT.derive
  simp only [im_mul, re_scale, im_scale, imaginaryCode, eval_im_code, eval_re_code, ZT.toZ_mul, ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem cancel_quarter (a b C D p z : PTm n)
    (h : Γ ⊢[PRAAx] upper (sndT (qmul a (ap2 quarterF p z))) (sndT (qmul b (ap2 quarterF p z))) C D) :
    Γ ⊢[PRAAx] upper (fstT a) (fstT b) C D := by
  let F := quarterDenominator p
  let Q := quarterNumerator p
  let E := rawDen a
  let H := rawDen b
  let U := re (rawGaussian a)
  let V := re (rawGaussian b)
  have hF : Γ ⊢[PRAAx] le one F := GaussianRationalPolynomialExponential.factorial_positive _
  have hq : Γ ⊢[PRAAx] le F Q := quarter_lower p
  have hE := raw_den_positive (Γ := Γ) a
  have hH := raw_den_positive (Γ := Γ) b
  have ha := raw_represents (Γ := Γ) a
  have hb := raw_represents (Γ := Γ) b
  have signed := to_signed _ _ _ _ _ _ _ _ (scaled_ordinate _ _ _ p z hE ha) (scaled_ordinate _ _ _ p z hH hb) h
  let l := left (U*ZT.ofNat Q) (H*F) D
  let r := right (V*ZT.ofNat Q) (E*F) (H*F) C D
  let s := slack l r
  have eq := zle_toZ signed
  change ZT.toZ Γ l + 𝔞 s = ZT.toZ Γ r at eq
  have budget := natEq (eq_add_of_le hq)
  apply from_signed _ _ _ _ E H C D hE hH ha.andE₁ hb.andE₁
  apply zle_scale_cancel (c := F*Q) (positive_product _ _ hF (le_trans hF hq))
  apply zle_of_toZ (s+C*E*H*F*monus Q F)
  simp only [IPRA.Q.mk_add,map_add] at budget
  simp only [l,r,left,right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,IPRA.Q.mk_mul,IPRA.Q.mk_add,map_add,map_mul] at eq ⊢
  linear_combination eq - (𝔞 C*𝔞 E*𝔞 H*𝔞 F)*budget

def chordSineData (k m z : PTm n) : PTm n := sineData nameF (GaussianNameBounds.U nameF (data k m z)) (data k m z)
def exactSineData (k m z : PTm n) : PTm n := sineData nameF two (data k m z)
def amplitude (k m z : PTm n) : PTm n := multiplyModulus (sineF nameF) quarterF (chordSineData k m z) z+num 5

private theorem chord_exp_input (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input nameF (GaussianNameBounds.U nameF (data k m z)) (data k m z) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _ (GaussianArctangentDivisionAngles.name_regular k m z h)

private theorem diagonal_bound (k m z p : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] upper (fstT (coefficient k m)) (fstT (ap2 (sineF nameF) p (chordSineData k m z)))
      (amplitude k m z) (unit p) := by
  let X := data k m z
  let c := coefficient k m
  let U := unit p
  let V := unit (clock p)
  let v := ap2 quarterF p z
  let y := ap2 nameF p X
  let S := ap2 (sineF nameF) p (chordSineData k m z)
  let H := ap2 (GaussianArctangentAngleChord.productF nameF) p (GaussianArctangentAngleChord.productData nameF X z)
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) (clock p)
  have hUV := positive_product _ _ hU hV
  have hUUV : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have d := multiply_distance c _ _ one _ _ hUV (coefficient_bound k m h)
    (point_at quarterF z p (clock p) (quarter_regular z))
  have d' := imaginary_coordinate_radius _ _ _ _ hUV
    (distance_congr (.eqRefl _) (sample_at k m z p).eqSymm (one_mul _) (.eqRefl _) d)
  have leftBound : Γ ⊢[PRAAx] upper (sndT (qmul c v)) (sndT y) two U :=
    RationalValueBounds.upper_two_errors hUV hU (le_refl U) hUUV (upper_of_radius _ _ _ _ d')
  have chord := GaussianArctangentAngleChord.original_chord nameF X z (interval_input k m z h) (imaginary_samples k m z h.andE₁)
  have middle : Γ ⊢[PRAAx] upper (sndT y) (sndT H) two U :=
    RationalValueBounds.upper_two_errors_same hU (imaginary_order_at _ _ _ _ p p chord)
  have readback := multiply_sample_error (sineF nameF) quarterF (chordSineData k m z) z p
    (sine_regular _ _ _ (chord_exp_input k m z h)) (quarter_regular z)
  have rightBound := upper_of_radius _ _ _ _ (imaginary_coordinate_radius _ _ _ _ hU readback)
  have joined := RationalValueBounds.upper_triangle_same hU (RationalValueBounds.upper_triangle_same hU leftBound middle) rightBound
  exact cancel_quarter c S _ U p z (upper_congr (.eqRefl _) (.eqRefl _) (by unfold amplitude; ipra_ring) (.eqRefl _) joined)

private theorem cofinal_bound (k m z q : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] upper (fstT (coefficient k m)) (fstT (ap2 (sineF nameF) q (chordSineData k m z))) one (unit q) := by
  let a := fstT (coefficient k m)
  let x := chordSineData k m z
  let b := fstT (ap2 (sineF nameF) q x)
  let K := amplitude k m z
  let Q := unit q
  let t := precision a b Q (K+one)
  let T := unit t
  have hQ := unit_positive (Γ := Γ) q
  have hT := unit_positive (Γ := Γ) t
  have hS := sine_regular _ _ _ (chord_exp_input k m z h)
  have mid := diagonal_bound k m z t h
  have d := scalar_coordinate_distance _ _ _ _ (positive_product _ _ hT hQ) (point_at (sineF nameF) x t q hS)
  have joined := upper_triangle _ _ _ _ _ _ _ mid (upper_of_radius _ _ _ _ d)
  apply remove_upper_slack _ _ _ _ (K+one)
  change Γ ⊢[PRAAx] upper a b (one*T+(K+one)*Q) (Q*T)
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hT (positive_product _ _ hT hQ))
    joined (le_of_eq_add (d := zero) (by dsimp only [T,Q,K]; ipra_ring))

private theorem chord_sine_lower (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] realOrder constantF (sineF nameF) (coefficient k m) (chordSineData k m z) := by
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let a := Syn.shift (Syn.shift k)
  let d := Syn.shift (Syn.shift m)
  let x := Syn.shift (Syn.shift z)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hc : C ⊢[PRAAx] source a d := by simpa [Fm.shift,Syn.shift,C,a,d] using h.shift.shift
  have lower := cofinal_bound a d x q hc
  have bound : C ⊢[PRAAx] upper (fstT (coefficient a d)) (fstT (ap2 (sineF nameF) q (chordSineData a d x)))
      (unit p+unit q) (unit p*unit q) :=
    RationalValueBounds.upper_one_error (unit_positive q) (le_refl _) lower
  simpa only [realOrder, Syn.shift, chordSineData, GaussianArctangentDivisionAngles.subst_data,
    GaussianArctangentDivisionAngles.subst_coefficient, GaussianNameBounds.subst_U,
    GaussianNamedSineFromExponential.subst_sineData, a,d,x,p,q,C] using
    upper_congr (congrFst (constant_at p (coefficient a d))).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) bound

theorem sine_lower (k m z : PTm n) (h : Γ ⊢[PRAAx] source k m) :
    Γ ⊢[PRAAx] realOrder constantF (sineF nameF) (coefficient k m) (exactSineData k m z) := by
  have first := chord_exp_input k m z h
  have second := exponential_input k m z h
  have same := sine_proper _ _ _ _ _ _ first second (cross_refl _ _ first.andE₁)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (constant_regular _)) same (chord_sine_lower k m z h)

private theorem coefficient_first_represents (k m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (coefficient k m)) (ZT.ofNat (two*k)) m := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ hm).andE₁
  apply ZT.derive
  simp only [re_scale, GaussianRootAlgebra.re_one, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem uniform_positive (k J z : PTm n) (h₁ : Γ ⊢[PRAAx] le one k) (hJ : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] realOrder constantF (sineF nameF) (coefficient one (GaussianArctangentDivisionAngles.modulus J))
      (exactSineData k (GaussianArctangentDivisionAngles.modulus J) z) := by
  let m := GaussianArctangentDivisionAngles.modulus J
  let c := coefficient one m
  let d := coefficient k m
  let x := exactSineData k m z
  have h := GaussianArctangentDivisionAngles.odd_source k J hJ
  have hOrd := sine_lower k m z h
  refine .allI (.allI ?_)
  let C := (Γ.map Fm.shift).map Fm.shift
  let K := Syn.shift (Syn.shift k)
  let M := Syn.shift (Syn.shift m)
  let a := Syn.shift (Syn.shift c)
  let b := Syn.shift (Syn.shift d)
  let y := Syn.shift (Syn.shift x)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hm : C ⊢[PRAAx] le one M := by
    have e := h.andE₁.shift.shift
    simpa only [Fm.shift, subst_le, C, M, m, Syn.shift, one, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using e
  have hk : C ⊢[PRAAx] le one K := by simpa [Fm.shift,Syn.shift,C,K] using h₁.shift.shift
  have old : C ⊢[PRAAx] realOrder constantF (sineF nameF) b y := by
    simpa only [Fm.shift,GaussianNamedPositiveExponentialOrder.subst_realOrder,b,y,d,x,Syn.shift] using hOrd.shift.shift
  have ca : a = coefficient one M := by simp [a,c,M,Syn.shift]
  have cb : b = coefficient K M := by simp [b,d,K,M,Syn.shift]
  have order : C ⊢[PRAAx] RationalArgmin.rationalLE (fstT a) (fstT b) := by
    rw [ca,cb]
    apply GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hm hm
      (coefficient_first_represents one M hm) (coefficient_first_represents K M hm)
    exact le_congr (by ipra_ring) (by ipra_ring) (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hk (le_refl (two*M)))
  have compare := RationalArgmin.rationalLE_congr (congrFst (constant_at p a)).eqSymm
    (congrFst (constant_at p b)).eqSymm order
  exact upper_order_left _ _ _ _ _ compare
    (GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p q old)

theorem actual_division_sine_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ realOrder constantF (sineF nameF) (coefficient (var 0) (var 1))
      (exactSineData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (sine_lower _ _ _ Prf.hyp0))

theorem actual_odd_division_sine_positive_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le (var 0) (var 1) ⟶
      realOrder constantF (sineF nameF) (coefficient one (GaussianArctangentDivisionAngles.modulus (var 1)))
        (exactSineData (var 0) (GaussianArctangentDivisionAngles.modulus (var 1)) (var 2))) :=
  closeUniv 3 (.impI (.impI (uniform_positive _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionSinePositive

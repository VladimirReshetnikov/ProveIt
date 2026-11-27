import IPRADerivations.Analysis.Stirling.Binet.Kernel.Bounds.GaussianBinetKernelTimeContinuity
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialRealPartMajorant
import IPRADerivations.Analysis.Euler.VerticalBounds.Integrands.GaussianEulerVerticalNormTransfer
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualDomain
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder

/-!
# Complex Laplace damping at rational times

Use the original Gaussian exponential on the exact rational point
`-z*t`. Its time modulus uses a common certified exponential radius.
The real-part identity supplies a unit norm bound with the ordinary
observation error at each actual clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceExponential

open_ipra
open ComplexLogarithmRemainder (eval_re_code scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source subst_source)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian_represents positive_product qmul qmul_represents qzero)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qnegative qnegative_represents qnormSq)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_congr)
open GaussianReconstructionRoots (distance_zero_iff)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def exponent (X Y D sign A B : PTm n) : PTm n :=
  qmul (qnegative (argument X Y D sign)) (fraction A B)

abbrev nameF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def data (X Y D sign R T A B : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (R*T) (exponent X Y D sign A B)

def timeGain (R T : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (R*T)*R

ipra_subst exponent [argument, ZT.subst, ZT.ofNat]

ipra_subst data

ipra_subst timeGain

theorem parameter_bound (X Y D sign R : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] bounded (argument X Y D sign) R one := by
  let z := native X Y sign
  have hD := h.andE₁.andE₂
  apply (bounded_iff _ z D R one hD (le_refl one) (ofGaussian_represents _ _ hD)).iffMpr
  exact le_congr (by ipra_ring) (by ipra_ring) h.andE₂

theorem exponent_bound (X Y D sign R T A B : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (ht : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] bounded (exponent X Y D sign A B) (R*T) one :=
  bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ R one T one (le_refl one) (le_refl one)
      (bounded_negative _ _ _ (le_refl one) (parameter_bound X Y D sign R hz))
      (GaussianEulerExponentCompactBounds.fraction_bound A B T hB ht))

theorem exponent_nonpositive (X Y D sign A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] rationalLE (fstT (exponent X Y D sign A B)) (natCode zero) := by
  let x := native X Y sign
  let t := scale A oneCode
  let z := argument X Y D sign
  have hx : Γ ⊢[PRAAx] GaussianRationalHorner.represents z x D := ofGaussian_represents x D hD
  let nx := ComplexLogarithmRemainder.neg x
  have hs := qmul_represents (qnegative z) (fraction A B) nx t D B hD hB
    (qnegative_represents z x D hx) (ofGaussian_represents t B hB)
  have em : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.re (ComplexLogarithmRemainder.mul nx t))
      (-ZT.ofNat (X*A)) := by
    apply ZT.derive
    simp only [nx,x,t,native,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,eval_re_code,
      ZT.toZ_neg,ZT.toZ_ofNat]
    ipra_simps
    ring
  have rep := GaussianRationalHorner.scalar_congr (.eqRefl _) em (.eqRefl _) hs.andE₁
  apply RationalArithmetic.order_of_representations _ _ _ _ (D*B) one rep (natCode_represents zero)
    (positive_product _ _ hD hB) (le_refl one)
  apply zle_of_toZ (X*A)
  simp only [ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat]
  ipra_simps
  ring

theorem regular (X Y D sign R T A B : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (ht : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign R T A B) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianSignedNameExponentialOrder.constant_input _ _ (exponent_bound X Y D sign R T A B hz hB ht))

theorem time_rate (X Y D sign R T A B a b E Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (ht : Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source A B a b T E Q) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data X Y D sign R T A B) (data X Y D sign R T a b)
      (timeGain R T*E) Q := by
  let z := argument X Y D sign
  let x := exponent X Y D sign A B
  let y := exponent X Y D sign a b
  have hQ := ht.andE₂.andE₂.andE₁
  have bx := exponent_bound X Y D sign R T A B hz ht.andE₁ ht.andE₂.andE₂.andE₂.andE₁
  have by₀ := exponent_bound X Y D sign R T a b hz ht.andE₂.andE₁ ht.andE₂.andE₂.andE₂.andE₂.andE₁
  have dz := bounded_negative z R one (le_refl one) (parameter_bound X Y D sign R hz)
  have dxy : Γ ⊢[PRAAx] distanceBounded x y (R*E) Q :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference (qnegative z) _ _).eqSymm
      (.eqRefl _) (one_mul _) (bounded_product _ _ R one E Q (le_refl one) hQ dz ht.andE₂.andE₂.andE₂.andE₂.andE₂)
  have rd := GaussianRadiusExponentialLipschitzRate.independent_rate constantF constantF (R*T) x y (R*E) Q
    (.andI hQ (.andI (GaussianSignedNameExponentialOrder.constant_input x _ bx)
      (.andI (GaussianSignedNameExponentialOrder.constant_input y _ by₀)
        (GaussianNamedAddRate.constant_rate x y (R*E) Q hQ dxy))))
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _
    (by dsimp only [timeGain]; ipra_ring) rd

private theorem unit_reference (q t : PTm n) (hq : Γ ⊢[PRAAx] rationalLE (fstT q) (natCode zero)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF
      (GaussianExponentialRealPart.squarePrecision nameF (t+t) (GaussianExponentialRealPartMajorant.expData q))
      (GaussianExponentialRealPartMajorant.expData q)) (unit t+one) (unit t) := by
  have hs := GaussianExponentialRealPartMajorant.original_actual_squared_norm_upper q zero (t+t) hq
  have e : Γ ⊢[PRAAx] GaussianExponentialRealPartMajorant.majorant (zero : PTm n) ≐ one :=
    (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] two*zero ≐ zero) (.eqRefl _)).eqTrans (pw_zero (num 3))
  have repr : Γ ⊢[PRAAx] RationalArithmetic.represents (natCode (one : PTm n)) (ZT.ofNat (one*one)) (one*one) :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [ZT.toZ_ofNat]
      ipra_simps
      ring) (one_mul one).eqSymm (natCode_represents one)
  exact bound_congr (.eqRefl _) (by ipra_ring) (one_mul _)
    (GaussianSquaredNormUpper.bound_of_dyadic_squared_upper _ _ one one t (le_refl one) repr
      (RationalValueBounds.upper_congr (.eqRefl _) (natCode_congr e) (.eqRefl _) (.eqRefl _) hs))

private theorem unit_slack (q S p t : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF S q)
    (hq : Γ ⊢[PRAAx] rationalLE (fstT q) (natCode zero)) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (ap2 nameF p (GaussianRadiusExponentialName.data S q)) (unit p+one) (unit p) two t := by
  let x := GaussianRadiusExponentialName.data S q
  let y := GaussianExponentialRealPartMajorant.expData q
  let j := GaussianExponentialRealPart.squarePrecision nameF (t+t) y
  let P := unit p
  let U := unit t
  have hP := unit_positive (Γ := Γ) p
  have hU := unit_positive (Γ := Γ) t
  have hPU := positive_product _ _ hP hU
  have hJ := unit_positive (Γ := Γ) j
  have later : Γ ⊢[PRAAx] le t j :=
    le_trans (le_add_right _ _) (GaussianEulerVerticalNormTransfer.square_clock_later nameF (t+t) y)
  have grow := GaussianExponentialReference.unit_monotone later
  have hd := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF q (constant_regular q)
  have cross := GaussianExponentialRadiusIndependence.same_input_cross constantF S (GaussianNameBounds.U constantF q) q hs hd
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p x) (ap2 nameF j y) (P+U) (P*U) := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hP hJ) hPU ?_
      (GaussianNameEquivalence.cross_at _ _ _ _ p j cross)
    ipra_le 𝔞(P)*𝔞(P)*sl grow
  have reference : Γ ⊢[PRAAx] bounded (ap2 nameF j y) ((U+one)*P) (P*U) :=
    bounded_radius_mono _ _ _ _ _ hU hPU
    (le_of_eq_add (d := zero) (by ipra_ring)) (unit_reference q t hq)
  have total := distance_triangle_same _ _ qzero _ _ (P*U) hPU near
    ((distance_zero_iff _ _ _ hPU).iffMpr reference)
  exact bound_congr (.eqRefl _) (by dsimp only [P,U]; unfold unit; ipra_ring) (.eqRefl _)
    ((distance_zero_iff _ _ _ hPU).iffMp total)

theorem original_unit_bound (q S p : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF S q)
    (hq : Γ ⊢[PRAAx] rationalLE (fstT q) (natCode zero)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (GaussianRadiusExponentialName.data S q)) (unit p+one) (unit p) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two (unit_positive p) (unit_slack q S p _ hs hq)

theorem unit_bound (p X Y D sign R T A B : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (ht : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data X Y D sign R T A B)) (unit p+one) (unit p) :=
  original_unit_bound _ _ _ (GaussianSignedNameExponentialOrder.constant_input _ _
    (exponent_bound X Y D sign R T A B hz hB ht)) (exponent_nonpositive X Y D sign A B hz.andE₁.andE₂ hB)

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceExponential

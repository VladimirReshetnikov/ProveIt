import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseLinearApproximation
import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseIntegrandBound
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.GaussianBinetArctangentLinearApproximation

/-!
# The continuous endpoint of the original second Binet integrand

The original normalized reciprocal reads a finite Bose denominator.
Compare it first at the same Pi observation. Only the comparison of
two observations of the inverse Pi factor requires dyadic slack.
-/

set_option autoImplicit false
set_option maxHeartbeats 240000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseIntegrandEndpoint

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetArctangentLinearApproximation (linear cube)
open GaussianBinetBoseLinearApproximation (coefficient coefficientClock query query_factor query_lower)
open GaussianBinetBoseExponential (scaleF scaleData piClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianNameArithmetic (multiplyF multiplyData multiplyRaw multiplyModulus)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul qmul_canonical positive_product)
open GaussianRationalLowerBounds (name_lower inverse_bound lower_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "Den" => GaussianBinetBoseDenominator.nameF
local notation "denData" => GaussianBinetBoseDenominator.data
local notation "Inv" => GaussianBinetBoseDenominator.reciprocalF
local notation "invData" => GaussianBinetBoseDenominator.reciprocalData
local notation "F" => GaussianBinetBoseIntegrandBound.nameF
local notation "fd" => GaussianBinetBoseIntegrandBound.data

def factor (X Y D sign : PTm n) : PTm n := reciprocal (argument X Y D sign)
def piData : PTm n := scaleData false one one
def inversePiF : PR 2 := GaussianNameReciprocal.nameF scaleF
def inversePiData : PTm n := GaussianNameReciprocal.nameData one piData
def endpointF : PR 2 := multiplyF constantF inversePiF
def endpointData (X Y D sign : PTm n) : PTm n := multiplyData constantF inversePiF (factor X Y D sign) inversePiData

ipra_subst endpointData [factor, GaussianLogGammaEulerRepresentation.subst_argument, inversePiData, piData, one]

private theorem inversePi_regular : Γ ⊢[PRAAx] pointCN inversePiF (inversePiData : PTm n) := by
  let r := GaussianNameReciprocal.anchor (one : PTm n)
  let q := ap2 scaleF r (piData : PTm n)
  let v := coefficient (piClock r one)
  have old := name_lower v one one (le_refl one) (le_refl one)
    (GaussianBinetBoseLinearApproximation.coefficient_lower (Γ := Γ) (piClock r one))
  have lo := GaussianNamedFiniteProductApartness.weaken_margin v one (unit one) (le_refl one) (unit_positive one) old
  have lp := GaussianNameReciprocal.lower_congr (GaussianBinetBoseLinearApproximation.unit_scale r).eqSymm (.eqRefl _) lo
  exact GaussianNameReciprocal.name_fast scaleF one piData
    (GaussianBinetBoseExponential.exp_input false one one (le_refl one)).andE₁
    (show Γ ⊢[PRAAx] GaussianNameReciprocal.lower q (unit one) from lp)

theorem endpoint_regular (X Y D sign : PTm n) : Γ ⊢[PRAAx] pointCN endpointF (endpointData X Y D sign) :=
  GaussianNameArithmetic.multiply_fast constantF inversePiF _ _ (constant_regular _) inversePi_regular

def endpointClock (p X Y D sign : PTm n) : PTm n :=
  piClock (exponent (GaussianNameReciprocal.modulus one)
    (exponent (multiplyModulus constantF inversePiF (factor X Y D sign) inversePiData) p)+GaussianNameReciprocal.anchor one) one

theorem endpoint_at (p X Y D sign : PTm n) :
    Γ ⊢[PRAAx] ap2 endpointF p (endpointData X Y D sign) ≐
      qmul (factor X Y D sign) (reciprocal (coefficient (endpointClock p X Y D sign))) := by
  let a := factor X Y D sign
  let q := exponent (multiplyModulus constantF inversePiF a inversePiData) p
  let r := exponent (GaussianNameReciprocal.modulus one) q+GaussianNameReciprocal.anchor one
  let c := coefficient (piClock r one)
  have old := (GaussianNameReciprocal.name_at (Γ := Γ) scaleF one piData q).eqTrans
    (GaussianExponentialReference.recode_fixed _ (reciprocal_canonical (ap2 scaleF r piData)))
  have e := old.eqTrans (GaussianNameReciprocal.reciprocal_congr (GaussianBinetBoseLinearApproximation.unit_scale r))
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) constantF inversePiF a inversePiData p).eqTrans
    (GaussianExponentialReference.recode_fixed (multiplyRaw constantF inversePiF q a inversePiData) (qmul_canonical _ _))
  exact read.eqTrans (qmul_congr (constant_at q a) (show Γ ⊢[PRAAx] ap2 inversePiF q inversePiData ≐ reciprocal c from e))

private theorem endpoint_clock_later (p X Y D sign : PTm n) :
    Γ ⊢[PRAAx] le p (endpointClock p X Y D sign) :=
  le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _)))

private theorem scaled_distance (w u v A B H E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hw : Γ ⊢[PRAAx] bounded w A B) (h : Γ ⊢[PRAAx] distanceBounded u v H E) :
    Γ ⊢[PRAAx] distanceBounded (qmul w u) (qmul w v) (A*H) (B*E) :=
  bound_congr (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm
    (.eqRefl _) (.eqRefl _) (bounded_product _ _ _ _ _ _ hB hE hw h)

private theorem rational_time_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (fraction A B) A B :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded A B hB)

theorem factor_bound (X Y D sign K : PTm n) (hz : Γ ⊢[PRAAx] source X D sign) (margin : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] bounded (factor X Y D sign) K one := by
  have hX := hz.andE₁.andE₁
  have hD := hz.andE₂
  have decom := inverse_bound _ X D hX hD (GaussianBinetReciprocalRows.real_part_lower X Y D sign hz)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hX (le_refl one)
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] D ≐ D*one) (.eqRefl _) margin) decom

private theorem denominator_inverse_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (reciprocal (ap2 Den p (denData A B))) B A := by
  have h4 : Γ ⊢[PRAAx] le one (num 4*A) := positive_product _ _ (by ipra_le 3) hA
  have old := inverse_bound (ap2 Den p (denData A B)) (num 4*A) B h4 hB (GaussianBinetBoseDenominator.observation_lower p A B hB)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ h4 hA (by ipra_le 3*𝔞(B*A)) old

private theorem inverse_error (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (small : Γ ⊢[PRAAx] le (num 10*A) B) :
    Γ ⊢[PRAAx] distanceBounded (reciprocal (ap2 Den p (denData A B))) (reciprocal (query p A B)) (num 100) one := by
  let u := ap2 Den p (denData A B)
  let v := query p A B
  have ha : Γ ⊢[PRAAx] le one (num 4*A) := positive_product _ _ (by ipra_le 3) hA
  have uP := GaussianRationalLowerBounds.norm_positive u (num 4*A) B ha hB
    (GaussianBinetBoseDenominator.observation_lower p A B hB)
  have vP := GaussianRationalLowerBounds.norm_positive v A B hA hB (query_lower p A B hB)
  have d := GaussianBinetBoseLinearApproximation.denominator_error p A B hB small
  have hE := positive_product _ _ hB hB
  have uB := denominator_inverse_bound p A B hA hB
  have vB := inverse_bound v A B hA hB (query_lower p A B hB)
  have prod := bounded_product _ _ _ _ _ _ (positive_product _ _ hA hE) hA
    (bounded_product _ _ _ _ _ _ hA hE uB (distance_symmetric _ _ _ _ hE d)) vB
  have raw := bound_congr (GaussianNameReciprocal.inverse_difference u v uP vP).eqSymm (.eqRefl _) (.eqRefl _) prod
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hA hE) hA) (le_refl one)
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

private theorem cancelled_time (p X Y D sign A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (linear X Y D sign A B) (reciprocal (query p A B)) ≐
      qmul (factor X Y D sign) (reciprocal (coefficient (coefficientClock p A))) := by
  let t := fraction A B
  let v := query p A B
  let c := coefficient (coefficientClock p A)
  let Z := factor X Y D sign
  have iv := GaussianRationalLowerBounds.reciprocal_identity_of_lower v A B hA hB (query_lower p A B hB)
  have ic := GaussianRationalLowerBounds.reciprocal_identity_of_lower (Γ := Γ) c one one (le_refl one) (le_refl one)
    (GaussianBinetBoseLinearApproximation.coefficient_lower (coefficientClock p A))
  have product := GaussianEulerBetaProductPascal.inverse_factor t c v (reciprocal v) (reciprocal c)
    (reciprocal_canonical c) ((query_factor p A B hB).eqTrans (qmul_commutative t c)) iv ic
  exact (qmul_congr (qmul_commutative t Z) (.eqRefl (reciprocal v))).eqTrans
    ((qmul_associative Z t (reciprocal v)).eqTrans (qmul_congr (.eqRefl Z) product.eqSymm))

def slopeBound (K : PTm n) : PTm n := cube K+num 100*K

private theorem frozen_error (p q X Y D sign A B K : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (small : Γ ⊢[PRAAx] le (num 10*A) B)
    (margin : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] distanceBounded (qmul (ap2 Atan p (atanData X Y D sign A B)) (reciprocal (ap2 Den q (denData A B))))
      (qmul (factor X Y D sign) (reciprocal (coefficient (coefficientClock q A)))) (A*slopeBound K) B := by
  let u := ap2 Atan p (atanData X Y D sign A B)
  let w := reciprocal (ap2 Den q (denData A B))
  let v := reciprocal (query q A B)
  let l := linear X Y D sign A B
  let T := cube (B*X)
  have hX := hz.andE₁.andE₁
  have hBX := positive_product _ _ hB hX
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ (positive_product _ _ hBX hBX) hBX
  have A_le : Γ ⊢[PRAAx] le A B := le_trans (by ipra_le 9*𝔞(A)) small
  have Dcube : Γ ⊢[PRAAx] le (cube D) (cube K*cube X) :=
    le_congr (.eqRefl _) (by unfold cube; ipra_ring) (le_mul_mono (le_mul_mono margin margin) margin)
  have first := scaled_distance w u l B A (cube (A*D)) T hA hT (denominator_inverse_bound q A B hA hB)
    (GaussianBinetArctangentLinearApproximation.name_error p X Y D sign A B hz hB)
  have e1 : Γ ⊢[PRAAx] distanceBounded (qmul u w) (qmul l w) (A*cube K) B := by
    apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hA hT) hB ?_
      (distance_congr (qmul_commutative w u) (qmul_commutative w l) (.eqRefl _) (.eqRefl _) first)
    exact le_congr (by dsimp only [T,cube]; ipra_ring) (by dsimp only [T,cube]; ipra_ring)
      (mul_le_mul_right (A*A*B*B) (le_mul_mono A_le Dcube))
  have lb : Γ ⊢[PRAAx] bounded l (A*K) B :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product (fraction A B) (factor X Y D sign) A B K one hB (le_refl one)
        (rational_time_bound A B hB) (factor_bound X Y D sign K hz margin))
  have raw := scaled_distance l w v (A*K) B (num 100) one hB (le_refl one) lb (inverse_error q A B hA hB small)
  have e2 : Γ ⊢[PRAAx] distanceBounded (qmul l w) (qmul l v) ((A*K)*num 100) B :=
    distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (by ipra_ring) raw
  exact distance_congr (.eqRefl _) (cancelled_time q X Y D sign A B hA hB)
    (by unfold slopeBound; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hB e1 e2)

private theorem coefficients_error (r s X Y D sign K : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (margin : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (factor X Y D sign) (reciprocal (coefficient r)))
      (qmul (factor X Y D sign) (reciprocal (coefficient s))) (two*K*(unit r+unit s)) (unit r*unit s) := by
  let Q := unit r*unit s
  have hQ := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive s)
  let x := coefficient r
  let y := coefficient s
  have h1 := le_refl (Γ := Γ) (one : PTm n)
  have lr := name_lower x one one h1 h1 (GaussianBinetBoseLinearApproximation.coefficient_lower r)
  have ls := name_lower y one one h1 h1 (GaussianBinetBoseLinearApproximation.coefficient_lower s)
  have e := GaussianNameReciprocal.inverse_distance x y one _ Q h1 hQ lr ls
    (GaussianBinetBoseLinearApproximation.coefficient_distance r s)
  have d := scaled_distance _ _ _ K one _ Q h1 hQ (factor_bound X Y D sign K hz margin) e
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (one_mul Q) d

def numerator (p q A B K : PTm n) : PTm n := A*slopeBound K*unit p*unit q+B*two*K*(unit p+unit q)

theorem observations (p q X Y D sign A B K : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (small : Γ ⊢[PRAAx] le (num 10*A) B)
    (margin : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (fd X Y D sign A B)) (ap2 endpointF q (endpointData X Y D sign))
      (numerator p q A B K) (B*unit p*unit q) := by
  let x := atanData X Y D sign A B
  let y := invData A B
  let r := exponent (multiplyModulus Atan Inv x y) p
  let u := exponent (GaussianNameReciprocal.modulus B) r+GaussianNameReciprocal.anchor B
  let v := coefficientClock u A
  let w := endpointClock q X Y D sign
  let P := unit p
  let Q := unit q
  let H := unit v
  let I := unit w
  let E := B*P*Q
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hHI := positive_product _ _ (unit_positive (Γ := Γ) v) (unit_positive w)
  have hE := positive_product _ _ (positive_product _ _ hB hP) hQ
  have later : Γ ⊢[PRAAx] le p v := by
    have pr : Γ ⊢[PRAAx] le p r := le_add_right _ _
    have ru : Γ ⊢[PRAAx] le r u := le_trans (le_add_right _ _) (le_add_right _ _)
    have uv := GaussianBinetBoseLinearApproximation.coefficient_clock_later (Γ := Γ) u A
    exact le_trans pr (le_trans ru uv)
  have PH : Γ ⊢[PRAAx] le P H := GaussianExponentialReference.unit_monotone later
  have QI : Γ ⊢[PRAAx] le Q I := GaussianExponentialReference.unit_monotone (endpoint_clock_later q X Y D sign)
  have inv := (GaussianNameReciprocal.name_at (Γ := Γ) Den B (denData A B) r).eqTrans
    (GaussianExponentialReference.recode_fixed _ (reciprocal_canonical (ap2 Den u (denData A B))))
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) Atan Inv x y p).eqTrans
    ((GaussianExponentialReference.recode_fixed (multiplyRaw Atan Inv r x y) (qmul_canonical _ _)).eqTrans
      (qmul_congr (.eqRefl _) inv))
  have first := frozen_error r u X Y D sign A B K hz hA hB small margin
  have second := coefficients_error v w X Y D sign K hz margin
  have mid := distance_radius_mono _ _ _ _ (A*slopeBound K*P*Q) E hB hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) first
  have last := distance_radius_mono _ _ _ _ (B*two*K*(P+Q)) E hHI hE (by
    dsimp only [E]
    ipra_le 2*𝔞(B*K*H*P)*sl QI+2*𝔞(B*K*I*Q)*sl PH) second
  exact distance_congr read.eqSymm (endpoint_at q X Y D sign).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE mid last)

theorem actual_second_Binet_integrand_zero_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 4) (var 5) ⟶ le one (var 6) ⟶ le one (var 7) ⟶
      le (num 10*var 6) (var 7) ⟶ le (var 4) (var 8*var 2) ⟶
      distanceBounded (ap2 F (var 0) (fd (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (ap2 endpointF (var 1) (endpointData (var 2) (var 3) (var 4) (var 5)))
        (numerator (var 0) (var 1) (var 6) (var 7) (var 8)) (var 7*unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (observations _ _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseIntegrandEndpoint

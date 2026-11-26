import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalFirstTaylorEvenReadback
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorDerivativeChart
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalValueDerivativeProperness

/-!
# The cofinal degree-one Barnes Taylor name is the original derivative

A single refined rational chart admits both signed unit steps. The
original quotient estimates and the first even grid meet at the actual
signed observations. Finite rational slack removal identifies the
factorial Taylor name with the original derivative name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorFirstDerivativeAnchor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add bounded bounded_add bounded_mono bounded_neg bounded_scale normSq normSq_one oneCode scale)
open GaussianBarnesCanonicalCofinalTaylorEvenGridLimit (observationClock observed uniformGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial_positive)
open GaussianBarnesCanonicalValueDerivative (denominator numerator stepGain)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1 norm1_negative norm1_one)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianNamedDifferenceQuotient (raw)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical canonical_unique ofGaussian ofGaussian_represents positive_product qadd qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale natScale_as_product natScale_congr naturalPoint)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qone_canonical)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "D" => GaussianBarnesCanonicalValueDerivative.nameF
local notation "dd" => GaussianBarnesCanonicalValueDerivative.data
local notation "Q" => GaussianBarnesCanonicalValueDerivative.quotientF
local notation "qd" => GaussianBarnesCanonicalValueDerivative.quotientData
local notation "L" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "ld" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "half" => ofGaussian oneCode two
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def refinement (p R : PTm n) : PTm n :=
  stepGain (R+one)+stepDivisor R+(uniformGain R zero one+numerator (R+one) oneCode)*unit p+one

def coefficientClock (p E : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.quadraticClock E+p

private theorem widened (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] source z (R+one) B :=
  .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))

private theorem signed_quotient (p t s z w h R B E : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R E)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w E)
    (hh : Γ ⊢[PRAAx] bounded h one) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hm : Γ ⊢[PRAAx] le (stepGain (R+one)*norm1 h) E)
    (hp : Γ ⊢[PRAAx] le (numerator (R+one) h*unit p) E)
    (hs : Γ ⊢[PRAAx] le p s) (ht : Γ ⊢[PRAAx] le (two*E*unit p) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded
      (raw V V t t (vd (add w h) (R+one) E) (vd w (R+one) E) h E)
      (ap2 D s (dd z (R+one) B)) (num 5) (unit p) := by
  let S := R+one
  let P := unit p
  let U := unit s
  let T := unit t
  let x := vd (add w h) S E
  let y := vd w S E
  let a := qd w h S E
  let b := dd z S B
  have hE := hw.andE₁
  have hP := unit_positive (Γ := Γ) p
  have hU := unit_positive (Γ := Γ) s
  have hT := unit_positive (Γ := Γ) t
  have late : Γ ⊢[PRAAx] le P U := unit_monotone hs
  have shiftRadius : Γ ⊢[PRAAx] le (R*E+one) (S*E) := by
    dsimp only [S]
    ipra_le sl hE
  have hshift : Γ ⊢[PRAAx] source (add w h) S E :=
    .andI hE (bounded_mono (bounded_add hw.andE₂ hh) shiftRadius)
  have hbase := widened w R E hw
  have admitted := GaussianBarnesCanonicalValueDerivative.input_of_margin w h S E hbase hshift hn hm
  have lead := GaussianBarnesCanonicalValueDerivativeProperness.fixed_reference_rate w z h S E B admitted (widened z R B hz) he
  have hinit := initial_positive (Γ := Γ) S
  have hDen : Γ ⊢[PRAAx] le one (denominator S E) := positive_product _ _ hE hinit
  have larger : Γ ⊢[PRAAx] le E (denominator S E) :=
    le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E hinit)
  have fit : Γ ⊢[PRAAx] le (numerator S h*P) (one*denominator S E) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_trans hp larger)
  have lead' := GaussianNamedRateRadius.weaken Q D a b _ _ one P hDen hP fit lead
  have rawD := GaussianNamedInverseRate.rate_at Q D a b one P s s lead'
  have rawQ := GaussianNamedDifferenceQuotient.independent_readback V V s t t x y h E
    (.andI (GaussianBarnesCanonicalValue.regular _ _ _ hshift)
      (.andI (GaussianBarnesCanonicalValue.regular _ _ _ hbase) (.andI hE hn)))
  have payQ : Γ ⊢[PRAAx]
      le (GaussianNamedDifferenceQuotient.numerator E s t t*P) (two*GaussianNamedDifferenceQuotient.denominator s t t) := by
    change Γ ⊢[PRAAx] le ((T*T+E*U*(T+T))*P) (two*(U*T*T))
    ipra_le 𝔞(T)*𝔞(T)*sl late+𝔞(U)*𝔞(T)*sl ht
  have payD : Γ ⊢[PRAAx]
      le (GaussianNamedInverseRate.rateNumerator one P s s*P) (num 3*GaussianNamedInverseRate.rateDenominator P s s) := by
    change Γ ⊢[PRAAx] le ((one*U*U+P*(U+U))*P) (num 3*(P*U*U))
    ipra_le 2*𝔞(P)*𝔞(U)*sl late
  have nearQ : Γ ⊢[PRAAx] distanceBounded (ap2 Q s a) (raw V V t t x y h E) two P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hU hT) hT) hP payQ rawQ
  have nearD : Γ ⊢[PRAAx] distanceBounded (ap2 Q s a) (ap2 D s b) (num 3) P :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive P s s hP) hP payD rawD
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hP (distance_symmetric _ _ _ _ hP nearQ) nearD)

private theorem double_self (x : PTm n) (hx : Γ ⊢[PRAAx] canonical x) :
    Γ ⊢[PRAAx] qadd x x ≐ natScale two x := by
  have read := natScale_congr (by ipra_ring : Γ ⊢[PRAAx] (two : PTm n) ≐ one+one) (.eqRefl x)
  have h := GaussianRationalNaturalScale.natScale_one_canonical x hx
  exact (read.eqTrans ((GaussianRationalNaturalScale.natScale_add one one x).eqTrans (qadd_congr h h))).eqSymm

private theorem half_double (x : PTm n) (hx : Γ ⊢[PRAAx] canonical x) :
    Γ ⊢[PRAAx] qmul (half : PTm n) (natScale two x) ≐ x := by
  let a : PTm n := half
  let m : PTm n := naturalPoint two
  have ht : Γ ⊢[PRAAx] le one (two : PTm n) := zero_lt_succ one
  have hm : Γ ⊢[PRAAx] qmul m a ≐ qone :=
    canonical_unique _ _ _ two (GaussianRationalHorner.qmul_canonical _ _) qone_canonical ht
      (GaussianRationalHorner.represents_congr (natScale_as_product two a) (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
        (GaussianRationalNaturalScale.natScale_represents two a oneCode two ht (ofGaussian_represents oneCode two ht)))
      (GaussianRationalReciprocal.qone_represents_scaled two)
  exact (qmul_congr (.eqRefl a) (natScale_as_product two x)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative a m x).eqSymm.eqTrans
      ((qmul_congr ((GaussianRationalPowerAlgebra.qmul_commutative a m).eqTrans hm) (.eqRefl x)).eqTrans
        ((GaussianRationalFiniteProduct.raw_one_left x).eqTrans (GaussianTranslatedNonconstant.recode_eq x hx))))

private theorem remove_double (x y A E : PTm n) (hx : Γ ⊢[PRAAx] canonical x) (hy : Γ ⊢[PRAAx] canonical y)
    (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] distanceBounded (natScale two x) (natScale two y) A E) :
    Γ ⊢[PRAAx] distanceBounded x y A E := by
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have hhalf : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (half : PTm n) one one := by
    apply GaussianRationalMetric.bounded_of_cleared _ _ two one one h₂ (le_refl _) (ofGaussian_represents _ _ h₂)
    have h := (congrMul (.eqRefl (one*one)) (normSq_one (Γ := Γ))).eqTrans
      (by ipra_ring : Γ ⊢[PRAAx] (one*one)*one ≐ one)
    exact le_congr h.eqSymm (by ipra_ring)
      (le_of_eq_add (d := num 3) (by ipra_ring) : Γ ⊢[PRAAx] le one (two*two))
  exact distance_congr (half_double x hx) (half_double y hy) (one_mul A) (.eqRefl _)
    (GaussianNamedDifferenceQuotient.scale_distance (half : PTm n) _ _ one A E hE hhalf h)

theorem common_late (p z R B J : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    let s := coefficientClock p (refinement p R*B)
    Γ ⊢[PRAAx] distanceBounded (ap2 L s (ld z (R+one) B J one)) (ap2 D s (dd z (R+one) B)) (num 15) (unit p) := by
  let A := refinement p R
  let E := A*B
  let w := scale A z
  let S := R+one
  let P := unit p
  let K := uniformGain R zero one
  let N := numerator S oneCode
  let s := coefficientClock p E
  let t := observationClock E one+exponent (two*E) p
  let a := ap2 L s (ld z S B J one)
  let b := ap2 L s (ld w S E J one)
  let d := ap2 D s (dd z S B)
  let x := observed t w oneCode R E one
  have hA : Γ ⊢[PRAAx] le one A := le_add_left _ _
  have hE := positive_product _ _ hA hz.andE₁
  have hP := unit_positive (Γ := Γ) p
  have grow : Γ ⊢[PRAAx] le A E :=
    le_congr (one_mul A) (mul_comm _ _) (mul_le_mul_right A hz.andE₁)
  have hw : Γ ⊢[PRAAx] source w R E := by
    refine .andI hE (le_congr (.eqRefl _) ?_ (bounded_scale A hz.andE₂))
    change Γ ⊢[PRAAx] (A*(R*B))*(A*(R*B)) ≐ (R*(A*B))*(R*(A*B))
    ipra_ring
  have chart : Γ ⊢[PRAAx] ofGaussian w E ≐ ofGaussian z B :=
    GaussianGammaEncodingRescaling.fraction_rescale z B A hz.andE₁ hA
  have hl : Γ ⊢[PRAAx] le (stepGain S) E := le_trans (le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))) grow
  have hd : Γ ⊢[PRAAx] le (stepDivisor R) E := le_trans (le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_add_right _ _))) grow
  have paid : Γ ⊢[PRAAx] le ((K+N)*P) E := le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) grow
  have pk : Γ ⊢[PRAAx] le (K*P) E := le_trans (mul_le_mul_right P (le_add_right _ _)) paid
  have pn : Γ ⊢[PRAAx] le (N*P) E := le_trans (mul_le_mul_right P (le_add_left _ _)) paid
  have hs : Γ ⊢[PRAAx] le p s := le_add_left _ _
  have hclock : Γ ⊢[PRAAx] le (two*E*P) (unit t) :=
    le_trans (query_budget _ _) (unit_monotone (le_add_left _ _))
  have hnorm : Γ ⊢[PRAAx] le one (normSq (oneCode : PTm n)) := le_congr (.eqRefl _) normSq_one.eqSymm (le_refl _)
  have hbn : Γ ⊢[PRAAx] bounded (oneCode : PTm n) one :=
    le_congr normSq_one.eqSymm (one_mul one).eqSymm (le_refl _)
  have normBack : Γ ⊢[PRAAx] norm1 (gneg (oneCode : PTm n)) ≐ one :=
    (norm1_negative oneCode).eqTrans norm1_one
  have margin : Γ ⊢[PRAAx] stepGain S*norm1 (oneCode : PTm n) ≐ stepGain S :=
    (congrMul (.eqRefl _) norm1_one).eqTrans (Common.mul_one_right _)
  have marginBack : Γ ⊢[PRAAx] stepGain S*norm1 (gneg (oneCode : PTm n)) ≐ stepGain S :=
    (congrMul (.eqRefl _) normBack).eqTrans (Common.mul_one_right _)
  have numeratorBack : Γ ⊢[PRAAx] numerator S (gneg (oneCode : PTm n)) ≐ N := by
    unfold numerator GaussianBarnesCanonicalValueDerivativeJoin.numerator
    exact congrMul (.eqRefl _) (norm1_negative oneCode)
  have pos := signed_quotient p t s z w oneCode R B E hz hw chart.eqSymm hbn hnorm
    (le_congr margin.eqSymm (.eqRefl _) hl) pn hs hclock
  have neg := signed_quotient p t s z w (gneg oneCode) R B E hz hw chart.eqSymm (bounded_neg hbn)
    (le_congr (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg oneCode).eqSymm hnorm)
    (le_congr marginBack.eqSymm (.eqRefl _) hl) (le_congr (congrMul numeratorBack (.eqRefl P)).eqSymm (.eqRefl _) pn) hs hclock
  have dc : Γ ⊢[PRAAx] canonical d := GaussianNameArithmetic.add_canonical _ _ _ _ _
  have xToD : Γ ⊢[PRAAx] distanceBounded x (natScale two d) (num 10) P :=
    distance_congr (GaussianBarnesCanonicalFirstTaylorEvenReadback.literal_quotients t z A oneCode R E (.andI hE hnorm)).eqSymm
      (double_self d dc) (by ipra_ring) (.eqRefl _) (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hP pos neg)
  have step : Γ ⊢[PRAAx] le ((one*stepDivisor R)*norm1 (oneCode : PTm n)) E :=
    le_congr ((congrMul (one_mul _) norm1_one).eqTrans (Common.mul_one_right _)).eqSymm (.eqRefl _) hd
  have hJ : Γ ⊢[PRAAx] le one (previous J) := zero_lt_succ (succ J)
  have grid := GaussianBarnesCanonicalCofinalTaylorEvenGridLimit.uniform_rate w (oneCode : PTm n) R E zero J one t s hw hnorm
    step (.eqRefl _) hJ (le_add_right _ _) (le_add_right _ _)
  have sq : Γ ⊢[PRAAx] le E (E*E) := le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E hE)
  have budget : Γ ⊢[PRAAx] le ((K*(norm1 (oneCode : PTm n)*norm1 (oneCode : PTm n)))*P) (one*(E*E)) :=
    le_congr (congrMul ((congrMul (.eqRefl K) ((congrMul norm1_one norm1_one).eqTrans (one_mul one))).eqTrans
      (Common.mul_one_right K)).eqSymm (.eqRefl P)) (one_mul _).eqSymm (le_trans pk sq)
  have xToB : Γ ⊢[PRAAx] distanceBounded x (natScale two b) one P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE hE) hP budget grid
  have same := GaussianBarnesCanonicalTaylorDerivativeChart.cofinal_cross z w S B E J one
    (widened z R B hz) (widened w R E hw) hJ chart.eqSymm
  have chartObs := cross_at L L (ld z S B J one) (ld w S E J one) s s same
  have hU := unit_positive (Γ := Γ) s
  have close : Γ ⊢[PRAAx] distanceBounded a b two P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hP
      (by have late := unit_monotone hs; ipra_le 2*𝔞(unit s)*sl late) chartObs
  have aToB : Γ ⊢[PRAAx] distanceBounded (natScale two a) (natScale two b) (num 4) P :=
    distance_congr (natScale_as_product two a).eqSymm (natScale_as_product two b).eqSymm (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifferenceQuotient.scale_distance (naturalPoint two) a b two two P hP
        (GaussianNamedNaturalScale.natural_point_bound two) close)
  have track := distance_triangle_same _ _ _ _ _ _ hP aToB
    (distance_triangle_same _ _ _ _ _ _ hP (distance_symmetric _ _ _ _ hP xToB) xToD)
  have ac : Γ ⊢[PRAAx] canonical a := GaussianNameArithmetic.multiply_canonical _ _ _ _ _
  exact remove_double a d (num 15) P ac dc hP (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) track)

theorem comparison_slack (p q m z R B J : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] slack (qsub (ap2 L p (ld z (R+one) B J one)) (ap2 D q (dd z (R+one) B)))
      (unit p+unit q) (unit p*unit q) (num 17) m := by
  let s := coefficientClock m (refinement m R*B)
  let U := unit m
  let X := unit p
  let Y := unit q
  let T := unit s
  let Z := (X*Y)*U
  let a := ld z (R+one) B J one
  let b := dd z (R+one) B
  let M : PTm n := num 17
  have hb := widened z R B hz
  have hA := GaussianBarnesCanonicalTaylorProductDerivativeName.regular z (R+one) B J one hb (zero_lt_succ (succ J))
  have hB := GaussianBarnesCanonicalValueDerivative.regular z (R+one) B hb
  have late : Γ ⊢[PRAAx] le U T := unit_monotone (le_add_left m _)
  have hx := unit_positive (Γ := Γ) p
  have hy := unit_positive (Γ := Γ) q
  have hu := unit_positive (Γ := Γ) m
  have ht := unit_positive (Γ := Γ) s
  have hZ := positive_product _ _ (positive_product _ _ hx hy) hu
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 L p a) (ap2 L s a) ((U+X)*Y) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hx ht) hZ
      (by dsimp only [Z]; ipra_le 𝔞(X)*𝔞(X)*𝔞(Y)*sl late) (point_at L a p s hA)
  have middle : Γ ⊢[PRAAx] distanceBounded (ap2 L s a) (ap2 D s b) (num 15*(X*Y)) Z :=
    distance_radius_mono _ _ _ _ _ _ hu hZ (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
      (common_late m z R B J hz)
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 D s b) (ap2 D q b) ((U+Y)*X) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht hy) hZ
      (by dsimp only [Z]; ipra_le 𝔞(Y)*𝔞(Y)*𝔞(X)*sl late) (point_at D b s q hB)
  change Γ ⊢[PRAAx] distanceBounded (ap2 L p a) (ap2 D q b) ((X+Y)*U+M*(X*Y)) Z
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [M]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ first (distance_triangle_same _ _ _ _ _ _ hZ middle last))

theorem cross (z R B J : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent L D (ld z (R+one) B J one) (dd z (R+one) B) := by
  refine .allI (.allI ?_)
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let r := sh R+one
  let x := ap2 L p (ld (sh z) r (sh B) (sh J) one)
  let y := ap2 D q (dd (sh z) r (sh B))
  let A := unit p+unit q
  let E := unit p*unit q
  let m := GaussianRationalSlackRemoval.precision (qsub x y) A E (num 17)
  have h : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Δ,Fm.shift,Syn.shift] using hz.shift.shift
  have exactBound := slack_removal_at (qsub x y) A E (num 17) (positive_product _ _ (unit_positive p) (unit_positive q))
    (comparison_slack p q m (sh z) (sh R) (sh B) (sh J) h)
  simpa [crossEquivalent,sh,Δ,p,q,r,x,y,A,E,Syn.shift,one,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
    GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData,GaussianBarnesCanonicalValueDerivative.data,
    GaussianBarnesCanonicalValueDerivativeJoin.derivativeData,GaussianNamedNativeProductDerivativeRate.derivativeData,
    distanceBounded] using exactBound

theorem actual_Barnes_factorial_degree_one_original_derivative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let z := var 0
       let R := var 1
       let B := var 2
       let J := var 3
       source z R B ⟶ crossEquivalent L D (ld z (R+one) B J one) (dd z (R+one) B)) :=
  closeUniv 4 (.impI (cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorFirstDerivativeAnchor

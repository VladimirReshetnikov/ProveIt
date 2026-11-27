import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Convexity.GaussianGammaDigammaConvexComparison
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftBinding
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementAffine

/-!
# Secants of the native log-Gamma name

A forward difference between two positive rational endpoints lies
between the two unit chord differences immediately outside the interval,
multiplied by the interval length. The finite bounds record only an
explicit dyadic observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftSecants

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaConvexComparison (barycenter_order)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianStirlingGammaFractionalIncrementObservations (weighted_at weightedCost)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "lg" => logGammaData

theorem upper_negative (x y K P : PTm n) (h : Γ ⊢[PRAAx] upper (fstT x) (fstT y) K P) :
    Γ ⊢[PRAAx] upper (fstT (qnegative y)) (fstT (qnegative x)) K P := by
  let a := ComplexLogarithmRemainder.re (rawGaussian x)
  let b := ComplexLogarithmRemainder.re (rawGaussian y)
  let E := rawDen x
  let F := rawDen y
  have hx := (raw_represents (Γ := Γ) x).andE₁
  have hy := (raw_represents (Γ := Γ) y).andE₁
  have nx := (GaussianRationalMetric.qnegative_represents x _ E (raw_represents (Γ := Γ) x)).andE₁
  have ny := (GaussianRationalMetric.qnegative_represents y _ F (raw_represents (Γ := Γ) y)).andE₁
  have nx' : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qnegative x)) (-a) E := GaussianRationalHorner.scalar_congr (.eqRefl _) (by apply ZT.derive; simp [a,GaussianRootAlgebra.re_neg])
    (.eqRefl _) nx
  have ny' : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qnegative y)) (-b) F := GaussianRationalHorner.scalar_congr (.eqRefl _) (by apply ZT.derive; simp [b,GaussianRootAlgebra.re_neg])
    (.eqRefl _) ny
  have h := to_signed _ _ a b E F K P hx hy h
  apply from_signed _ _ (-b) (-a) F E K P (raw_den_positive y) (raw_den_positive x) ny' nx'
  apply zle_of_toZ (PolynomialBisection.slack (left a F P) (right b E F K P))
  have eq := zle_toZ h
  simp only [left,right,PolynomialBisection.slack,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat,Q.mk_mul,map_mul] at eq ⊢
  linear_combination eq

theorem negative_mul (x y : PTm n) : Γ ⊢[PRAAx] qnegative (qmul x y) ≐ qmul x (qnegative y) := by
  let M : PTm n := GaussianRationalMatrixFiniteSums.minusOne
  have h := GaussianRationalMatrixFiniteSums.negative_as_minusOne (Γ := Γ) (qmul x y)
  have e := (GaussianReciprocalHorner.qmul_associative (Γ := Γ) M x y).eqSymm.eqTrans
    (qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative M x) (.eqRefl y))
  exact h.eqTrans (e.eqTrans ((GaussianReciprocalHorner.qmul_associative x M y).eqTrans
    (qmul_congr (.eqRefl _) (GaussianRationalMatrixFiniteSums.negative_as_minusOne y).eqSymm)))

def logSample (p u b : PTm n) : PTm n := ap2 logGammaF p (lg u b)

theorem unit_chord_sample (p u b : PTm n) (hs : Γ ⊢[PRAAx] source u b) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (qsub (logSample p (u+b) b) (logSample p u b))
      (GaussianHarmonicLogarithmName.sample p u b) (num 5) (unit p) := by
  let g := logSample p u b
  let l := GaussianHarmonicLogarithmName.sample p u b
  let U := unit p
  have hp := unit_positive (Γ := Γ) p
  have law := GaussianStirlingGammaLogShift.log_gamma_increment u b hs
  have diag := GaussianNameEquivalence.diagonal_at _ _ _ _ p (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ law)
  have named := GaussianNameRingLaws.add_sample_error GaussianHarmonicLogarithmName.nameF logGammaF
    (GaussianHarmonicLogarithmName.data u b) (lg u b) p
    (GaussianHarmonicLogarithmName.name_regular u b hs) (log_gamma_regular u b hs)
  have sumError := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hp diag named
  have same := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) g U hp
  have diff := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hp sumError same
  have e := (GaussianRationalSyntheticDivision.qsub_congr (GaussianReciprocalHorner.qadd_commutative (Γ := Γ) l g)
      (.eqRefl g)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel g l (GaussianHarmonicLogarithmName.sample_real p u b).andE₁)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) e
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) diff

def leftCost (u b r : PTm n) : PTm n :=
  weightedCost (r+b) r b (lg (u+b) b) (lg u b) (lg (u+b+r) b)

def rightCost (u b r : PTm n) : PTm n :=
  weightedCost (r+b) r b (lg (u+b+r) b) (lg (u+b+r+b) b) (lg (u+b) b)

theorem lower_secant (p u b r : PTm n) (hs : Γ ⊢[PRAAx] source u b) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] upper (fstT (qmul (fraction r b) (qsub (logSample p (u+b) b) (logSample p u b))))
      (fstT (qsub (logSample p (u+b+r) b) (logSample p (u+b) b))) (leftCost u b r) (unit p) := by
  let d := u+b
  let c := d+r
  have hD := GaussianStirlingGammaLogarithm.source_shift u b hs
  have hC : Γ ⊢[PRAAx] source c b := .andI (le_trans hD.andE₁ (le_add_right _ _)) hs.andE₂
  have h := barycenter_order u c d b r b hs hC hD hr (by unfold c d; ipra_ring)
  have raw := weighted_at p _ _ _ _ _ _ (log_gamma_regular d b hD) (log_gamma_regular u b hs)
    (log_gamma_regular c b hC) h
  have eq := GaussianStirlingGammaFractionalIncrementAffine.lower_increment (logSample p c b) (logSample p u b)
    (logSample p d b) b r (leftCost u b r) (unit p) hs.andE₂ raw
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hs.andE₂ (unit_positive p)) eq
    (by ipra_le 𝔞(leftCost u b r)*𝔞(unit p)*sl hs.andE₂)

theorem upper_secant (p u b r : PTm n) (hs : Γ ⊢[PRAAx] source u b) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] upper (fstT (qsub (logSample p (u+b+r) b) (logSample p (u+b) b)))
      (fstT (qmul (fraction r b) (qsub (logSample p (u+b+r+b) b) (logSample p (u+b+r) b))))
      (rightCost u b r) (unit p) := by
  let d := u+b
  let c := d+r
  let f := c+b
  let C := logSample p c b
  let D := logSample p d b
  let F := logSample p f b
  have hD := GaussianStirlingGammaLogarithm.source_shift u b hs
  have hC : Γ ⊢[PRAAx] source c b := .andI (le_trans hD.andE₁ (le_add_right _ _)) hs.andE₂
  have hF := GaussianStirlingGammaLogarithm.source_shift c b hC
  have h := barycenter_order f d c b r b hF hD hC hr (by unfold f c d; ipra_ring)
  have raw := weighted_at p _ _ _ _ _ _ (log_gamma_regular c b hC) (log_gamma_regular f b hF)
    (log_gamma_regular d b hD) h
  have eq := GaussianStirlingGammaFractionalIncrementAffine.lower_increment D F C b r (rightCost u b r)
    (unit p) hs.andE₂ raw
  have rev := upper_negative _ _ _ _ eq
  have first := GaussianRationalDistanceOrder.reversed_difference (Γ := Γ) D C
  have last := (negative_mul (Γ := Γ) (fraction r b) (qsub C F)).eqTrans
    (qmul_congr (.eqRefl _) (GaussianRationalDistanceOrder.reversed_difference _ _))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hs.andE₂ (unit_positive p))
    (upper_congr (congrFst first) (congrFst last) (.eqRefl _) (.eqRefl _) rev)
    (by ipra_le 𝔞(rightCost u b r)*𝔞(unit p)*sl hs.andE₂)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftSecants

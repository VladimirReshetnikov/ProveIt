import IPRADerivations.Analysis.Logarithm.Robin.GaussianRobinLogarithmParity
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmName
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic

/-!
# Cofinal observations of the original Robin artanh series

The finite parity identity uses a degree of twice the Robin cutoff.
An even observation clock makes that degree exactly the one used by both
original Gaussian logarithm samplers. Their actual rounding certificates
control the error of the original Robin rational sample.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinOddLogarithmName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz)
open GaussianRobinLogarithmParity (native)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (p : PTm n) : PTm n := two*(p+two)
def cutoff (p : PTm n) : PTm n := p+num 5
def negativeArgument (a : PTm n) : PTm n := ComplexLogarithmRemainder.neg (native a)
def stored (K a b : PTm n) : PTm n :=
  RationalGaussianEmbedding.embed (RationalCubeMidpoint.fraction (Nz K a b) (Dz K a b))
def sample (p a b : PTm n) : PTm n := stored (cutoff p) a b
def difference (p a b : PTm n) : PTm n :=
  qsub (GaussianLocalLogarithmName.value p (native a) a b)
    (GaussianLocalLogarithmName.value p (negativeArgument a) a b)

ipra_subst sample [stored, cutoff]
ipra_subst difference [negativeArgument]

theorem exact_degree (p : PTm n) : Γ ⊢[PRAAx]
    DyadicComplexLogarithm.precision (clock p)+two ≐ two*cutoff p := by
  unfold DyadicComplexLogarithm.precision clock cutoff
  ipra_ring

theorem original_finite_difference (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub
      (GaussianFiniteLogarithmSampler.sample (native a) b (DyadicComplexLogarithm.precision (clock p)))
      (GaussianFiniteLogarithmSampler.sample (negativeArgument a) b (DyadicComplexLogarithm.precision (clock p)))
      ≐ sample p a b := by
  have comparison (z : PTm n) : Γ ⊢[PRAAx]
      GaussianFiniteLogarithmSampler.sample z b (DyadicComplexLogarithm.precision (clock p)) ≐
        GaussianFiniteLogarithmPolynomial.value (two*cutoff p) (GaussianRationalHorner.ofGaussian z b) :=
    (GaussianFiniteLogarithmSampler.value_eq_original_sample z b _ hb).eqSymm.eqTrans
      (GaussianRationalFiniteSum.sum_index_congr GaussianFiniteLogarithmPolynomial.sourceTerm
        (exact_degree p) (.eqRefl _))
  exact (qsub_congr (comparison (native a)) (comparison (negativeArgument a))).eqTrans
    (GaussianRobinLogarithmParity.original_Robin_logarithm_value a b (cutoff p) hb)

theorem shifted_clock_lower (p : PTm n) : Γ ⊢[PRAAx] le (p+two) (clock p) :=
  le_of_eq_add (d := p+two) (by unfold clock; ipra_ring)

theorem clock_unit_lower (p : PTm n) : Γ ⊢[PRAAx] le (num 4*unit p) (unit (clock p)) := by
  have factor : Γ ⊢[PRAAx] unit (p+two) ≐ num 4*unit p :=
    (pw_add_numeral 2 2 p).eqTrans (mul_comm _ _)
  exact le_congr factor (.eqRefl _) (GaussianBalancedRadiusArithmetic.unit_monotone _ _ (shifted_clock_lower p))

theorem rounding_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (difference (clock p) a b) (sample p a b) one (num 8*unit p) := by
  let t := clock p
  let U := DyadicComplexLogarithm.unit t
  have hu := GaussianLocalLogarithmName.unit_positive (Γ := Γ) t
  have eight : Γ ⊢[PRAAx] le one (num 8 : PTm n) := le_of_eq_add (d := num 7) (by ipra_ring)
  have target := positive_product _ _ eight (unit_positive p)
  have metric := GaussianFastValueCut.distance_difference_same _ _ _ _ _ _ _ hu
    (GaussianLocalLogarithmName.observation_distance t (native a) a b hb)
    (GaussianLocalLogarithmName.observation_distance t (negativeArgument a) a b hb)
  have raw : Γ ⊢[PRAAx] distanceBounded (difference t a b) (sample p a b) (num 8) U :=
    distance_congr (.eqRefl _) (original_finite_difference p a b hb) (by ipra_ring) (.eqRefl _) metric
  have scaleBound : Γ ⊢[PRAAx] le (num 8*(num 8*unit p)) (one*U) :=
    le_congr (by ipra_ring) (by
      have e := natEq (GaussianLocalLogarithmName.unit_factor (Γ := Γ) t)
      apply deriveNat; ipra_simps; rw [e]; ring)
      (mul_le_mul_right (num 16) (clock_unit_lower p))
  exact distance_radius_mono _ _ _ _ _ _ hu target scaleBound raw

def source (a b : PTm n) : Fm PTm n := le one b ⋏ le (two*a) b

theorem log_sources (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source (native a) a b ⋏
      GaussianLocalLogarithmName.source (negativeArgument a) a b := by
  open ComplexLogarithmRemainder in
  have norm : Γ ⊢[PRAAx] bounded (native a) a := by
    change Γ ⊢[PRAAx] le (normSq (scale a oneCode)) (a*a)
    exact le_congr ((normSq_scale a oneCode).eqTrans
      ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))).eqSymm (.eqRefl _) (le_refl _)
  exact .andI (.andI h.andE₁ (.andI norm h.andE₂))
    (.andI h.andE₁ (.andI (ComplexLogarithmRemainder.bounded_neg norm) h.andE₂))

theorem log_difference_bound (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (difference p a b) (difference q a b)
      (two*(unit p+unit q)) (unit p*unit q) := by
  have sources := log_sources a b h
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianFastValueCut.distance_difference_same _ _ _ _ _ _ _
      (positive_product _ _ (unit_positive p) (unit_positive q))
      (GaussianLocalLogarithmName.value_regularity p q (native a) a b sources.andE₁)
      (GaussianLocalLogarithmName.value_regularity p q (negativeArgument a) a b sources.andE₂))

theorem regularity_at (p q a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (sample p a b) (sample q a b) (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let P := unit (clock p)
  let Q := unit (clock q)
  let E := num 8*(U*V)
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := le_of_eq_add (d := num 7) (by ipra_ring)
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have hp := unit_positive (Γ := Γ) (clock p)
  have hq := unit_positive (Γ := Γ) (clock q)
  have uv := positive_product _ _ hu hv
  have he := positive_product _ _ h8 uv
  have h8u := positive_product _ _ h8 hu
  have h8v := positive_product _ _ h8 hv
  have left := distance_radius_mono _ _ _ _ V E h8u he
    (le_congr (by unfold E; ipra_ring) (.eqRefl _) (le_refl _))
    (distance_symmetric _ _ _ _ h8u (rounding_bound p a b h.andE₁))
  have right := distance_radius_mono _ _ _ _ U E h8v he
    (le_congr (by unfold E; ipra_ring) (by ipra_ring) (le_refl (num 8*(U*V))))
    (rounding_bound q a b h.andE₁)
  have midScale : Γ ⊢[PRAAx] le ((two*(P+Q))*E) ((num 4*(U+V))*(P*Q)) := by
    have x := mul_le_mul_right (num 4*Q*V) (clock_unit_lower (Γ := Γ) p)
    have y := mul_le_mul_right (num 4*P*U) (clock_unit_lower (Γ := Γ) q)
    exact le_congr (by unfold E; ipra_ring) (by ipra_ring) (add_le_add₂ x y)
  have mid := distance_radius_mono _ _ _ _ (num 4*(U+V)) E
    (positive_product _ _ hp hq) he midScale (log_difference_bound (clock p) (clock q) a b h)
  have total := distance_triangle_same _ _ _ _ _ _ he (distance_triangle_same _ _ _ _ _ _ he left mid) right
  exact distance_radius_mono _ _ _ _ _ _ he uv
    (le_of_eq_add (d := num 3*(U+V)*(U*V)) (by ipra_ring)) total

def inputs (a b : PTm n) : PTm n := pairT a b
def pointTerm (p x : PTm n) : PTm n := sample p (fstT x) (sndT x)
def pointF : PR 2 := PTm.toPR (pointTerm (var 0) (var 1))
def point (p a b : PTm n) : PTm n := ap2 pointF p (inputs a b)

ipra_subst pointTerm
ipra_subst source
ipra_subst inputs

theorem point_at (p a b : PTm n) : Γ ⊢[PRAAx] point p a b ≐ sample p a b := by
  have prog : Γ ⊢[PRAAx] point p a b ≐ pointTerm p (inputs a b) := by
    simpa only [point,pointF,ap2,subst_pointTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (pointTerm (var 0) (var 1) : PTm 2) ![p,inputs a b]
  refine prog.eqTrans ?_
  ipra_congr (sample (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl p, (show _ ⊢[PRAAx] fstT (inputs a b) ≐ a from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (inputs a b) ≐ b from snd_pair _ _)] using [pointTerm]

theorem name_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN pointF (inputs a b) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) := by
    simpa only [Fm.shift,Syn.shift,subst_source] using h.shift.shift
  let A := Syn.shift (Syn.shift a)
  let B := Syn.shift (Syn.shift b)
  have e := distance_congr
    (point_at (var 1) A B).eqSymm (point_at (var 0) A B).eqSymm (.eqRefl _) (.eqRefl _)
    (regularity_at (var 1) (var 0) A B hs)
  simpa only [point,Syn.shift,subst_inputs,A,B,GaussianEuclideanPointDistance.unit,unit] using e

open GaussianLocalLogarithmName renaming pointF → localF
open GaussianNameArithmetic (addF addData)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)

def plusData (a b : PTm n) : PTm n := GaussianLocalLogarithmName.data (native a) a b
def minusData (a b : PTm n) : PTm n := GaussianLocalLogarithmName.data (negativeArgument a) a b
def logDifferenceF : PR 2 := addF localF (negativeF localF)
def logDifferenceData (a b : PTm n) : PTm n := addData (plusData a b) (negativeData (minusData a b))

ipra_subst logDifferenceData [plusData, minusData, negativeArgument]

theorem log_difference_name (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN logDifferenceF (logDifferenceData a b) := by
  have hs := log_sources a b h
  have u := GaussianLocalLogarithmName.name_regular _ _ _ hs.andE₁
  have v := GaussianLocalLogarithmName.name_regular _ _ _ hs.andE₂
  exact GaussianNameArithmetic.add_fast _ _ _ _ u (GaussianNameRingLaws.negative_fast _ _ v)

theorem log_difference_observation_error (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logDifferenceF p (logDifferenceData a b))
      (difference p a b) (num 6) (unit p) := by
  let X := plusData a b
  let Y := minusData a b
  let A := ap2 localF p X
  let B := ap2 localF p Y
  have hs := log_sources a b h
  have u := GaussianLocalLogarithmName.name_regular _ _ _ hs.andE₁
  have v := GaussianLocalLogarithmName.name_regular _ _ _ hs.andE₂
  have hn := GaussianNameRingLaws.negative_fast _ _ v
  have added := GaussianNameRingLaws.add_sample_error localF (negativeF localF) X (negativeData Y) p u hn
  have negated := GaussianNameRingLaws.sum_right_error A _ _ _ _ (unit_positive p)
    (GaussianNameRingLaws.negative_sample_error localF Y p v)
  have e : Γ ⊢[PRAAx] GaussianRationalHorner.qadd A (qsub GaussianRationalHorner.qzero B) ≐ difference p a b := by
    have er := GaussianRationalSyntheticDivision.qzero_add (Γ := Γ) (GaussianRationalMetric.qnegative B)
      (GaussianRationalMetric.qnegative_canonical B)
    exact (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) er).eqTrans
      (qsub_congr (GaussianLocalLogarithmName.point_at _ _ _ _) (GaussianLocalLogarithmName.point_at _ _ _ _))
  exact distance_congr (.eqRefl _) e
    (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) added negated)

theorem stored_observation_error (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (difference p a b) (point p a b) (num 3) (unit p) := by
  have hs := log_sources a b h
  have hu := unit_positive (Γ := Γ) p
  have ht := le_trans (le_add_right p two) (shifted_clock_lower (Γ := Γ) p)
  have pos := GaussianLocalLogarithmName.later_distance p (clock p) _ _ _ hs.andE₁ ht
  have neg := GaussianLocalLogarithmName.later_distance p (clock p) _ _ _ hs.andE₂ ht
  have mid := distance_symmetric _ _ _ _ hu
    (GaussianFastValueCut.distance_difference_same _ _ _ _ _ _ _ hu pos neg)
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := le_of_eq_add (d := num 7) (by ipra_ring)
  have right := distance_radius_mono _ _ _ _ one (unit p) (positive_product _ _ h8 hu) hu
    (le_of_eq_add (d := num 7*unit p) (by ipra_ring))
    (rounding_bound p a b h.andE₁)
  exact distance_congr (.eqRefl _) (point_at p a b).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu mid right)

theorem original_difference_name (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent logDifferenceF pointF (logDifferenceData a b) (inputs a b) := by
  refine GaussianNameRingLaws.equivalent_of_envelope logDifferenceF pointF
    (logDifferenceData a b) (inputs a b) (num 9) (log_difference_name a b h) (name_regular a b h) ?_
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,subst_source] using h.shift
  have e : Γ.map Fm.shift ⊢[PRAAx] distanceBounded
      (ap2 logDifferenceF (var 0) (logDifferenceData (Syn.shift a) (Syn.shift b)))
      (point (var 0) (Syn.shift a) (Syn.shift b)) (num 9) (unit (var 0)) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ (unit_positive (var 0))
        (log_difference_observation_error (var 0) (Syn.shift a) (Syn.shift b) hs)
        (stored_observation_error (var 0) (Syn.shift a) (Syn.shift b) hs))
  simpa only [point,Syn.shift,subst_inputs,subst_logDifferenceData,LeanProofs.IPRA.PTm.subst_num] using e

theorem original_Robin_odd_name_rounding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ distanceBounded (difference (clock (var 0)) (var 1) (var 2))
      (sample (var 0) (var 1) (var 2)) one (num 8*unit (var 0))) :=
  closeUniv 3 (.impI (rounding_bound _ _ _ Prf.hyp0))

theorem original_Robin_odd_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ GaussianEuclideanDistanceName.pointCN pointF (inputs (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular _ _ Prf.hyp0))

theorem original_Robin_odd_log_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶
      crossEquivalent logDifferenceF pointF (logDifferenceData (var 0) (var 1)) (inputs (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_difference_name _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRobinOddLogarithmName

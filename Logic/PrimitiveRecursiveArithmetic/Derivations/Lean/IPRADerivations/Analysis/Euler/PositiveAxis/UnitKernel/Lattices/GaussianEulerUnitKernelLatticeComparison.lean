import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.Lattices.GaussianEulerUnitKernelLatticeSum
import IPRADerivations.Analysis.Integration.CompactGrids.Comparisons.GaussianCompactUniformGridComparison
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandTimeProperness
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds

/-!
# The original unit-kernel lattice versus its ordinary affine quadrature

The literal lattice times (a+i)/M and the ordinary quadrature times
(a*C+C*i)/(M*C) have exactly the same value. The original compact
modulus at distance zero retains both independently requested queries.
The genuine finite sum and common weight give precisely the panel width
times these two dyadic errors. Count and width zero are included.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelLatticeComparison

open_ipra
open GaussianEulerUnitKernelCompactName (source evaluatorF fixedData lipschitz)
open GaussianCompactRiemannName (inside grid value sampleBody sampleData quadrature)
open GaussianEulerUnitKernelLatticeSum (lattice)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p q C : PTm n) : PTm n := C*(unit p+unit q)
def denominator (p q M : PTm n) : PTm n := M*unit p*unit q
ipra_subst numerator
ipra_subst denominator

theorem lattice_inside (i a C M : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] le i C) : Γ ⊢[PRAAx] inside a C M (pairT (a+i) M) := by
  have hp := le_trans ha (le_add_right a i)
  have low : Γ ⊢[PRAAx] le (a*M) (M*(a+i)) := le_of_eq_add (d := M*i) (by ipra_ring)
  have high : Γ ⊢[PRAAx] le (M*(a+i)) ((a+C)*M) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (a*M) (mul_le_mul_right M hi))
  exact .andI (le_congr (.eqRefl _) (fst_pair _ _).eqSymm hp)
    (.andI (le_congr (.eqRefl _) (snd_pair _ _).eqSymm hM)
      (.andI (le_congr (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm low)
        (le_congr (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm high)))

theorem time_values_equal (i a C M : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    value (pairT (a+i) M) ≐ value (grid i C a C M) :=
  (GaussianCompactRiemannName.fraction_congr _ _ _ _ (fst_pair _ _) (snd_pair _ _)).eqTrans
    ((GaussianEulerIntegrandTimeProperness.fraction_proper (a+i) M (a*C+C*i) (M*C) hM
      (positive_product _ _ hM hC) (by ipra_ring)).eqTrans (GaussianCompactRiemannName.value_grid i C a C M).eqSymm)

theorem original_row (i p q z R B a C M G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C M G)
    (hC : Γ ⊢[PRAAx] le one C) (hi : Γ ⊢[PRAAx] lt i C) : Γ ⊢[PRAAx]
    distanceBounded (inst2 GaussianEulerUnitKernelLatticeSum.body i (GaussianEulerUnitKernelLatticeSum.data p z B a M))
      (inst2 (sampleBody evaluatorF) i (sampleData q C a C M (fixedData z B)))
      (unit p+unit q) (unit p*unit q) := by
  have ha := GaussianEulerUnitKernelCompactName.start_positive z R B a C M G h
  have ht := lattice_inside i a C M ha h.andE₂.andE₁ (le_of_lt hi)
  have hu := GaussianCompactRiemannName.grid_inside i C a C M ha h.andE₂.andE₁ hC (le_of_lt hi)
  have same := time_values_equal (Γ := Γ) i a C M h.andE₂.andE₁ hC
  have near : Γ ⊢[PRAAx] distanceBounded (value (pairT (a+i) M)) (value (grid i C a C M)) zero one :=
    distance_congr (.eqRefl _) same (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero _ one (le_refl one))
  have rate := GaussianCompactRiemannName.sampled_modulus_at evaluatorF a C M (lipschitz R G) (fixedData z B)
    p q (pairT (a+i) M) (grid i C a C M) zero one
    (GaussianEulerUnitKernelCompactName.sampled_modulus z R B a C M G h) (le_refl one) ht hu near
  exact distance_congr ((GaussianEulerUnitKernelCompactName.sample_at p z B (a+i) M).eqTrans
      (GaussianEulerUnitKernelLatticeSum.row_at i p z B a M).eqSymm)
    (GaussianCompactRiemannName.sample_body_at evaluatorF i q C a C M (fixedData z B)).eqSymm
    (by unfold GaussianNamedInverseRate.rateNumerator; ipra_ring)
    (by unfold GaussianNamedInverseRate.rateDenominator; ipra_ring) rate

theorem original_terms (p q z R B a C M G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C M G)
    (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    termsDistance GaussianEulerUnitKernelLatticeSum.body (sampleBody evaluatorF) C
      (GaussianEulerUnitKernelLatticeSum.data p z B a M) (sampleData q C a C M (fixedData z B))
      (unit p+unit q) (unit p*unit q) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift M) (Syn.shift G) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift C) := by simpa [Fm.shift,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  simpa only [termsDistance,GaussianEulerUnitKernelLatticeSum.subst_data,GaussianCompactRiemannName.subst_sampleData,
    GaussianEulerUnitKernelCompactName.subst_fixedData,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,Syn.shift] using
    original_row (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift a) (Syn.shift C) (Syn.shift M) (Syn.shift G) hs.wk cs.wk Prf.hyp0

theorem positive_comparison (p q z R B a C M G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C M G)
    (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    distanceBounded (lattice p C z B a M) (quadrature evaluatorF q C a C M (fixedData z B))
      (numerator p q C) (denominator p q M) := by
  let u := GaussianRationalFiniteSum.sum GaussianEulerUnitKernelLatticeSum.body C (GaussianEulerUnitKernelLatticeSum.data p z B a M)
  let v := GaussianRationalFiniteSum.sum (sampleBody evaluatorF) C (sampleData q C a C M (fixedData z B))
  let w := fraction one M
  have hM := h.andE₂.andE₁
  have hD := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have rows := sum_distance GaussianEulerUnitKernelLatticeSum.body (sampleBody evaluatorF) C
    (GaussianEulerUnitKernelLatticeSum.data p z B a M) (sampleData q C a C M (fixedData z B))
    (unit p+unit q) (unit p*unit q) hD (original_terms p q z R B a C M G h hC)
  have wb : Γ ⊢[PRAAx] bounded w one M := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point one M hM).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded one M hM)
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul w u) (qmul w v) (numerator p q C) (denominator p q M) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm
      (by unfold numerator; ipra_ring) (by unfold denominator; ipra_ring)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hM hD wb rows)
  have weight := GaussianEulerIntegrandTimeProperness.fraction_proper one M C (M*C) hM (positive_product _ _ hM hC) (by ipra_ring)
  have right : Γ ⊢[PRAAx] qmul w v ≐ quadrature evaluatorF q C a C M (fixedData z B) :=
    GaussianRationalSyntheticDivision.qmul_congr weight (.eqRefl _)
  exact distance_congr (.eqRefl _) right (.eqRefl _) (.eqRefl _) scaled

theorem empty_comparison (p q z B a C M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hC : Γ ⊢[PRAAx] C ≐ zero) : Γ ⊢[PRAAx]
    distanceBounded (lattice p C z B a M) (quadrature evaluatorF q C a C M (fixedData z B))
      (numerator p q C) (denominator p q M) := by
  have left : Γ ⊢[PRAAx] lattice p C z B a M ≐ qzero :=
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      ((GaussianRationalFiniteSum.sum_index_congr GaussianEulerUnitKernelLatticeSum.body hC (.eqRefl _)).eqTrans
        (GaussianRationalFiniteSum.sum_zero _ _))).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
  have right := (GaussianCompactRiemannName.quadrature_index_congr evaluatorF q C zero a C M (fixedData z B) hC).eqTrans
    (GaussianCompactUniformGridComparison.empty_quadrature evaluatorF q a C M (fixedData z B))
  have zeroN : Γ ⊢[PRAAx] zero ≐ numerator p q C := ((congrMul hC (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  exact distance_congr left.eqSymm right.eqSymm zeroN (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qzero (denominator p q M)
      (positive_product _ _ (positive_product _ _ hM (unit_positive p)) (unit_positive q)))

/-- Arbitrary independent observations and the actual count-zero case. -/
theorem original_comparison (p q z R B a C M G : PTm n) (h : Γ ⊢[PRAAx] source z R B a C M G) : Γ ⊢[PRAAx]
    distanceBounded (lattice p C z B a M) (quadrature evaluatorF q C a C M (fixedData z B))
      (numerator p q C) (denominator p q M) := by
  refine .orE (zero_or_succ C) ?_ ?_
  · exact empty_comparison _ _ _ _ _ _ _ h.andE₂.andE₁.wk Prf.hyp0
  · exact positive_comparison _ _ _ _ _ _ _ _ _ h.wk (Order.zero_lt_of_eq_succ Prf.hyp0)

theorem actual_original_unit_lattice_quadrature_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (lattice (var 0) (var 6) (var 2) (var 4) (var 5) (var 7))
        (quadrature evaluatorF (var 1) (var 6) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4)))
        (numerator (var 0) (var 1) (var 6)) (denominator (var 0) (var 1) (var 7))) :=
  closeUniv 9 (.impI (original_comparison _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelLatticeComparison

import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetWeightedExponentialUniform
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImageWeights
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant
import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScaleRepresentation
import IPRADerivations.Analysis.Polynomials.Products.LinearFactors.GaussianPolynomialLinearFactorCoefficients

/-!
# Uniform finite midpoint readback of the weighted Binet quadrature

The midpoint tags use the same original weighted decay observations.
Their separation from the original left tags is exactly half a panel,
giving a uniform comparison even at zero decay.
-/

set_option autoImplicit false
set_option maxHeartbeats 680000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialMidpoint

open_ipra
open GaussianBinetWeightedExponentialGrid (evaluatorF rowValue primitiveData subst_primitiveData cell_at)
open GaussianBinetWeightedExponentialRowRate (gain row_error numerator subst_numerator)
open GaussianBinetWeightedExponentialUniform (readBudget finite_readback)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianNamedInverseRate (rateDenominator subst_rateDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def midpointRow (p a b i M : PTm n) : PTm n :=
  rowValue p a b (succ (two*i)) (two*M)
def midpointBody : PTm 2 := midpointRow (fstT (var 1)) (fstT (fstT (sndT (var 1))))
  (sndT (fstT (sndT (var 1)))) (var 0) (sndT (sndT (var 1)))
def midpointValue (p M a b : PTm n) : PTm n :=
  leftSum midpointBody M (primitiveData p a b M) one one
def midpointBudget (p M T : PTm n) : PTm n := two*gain T*unit p+(gain T+num 12)*M

private theorem subst_midpointRow {m : ℕ} (σ : Fin n → PTm m) (p a b i M : PTm n) :
    Syn.subst σ (midpointRow p a b i M) = midpointRow (Syn.subst σ p) (Syn.subst σ a)
      (Syn.subst σ b) (Syn.subst σ i) (Syn.subst σ M) := by simp [midpointRow,two]

theorem midpoint_at (i p M a b : PTm n) :
    Γ ⊢[PRAAx] inst2 midpointBody i (primitiveData p a b M) ≐
      rowValue p a b (succ (two*i)) (two*M) := by
  let x := primitiveData p a b M
  have hi : Γ ⊢[PRAAx] sndT x ≐ pairT (pairT a b) M := snd_pair _ _
  have hr := (congrFst hi).eqTrans (fst_pair (pairT a b) M)
  have proof := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (midpointRow (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT x,fstT (fstT (sndT x)),sndT (fstT (sndT x)),i,sndT (sndT x)]) (σ' := ![p,a,b,i,M])
    (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (congrFst hr).eqTrans (fst_pair _ _)
      · exact (congrSnd hr).eqTrans (snd_pair _ _)
      · exact .eqRefl _
      · exact (congrSnd hi).eqTrans (snd_pair _ _))
  change Γ ⊢[PRAAx] inst2 midpointBody i x ≐ midpointRow p a b i M
  simpa only [midpointBody,inst2,subst_midpointRow,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.head_cons,Matrix.tail_cons,x] using proof

theorem midpoint_tag_distance (i M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (fraction (succ (two*i)) (two*M)) (fraction i M) one (two*M) := by
  have ht := le_succ_self (Γ := Γ) one
  have hd := positive_product _ _ ht hM
  have r : Γ ⊢[PRAAx] fraction (two*i) (two*M) ≐ fraction i M :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hd).eqTrans
      ((GaussianPiRationalScaleRepresentation.point_rescale false i M two hM ht).eqTrans
        (GaussianEulerDecayFactorBounds.fraction_is_radius_point i M hM).eqSymm)
  have e := (GaussianEulerPositivePowerChartImageWeights.fraction_difference (two*i) (succ (two*i)) (two*M) hd
      (le_succ_self _)).eqTrans
    (GaussianCompactRiemannName.fraction_congr _ _ _ _
      (GaussianPolynomialLinearFactorCoefficients.successor_difference (two*i)) (.eqRefl _))
  have bound := GaussianRationalReciprocal.bound_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point one (two*M) hd).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one (two*M) hd)
  exact GaussianRationalReciprocal.bound_congr
    ((GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) r.eqSymm).eqTrans e).eqSymm
    (.eqRefl _) (.eqRefl _) bound

theorem midpoint_left_error (p M a b T : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded (midpointValue p M a b) (GaussianBinetWeightedExponentialGrid.value p M a b)
      (gain T*unit p+num 4*M) (M*unit p) := by
  let f := sampleBody evaluatorF
  let x := primitiveData p a b M
  let y := sampleData p M one one one (pairT a b)
  let A := numerator p p T one (two*M)
  let D := rateDenominator (two*M) p p
  have hD := GaussianNamedInverseRate.denominator_positive (two*M) p p
    (positive_product _ _ (le_succ_self one) hM)
  have rows : Γ ⊢[PRAAx] termsDistance midpointBody f M x y A D := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    have hm : Δ ⊢[PRAAx] le one (s M) := (Order.shift_one_le hM).wk
    have hB : Δ ⊢[PRAAx] le one (s b) := (Order.shift_one_le hb).wk
    have hT : Δ ⊢[PRAAx] le (s a) (s T*s b) := by simpa [s,Δ,Fm.shift,Syn.shift] using ht.shift.wk
    have hi : Δ ⊢[PRAAx] lt (var 0) (s M) := Prf.hyp0
    have hm2 : Δ ⊢[PRAAx] le one (two*s M) := positive_product _ _ (le_succ_self one) hm
    have top : Δ ⊢[PRAAx] le (succ (two*var 0)) (two*s M) :=
      le_trans (le_succ_self _) (by
        have cap := mul_le_mul_right two hi
        exact le_congr (by ipra_ring) (by ipra_ring) cap)
    have d := row_error (s p) (s p) (s a) (s b) (succ (two*var 0)) (two*s M) (var 0) (s M)
      (s T) one (two*s M) hB hT hm2 top hm (le_of_lt hi) hm2 (midpoint_tag_distance (var 0) (s M) hm)
    simpa only [s,Δ,f,x,y,A,D,Syn.shift,subst_primitiveData,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      subst_numerator,subst_rateDenominator,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] using distance_congr (midpoint_at _ _ _ _ _).eqSymm
        (cell_at _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) d
  have raw := GaussianCompactScalarMajorant.common_mesh_distance midpointBody f M x y one one A D
    hM (le_refl one) hD rows
  have d := distance_congr (.eqRefl _) (.eqRefl _) (one_mul A) (one_mul D) raw
  apply distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ hM (unit_positive p)) ?_ d
  apply le_of_eq_add (d := gain T*M*unit p*unit p*unit p)
  dsimp only [A,D,numerator,rateDenominator]
  ipra_ring

theorem finite_readback_midpoint (p M a b T : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetWeightedExponential.nameF p (GaussianBinetWeightedExponential.data a b))
      (midpointValue p M a b) (midpointBudget p M T) (M*unit p) := by
  have hd := positive_product _ _ hM (unit_positive p)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [readBudget,midpointBudget]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (finite_readback p M a b T hM hb ht)
      (distance_symmetric _ _ _ _ hd (midpoint_left_error p M a b T hM hb ht)))

theorem actual_weighted_Binet_midpoint_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ le (var 2) (var 4*var 3) ⟶
      distanceBounded
        (ap2 GaussianBinetWeightedExponential.nameF (var 0) (GaussianBinetWeightedExponential.data (var 2) (var 3)))
        (midpointValue (var 0) (var 1) (var 2) (var 3))
        (midpointBudget (var 0) (var 1) (var 4)) (var 1*unit (var 0))) :=
  closeUniv 5 (.impI (.impI (.impI (finite_readback_midpoint _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialMidpoint

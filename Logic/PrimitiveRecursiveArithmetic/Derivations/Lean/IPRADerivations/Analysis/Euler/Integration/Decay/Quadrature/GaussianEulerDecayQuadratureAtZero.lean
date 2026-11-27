import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadraturePrecision
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadrature
import IPRADerivations.Analysis.Gamma.Ratios.Wendel.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPrimitiveEvaluationPascal

/-!
# The original decay quadrature with a zero left endpoint

The original decay sample at zero is exactly one. The zero cell uses
the existing local exponential Taylor remainder, and the positive
cells retain their original increment bound. The same finite telescope
therefore applies on the original grid starting at zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadratureAtZero

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianEulerDecayAddition (original_decay_linear_remainder)
open GaussianEulerDecayMesh (observation observation_numerator_congr adjacent_step
  consecutiveDifference stepError errorDen)
open GaussianEulerDecayQuadrature (evaluatorF cell_distance_of_adjacent quadrature_of_adjacent)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalFiniteSum (multiplyBody)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem zero_observation (b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] observation zero b p ≐ qone := by
  let x := decayPoint zero b
  let S := GaussianNameBounds.U constantF x
  have atZero : Γ ⊢[PRAAx] x ≐ qzero :=
    (GaussianInverseBinomialRows.negative_congr (GaussianGammaRationalWendelBoundary.fraction_zero b hb)).eqTrans
      GaussianEulerBetaPrimitiveEvaluationPascal.negative_zero
  have read := GaussianRadiusExponentialName.sample_at (Γ := Γ) constantF S p x
  exact read.eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl _) ((constant_at _ x).eqTrans atZero)).eqTrans
        (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem adjacent_at_zero (b c p : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] distanceBounded (qmul (observation zero b p) (fraction c b))
      (qsub (observation zero b p) (observation c b p)) (stepError b c p) (errorDen b p) := by
  let w := fraction c b
  let y := observation c b p
  let z := observation zero b p
  let v := qsub qone w
  let U := unit p
  let B := b*b
  let Z := errorDen b p
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hb hb
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ hB (unit_positive p)
  have wz := zero_observation b p hb
  have canonical : Γ ⊢[PRAAx] GaussianRationalHorner.canonical w := GaussianRationalHorner.ofGaussian_canonical _ _ hb
  have e : Γ ⊢[PRAAx] qsub qone v ≐ w :=
    (qsub_congr (GaussianRationalLinearProduct.add_sub_right w qone qone_canonical).eqSymm (.eqRefl v)).eqTrans
      (GaussianReciprocalHorner.qsub_add_cancel w v canonical)
  have l : Γ ⊢[PRAAx] qmul z w ≐ w :=
    (qmul_congr wz (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone w).eqTrans
        (GaussianReciprocalHorner.qmul_one_right w canonical))
  have first : Γ ⊢[PRAAx] distanceBounded y v (c*c*U+two*B) Z :=
    original_decay_linear_remainder c b p hb hc
  have both := GaussianNamedDifference.difference_distance qone qone v y zero _ Z hZ
    (GaussianRationalPowerDifference.distance_refl_zero qone Z hZ)
    (distance_symmetric y v _ Z hZ first)
  have narrow : Γ ⊢[PRAAx] distanceBounded (qmul z w) (qsub z y) (c*c*U+two*B) Z :=
    distance_congr (e.eqTrans l.eqSymm) (qsub_congr wz.eqSymm (.eqRefl y))
      (by ipra_ring) (.eqRefl _) both
  apply distance_radius_mono _ _ _ _ _ _ hZ hZ ?_ narrow
  refine le_of_eq_add (d := (two*c*c*U+num 18*B)*Z) ?_
  dsimp only [stepError,GaussianNameRingLaws.three,B,U]
  ipra_ring

private theorem adjacent (a b c p : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hcb : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] distanceBounded (qmul (observation a b p) (fraction c b))
      (qsub (observation a b p) (observation (a+c) b p)) (stepError b c p) (errorDen b p) := by
  refine .orE (zero_or_succ a) ?_ ?_
  · let Δ := (a ≐ zero)::Γ
    have s : Δ ⊢[PRAAx] a+c ≐ c :=
      (congrAdd Prf.hyp0 (.eqRefl c)).eqTrans (by ipra_ring)
    have first := observation_numerator_congr (Γ := Δ) a zero b p Prf.hyp0
    have second := observation_numerator_congr (Γ := Δ) (a+c) c b p s
    exact distance_congr (qmul_congr first.eqSymm (.eqRefl _))
      (qsub_congr first.eqSymm second.eqSymm) (.eqRefl _) (.eqRefl _)
      (adjacent_at_zero b c p hb.wk hcb.wk)
  · have ha : (a ≐ succ (pred a))::Γ ⊢[PRAAx] le one a :=
      Order.zero_lt_of_eq_succ Prf.hyp0
    exact adjacent_step a b c p ha hb.wk hc.wk hcb.wk

theorem cell_distance (i p N a C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (multiplyBody (sampleBody evaluatorF)) i (pairT (weight C E N) (sampleData p N a C E x)))
      (inst2 (consecutiveDifference (sampleBody evaluatorF)) i (sampleData p N a C E x))
      (stepError (E*N) C p) (errorDen (E*N) p) :=
  cell_distance_of_adjacent i p N a C E x (adjacent (a*N+C*i) (E*N) C p (positive_product E N hE hN) hC hstep)

theorem actual_decay_quadrature (p N a C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p N a C E x)
      (endpointDifference a C E p) (N*stepError (E*N) C p) (errorDen (E*N) p) := by
  apply quadrature_of_adjacent p N a C E x hN hE
  have den := positive_product _ _ (Order.shift_one_le hE) (Order.shift_one_le hN)
  have step : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift C) (Syn.shift E*Syn.shift N) :=
    by simpa [Fm.shift,Syn.shift] using hstep.shift
  exact adjacent _ _ _ _ den.wk (Order.shift_one_le hC).wk step.wk

theorem actual_decay_quadrature_including_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ le one (var 4)) ⟶ le one (var 3) ⟶ le (var 3) (var 4*var 1) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (endpointDifference (var 2) (var 3) (var 4) (var 0))
        (var 1*stepError (var 4*var 1) (var 3) (var 0)) (errorDen (var 4*var 1) (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (actual_decay_quadrature _ _ _ _ _ _
    Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadratureAtZero

import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayQuadraturePrecision
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Beta.GaussianEulerBetaPrimitiveEvaluationPascal

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature sampleBody sampleData)
open GaussianEulerDecayAddition (original_decay_linear_remainder)
open GaussianEulerDecayMesh (observation observation_numerator_congr adjacent_step
  consecutiveDifference consecutive_difference_at consecutive_difference_sum stepError errorDen)
open GaussianEulerDecayQuadrature (evaluatorF cell_at endpoint_left_at endpoint_right_at)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalRiemannRefinement (weight termsDistance sum_distance)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qsub_congr)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)
open Syn
open scoped Fm

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
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact adjacent_step a b c p ha hb.wk hc.wk hcb.wk

theorem cell_distance (i p N a C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (multiplyBody (sampleBody evaluatorF)) i (pairT (weight C E N) (sampleData p N a C E x)))
      (inst2 (consecutiveDifference (sampleBody evaluatorF)) i (sampleData p N a C E x))
      (stepError (E*N) C p) (errorDen (E*N) p) := by
  let f := sampleBody evaluatorF
  let d := sampleData p N a C E x
  let X := observation (a*N+C*i) (E*N) p
  let Y := observation (a*N+C*i+C) (E*N) p
  let w := weight C E N
  have first : Γ ⊢[PRAAx] inst2 (multiplyBody f) i (pairT w d) ≐ qmul X w :=
    (multiply_body_at f w i d).eqTrans ((qmul_congr (.eqRefl _) (cell_at i p N a C E x)).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative w X))
  have next : Γ ⊢[PRAAx] inst2 f (succ i) d ≐ Y :=
    (cell_at (succ i) p N a C E x).eqTrans (observation_numerator_congr _ _ _ _ (by ipra_ring))
  have second : Γ ⊢[PRAAx] inst2 (consecutiveDifference f) i d ≐ qsub X Y := by
    rw [consecutive_difference_at]
    exact qsub_congr (cell_at i p N a C E x) next
  exact distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _)
    (adjacent (a*N+C*i) (E*N) C p (positive_product E N hE hN) hC hstep)

theorem actual_decay_quadrature (p N a C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p N a C E x)
      (endpointDifference a C E p) (N*stepError (E*N) C p) (errorDen (E*N) p) := by
  let f := sampleBody evaluatorF
  let w := weight C E N
  let d := sampleData p N a C E x
  let A := stepError (E*N) C p
  let D := errorDen (E*N) p
  have hb := positive_product E N hE hN
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hb hb) (unit_positive p)
  have entries : Γ ⊢[PRAAx] termsDistance (multiplyBody f) (consecutiveDifference f) N (pairT w d) d A D := by
    have hn' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have he' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
    have hc' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift C) := by simpa [Fm.shift,Syn.shift] using hC.shift
    have hs' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift C) (Syn.shift E*Syn.shift N) :=
      by simpa [Fm.shift,Syn.shift] using hstep.shift
    refine .allI (.impI ?_)
    simpa [termsDistance,A,D,w,d,f,Syn.shift,stepError,errorDen,GaussianNameRingLaws.three] using
      cell_distance (var 0) (Syn.shift p) (Syn.shift N) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x)
        hn'.wk he'.wk hc'.wk hs'.wk
  have endpoints := (consecutive_difference_sum f d N).eqTrans
    (qsub_congr (endpoint_left_at p N a C E x hE hN) (endpoint_right_at p N a C E x hE hN))
  exact distance_congr (sum_multiply f w N d) endpoints (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ hD entries)

theorem actual_decay_quadrature_including_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ le one (var 4)) ⟶ le one (var 3) ⟶ le (var 3) (var 4*var 1) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (endpointDifference (var 2) (var 3) (var 4) (var 0))
        (var 1*stepError (var 4*var 1) (var 3) (var 0)) (errorDen (var 4*var 1) (var 0))) :=
  closeUniv 6 (.impI (.impI (.impI (actual_decay_quadrature _ _ _ _ _ _
    Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadratureAtZero

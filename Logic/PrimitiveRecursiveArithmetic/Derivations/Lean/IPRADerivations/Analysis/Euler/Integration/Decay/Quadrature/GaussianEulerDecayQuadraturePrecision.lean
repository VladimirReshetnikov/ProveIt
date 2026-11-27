import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadrature
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.SlackRemoval.GaussianRationalSlackRemoval
import IPRADerivations.Analysis.Polynomials.RootFinding.Characteristic.GaussianCharacteristicEntryNorm

/-!
# Independent precision for the compact decay endpoint estimate

Re-evaluating the same finite grid costs its length times the point
observation error. The finite telescope can therefore be evaluated at
an auxiliary precision and its accumulated dyadic slack removed by an
explicit integer-gap query. The remaining error is the mesh term plus
the original grid and endpoint observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadraturePrecision

open_ipra
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianEulerDecayMesh (observation stepError errorDen)
open GaussianEulerDecayQuadrature (evaluatorF cell_at actual_decay_quadrature)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (point_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCompactRiemannName (sampleBody sampleData quadrature)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalRiemannRefinement (sum_distance termsDistance weight weight_bound)
open GaussianRationalReciprocal (bounded_product bound_congr bounded_negative)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameRingLaws (three)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem observation_regular (a E : PTm n) : Γ ⊢[PRAAx] pointCN decayF (decayData a E) :=
  GaussianRadiusExponentialName.name_regular constantF _ _ (GaussianGammaFiniteApproximantName.exponential_input
    constantF (decayPoint a E) (constant_regular _))

theorem cell_precision (i p q N a C E x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (inst2 (sampleBody evaluatorF) i (sampleData p N a C E x))
      (inst2 (sampleBody evaluatorF) i (sampleData q N a C E x)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (cell_at i p N a C E x).eqSymm (cell_at i q N a C E x).eqSymm (.eqRefl _) (.eqRefl _)
    (point_at decayF (decayData (a*N+C*i) (E*N)) p q (observation_regular _ _))

theorem same_mesh_precision (p q N a C E x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF p N a C E x) (quadrature evaluatorF q N a C E x)
      (C*(unit p+unit q)) (E*(unit p*unit q)) := by
  let f := sampleBody evaluatorF
  let X := sampleData p N a C E x
  let Y := sampleData q N a C E x
  let V := unit p*unit q
  let B := E*N
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (unit_positive p) (unit_positive q)
  have hB : Γ ⊢[PRAAx] le one B := positive_product E N hE hN
  have entries : Γ ⊢[PRAAx] termsDistance f f N X Y (unit p+unit q) V := by
    refine .allI (.impI ?_)
    simpa [termsDistance,X,Y,V,f,Syn.shift] using
      (cell_precision (Γ := _ :: Γ.map Fm.shift) (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift N)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift x))
  have near := sum_distance f f N X Y (unit p+unit q) V hV entries
  have scaled := GaussianRationalRoundedPower.distance_mul_left hB hV
    (weight_bound C E N hE hN) near
  refine distance_radius_mono _ _ (C*(N*(unit p+unit q))) (B*V) _ _
    (positive_product _ _ hB hV) (positive_product _ _ hE hV) ?_ scaled
  exact le_of_eq_add (d := zero) (by dsimp [B,V]; ipra_ring)

def endpointDifference (a C E p : PTm n) : PTm n := qsub (observation a E p) (observation (a+C) E p)

theorem endpoint_precision (a C E p q : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (endpointDifference a C E p) (endpointDifference a C E q)
      (two*(unit p+unit q)) (unit p*unit q) := by
  let Y := observation (a+C) E p
  let Z := observation (a+C) E q
  have h := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive q)
  have left := point_at decayF (decayData a E) p q (observation_regular (Γ := Γ) a E)
  have right := point_at decayF (decayData (a+C) E) p q (observation_regular (Γ := Γ) (a+C) E)
  have neg := bound_congr (GaussianCharacteristicEntryNorm.negative_difference Y Z).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative (qsub Y Z) _ _ h right)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ h left neg)

def numerator (p q N C E : PTm n) : PTm n :=
  three*C*C*unit p*unit q+C*E*N*unit q+two*E*E*N*unit p
def denominator (p q N E : PTm n) : PTm n := E*E*N*unit p*unit q
def accumulatedSlack (N C : PTm n) : PTm n := C+num 20*N+two

private theorem denominator_positive (p q N E : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] le one (denominator p q N E) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product E E hE hE) hN) (unit_positive p)) (unit_positive q)

theorem auxiliary_precision (p q s N a C E x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (qsub (quadrature evaluatorF p N a C E x) (endpointDifference a C E q))
      (numerator p q N C E) (denominator p q N E) (accumulatedSlack N C) s := by
  let D := denominator p q N E*unit s
  let A := C*(unit p+unit s)*E*N*unit q
  let M := (three*C*C*unit s+num 20*(E*N)*(E*N))*unit p*unit q
  let Z := two*(unit s+unit q)*E*E*N*unit p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (denominator_positive p q N E hN hE) (unit_positive s)
  have U := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive s)
  have B := positive_product (Γ := Γ) E N hE hN
  have V := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive q)
  have first := distance_radius_mono _ _ _ _ A D (positive_product _ _ hE U) hD
    (le_of_eq_add (d := zero) (by dsimp [A,D,denominator]; ipra_ring))
    (same_mesh_precision p s N a C E x hN hE)
  have second := distance_radius_mono _ _ _ _ M D (positive_product _ _ (positive_product _ _ B B) (unit_positive s)) hD
    (le_of_eq_add (d := zero) (by dsimp [M,D,denominator,stepError,errorDen]; ipra_ring))
    (actual_decay_quadrature s N a C E x ha hN hE hC hstep)
  have third := distance_radius_mono _ _ _ _ Z D V hD
    (le_of_eq_add (d := zero) (by dsimp [Z,D,denominator]; ipra_ring))
    (endpoint_precision a C E s q)
  have combined := distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD first second) third
  change Γ ⊢[PRAAx] distanceBounded _ _ (numerator p q N C E*unit s+accumulatedSlack N C*denominator p q N E) D
  refine distance_radius_mono _ _ (A+M+Z) D _ D hD hD ?_ combined
  dsimp [A,M,Z,D,numerator,denominator,accumulatedSlack]
  ipra_le (𝔞(C)*𝔞(E)*𝔞(N)*𝔞(unit p)*𝔞(unit q)*𝔞(E*E*N*unit p*unit q*unit s))*sl hE

theorem independent_quadrature_endpoint (p q N a C E x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hC : Γ ⊢[PRAAx] le one C) (hstep : Γ ⊢[PRAAx] le C (E*N)) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p N a C E x) (endpointDifference a C E q)
      (numerator p q N C E) (denominator p q N E) := by
  apply GaussianRationalSlackRemoval.slack_removal_at _ _ _ (accumulatedSlack N C)
    (denominator_positive p q N E hN hE)
  exact auxiliary_precision p q _ N a C E x ha hN hE hC hstep

theorem original_decay_quadrature_independent_endpoint_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((le one (var 3) ⋏ le one (var 2)) ⟶ (le one (var 5) ⋏ le one (var 4)) ⟶
        le (var 4) (var 5*var 2) ⟶ distanceBounded
          (quadrature evaluatorF (var 0) (var 2) (var 3) (var 4) (var 5) (var 6))
          (endpointDifference (var 3) (var 4) (var 5) (var 1))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 5)) (denominator (var 0) (var 1) (var 2) (var 5))) :=
  closeUniv 7 (.impI (.impI (.impI (independent_quadrature_endpoint _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayQuadraturePrecision

import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingFiniteSubstitution

/-!
# Separate mesh and observation errors for finite Gamma power substitution

Cancel the repeated mesh factors in the accumulated original bound.
The resulting fraction keeps the first-order mesh error separate from
the source and chart observation errors, and uses a common denominator
for the corrected image displacement.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFiniteBudget

open_ipra
open GaussianEulerPowerScalingFiniteSubstitution (source)
open GaussianEulerPowerScalingCell (scaleBound scaleSample eulerBound)
open GaussianEulerPowerScalingFrozenIntegrand (factorBound)
open GaussianEulerPowerChartFrozenKernel (cost)
open GaussianEulerPositivePowerChartImage (query)
open GaussianEulerPositivePowerChartJacobian (curvature)
open GaussianEulerPositivePowerChart (lipschitz)
open GaussianEulerPowerScalingCorrectedQuadrature (gain correctedSum)
open GaussianEulerPowerScalingCompactName (evaluatorF fixedData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCompactRiemannName (quadrature)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def numerator (E N P K U Q C A M J V H G : PTm n) : PTm n :=
  Q*C*(A*P+two*K)*N*(U*U)+
    M*J*(V*E*(U*U)*P*K+num 8*E*(N*N)*U*P*K)+
    (H*C*U+num 4*E*N)*(two*J+M*two)*N*U*K+
    M*(H*C*U+num 4*E*N)*(G*P+two*U)*N*K
def denominator (E N P K U : PTm n) : PTm n := E*N*(U*U)*P*K

def meshCost (M J V : PTm n) : PTm n := M*J*V
def chartCost (N Q C A M J H G : PTm n) : PTm n :=
  Q*C*A+num 8*M*J*N+M*(H*C+two)*G
def observationCost (Q C M J H : PTm n) : PTm n := Q*C*two+(H*C+two)*(two*J+M*(two+two))
def separatedNumerator (N P K Q C A M J V H G : PTm n) : PTm n :=
  meshCost M J V*P*K+N*chartCost N Q C A M J H G*P+N*observationCost Q C M J H*K
def separatedDenominator (N P K : PTm n) : PTm n := N*P*K

theorem bound_separated_numerator (E N P K U Q C A M J V H G : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le (two*N) U) (hk : Γ ⊢[PRAAx] le K U) :
    Γ ⊢[PRAAx] le (numerator E N P K U Q C A M J V H G)
      ((E*(U*U))*separatedNumerator N P K Q C A M J V H G) := by
  have span : Γ ⊢[PRAAx] le (H*C*U+num 4*E*N) ((H*C+two)*E*U) := by
    ipra_le 𝔞(H*C*U)*sl hE+𝔞(two*E)*sl hN
  unfold numerator separatedNumerator meshCost chartCost observationCost
  ipra_le 𝔞(Q*C*(A*P+two*K)*N*(U*U))*sl hE+
    𝔞(num 8*E*M*J*(N*N)*U*P)*sl hk+
    (𝔞((two*J+M*two)*N*U*K)+𝔞(M*(G*P+two*U)*N*K))*sl span+
    𝔞(M*(H*C+two)*E*U*G*P*N)*sl hk

theorem denominator_positive (E N P K U : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hP : Γ ⊢[PRAAx] le one P) (hK : Γ ⊢[PRAAx] le one K) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] le one (denominator E N P K U) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hE hN)
    (positive_product _ _ hU hU)) hP) hK

theorem native_budget_identity (p k z R B e f d h L Q S E T C N : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerPowerScalingFiniteSubstitution.numerator p k z R B e f d h L Q S E T C N*
      denominator E N (unit p) (unit k) (unit (query k h Q E T)) ≐
    numerator E N (unit p) (unit k) (unit (query k h Q E T)) Q C
      (factorBound z B e f d h E*cost (L*R) h Q S E T) (scaleBound z B e f d h)
      (eulerBound (L*R) h Q S E T) (curvature Q S E T C) (lipschitz Q S E T) (gain (L*R) h Q S E T N)*
        GaussianEulerPowerScalingFiniteSubstitution.denominator p k h Q E T N := by
  unfold GaussianEulerPowerScalingFiniteSubstitution.numerator GaussianEulerPowerScalingFiniteSubstitution.denominator
    GaussianEulerPowerScalingCell.numerator GaussianEulerPowerScalingCell.denominator
    GaussianEulerPowerScalingCell.frozenNumerator GaussianEulerPowerScalingCell.frozenDenominator
    GaussianEulerPowerScalingCell.jacobianNumerator GaussianEulerPowerScalingCell.jacobianDenominator
    GaussianEulerPowerScalingCell.clockNumerator GaussianEulerPowerScalingCell.clockDenominator
    GaussianEulerPowerScalingCorrectedQuadrature.numerator GaussianEulerPowerScalingCorrectedQuadrature.denominator
    GaussianEulerPositivePowerChartMeshJacobian.numerator GaussianEulerPositivePowerChartMeshJacobian.denominator
    GaussianEulerPositivePowerChartMesh.widthNumerator GaussianEulerPositivePowerChartMesh.cellDenominator
    GaussianEulerPositivePowerChartMesh.timeDenominator numerator denominator
  ipra_ring

theorem original_finite_budget (p k z R B A e f d h L Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B A e f d h L Q S E T a C N) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (fraction e f) (quadrature evaluatorF p N a C E (fixedData z B e f d h S)))
      (qmul (scaleSample p z B e f d h) (correctedSum p k z B e f d h Q S E T a C N))
      (numerator E N (unit p) (unit k) (unit (query k h Q E T)) Q C
        (factorBound z B e f d h E*cost (L*R) h Q S E T) (scaleBound z B e f d h)
        (eulerBound (L*R) h Q S E T) (curvature Q S E T C) (lipschitz Q S E T) (gain (L*R) h Q S E T N))
      (denominator E N (unit p) (unit k) (unit (query k h Q E T))) := by
  have hm := hs.andE₂.andE₁.andE₁
  have hE := hm.andE₂.andE₁
  have hN := hm.andE₂.andE₂.andE₂.andE₂
  have hU := unit_positive (Γ := Γ) (query k h Q E T)
  have hWide : Γ ⊢[PRAAx] le one (GaussianEulerPowerScalingFiniteSubstitution.denominator p k h Q E T N) := positive_product _ _
    (GaussianEulerPowerScalingCell.denominator_positive p k h Q E T N hE hN)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hE hN) hU) (positive_product _ _ hU (unit_positive p)))
  have hNew := denominator_positive E N (unit p) (unit k) _ hE hN (unit_positive p) (unit_positive k) hU
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hWide hNew
    (le_of_eq_add (d := zero) ((native_budget_identity p k z R B e f d h L Q S E T C N).eqSymm.eqTrans (by ipra_ring)))
    (GaussianEulerPowerScalingFiniteSubstitution.original_finite_substitution p k z R B A e f d h L Q S E T a C N hs)

theorem original_separated_budget (p k z R B A e f d h L Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B A e f d h L Q S E T a C N) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (fraction e f) (quadrature evaluatorF p N a C E (fixedData z B e f d h S)))
      (qmul (scaleSample p z B e f d h) (correctedSum p k z B e f d h Q S E T a C N))
      (separatedNumerator N (unit p) (unit k) Q C
        (factorBound z B e f d h E*cost (L*R) h Q S E T) (scaleBound z B e f d h)
        (eulerBound (L*R) h Q S E T) (curvature Q S E T C) (lipschitz Q S E T) (gain (L*R) h Q S E T N))
      (separatedDenominator N (unit p) (unit k)) := by
  let U := unit (query k h Q E T)
  let P := unit p
  let K := unit k
  let A₀ := factorBound z B e f d h E*cost (L*R) h Q S E T
  let M := scaleBound z B e f d h
  let J := eulerBound (L*R) h Q S E T
  let V := curvature Q S E T C
  let H := lipschitz Q S E T
  let G := gain (L*R) h Q S E T N
  let D := separatedDenominator N P K
  let N' := separatedNumerator N P K Q C A₀ M J V H G
  have hm := hs.andE₂.andE₁.andE₁
  have hE := hm.andE₂.andE₁
  have hN := hm.andE₂.andE₂.andE₂.andE₂
  have hU : Γ ⊢[PRAAx] le one U := unit_positive _
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hN (unit_positive p)) (unit_positive k)
  have grow : Γ ⊢[PRAAx] le K U := GaussianExponentialReference.unit_monotone (GaussianEulerPositivePowerChartImage.query_later k h Q E T)
  have bound := bound_separated_numerator E N P K U Q C A₀ M J V H G hE hs.andE₂.andE₂ grow
  have compare : Γ ⊢[PRAAx] le (numerator E N P K U Q C A₀ M J V H G*D) (N'*denominator E N P K U) := by
    have lifted := mul_le_mul_right D bound
    exact le_congr (.eqRefl _) (by unfold D denominator separatedDenominator; ipra_ring) lifted
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (denominator_positive E N P K U hE hN (unit_positive p) (unit_positive k) hU) hd compare
    (original_finite_budget p k z R B A e f d h L Q S E T a C N hs)

theorem separated_radius_budget (N P K Q C A M J V H G U : PTm n)
    (hn : Γ ⊢[PRAAx] le (num 3*meshCost M J V*U) N)
    (hk : Γ ⊢[PRAAx] le (num 3*chartCost N Q C A M J H G*U) K)
    (hp : Γ ⊢[PRAAx] le (num 3*observationCost Q C M J H*U) P) :
    Γ ⊢[PRAAx] le (separatedNumerator N P K Q C A M J V H G*U) (separatedDenominator N P K) := by
  apply mul_le_cancel (d' := two)
  unfold separatedNumerator separatedDenominator
  ipra_le 𝔞(P*K)*sl hn+𝔞(N*P)*sl hk+𝔞(N*K)*sl hp

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFiniteBudget

import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCutoffGeometry
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingFactorExtraction
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingConstant
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCancellation
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedCompactName
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Actual compact Euler dilation and its extracted factor

A product refinement of the two original meshes is used for each
comparison precision. The finite maximum of the costs on this grid
is paid by a later evaluation query. The two outputs are still the
original compact names, with their own meshes and query schedules.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingCompact

open_ipra
open GaussianEulerPositiveScalingCutoffGeometry (source pullback_interval original_scaled_grid_comparison)
open GaussianEulerPositiveScalingConstant (scaleF scaleData)
open GaussianEulerPositiveScalingCancellation (scale_regular)
open GaussianEulerIntegrandName (powerF powerData power_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianCompactRiemannName (quadrature mesh precision mesh_positive quadrature_index_congr)
open GaussianCompactMeshIndependence (arbitrary_refinement)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianEulerExponentCompactBounds (scale_value_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "EulerF" => GaussianEulerCompactAdditivity.nameF
local notation "eulerData" => GaussianEulerCompactAdditivity.data
local notation "DampF" => GaussianEulerDampedCompactName.nameF
local notation "EF" => GaussianEulerIntegrandName.evaluatorF
local notation "DF" => GaussianEulerPositiveScalingIntegrand.evaluatorF
local notation "eData" => GaussianEulerIntegrandName.fixedData
local notation "dData" => GaussianEulerPositiveScalingIntegrand.fixedData
local notation "bound" => GaussianNameBounds.U

def dampedDatum (z R B a C E T c d : PTm n) : PTm n :=
  GaussianEulerDampedCompactName.data z R B c d (d*a) (d*C) (c*E) (d*T)
def productDatum (z R B a C E T c d : PTm n) : PTm n :=
  multiplyData scaleF DampF (scaleData z B c d) (dampedDatum z R B a C E T c d)
def factorBound (z B c d : PTm n) : PTm n := c*bound powerF (powerData z B c d)
def factorCost (z B c d : PTm n) : PTm n := multiplyModulus constantF powerF (fraction c d) (powerData z B c d)+one+two*c
def diagonalCost (z R B a C E T c d : PTm n) : PTm n :=
  num 6+num 3*factorBound z B c d+factorCost z B c d*bound DampF (dampedDatum z R B a C E T c d)+
    (multiplyModulus scaleF DampF (scaleData z B c d) (dampedDatum z R B a C E T c d)+one)

ipra_subst dampedDatum
ipra_subst productDatum [scaleData]
ipra_subst diagonalCost [factorBound, factorCost, scaleData]

private theorem factor_drift (s t z B c d : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B c d)
    (hl : Γ ⊢[PRAAx] le t s) : Γ ⊢[PRAAx]
    distanceBounded (qmul (fraction c d) (ap2 powerF s (powerData z B c d)))
      (ap2 scaleF t (scaleData z B c d)) (factorCost z B c d) (unit t) := by
  let a := fraction c d
  let x := powerData z B c d
  let P := unit t
  have hp := power_regular z B c d h
  have near := GaussianNameEquivalence.point_at_later powerF x t s hp hl
  have first := GaussianNamedDifferenceQuotient.scale_distance a _ _ c two P (unit_positive t)
    (scale_value_bound c d h.andE₂.andE₂) near
  have second := distance_congr (.eqRefl _)
    (GaussianRationalSyntheticDivision.qmul_congr (constant_at t a) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF powerF a x t (constant_regular a) hp)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold factorCost; dsimp only [a,x]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive t) first (distance_symmetric _ _ _ _ (unit_positive t) second))

theorem original_diagonal (t z R B a C E T c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T c d) :
    Γ ⊢[PRAAx] distanceBounded (ap2 EulerF t (eulerData z R B a C E T))
      (ap2 (multiplyF scaleF DampF) t (productDatum z R B a C E T c d)) (diagonalCost z R B a C E T c d) (unit t) := by
  let L := GaussianEulerCompactModulus.lipschitz R E T
  let b := d*a
  let W := d*C
  let F := c*E
  let S := d*T
  let Ld := GaussianEulerDampedTimeRate.lipschitz R F S c d
  let O := mesh t L T
  let V := mesh t Ld S
  let N := O*V
  let J := GaussianEulerPositiveScalingFactorExtraction.maximumCost N z B b W F c d
  let s := precision t T+precision t S+GaussianFastValueCut.exponent ((J+two)*T) t
  let U := unit t
  let H := unit s
  let x := eData z B
  let y := dData z B c d
  let r := dampedDatum z R B a C E T c d
  let v := scaleData z B c d
  let α := fraction c d
  let P := powerData z B c d
  let w := qmul α (ap2 powerF s P)
  have hc := hs.andE₂.andE₁
  have hd := hs.andE₂.andE₂
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hF := positive_product _ _ hc hE
  have hWidth : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left _ _) hs.andE₁.andE₂.andE₂
  have hO := mesh_positive (Γ := Γ) t L T
  have hV := mesh_positive (Γ := Γ) t Ld S
  have hN := positive_product _ _ hO hV
  have ps : Γ ⊢[PRAAx] le one U := unit_positive t
  have ph : Γ ⊢[PRAAx] le one H := unit_positive s
  have lateOld : Γ ⊢[PRAAx] le (precision t T) s := le_trans (le_add_right _ _) (le_add_right _ _)
  have lateDamp : Γ ⊢[PRAAx] le (precision t S) s := le_trans (le_add_left _ _) (le_add_right _ _)
  have grow : Γ ⊢[PRAAx] le t s := le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) lateOld
  have pays : Γ ⊢[PRAAx] le ((J+two)*T*U) H := le_trans
    (GaussianFastValueCut.query_budget _ _) (unit_monotone (le_add_left _ _))
  have elementary : Γ ⊢[PRAAx] le (T*U) H := le_trans
    (le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (T*U) (le_trans (le_succ_self one) (le_add_left two J)))) pays
  have primary : Γ ⊢[PRAAx] le (C*(J+two)*U) (((J+two)*T*U)*E) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right ((J+two)*U) hWidth)
  have relation : Γ ⊢[PRAAx] le (C*(J+two)*U) (E*H) :=
    le_trans primary (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right E pays))
  have ordinary := GaussianEulerCompactAdditivity.compact_input z R B a C E T hs.andE₁
  have dampSrc : Γ ⊢[PRAAx] GaussianEulerDampedCompactName.source z R B c d b W F S :=
    .andI (pullback_interval z R B a C E T c d hs) hs.andE₂
  have dampInput := GaussianEulerDampedCompactName.compact_input z R B c d b W F S dampSrc
  have scaleSrc : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B c d := .andI hs.andE₁.andE₁.andE₁ hs.andE₂
  have dq := GaussianEulerDampedCompactName.name_regular z R B c d b W F S dampSrc
  have sq := scale_regular z B c d scaleSrc
  have pq := power_regular z B c d scaleSrc
  have factorBounded : Γ ⊢[PRAAx] bounded w (factorBound z B c d) one := GaussianRationalReciprocal.bound_congr
    (.eqRefl _) (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ c (one : PTm n) (bound powerF P) one (le_refl _) (le_refl _)
      (scale_value_bound c d hd) (GaussianNameBounds.sample_bound powerF P s pq))
  have move : Γ ⊢[PRAAx] le U (unit (t+num 6)) := unit_monotone (le_add_right _ _)
  have payMove : Γ ⊢[PRAAx] le (num 3*U) (num 3*unit (t+num 6)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 3) move)
  have eFine := arbitrary_refinement EF t s V a C E L T x ordinary hV lateOld
  have eDen := unit_positive (Γ := Γ) (t+num 6)
  have eRaw := distance_congr (quadrature_index_congr EF s _ N a C E x (by unfold N; ipra_ring))
    (GaussianCompactRiemannName.name_at EF t a C E L T x).eqSymm (.eqRefl _) (.eqRefl _) eFine
  have first := distance_radius_mono _ _ _ _ (num 3) U eDen ps payMove
    (distance_symmetric _ _ _ _ eDen eRaw)
  have intervalPay : Γ ⊢[PRAAx] le ((C*two)*U) ((two*E)*(T*U)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*U) hWidth)
  have rescalePay : Γ ⊢[PRAAx] le ((two*E)*(T*U)) (two*(E*H)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*E) elementary)
  have second := distance_radius_mono _ _ _ _ two U (positive_product _ _ hE ph) ps
    (le_trans intervalPay rescalePay)
    (original_scaled_grid_comparison s N z R B a C E T c d hs hN)
  have extract := GaussianEulerPositiveScalingFactorExtraction.original_scaled_quadrature s s N z B b W F c d
    (.andI scaleSrc.andE₁ (.andI dampSrc.andE₁.andE₂.andE₁ (.andI hF (.andI hN hs.andE₂))))
  have third := distance_radius_mono _ _ _ _ one U
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hd hF) ph) ph) ps
    (by dsimp only [W,F,H,J,U]
        exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (c*d*H) relation))
    (distance_congr (.eqRefl _) (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm (.eqRefl _) (.eqRefl _) extract)
  have dFine := arbitrary_refinement DF t s O b W F Ld S y dampInput hO lateDamp
  have dRaw := distance_congr (.eqRefl _) (GaussianCompactRiemannName.name_at DF t b W F Ld S y).eqSymm
    (.eqRefl _) (.eqRefl _) dFine
  have dNear := distance_radius_mono _ _ _ _ (num 3) U eDen ps payMove dRaw
  have fourth := GaussianNamedDifferenceQuotient.scale_distance w _ _ (factorBound z B c d) (num 3) U ps factorBounded dNear
  have drift := factor_drift s t z B c d scaleSrc grow
  have dBound := GaussianNameBounds.sample_bound DampF r t dq
  have fifth := distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)
    (.eqRefl _) (.eqRefl _) (GaussianNamedDifferenceQuotient.scale_distance (ap2 DampF t r) _ _
      (bound DampF r) (factorCost z B c d) U ps dBound drift)
  have last := distance_symmetric _ _ _ _ ps (GaussianNameRingLaws.multiply_sample_error scaleF DampF v r t sq dq)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalCost; dsimp only [r,v]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ ps first (distance_triangle_same _ _ _ _ _ _ ps second
      (distance_triangle_same _ _ _ _ _ _ ps third (distance_triangle_same _ _ _ _ _ _ ps fourth
        (distance_triangle_same _ _ _ _ _ _ ps fifth last)))))

theorem original_compact_cross (z R B a C E T c d : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T c d) :
    Γ ⊢[PRAAx] crossEquivalent EulerF (multiplyF scaleF DampF) (eulerData z R B a C E T) (productDatum z R B a C E T c d) := by
  have scaleSrc : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B c d := .andI hs.andE₁.andE₁.andE₁ hs.andE₂
  have dampSrc : Γ ⊢[PRAAx] GaussianEulerDampedCompactName.source z R B c d (d*a) (d*C) (c*E) (d*T) :=
    .andI (pullback_interval z R B a C E T c d hs) hs.andE₂
  refine GaussianNameRingLaws.equivalent_of_envelope EulerF (multiplyF scaleF DampF) (eulerData z R B a C E T)
    (productDatum z R B a C E T c d) (diagonalCost z R B a C E T c d)
    (GaussianEulerCompactAdditivity.name_regular z R B a C E T hs.andE₁)
    (GaussianNameArithmetic.multiply_fast scaleF DampF (scaleData z B c d) (dampedDatum z R B a C E T c d)
      (scale_regular z B c d scaleSrc) (GaussianEulerDampedCompactName.name_regular z R B c d _ _ _ _ dampSrc)) ?_
  refine .allI ?_
  let sh (u : PTm n) := Syn.shift u
  have next : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) (sh c) (sh d) :=
    by simpa only [Fm.shift,GaussianEulerPositiveScalingCutoffGeometry.subst_source,Syn.shift,sh] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianEulerCompactAdditivity.subst_data,
    subst_productDatum,subst_diagonalCost,Syn.shift,sh] using
    original_diagonal (var 0) (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) (sh c) (sh d) next

theorem actual_Euler_compact_rational_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      crossEquivalent EulerF (multiplyF scaleF DampF) (eulerData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (productDatum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_compact_cross _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingCompact

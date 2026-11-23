import IPRADerivations.Analysis.GaussianEulerPowerScalingFrozenRow
import IPRADerivations.Analysis.GaussianEulerExponentCompactBounds

/-!
# Power substitution on one original affine cell

The physical cell of the original power-damped quadrature, multiplied
by e/f, is compared with the corrected image width times the original
rescaled Euler observation. The inverse scale factor and the Euler
observation use one common precision. The proof combines the frozen
row rate, the width--Jacobian remainder, and the two clock changes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartMesh (timeNumerator timeDenominator widthNumerator cellDenominator)
open GaussianEulerPositivePowerChartMeshJacobian (width linearTerm)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPowerChartFrozenKernel (parameter cost)
open GaussianEulerPowerScalingFrozenIntegrand (factorBound)
open GaussianEulerPowerScalingKernel (scaleExpF scaleExpData)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPowerScalingFrozenRow
  (I scaleObservation scaleClock eulerObservation eulerClock eulerData frozenObservation decodedNumerator decodedDenominator)
open GaussianEulerPositivePowerChart (majorant)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "D" => GaussianEulerPowerScalingCompactRate.nameF
local notation "DD" => GaussianEulerPowerScalingCompactRate.data

def source (z R B e f d h Q S E T a C N : PTm n) : Fm PTm n :=
  (le one B ⋏ parameter z R B e f) ⋏ GaussianEulerPositivePowerChartMeshJacobian.input e f d h Q S E T a C N
def scaleSample (p z B e f d h : PTm n) : PTm n := ap2 scaleExpF p (scaleExpData z B e f d h)
def scaleBound (z B e f d h : PTm n) : PTm n := GaussianNameBounds.U scaleExpF (scaleExpData z B e f d h)
def eulerBound (R h Q S E T : PTm n) : PTm n :=
  pw (num 3) (GaussianEulerExponentCompactBounds.radius R (reciprocalMargin h Q E T) (majorant Q S E T))
def physicalCell (p i z B e f d h S E a C N : PTm n) : PTm n :=
  qmul (qmul (fraction e f) (fraction C (timeDenominator N E)))
    (ap2 D p (DD z B e f d h S (timeNumerator i N a C) (timeDenominator N E)))
def imageEuler (p k i z B e f d h Q S E T a C N : PTm n) : PTm n :=
  ap2 I p (eulerData k z B e f d h Q S E T (timeNumerator i N a C) (timeDenominator N E))
def imageCell (p k i z B e f d h Q S E T a C N : PTm n) : PTm n :=
  qmul (width k i e f d h Q S E T a C N) (imageEuler p k i z B e f d h Q S E T a C N)

def frozenNumerator (p k z R B e f d h Q S E T C : PTm n) : PTm n :=
  (Q*C)*(factorBound z B e f d h E*cost R h Q S E T*unit p+two*unit k)
def frozenDenominator (p k E N : PTm n) : PTm n := timeDenominator N E*(unit k*unit p)
def jacobianNumerator (k z R B e f d h Q S E T C N : PTm n) : PTm n :=
  scaleBound z B e f d h*(eulerBound R h Q S E T*GaussianEulerPositivePowerChartMeshJacobian.numerator k h Q S E T C N)
def jacobianDenominator (k h Q E T N : PTm n) : PTm n := GaussianEulerPositivePowerChartMeshJacobian.denominator k h Q E T N
def clockNumerator (k z R B e f d h Q S E T C N : PTm n) : PTm n :=
  widthNumerator k h Q S E T C N*(two*eulerBound R h Q S E T+scaleBound z B e f d h*two)
def clockDenominator (p k h Q E T N : PTm n) : PTm n := cellDenominator k h Q E T N*unit p
def numerator (p k z R B e f d h Q S E T C N : PTm n) : PTm n :=
  (frozenNumerator p k z R B e f d h Q S E T C*jacobianDenominator k h Q E T N+
    jacobianNumerator k z R B e f d h Q S E T C N*frozenDenominator p k E N)*clockDenominator p k h Q E T N+
    clockNumerator k z R B e f d h Q S E T C N*(frozenDenominator p k E N*jacobianDenominator k h Q E T N)
def denominator (p k h Q E T N : PTm n) : PTm n :=
  (frozenDenominator p k E N*jacobianDenominator k h Q E T N)*clockDenominator p k h Q E T N

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B e f d h Q S E T a C N : PTm n) :
    (source z R B e f d h Q S E T a C N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by
  simp [source,parameter,scaled,ComplexLogarithmRemainder.scale,ComplexLogarithmRemainder.bounded]

@[simp] theorem subst_scaleSample {m : ℕ} (σ : Fin n → PTm m) (p z B e f d h : PTm n) :
    Syn.subst σ (scaleSample p z B e f d h) =
      scaleSample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ e)
        (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) := by simp [scaleSample]

@[simp] theorem subst_imageCell {m : ℕ} (σ : Fin n → PTm m) (p k i z B e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (imageCell p k i z B e f d h Q S E T a C N) =
      imageCell (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ i) (Syn.subst σ z) (Syn.subst σ B)
        (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S)
        (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by
  simp [imageCell,imageEuler,eulerData,scaled,ComplexLogarithmRemainder.scale,decodedNumerator,decodedDenominator]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p k z R B e f d h Q S E T C N : PTm n) :
    Syn.subst σ (numerator p k z R B e f d h Q S E T C N) =
      numerator (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
        (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S)
        (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) (Syn.subst σ N) := by
  simp [numerator,frozenNumerator,frozenDenominator,jacobianNumerator,jacobianDenominator,clockNumerator,clockDenominator,
    scaleBound,eulerBound,cost,GaussianEulerPositivePowerChart.majorant,GaussianEulerCompactPowerMajorant.majorant,
    GaussianEulerCompactPowerMajorant.exponentRadius]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p k h Q E T N : PTm n) :
    Syn.subst σ (denominator p k h Q E T N) =
      denominator (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ E)
        (Syn.subst σ T) (Syn.subst σ N) := by
  simp [denominator,frozenDenominator,jacobianDenominator,clockDenominator]

private theorem fixed_product_distance (x y u A B C E : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hxy : Γ ⊢[PRAAx] distanceBounded x y A B) (hu : Γ ⊢[PRAAx] bounded u C E) :
    Γ ⊢[PRAAx] distanceBounded (qmul u x) (qmul u y) (C*A) (E*B) :=
  bound_congr (GaussianRationalRoundedPower.multiplication_difference u x y).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_product _ _ _ _ _ _ hE hB hu hxy)

private theorem weighted_form (c x w : PTm n) :
    Γ ⊢[PRAAx] qmul (qmul c x) w ≐ qmul (qmul c w) x :=
  (qmul_associative c x w).eqTrans
    ((qmul_congr (.eqRefl _) (qmul_commutative x w)).eqTrans (qmul_associative c w x).eqSymm)

private theorem later_sample_distance (F : PR 2) (p j x : PTm n)
    (hj : Γ ⊢[PRAAx] le p j) (hf : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F j x) (ap2 F p x) two (unit p) := by
  have grow := GaussianExponentialReference.unit_monotone hj
  exact distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ (unit_positive j) (unit_positive p))
    (unit_positive p) (by ipra_le 𝔞(unit p)*sl grow) (GaussianNameEquivalence.point_at F x j p hf)

private theorem physical_weight_bound (e f Q C E N : PTm n)
    (hf : Γ ⊢[PRAAx] le one f) (he : Γ ⊢[PRAAx] le e (Q*f)) (hD : Γ ⊢[PRAAx] le one (timeDenominator N E)) :
    Γ ⊢[PRAAx] bounded (qmul (fraction e f) (fraction C (timeDenominator N E))) (Q*C) (timeDenominator N E) := by
  have left := GaussianEulerExponentCompactBounds.fraction_bound e f Q hf he
  have right := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point C (timeDenominator N E) hD).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded C (timeDenominator N E) hD)
  exact bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ (le_refl one) hD left right)

theorem euler_sample_bound (p z R B a b G H : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B G)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b G H) :
    Γ ⊢[PRAAx] bounded (ap2 I p (GaussianEulerIntegrandName.data z B a b))
      (pw (num 3) (GaussianEulerExponentCompactBounds.radius R G H)) one := by
  let r := GaussianEulerIntegrandName.radius z B a b
  let x := GaussianEulerIntegrandName.exponentData z B a b
  let F := GaussianEulerIntegrandName.exponentF
  have hb := GaussianEulerExponentCompactBounds.exponent_bound (GaussianRadiusExponentialName.inputPrecision r p) z R B G H a b hz ht
  have read := GaussianRadiusExponentialName.sample_at (Γ := Γ) F r p x
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ (GaussianRadiusExponentialName.index r p) hb)

theorem corrected_width_bound (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] bounded (width k i e f d h Q S E T a C N)
      (widthNumerator k h Q S E T C N) (cellDenominator k h Q E T N) := by
  let U := unit (query k h Q E T)
  let V := cellDenominator k h Q E T N
  have hU := unit_positive (Γ := Γ) (query k h Q E T)
  have hd := positive_product _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ hd hU
  have base := GaussianEulerPositivePowerChartMesh.original_adjacent_distance k i e f d h Q S E T a C N hs hi
  have reverse := distance_symmetric _ _ _ _ hV base
  have tilt := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point two U hU).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded two U hU)
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ hV hU reverse tilt
  have actual := bound_congr (GaussianEulerPositivePowerChartMeshJacobian.width_identity k i e f d h Q S E T a C N hs).eqSymm
    (.eqRefl _) (.eqRefl _) sum
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hV hU) hV
    (le_of_eq_add (d := zero) (by
      dsimp only [V,U]
      unfold widthNumerator GaussianEulerPositivePowerChartMesh.cellNumerator cellDenominator
      ipra_ring)) actual

theorem denominator_positive (p k h Q E T N : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (denominator p k h Q E T N) := by
  have hD : Γ ⊢[PRAAx] le one (timeDenominator N E) := positive_product _ _ hE hN
  have hu := unit_positive (Γ := Γ) (query k h Q E T)
  exact positive_product _ _ (positive_product _ _
    (positive_product _ _ hD (positive_product _ _ (unit_positive k) (unit_positive p)))
    (positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ hu hu)))
    (positive_product _ _ (positive_product _ _ hD hu) (unit_positive p))

theorem original_cell (p k i z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded (physicalCell p i z B e f d h S E a C N)
      (qmul (scaleSample p z B e f d h) (imageCell p k i z B e f d h Q S E T a C N))
      (numerator p k z R B e f d h Q S E T C N) (denominator p k h Q E T N) := by
  let t := timeNumerator i N a C
  let b := timeDenominator N E
  let w := width k i e f d h Q S E T a C N
  let j := linearTerm k i e f d h Q S E T a C N
  let α := scaleObservation p k z B e f d h Q S E T t b
  let α' := scaleSample p z B e f d h
  let y := eulerObservation p k z B e f d h Q S E T t b
  let y' := imageEuler p k i z B e f d h Q S E T a C N
  let x := ap2 D p (DD z B e f d h S t b)
  let x' := frozenObservation p k z B e f d h Q S E T t b
  let G := reciprocalMargin h Q E T
  let H := majorant Q S E T
  let A := factorBound z B e f d h E*cost R h Q S E T
  let W := scaled z f
  let L := B*e
  let u := decodedNumerator k e f d h Q S E T t b
  let v := decodedDenominator k e f d h Q S E T t b
  let M := scaleBound z B e f d h
  let J := eulerBound R h Q S E T
  have hm := hs.andE₂.andE₁
  have hb : Γ ⊢[PRAAx] le one b := positive_product _ _ hm.andE₂.andE₁ hm.andE₂.andE₂.andE₂.andE₂
  have hu := unit_positive (Γ := Γ) (query k h Q E T)
  have ht := GaussianEulerPositivePowerChartMesh.node_source i e f d h Q S E T a C N hm (le_trans (le_succ_self i) hi)
  have hd := GaussianEulerPositivePowerChartImage.image_domain k e f d h Q S E T t b ht
  have hG := GaussianEulerPositivePowerChartImage.margin_positive h Q E T hm.andE₁.andE₂.andE₁.andE₂
  have hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source W R L G := .andI hs.andE₁.andE₂.andE₁
    (.andI hG hs.andE₁.andE₂.andE₂)
  have hα := GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B e f d h hm.andE₁.andE₂.andE₁
  have αBound : Γ ⊢[PRAAx] bounded α M one := GaussianNameBounds.sample_bound _ _ _ hα
  have αFixed : Γ ⊢[PRAAx] bounded α' M one := GaussianNameBounds.sample_bound _ _ _ hα
  have observed : Γ ⊢[PRAAx] bounded y J one := euler_sample_bound _ W R L u v G H hz hd
  have hDamp := GaussianEulerPowerScalingFrozenIntegrand.original_frozen_integrand k z R B e f d h Q S E T t b
    hs.andE₁.andE₁ hs.andE₁.andE₂ ht
  have hd1 : Γ ⊢[PRAAx] le one (unit k*unit p) := positive_product _ _ (unit_positive k) (unit_positive p)
  have near : Γ ⊢[PRAAx] distanceBounded x x' (A*unit p+two*unit k) (unit k*unit p) :=
    GaussianNamedInverseRate.diagonal_rate _ _ _ _ A (unit k) p (unit_positive k) hDamp
  have wt := physical_weight_bound e f Q C E N hm.andE₁.andE₁.andE₂ hm.andE₁.andE₂.andE₂.andE₂.andE₁ hb
  have raw := fixed_product_distance x x' (qmul (fraction e f) (fraction C b)) _ _ _ _ hd1 hb near wt
  have toJac := (weighted_form (fraction e f) x' (fraction C b)).eqSymm.eqTrans
    (GaussianEulerPowerScalingFrozenRow.original_mesh_weighted_row p k i z B e f d h Q S E T a C N hm (le_trans (le_succ_self i) hi))
  have first : Γ ⊢[PRAAx] distanceBounded (physicalCell p i z B e f d h S E a C N)
      (qmul α (qmul j y)) (frozenNumerator p k z R B e f d h Q S E T C) (frozenDenominator p k E N) :=
    distance_congr (.eqRefl _) toJac (.eqRefl _) (.eqRefl _) raw
  have hdj : Γ ⊢[PRAAx] le one (jacobianDenominator k h Q E T N) :=
    positive_product _ _ (positive_product _ _ hb hb) (positive_product _ _ hu hu)
  have widthError := GaussianEulerPositivePowerChartMeshJacobian.original_cell_bound k i e f d h Q S E T a C N hs.andE₂ hi
  have reversed := distance_symmetric _ _ _ _ hdj widthError
  have timesY := fixed_product_distance j w y _ _ _ _ hdj (le_refl one) reversed observed
  have timesBoth := fixed_product_distance (qmul y j) (qmul y w) α _ _ _ _
    (positive_product _ _ (le_refl one) hdj) (le_refl one) timesY αBound
  have second : Γ ⊢[PRAAx] distanceBounded (qmul α (qmul j y)) (qmul α (qmul w y))
      (jacobianNumerator k z R B e f d h Q S E T C N) (jacobianDenominator k h Q E T N) :=
    distance_congr (qmul_congr (.eqRefl _) (qmul_commutative y j)) (qmul_congr (.eqRefl _) (qmul_commutative y w))
      (.eqRefl _) (by unfold jacobianDenominator; ipra_ring) timesBoth
  have scaleLater : Γ ⊢[PRAAx] le p (scaleClock p k z B e f d h Q S E T t b) := le_trans (le_add_right _ _) (le_add_right _ _)
  have eulerLater : Γ ⊢[PRAAx] le p (eulerClock p k z B e f d h Q S E T t b) := le_trans (le_add_right _ _) (le_add_right _ _)
  have hy := GaussianEulerIntegrandName.name_regular W L u v (.andI hz.andE₁ hd.andE₁)
  have s := later_sample_distance scaleExpF p _ (scaleExpData z B e f d h) scaleLater hα
  have eul := later_sample_distance I p _ (eulerData k z B e f d h Q S E T t b) eulerLater hy
  have retimed := GaussianNameArithmetic.product_distance α α' y y' two two (unit p) J M (unit_positive p) s eul observed αFixed
  have hW : Γ ⊢[PRAAx] le one (cellDenominator k h Q E T N) := positive_product _ _ hb hu
  have scaledDifference := fixed_product_distance (qmul α y) (qmul α' y') w _ _ _ _ (unit_positive p) hW retimed
    (corrected_width_bound k i e f d h Q S E T a C N hm hi)
  have third : Γ ⊢[PRAAx] distanceBounded (qmul α (qmul w y)) (qmul α' (qmul w y'))
      (clockNumerator k z R B e f d h Q S E T C N) (clockDenominator p k h Q E T N) :=
    distance_congr
      ((qmul_associative w α y).eqSymm.eqTrans ((qmul_congr (qmul_commutative w α) (.eqRefl _)).eqTrans (qmul_associative α w y)))
      ((qmul_associative w α' y').eqSymm.eqTrans ((qmul_congr (qmul_commutative w α') (.eqRefl _)).eqTrans (qmul_associative α' w y')))
      (.eqRefl _) (.eqRefl _) scaledDifference
  have hf : Γ ⊢[PRAAx] le one (frozenDenominator p k E N) := positive_product _ _ hb hd1
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (positive_product _ _ hf hdj)
    (positive_product _ _ hW (unit_positive p)) (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hf hdj first second) third

theorem actual_original_power_scaling_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 17
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
        (var 12) (var 13) (var 14) (var 15) (var 16) ⋏ lt (var 2) (var 16)) ⟶
      distanceBounded (physicalCell (var 0) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 11)
        (var 12) (var 14) (var 15) (var 16))
        (qmul (scaleSample (var 0) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9))
          (imageCell (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
            (var 12) (var 13) (var 14) (var 15) (var 16)))
        (numerator (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
          (var 12) (var 13) (var 15) (var 16))
        (denominator (var 0) (var 1) (var 9) (var 10) (var 12) (var 13) (var 16))) :=
  closeUniv 17 (.impI (original_cell _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCell

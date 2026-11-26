import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartImage
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionTiltedNodes

/-!
# Literal positive power chart mesh and exactly ordered corrected nodes

Every original affine node is evaluated by the same uniformly retimed
chart program and its literal positive rational image decoder. Actual
chart monotonicity supplies the two-dyadic adjacent order allowance; the
explicit scalar tilt 2*i/2^query makes the computed nodes exactly ordered.
The true chart Lipschitz rate controls every original image cell, with
C=0 admitted and no local analytic or rounded-node premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartImage (query)
open GaussianEulerPositivePowerChart (parameters lipschitz)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerUnitSubstitutionTiltedNodes (tilt tilt_step_order tilt_error)
open RationalValueBounds (upper radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (e f d h Q S E T a C N : PTm n) : Fm PTm n :=
  parameters e f d h Q S ⋏ (le one E ⋏ (le one a ⋏ (le (a+C) (T*E) ⋏ le one N)))
def timeNumerator (i N a C : PTm n) : PTm n := a*N+C*i
def timeDenominator (N E : PTm n) : PTm n := E*N
def node (p i e f d h Q S E T a C N : PTm n) : PTm n :=
  GaussianEulerPositivePowerChartImage.sample p e f d h Q S E T (timeNumerator i N a C) (timeDenominator N E)
def correctedNode (p i e f d h Q S E T a C N : PTm n) : PTm n :=
  tilt (fstT (node p i e f d h Q S E T a C N)) i two (unit (query p h Q E T))
def cellNumerator (p h Q S E T C N : PTm n) : PTm n :=
  lipschitz Q S E T*C*unit (query p h Q E T)+two*timeDenominator N E
def cellDenominator (p h Q E T N : PTm n) : PTm n := timeDenominator N E*unit (query p h Q E T)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (e f d h Q S E T a C N : PTm n) :
    (source e f d h Q S E T a C N).subst σ = source (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d)
      (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_timeNumerator {m : ℕ} (σ : Fin n → PTm m) (i N a C : PTm n) :
    Syn.subst σ (timeNumerator i N a C) = timeNumerator (Syn.subst σ i) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ C) := by simp [timeNumerator]
@[simp] theorem subst_timeDenominator {m : ℕ} (σ : Fin n → PTm m) (N E : PTm n) :
    Syn.subst σ (timeDenominator N E) = timeDenominator (Syn.subst σ N) (Syn.subst σ E) := by simp [timeDenominator]
@[simp] theorem subst_node {m : ℕ} (σ : Fin n → PTm m) (p i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (node p i e f d h Q S E T a C N) = node (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [node]
@[simp] theorem subst_correctedNode {m : ℕ} (σ : Fin n → PTm m) (p i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (correctedNode p i e f d h Q S E T a C N) = correctedNode (Syn.subst σ p) (Syn.subst σ i) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [correctedNode]
@[simp] theorem subst_cellNumerator {m : ℕ} (σ : Fin n → PTm m) (p h Q S E T C N : PTm n) :
    Syn.subst σ (cellNumerator p h Q S E T C N) = cellNumerator (Syn.subst σ p) (Syn.subst σ h) (Syn.subst σ Q)
      (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) (Syn.subst σ N) := by simp [cellNumerator]
@[simp] theorem subst_cellDenominator {m : ℕ} (σ : Fin n → PTm m) (p h Q E T N : PTm n) :
    Syn.subst σ (cellDenominator p h Q E T N) = cellDenominator (Syn.subst σ p) (Syn.subst σ h) (Syn.subst σ Q)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) := by simp [cellDenominator]

theorem time_domain (i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    domain (timeNumerator i N a C) (timeDenominator N E) E T := by
  have ha := hs.andE₂.andE₂.andE₁
  have hN := hs.andE₂.andE₂.andE₂.andE₂
  have hE := hs.andE₂.andE₁
  have aN := positive_product _ _ ha hN
  have lower : Γ ⊢[PRAAx] le N (timeNumerator i N a C) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right N ha)) (le_add_right _ _)
  refine .andI (.andI (le_trans aN (le_add_right _ _)) (positive_product _ _ hE hN)) (.andI ?_ ?_)
  · exact le_congr (by unfold timeDenominator; ipra_ring) (by ipra_ring) (mul_le_mul_right E lower)
  · unfold timeNumerator timeDenominator
    ipra_le 𝔞 C*sl hi+𝔞 N*sl hs.andE₂.andE₂.andE₂.andE₁

theorem node_source (i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianEulerPositivePowerChart.source e f d h Q S E T (timeNumerator i N a C) (timeDenominator N E) :=
  .andI hs.andE₁ (.andI hs.andE₂.andE₁ (time_domain i e f d h Q S E T a C N hs hi))

theorem actual_image_domain (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    domain (GaussianUnitIntervalInputDecoding.numerator (node p i e f d h Q S E T a C N))
      (GaussianUnitIntervalInputDecoding.denominator (node p i e f d h Q S E T a C N))
      (GaussianEulerPositivePowerChartImage.reciprocalMargin h Q E T) (GaussianEulerPositivePowerChart.majorant Q S E T) :=
  GaussianEulerPositivePowerChartImage.image_domain _ _ _ _ _ _ _ _ _ _ _ (node_source i e f d h Q S E T a C N hs hi)

theorem original_adjacent_order (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    upper (fstT (node p i e f d h Q S E T a C N)) (fstT (node p (succ i) e f d h Q S E T a C N))
      two (unit (query p h Q E T)) := by
  have first := node_source i e f d h Q S E T a C N hs (le_trans (le_succ_self i) hi)
  have second := time_domain (succ i) e f d h Q S E T a C N hs hi
  have order : Γ ⊢[PRAAx] le (timeNumerator i N a C*timeDenominator N E)
      (timeDenominator N E*timeNumerator (succ i) N a C) := le_of_eq_add (d := timeDenominator N E*C) (by unfold timeNumerator; ipra_ring)
  have actual := GaussianEulerPositivePowerChartOrder.original_observations (query p h Q E T) (query p h Q E T)
    e f d h Q S E T _ _ _ _ (.andI first (.andI second order))
  exact RationalValueBounds.upper_mono _ _ _ _ two (unit (query p h Q E T))
    (positive_product _ _ (unit_positive _) (unit_positive _)) actual (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring))

theorem corrected_order (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (correctedNode p i e f d h Q S E T a C N) (correctedNode p (succ i) e f d h Q S E T a C N) :=
  tilt_step_order _ _ i two _ (unit_positive _) (original_adjacent_order p i e f d h Q S E T a C N hs hi)

theorem corrected_displacement (p i e f d h Q S E T a C N : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    radius (correctedNode p i e f d h Q S E T a C N) (fstT (node p i e f d h Q S E T a C N))
      (two*N) (unit (query p h Q E T)) :=
  RationalValueBounds.radius_mono _ _ _ _ _ _ (unit_positive _) (tilt_error _ i two _ (unit_positive _))
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (unit (query p h Q E T)*two) hi))

/-- The actual two affine rational times differ by exactly the cell width. -/
theorem time_distance (i N a C E : PTm n) (hD : Γ ⊢[PRAAx] le one (timeDenominator N E)) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.fraction (timeNumerator i N a C) (timeDenominator N E))
      (GaussianPositiveRationalLogarithm.fraction (timeNumerator (succ i) N a C) (timeDenominator N E)) C (timeDenominator N E) := by
  let A := ComplexLogarithmRemainder.scale (timeNumerator i N a C) ComplexLogarithmRemainder.oneCode
  let B := ComplexLogarithmRemainder.scale (timeNumerator (succ i) N a C) ComplexLogarithmRemainder.oneCode
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (GaussianRootAlgebra.sub A B) ≐ C*C := by
    apply deriveNat
    rw [ComplexLogarithmRemainder.normSq_eval]
    simp only [A,B,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,timeNumerator]
    ipra_simps
    ring
  apply (GaussianRationalMetric.bounded_difference_iff _ _ A B (timeDenominator N E) C (timeDenominator N E) hD hD
    (GaussianRationalHorner.ofGaussian_represents _ _ hD) (GaussianRationalHorner.ofGaussian_represents _ _ hD)).iffMpr
  exact le_of_eq_add (d := ConciseIPRA.PTm.zero) (by
    apply deriveNat
    have exactNorm := natEq norm
    ipra_simps
    rw [exactNorm]
    ring)

theorem original_adjacent_distance (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (node p i e f d h Q S E T a C N) (node p (succ i) e f d h Q S E T a C N)
      (cellNumerator p h Q S E T C N) (cellDenominator p h Q E T N) := by
  let t := query p h Q E T
  let D := timeDenominator N E
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂
  have first := node_source i e f d h Q S E T a C N hs (le_trans (le_succ_self i) hi)
  have second := time_domain (succ i) e f d h Q S E T a C N hs hi
  have actual := GaussianEulerPositivePowerChart.original_observations t t e f d h Q S E T _ _ _ _ C D
    (.andI first (.andI second (.andI hD (time_distance i N a C E hD))))
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive D t t hD) (positive_product _ _ hD (unit_positive t))
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold cellNumerator cellDenominator GaussianNamedInverseRate.rateNumerator GaussianNamedInverseRate.rateDenominator; dsimp only [D,t]; ipra_ring)) actual

/-- Exact one-step tilt cancellation: only one A/B is added to the
original local upper radius, independently of the numerical index. -/
theorem tilt_successor_upper (a b i A B X Y : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper a b X Y) : Γ ⊢[PRAAx]
    upper (tilt a (succ i) A B) (tilt b i A B) (X*B+A*Y) (Y*B) := by
  let U := RationalSupMetric.denominatorOf a
  let V := RationalSupMetric.denominatorOf b
  let u := RationalSupMetric.numeratorOf a
  let v := RationalSupMetric.numeratorOf b
  let L := ZT.ofNat (Y*V)*u
  let R := ZT.ofNat (Y*U)*v+ZT.ofNat (X*U*V)
  have signed := RationalUpperRepresentation.upper_from_representations a b U V X Y u v
    (RationalRepresentations.represents_self a) (RationalRepresentations.represents_self b) h
  have e := zle_toZ signed
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ (U*B) (V*B) (X*B+A*Y) (Y*B)
    (positive_product _ _ (RationalArgmin.denominator_positive a) hB)
    (positive_product _ _ (RationalArgmin.denominator_positive b) hB)
    (GaussianEulerUnitSubstitutionTiltedNodes.tilt_represents a (succ i) A B hB)
    (GaussianEulerUnitSubstitutionTiltedNodes.tilt_represents b i A B hB)
  apply zle_of_toZ (B*B*B*PolynomialBisection.slack L R)
  dsimp only [L,R] at e ⊢
  simp only [GaussianEulerUnitSubstitutionTiltedNodes.tiltNumerator,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,
    U,V,u,v,PolynomialBisection.slack] at e ⊢
  ipra_simps
  linear_combination 𝔞 B*𝔞 B*𝔞 B*e

def widthNumerator (p h Q S E T C N : PTm n) : PTm n :=
  lipschitz Q S E T*C*unit (query p h Q E T)+num 4*timeDenominator N E
@[simp] theorem subst_widthNumerator {m : ℕ} (σ : Fin n → PTm m) (p h Q S E T C N : PTm n) :
    Syn.subst σ (widthNumerator p h Q S E T C N) = widthNumerator (Syn.subst σ p) (Syn.subst σ h) (Syn.subst σ Q)
      (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ C) (Syn.subst σ N) := by simp [widthNumerator]

/-- The actual ordered corrected image cell has width at most
L*C/(E*N)+4/2^query; the index has cancelled exactly. -/
theorem corrected_cell_radius (p i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    radius (correctedNode p (succ i) e f d h Q S E T a C N) (correctedNode p i e f d h Q S E T a C N)
      (widthNumerator p h Q S E T C N) (cellDenominator p h Q E T N) := by
  let t := query p h Q E T
  let D := timeDenominator N E
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂
  have denominator : Γ ⊢[PRAAx] le one (cellDenominator p h Q E T N) := positive_product _ _ hD (unit_positive t)
  have original := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ denominator
    (original_adjacent_distance p i e f d h Q S E T a C N hs hi)
  have raw := RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ original)
  have moved := tilt_successor_upper _ _ i two (unit t) _ _ (unit_positive t) raw
  have upperBound : Γ ⊢[PRAAx] upper
      (correctedNode p (succ i) e f d h Q S E T a C N) (correctedNode p i e f d h Q S E T a C N)
      (widthNumerator p h Q S E T C N) (cellDenominator p h Q E T N) :=
    RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ denominator (unit_positive t)) moved
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold cellNumerator cellDenominator widthNumerator; dsimp only [t,D]; ipra_ring))
  exact RationalValueBounds.radius_of_upper _ _ _ _ upperBound
    (RationalValueBounds.upper_of_order _ _ _ _ (corrected_order p i e f d h Q S E T a C N hs hi))

theorem actual_original_power_chart_corrected_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ lt (var 1) (var 12)) ⟶
      RationalArgmin.rationalLE
        (correctedNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (correctedNode (var 0) (succ (var 1)) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (corrected_order _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_power_chart_corrected_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ lt (var 1) (var 12)) ⟶
      radius
        (correctedNode (var 0) (succ (var 1)) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (correctedNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (widthNumerator (var 0) (var 5) (var 6) (var 7) (var 8) (var 9) (var 11) (var 12))
        (cellDenominator (var 0) (var 5) (var 6) (var 8) (var 9) (var 12))) :=
  closeUniv 13 (.impI (corrected_cell_radius _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartMesh

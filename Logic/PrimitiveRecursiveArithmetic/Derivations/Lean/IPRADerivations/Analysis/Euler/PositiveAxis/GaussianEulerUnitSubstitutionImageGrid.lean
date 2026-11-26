import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionCompactName
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayOrder

/-!
# The actual decay-image grid of the unit-substitution density

The literal original decay differences telescope to the unchanged
endpoint observations. On every positive affine grid with step at most
one their norms are at most 6*step+20*eps. This numerical cap is uniform
in time and follows from the original quadratic decay increment. The
actual density sampler's computed count and row query put every such
image cell within its requested dyadic radius. Named time reversal is
also proved; positivity of individual rounded cell codes is not assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionImageGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerDecayMesh (observation consecutiveDifference consecutive_difference_at consecutive_difference_sum stepError errorDen)
open GaussianEulerIntegrandName (decayF decayData fixedData)
open GaussianEulerUnitSubstitutionCompactName (count rowQuery stage)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded qsub qsub_canonical)
open GaussianRationalReciprocal (bounded_product bounded_sum bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def cellBody : PTm 2 := consecutiveDifference (sampleBody GaussianEulerDecayQuadrature.evaluatorF)
def node (i p N a C E : PTm n) : PTm n := observation (a*N+C*i) (E*N) p
def source (a C E N : PTm n) : Fm PTm n := le one a ⋏ (le one E ⋏ (le one N ⋏ (le one C ⋏ le C (E*N))))
def meshNumerator (p N C E : PTm n) : PTm n := num 6*C*unit p+num 20*(E*N)
def meshDenominator (p N E : PTm n) : PTm n := E*N*unit p

@[simp] theorem subst_node {m : ℕ} (σ : Fin n → PTm m) (i p N a C E : PTm n) :
    Syn.subst σ (node i p N a C E) = node (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [node]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (a C E N : PTm n) :
    (source a C E N).subst σ = source (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_meshNumerator {m : ℕ} (σ : Fin n → PTm m) (p N C E : PTm n) :
    Syn.subst σ (meshNumerator p N C E) = meshNumerator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ E) := by simp [meshNumerator]
@[simp] theorem subst_meshDenominator {m : ℕ} (σ : Fin n → PTm m) (p N E : PTm n) :
    Syn.subst σ (meshDenominator p N E) = meshDenominator (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ E) := by simp [meshDenominator]

theorem cell_at (i p N a C E x : PTm n) : Γ ⊢[PRAAx]
    inst2 cellBody i (sampleData p N a C E x) ≐ qsub (node i p N a C E) (node (succ i) p N a C E) := by
  unfold cellBody
  rw [consecutive_difference_at]
  exact qsub_congr (GaussianEulerDecayQuadrature.cell_at i p N a C E x)
    (GaussianEulerDecayQuadrature.cell_at (succ i) p N a C E x)

/-- Exact original finite telescope, including a zero-width interval. -/
theorem original_telescope (p N a C E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    sum cellBody N (sampleData p N a C E x) ≐ qsub (observation a E p) (observation (a+C) E p) :=
  (consecutive_difference_sum (sampleBody GaussianEulerDecayQuadrature.evaluatorF) _ N).eqTrans
    (qsub_congr (GaussianEulerDecayQuadrature.endpoint_left_at p N a C E x hE hN)
      (GaussianEulerDecayQuadrature.endpoint_right_at p N a C E x hE hN))

theorem original_cell_mesh (i p N a C E x : PTm n) (hs : Γ ⊢[PRAAx] source a C E N) : Γ ⊢[PRAAx]
    bounded (inst2 cellBody i (sampleData p N a C E x)) (meshNumerator p N C E) (meshDenominator p N E) := by
  let d := sampleData p N a C E x
  let X := node i p N a C E
  let B := E*N
  let U := unit p
  let w := weight C E N
  let ideal := inst2 (multiplyBody (sampleBody GaussianEulerDecayQuadrature.evaluatorF)) i (pairT w d)
  let cell := inst2 cellBody i d
  have hE := hs.andE₂.andE₁
  have hN := hs.andE₂.andE₂.andE₁
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hE hN
  have hU := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one (errorDen B p) := positive_product _ _ (positive_product _ _ hB hB) hU
  have ha : Γ ⊢[PRAAx] le one (a*N+C*i) := le_trans (positive_product _ _ hs.andE₁ hN) (le_add_right _ _)
  have read : Γ ⊢[PRAAx] ideal ≐ qmul X w :=
    (multiply_body_at (sampleBody GaussianEulerDecayQuadrature.evaluatorF) w i d).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianEulerDecayQuadrature.cell_at i p N a C E x)).eqTrans
        (GaussianRationalPowerAlgebra.qmul_commutative _ _))
  have base : Γ ⊢[PRAAx] bounded ideal ((num 3)*C) B :=
    bound_congr read.eqSymm (.eqRefl _) (one_mul _)
      (bounded_product X w (num 3) one C B (le_refl one) hB
        (bound_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
          (GaussianEulerDecayIncrement.decay_observation_uniform_bound _ _ p ha hB))
        (GaussianRationalRiemannRefinement.weight_bound C E N hE hN))
  have near := distance_symmetric _ _ _ _ hD (GaussianEulerDecayQuadrature.cell_distance i p N a C E x
    hs.andE₁ hN hE hs.andE₂.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂)
  have can : Γ ⊢[PRAAx] GaussianRationalHorner.canonical cell := by
    dsimp only [cell,cellBody]
    rw [consecutive_difference_at]
    exact qsub_canonical _ _
  have raw := bound_congr (GaussianRationalLinearProduct.add_sub_right ideal cell can) (.eqRefl _) (.eqRefl _)
    (bounded_sum ideal (qsub cell ideal) (num 3*C) B (stepError B C p) (errorDen B p) hB hD base near)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hB hD) (positive_product _ _ hB hU) _ raw
  dsimp only [meshNumerator,meshDenominator,stepError,errorDen,GaussianNameRingLaws.three,B,U]
  ipra_le (3*𝔞 C*𝔞(E*N)*𝔞(E*N)*𝔞(unit p)*𝔞(unit p))*sl hs.andE₂.andE₂.andE₂.andE₂

theorem original_named_orientation (i N a C E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.realOrder decayF decayF
      (decayData (a*N+C*succ i) (E*N)) (decayData (a*N+C*i) (E*N)) :=
  GaussianEulerDecayOrder.original_decay_order _ _ _ _ (positive_product _ _ hE hN) (positive_product _ _ hE hN)
    (le_of_eq_add (d := C*(E*N)) (by ipra_ring))

theorem original_orientation_observations (i p q N a C E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (node (succ i) p N a C E)) (fstT (node i q N a C E))
      (unit p+unit q) (unit p*unit q) :=
  GaussianNamedPositiveExponentialOrder.real_order_at _ _ _ _ p q (original_named_orientation i N a C E hE hN)

theorem density_cell_source (p z R B a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionCompactName.source z R B a C E T) : Γ ⊢[PRAAx]
    source a C E (count p R C E T) := by
  have old := GaussianEulerUnitSubstitutionCompactName.finite_source p z R B a C E T hs
  exact .andI hs.andE₁.andE₂.andE₁ (.andI hs.andE₁.andE₁.andE₂.andE₁
    (.andI old.andE₂.andE₁ old.andE₂.andE₂))

/-- Every literal image cell of the actual computed density sampler
has norm at most the requested output dyadic radius. -/
theorem original_computed_mesh (i p z R B a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionCompactName.source z R B a C E T) : Γ ⊢[PRAAx]
    bounded (inst2 cellBody i (sampleData (rowQuery p R C E T) (count p R C E T) a C E (fixedData z B))) one (unit p) := by
  let N := count p R C E T
  let s := rowQuery p R C E T
  let P := unit (stage p)
  let U := unit s
  let D := E*N
  let K := majorant R E T
  have hN := GaussianEulerUnitSubstitutionCompactName.count_positive (Γ := Γ) p R C E T
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hE hN
  have hK : Γ ⊢[PRAAx] le one K := GaussianPolynomialPerturbation.power_positive (num 3) _ (zero_lt_succ two)
  have hKC := positive_product _ _ hK hs.andE₂
  have threeCount : Γ ⊢[PRAAx] le (num 3*C*P) N := le_trans
    (le_congr (one_mul _) (by ipra_ring) (mul_le_mul_right (num 3*C*P) hKC))
    (GaussianEulerUnitSubstitutionCompactName.count_budget p R C E T)
  have threeStep : Γ ⊢[PRAAx] le (num 3*C*P) D := le_trans threeCount
    (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right N hE))
  have query : Γ ⊢[PRAAx] le (GaussianEulerUnitSubstitutionCompactName.rowBudget p R C E T*P) U :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone (le_add_left _ _))
  have hKN := positive_product _ _ hK hN
  have twenty : Γ ⊢[PRAAx] le (num 20*P) U := le_trans
    (le_congr (one_mul _) (by ipra_ring) (mul_le_mul_right (num 20*P) hKN))
    (le_trans (le_congr (.eqRefl _) (by dsimp only [GaussianEulerUnitSubstitutionCompactName.rowBudget]; ipra_ring)
      (mul_le_mul_right P (le_add_right (num 20*K*N) (T*GaussianEulerIntegrationByPartsGridObservation.rowCost R E T)))) query)
  have raw := original_cell_mesh i s N a C E (fixedData z B) (density_cell_source p z R B a C E T hs)
  have coarse : Γ ⊢[PRAAx] bounded (inst2 cellBody i (sampleData s N a C E (fixedData z B))) (num 3) P :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD (unit_positive s)) (unit_positive (stage p))
      (by
        change Γ ⊢[PRAAx] le ((num 6*C*U+num 20*D)*P) (num 3*(D*U))
        ipra_le 2*𝔞 U*sl threeStep+𝔞 D*sl twenty) raw
  exact bounded_radius_mono _ _ _ one (unit p) (unit_positive (stage p)) (unit_positive p)
    (le_congr (.eqRefl _) (by ipra_ring) (le_trans
      (le_of_eq_add (d := num 3*unit p) (by ipra_ring)) (GaussianEulerUnitSubstitutionCompactName.stage_budget p))) coarse

theorem actual_original_decay_image_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 4) ⋏ le one (var 1)) ⟶ sum cellBody (var 1)
      (sampleData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
      qsub (observation (var 2) (var 4) (var 0)) (observation (var 2+var 3) (var 4) (var 0))) :=
  closeUniv 6 (.impI (original_telescope _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_decay_image_cell_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 3) (var 4) (var 5) (var 2) ⟶ bounded
      (inst2 cellBody (var 0) (sampleData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
      (meshNumerator (var 1) (var 2) (var 4) (var 5)) (meshDenominator (var 1) (var 2) (var 5))) :=
  closeUniv 7 (.impI (original_cell_mesh _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_computed_unit_image_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (GaussianEulerUnitSubstitutionCompactName.source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (inst2 cellBody (var 0) (sampleData (rowQuery (var 1) (var 3) (var 6) (var 7) (var 8))
        (count (var 1) (var 3) (var 6) (var 7) (var 8)) (var 5) (var 6) (var 7) (fixedData (var 2) (var 4)))) one (unit (var 1))) :=
  closeUniv 9 (.impI (original_computed_mesh _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionImageGrid

import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionImageGrid
import IPRADerivations.Analysis.Names.GaussianNamedDifference

/-!
# Independent row precision for the original unit-chart density

At a fixed numerical grid count, the actual power and both actual decay
endpoint queries can be made arbitrarily late. Genuine original CN and
the uniform image-cell bound derive the full finite density comparison.
This allows rational-node approximation to choose its precision after
the grid is fixed, without assuming an output or quadrature identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionDensityPrecision

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionDensity (density densityBody power_grid_at density_row_at)
open GaussianEulerUnitSubstitutionImageGrid (cellBody cell_at node)
open GaussianEulerIntegrandName (powerF powerData decayF decayData fixedData)
open GaussianEulerPowerIncrement (point)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianCompactRiemannName (sampleData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B a C E T N : PTm n) : Fm PTm n := GaussianEulerUnitSubstitutionDensity.source z R B a C E T N
def rowGain (R E T : PTm n) : PTm n := num 26+two*majorant R E T
def minimumQuery (s R E T N : PTm n) : PTm n := GaussianFastValueCut.exponent (two*N*rowGain R E T) s

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T N : PTm n) :
    (source z R B a C E T N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) := by simp [source]
@[simp] theorem subst_rowGain {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (rowGain R E T) = rowGain (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [rowGain]
@[simp] theorem subst_minimumQuery {m : ℕ} (σ : Fin n → PTm m) (s R E T N : PTm n) :
    Syn.subst σ (minimumQuery s R E T N) = minimumQuery (Syn.subst σ s) (Syn.subst σ R)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ N) := by simp [minimumQuery]

theorem geometry_source (z R B a C E T N : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    GaussianEulerUnitSubstitutionImageGrid.source a C E N :=
  .andI hs.andE₁.andE₂.andE₁ (.andI hs.andE₁.andE₁.andE₂.andE₁ hs.andE₂)

theorem original_uniform_cell_bound (i p z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    bounded (inst2 cellBody i (sampleData p N a C E (fixedData z B))) (num 26) one := by
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have hN := hs.andE₂.andE₁
  have hB := positive_product _ _ hE hN
  have hU := unit_positive (Γ := Γ) p
  have raw := GaussianEulerUnitSubstitutionImageGrid.original_cell_mesh i p N a C E (fixedData z B)
    (geometry_source z R B a C E T N hs)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hB hU) (le_refl one) _ raw
  dsimp only [GaussianEulerUnitSubstitutionImageGrid.meshNumerator,GaussianEulerUnitSubstitutionImageGrid.meshDenominator]
  ipra_le 6*𝔞(unit p)*sl hs.andE₂.andE₂.andE₂+20*𝔞(E*N)*sl hU

theorem original_cell_precision (i p q N a C E x : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (inst2 cellBody i (sampleData p N a C E x)) (inst2 cellBody i (sampleData q N a C E x))
      (two*(unit p+unit q)) (unit p*unit q) := by
  have here := GaussianNameEquivalence.point_at (Γ := Γ) decayF (decayData (a*N+C*i) (E*N)) p q
    (GaussianEulerDecayQuadraturePrecision.observation_regular _ _)
  have later := GaussianNameEquivalence.point_at (Γ := Γ) decayF (decayData (a*N+C*succ i) (E*N)) p q
    (GaussianEulerDecayQuadraturePrecision.observation_regular _ _)
  exact distance_congr (cell_at i p N a C E x).eqSymm (cell_at i q N a C E x).eqSymm (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) here later)

theorem original_density_row_precision (i p q z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    distanceBounded (inst2 densityBody i (sampleData p N a C E (fixedData z B)))
      (inst2 densityBody i (sampleData q N a C E (fixedData z B)))
      (rowGain R E T*(unit p+unit q)) (unit p*unit q) := by
  have here := GaussianEulerIntegrationByPartsGridObservation.grid_source i N z R B a C E T hs.andE₁ hs.andE₂.andE₁ (le_of_lt hi)
  have hpCN := GaussianEulerIntegrandName.power_regular z B (a*N+C*i) (E*N) (.andI here.andE₁.andE₁ here.andE₂.andE₁)
  have powerNear := GaussianNameEquivalence.point_at powerF (powerData z B (a*N+C*i) (E*N)) p q hpCN
  have cellNear := original_cell_precision (Γ := Γ) i p q N a C E (fixedData z B)
  have finite := GaussianNameArithmetic.product_distance _ _ _ _ _ _ _ (num 26) (majorant R E T)
    (positive_product _ _ (unit_positive p) (unit_positive q)) powerNear cellNear
    (original_uniform_cell_bound i p z R B a C E T N hs)
    (original_power_observation q z R B E T _ _ here.andE₁ here.andE₂)
  have first : Γ ⊢[PRAAx] inst2 densityBody i (sampleData p N a C E (fixedData z B)) ≐
      qmul (point p z B (a*N+C*i) (E*N)) (inst2 cellBody i (sampleData p N a C E (fixedData z B))) := by
    rw [density_row_at]
    exact qmul_congr (power_grid_at i p N z B a C E) (.eqRefl _)
  have second : Γ ⊢[PRAAx] inst2 densityBody i (sampleData q N a C E (fixedData z B)) ≐
      qmul (point q z B (a*N+C*i) (E*N)) (inst2 cellBody i (sampleData q N a C E (fixedData z B))) := by
    rw [density_row_at]
    exact qmul_congr (power_grid_at i q N z B a C E) (.eqRefl _)
  exact distance_congr first.eqSymm second.eqSymm (by unfold rowGain; ipra_ring) (.eqRefl _) finite

theorem original_finite_precision (p q z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    distanceBounded (density p N z B a C E) (density q N z B a C E)
      (N*(rowGain R E T*(unit p+unit q))) (unit p*unit q) := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hs.shift
  have rows : Γ ⊢[PRAAx] termsDistance densityBody densityBody N
      (sampleData p N a C E (fixedData z B)) (sampleData q N a C E (fixedData z B))
      (rowGain R E T*(unit p+unit q)) (unit p*unit q) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
      PTm.subst_mul,PTm.subst_add,subst_rowGain,GaussianCoefficientNameBounds.subst_unit,Syn.shift] using
      original_density_row_precision (var 0) (Syn.shift p) (Syn.shift q) (Syn.shift z) (Syn.shift R) (Syn.shift B)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift N) ss.wk Prf.hyp0
  exact sum_distance _ _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) rows

/-- Both actual row queries may be chosen independently, after the
numerical grid count N and requested error s have been fixed. -/
theorem original_late_queries (p q s z R B a C E T N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T N)
    (hp : Γ ⊢[PRAAx] le (minimumQuery s R E T N) p) (hq : Γ ⊢[PRAAx] le (minimumQuery s R E T N) q) : Γ ⊢[PRAAx]
    distanceBounded (density p N z B a C E) (density q N z B a C E) one (unit s) := by
  let H := unit (minimumQuery s R E T N)
  have hH := unit_positive (Γ := Γ) (minimumQuery s R E T N)
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have growP : Γ ⊢[PRAAx] le H (unit p) := GaussianExponentialReference.unit_monotone hp
  have growQ : Γ ⊢[PRAAx] le H (unit q) := GaussianExponentialReference.unit_monotone hq
  have coarse := distance_radius_mono _ _ _ _ (two*N*rowGain R E T) H (positive_product _ _ hP hQ) hH
    (by ipra_le (𝔞(N)*𝔞(rowGain R E T)*𝔞(unit q))*sl growP+
      (𝔞(N)*𝔞(rowGain R E T)*𝔞(unit p))*sl growQ) (original_finite_precision p q z R B a C E T N hs)
  have budget : Γ ⊢[PRAAx] le (two*N*rowGain R E T*unit s) H := GaussianFastValueCut.query_budget _ _
  exact distance_radius_mono _ _ _ _ one (unit s) hH (unit_positive s)
    (le_congr (.eqRefl _) (by ipra_ring) budget) coarse

theorem actual_original_unit_density_precision_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (density (var 0) (var 9) (var 2) (var 4) (var 5) (var 6) (var 7))
        (density (var 1) (var 9) (var 2) (var 4) (var 5) (var 6) (var 7))
        (var 9*(rowGain (var 3) (var 7) (var 8)*(unit (var 0)+unit (var 1)))) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_finite_precision _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_unit_density_late_queries_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⋏
      (le (minimumQuery (var 2) (var 4) (var 8) (var 9) (var 10)) (var 0) ⋏
        le (minimumQuery (var 2) (var 4) (var 8) (var 9) (var 10)) (var 1))) ⟶
      distanceBounded (density (var 0) (var 10) (var 3) (var 5) (var 6) (var 7) (var 8))
        (density (var 1) (var 10) (var 3) (var 5) (var 6) (var 7) (var 8)) one (unit (var 2))) :=
  closeUniv 11 (.impI (original_late_queries _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionDensityPrecision

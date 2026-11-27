import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.Reindexing.GaussianRationalFiniteSumReversal
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.Densities.GaussianEulerUnitSubstitutionDensity
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionImageGrid
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Bounds.GaussianEulerUnitDecayInput

/-!
# Reversed original unit-substitution density rows and their real source

The original power and both decay endpoint observations retain the same
query and affine-grid denominator. Exact finite reversal preserves the
unchanged density sum. Every endpoint-inclusive grid time satisfies the
certified decay-input source, with T positivity derived from the actual
interval source. No row ordering, approximation, or output law is input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionReversedDensity

open_ipra
open GaussianEulerUnitSubstitutionDensity (source powerEvaluatorF)
open GaussianEulerUnitSubstitutionImageGrid (node)
open GaussianEulerIntegrandName (fixedData powerF powerData decayF decayData)
open GaussianEulerPowerIncrement (point)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub bounded)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leftIndex (N i : PTm n) : PTm n := monus N (succ i)
def rightIndex (N i : PTm n) : PTm n := monus N i
def data (p N z B a C E : PTm n) : PTm n := GaussianRationalFiniteSumReversal.data N
  (sampleData p N a C E (fixedData z B))
def coarsePowerBody : PTm 2 := GaussianRationalFiniteSumReversal.reverseBody (sampleBody powerEvaluatorF)
def coarseDensityBody : PTm 2 := GaussianRationalFiniteSumReversal.reverseBody GaussianEulerUnitSubstitutionDensity.densityBody

ipra_subst leftIndex
ipra_subst rightIndex
ipra_subst data

theorem reverse_successor (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    succ (leftIndex N i) ≐ rightIndex N i := by
  have e1 := natEq (eq_add_of_le hi)
  have e2 := natEq (eq_add_of_le (le_of_lt hi))
  apply deriveNat
  unfold leftIndex rightIndex
  ipra_simps
  linear_combination e2-e1

theorem power_row_at (i p N z B a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 coarsePowerBody i (data p N z B a C E) ≐ point p z B (a*N+C*leftIndex N i) (E*N) :=
  (GaussianRationalFiniteSumReversal.reverse_body_at (sampleBody powerEvaluatorF) i N _).eqTrans
    (GaussianEulerUnitSubstitutionDensity.power_grid_at (leftIndex N i) p N z B a C E)

/-- The two original decay observations retain their exact encoded times. -/
theorem density_row_at (i p N z B a C E : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    inst2 coarseDensityBody i (data p N z B a C E) ≐
      qmul (point p z B (a*N+C*leftIndex N i) (E*N))
        (qsub (node (leftIndex N i) p N a C E) (node (rightIndex N i) p N a C E)) := by
  have first := GaussianRationalFiniteSumReversal.reverse_body_at (Γ := Γ) GaussianEulerUnitSubstitutionDensity.densityBody i N
    (sampleData p N a C E (fixedData z B))
  rw [GaussianEulerUnitSubstitutionDensity.density_row_at] at first
  have cell := (GaussianEulerUnitSubstitutionImageGrid.cell_at (leftIndex N i) p N a C E (fixedData z B)).eqTrans
    (qsub_congr (.eqRefl _) (GaussianEulerDecayMesh.observation_numerator_congr _ _ (E*N) p
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (reverse_successor N i hi)))))
  exact first.eqTrans (qmul_congr (GaussianEulerUnitSubstitutionDensity.power_grid_at (leftIndex N i) p N z B a C E) cell)

/-- The literal original density, including its data and original query. -/
theorem original_density (p N z B a C E : PTm n) : Γ ⊢[PRAAx]
    sum coarseDensityBody N (data p N z B a C E) ≐ GaussianEulerUnitSubstitutionDensity.density p N z B a C E :=
  GaussianRationalFiniteSumReversal.sum_reverse GaussianEulerUnitSubstitutionDensity.densityBody N _

theorem top_positive (z R B a C E T N : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx] le one T := by
  have bound : Γ ⊢[PRAAx] le one (E*T) :=
    le_trans h.andE₁.andE₂.andE₁ (le_trans (le_add_right a C) h.andE₁.andE₂.andE₂)
  refine .orE (zero_or_succ T) ?_ ?_
  · have e : (T ≐ zero)::Γ ⊢[PRAAx] E*T ≐ zero := (congrMul (.eqRefl E) Prf.hyp0).eqTrans (mul_zero E)
    have bad : (T ≐ zero)::Γ ⊢[PRAAx] le one zero := le_congr (.eqRefl _) e bound.wk
    exact .botE _ (succ_ne_zero ((monus_zero one).eqSymm.eqTrans bad))
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred T))

/-- Endpoint-inclusive actual grid geometry supplies all unit-decay guards. -/
theorem grid_unit_source (j N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    GaussianEulerUnitDecayInput.source (a*N+C*j) (E*N) E T := by
  have here := GaussianEulerIntegrationByPartsGridObservation.grid_source j N z R B a C E T h.andE₁ h.andE₂.andE₁ hj
  exact .andI here.andE₂.andE₁.andE₂ (.andI h.andE₁.andE₁.andE₂.andE₁
    (.andI (top_positive z R B a C E T N h) here.andE₂.andE₂))

theorem left_index_bound (N i : PTm n) : Γ ⊢[PRAAx] le (leftIndex N i) N :=
  GaussianMonicResidualRadius.monus_le_left N (succ i)
theorem right_index_bound (N i : PTm n) : Γ ⊢[PRAAx] le (rightIndex N i) N :=
  GaussianMonicResidualRadius.monus_le_left N i

theorem reversed_unit_source (i N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    GaussianEulerUnitDecayInput.source (a*N+C*leftIndex N i) (E*N) E T :=
  grid_unit_source (leftIndex N i) N z R B a C E T h (left_index_bound N i)

theorem grid_power_bound (j p N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N)
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    bounded (point p z B (a*N+C*j) (E*N)) (GaussianEulerCompactPowerMajorant.majorant R E T) one := by
  have here := GaussianEulerIntegrationByPartsGridObservation.grid_source j N z R B a C E T h.andE₁ h.andE₂.andE₁ hj
  exact GaussianEulerCompactPowerMajorant.original_power_observation p z R B E T _ _ here.andE₁ here.andE₂

theorem reversed_power_bound (i p N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    bounded (inst2 coarsePowerBody i (data p N z B a C E)) (GaussianEulerCompactPowerMajorant.majorant R E T) one :=
  GaussianRationalReciprocal.bound_congr (power_row_at i p N z B a C E).eqSymm (.eqRefl _) (.eqRefl _)
    (grid_power_bound (leftIndex N i) p N z R B a C E T h (left_index_bound N i))

theorem grid_decay_real (j p N z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (node j p N a C E) ⋏ RationalGaussianEmbedding.axis (node j p N a C E) := by
  have hb := positive_product _ _ h.andE₁.andE₁.andE₂.andE₁ h.andE₂.andE₁
  exact .andI (GaussianRadiusExponentialName.sample_canonical GaussianGammaCanonicalExponent.constantF _ _ _)
    (GaussianEulerDecayRealSamples.original_observation_axis p _ _ hb)

theorem actual_original_reversed_density_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (sum coarseDensityBody (var 1) (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐
      GaussianEulerUnitSubstitutionDensity.density (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (original_density _ _ _ _ _ _ _)

theorem actual_reversed_original_density_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (lt (var 0) (var 2) ⟶ inst2 coarseDensityBody (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ≐
      qmul (point (var 1) (var 3) (var 4) (var 5*var 2+var 6*leftIndex (var 2) (var 0)) (var 7*var 2))
        (qsub (node (leftIndex (var 2) (var 0)) (var 1) (var 2) (var 5) (var 6) (var 7))
          (node (rightIndex (var 2) (var 0)) (var 1) (var 2) (var 5) (var 6) (var 7)))) :=
  closeUniv 8 (.impI (density_row_at _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_density_grid_decay_source_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 1) ⋏ le (var 0) (var 1)) ⟶
      GaussianEulerUnitDecayInput.source (var 5*var 1+var 6*var 0) (var 7*var 1) (var 7) (var 8)) :=
  closeUniv 9 (.impI (grid_unit_source _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionReversedDensity

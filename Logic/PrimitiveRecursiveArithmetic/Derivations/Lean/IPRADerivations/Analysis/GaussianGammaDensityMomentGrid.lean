import IPRADerivations.Analysis.GaussianEulerIntegerMomentGrid
import IPRADerivations.Analysis.GaussianGammaDensityMomentReference

/-!
# Actual cofinal normalized Gamma-density moment grids

Each finite observation multiplies ONE original C7 observation by the
literal t^N times base-Euler quadrature. The original shifted-Euler
cutoffs, cell count and evaluation precision are retained. A computed
outer query pays its C9 normalization factor. The finite comparison
therefore has a source-derived dyadic error, without an integral-value
or row-equivalence hypothesis.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDensityMomentGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianGammaC9Bound (majorant)
open GaussianGammaShiftTrajectory (point)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerVaryingCutoffName (evaluationPrecision cells)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "Ref" => GaussianGammaDensityMomentReference.nameF

def stage (p : PTm n) : PTm n := p+two
def outer (p R : PTm n) : PTm n := GaussianFastValueCut.exponent (majorant R) (stage p)
def cutoff (p z R B A N : PTm n) : PTm n := GaussianGammaDensityMomentReference.clock (outer p R) z R B A N
def rowQuery (p z R B A N : PTm n) : PTm n := evaluationPrecision (cutoff p z R B A N) A (R+N)
def count (p z R B A N : PTm n) : PTm n := cells (cutoff p z R B A N) A (R+N)
def observation (p z R B A N : PTm n) : PTm n := qmul
  (GaussianGammaC7Name.sample (cutoff p z R B A N) z R B)
  (GaussianCompactRiemannName.quadrature GaussianEulerIntegerMomentGrid.evaluatorF (rowQuery p z R B A N)
    (count p z R B A N) one (width (cutoff p z R B A N) A (R+N)) (etaDen (cutoff p z R B A N) A (R+N))
    (GaussianEulerIntegerMomentGrid.fixedData z B N (top (cutoff p z R B A N) A (R+N))))
@[simp] theorem subst_stage {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (stage p) = stage (Syn.subst σ p) := by simp [stage]
@[simp] theorem subst_outer {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (outer p R) = outer (Syn.subst σ p) (Syn.subst σ R) := by simp [outer]
@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (p z R B A N : PTm n) :
    Syn.subst σ (cutoff p z R B A N) = cutoff (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [cutoff]
@[simp] theorem subst_rowQuery {m : ℕ} (σ : Fin n → PTm m) (p z R B A N : PTm n) :
    Syn.subst σ (rowQuery p z R B A N) = rowQuery (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [rowQuery]
@[simp] theorem subst_count {m : ℕ} (σ : Fin n → PTm m) (p z R B A N : PTm n) :
    Syn.subst σ (count p z R B A N) = count (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [count]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B A N : PTm n) :
    Syn.subst σ (observation p z R B A N) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by
  simp [observation,top,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem outer_late (p R : PTm n) : Γ ⊢[PRAAx] le (stage p) (outer p R) := le_add_right _ _
theorem cutoff_late (p z R B A N : PTm n) : Γ ⊢[PRAAx] le (outer p R) (cutoff p z R B A N) := le_add_right _ _
theorem count_positive (p z R B A N : PTm n) : Γ ⊢[PRAAx] le one (count p z R B A N) :=
  GaussianCompactRiemannName.mesh_positive _ _ _

theorem original_reference_grid (p z R B A N : PTm n) : Γ ⊢[PRAAx]
    ap2 Ref (outer p R) (GaussianGammaDensityMomentReference.data z R B A N) ≐ qmul
      (GaussianGammaC7Name.sample (cutoff p z R B A N) z R B)
      (GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF (rowQuery p z R B A N)
        (count p z R B A N) one (width (cutoff p z R B A N) A (R+N)) (etaDen (cutoff p z R B A N) A (R+N))
        (GaussianEulerIntegrandName.fixedData (point z B N) B)) :=
  (GaussianGammaDensityMomentReference.sample_at (outer p R) z R B A N).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (GaussianEulerImproperName.actual_sampler (cutoff p z R B A N) (point z B N) (R+N) B A))

theorem row_budget (p z R B A N : PTm n) : Γ ⊢[PRAAx]
    le (two*majorant R*top (cutoff p z R B A N) A (R+N)*unit (stage p)) (unit (rowQuery p z R B A N)) := by
  let k := cutoff p z R B A N
  let T := top k A (R+N)
  have kb : Γ ⊢[PRAAx] le (majorant R*unit (stage p)) (unit k) :=
    le_trans (GaussianFastValueCut.query_budget (majorant R) (stage p))
      (GaussianExponentialReference.unit_monotone (cutoff_late p z R B A N))
  have tb : Γ ⊢[PRAAx] le T (unit T) := le_trans (le_succ_self T) (RationalClosure.succ_le_two_pow T)
  have early : Γ ⊢[PRAAx] le (succ (k+T)) (rowQuery p z R B A N) := by
    dsimp only [rowQuery,evaluationPrecision,k,T]
    ipra_le 9
  have power : Γ ⊢[PRAAx] unit (succ (k+T)) ≐ two*unit k*unit T :=
    (pw_succ two (k+T)).eqTrans ((congrMul (pw_add two k T) (.eqRefl _)).eqTrans (by dsimp only [unit]; ipra_ring))
  have grow : Γ ⊢[PRAAx] le (two*unit k*unit T) (unit (rowQuery p z R B A N)) :=
    le_congr power (.eqRefl _) (GaussianExponentialReference.unit_monotone early)
  exact le_trans (le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right two (AnalyticNumberTheory.PhiLower.le_mul_mono kb tb))) grow

theorem observation_to_reference (p z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B A N)
      (ap2 Ref (outer p R) (GaussianGammaDensityMomentReference.data z R B A N)) one (unit (stage p)) := by
  let k := cutoff p z R B A N
  let C := width k A (R+N)
  let E := etaDen k A (R+N)
  let T := top k A (R+N)
  let V := unit (rowQuery p z R B A N)
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A (R+N)
  have hv := unit_positive (Γ := Γ) (rowQuery p z R B A N)
  have hsource := GaussianGammaDensityDomain.base_gamma_source z R B A h
  have timeSource : Γ ⊢[PRAAx] GaussianEulerIntegerMomentGrid.source B one C E T :=
    .andI (.andI hsource.andE₁.andE₂.andE₁ he) (.andI (le_refl one)
      (le_congr (.eqRefl _) (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A (R+N)) (le_refl _)))
  have rows := GaussianEulerIntegerMomentGrid.original_grid_distance (rowQuery p z R B A N) (rowQuery p z R B A N)
    (count p z R B A N) z B N one C E T timeSource (count_positive p z R B A N)
  have denom := positive_product _ _ he (positive_product _ _ hv hv)
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) denom
    (GaussianGammaC9Bound.reciprocal_sample_bound k z R B hsource.andE₁) rows
  have scaled := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (.eqRefl _) (.eqRefl _) raw
  have budget : Γ ⊢[PRAAx] le ((majorant R*(C*(V+V)))*unit (stage p)) (one*(one*(E*(V*V)))) := by
    have wb := GaussianGammaCompactQuadratureBoundary.width_bound (Γ := Γ) k A (R+N)
    have rb := row_budget (Γ := Γ) p z R B A N
    ipra_le (𝔞 E*𝔞 V)*sl rb+(2*𝔞(majorant R)*𝔞(unit (stage p))*𝔞 V)*sl wb
  have fine := distance_radius_mono _ _ _ _ one (unit (stage p))
    (positive_product _ _ (le_refl one) denom) (unit_positive _) budget scaled
  exact distance_congr (.eqRefl _) (original_reference_grid p z R B A N).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ (unit_positive _) fine)

theorem actual_original_normalized_integer_moment_grid_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
      (observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (ap2 Ref (outer (var 0) (var 2)) (GaussianGammaDensityMomentReference.data (var 1) (var 2) (var 3) (var 4) (var 5)))
      one (unit (stage (var 0)))) :=
  closeUniv 6 (.impI (observation_to_reference _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDensityMomentGrid

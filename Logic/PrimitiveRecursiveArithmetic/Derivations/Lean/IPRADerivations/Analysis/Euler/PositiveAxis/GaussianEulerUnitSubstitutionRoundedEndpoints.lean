import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionLatticeGeometry
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionEndpoints
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReconstruction
import IPRADerivations.Core.CertificateTactics

/-!
# Exhaustion by the actual rounded rational unit panels

The endpoints are exactly the first and last absolute original floor cuts.
Their displacement from the unchanged decay observations is at most
1/M + 2N/2^r. The original eta/top endpoint estimates then give both an
explicit error and independent dyadic guards, with no positive-width guard.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionRoundedEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionLatticeGeometry (start count)
open GaussianEulerUnitSubstitutionFloorCuts (cut)
open GaussianEulerUnitSubstitutionTiltedNodes (reverseNode)
open GaussianEulerUnitDecayInput (clock)
open GaussianEulerUnitSubstitutionEndpoints (leftSample rightSample cutoff)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianEulerDecayMesh (observation observation_numerator_congr observation_rescale)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (radius radius_congr radius_triangle radius_mono)
open GaussianEuclideanDistanceName (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def left (k N a C E T M : PTm n) : PTm n := fraction (start k N a C E T M) M
def right (k N a C E T M : PTm n) : PTm n := fraction (start k N a C E T M+count k N a C E T M) M
def numerator (s k N E T M : PTm n) : PTm n :=
  M*unit (clock k E T)+(two*N*M+unit (clock k E T))*unit s
def denominator (s k E T M : PTm n) : PTm n := M*unit (clock k E T)*unit s
def source (k N t A R M : PTm n) : Fm PTm n :=
  GaussianEulerUnitSubstitutionFloorCuts.source k N one (width t A R) (etaDen t A R) (top t A R) M

@[simp] theorem subst_left {m : ℕ} (σ : Fin n → PTm m) (k N a C E T M : PTm n) :
    Syn.subst σ (left k N a C E T M) = left (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [left]
@[simp] theorem subst_right {m : ℕ} (σ : Fin n → PTm m) (k N a C E T M : PTm n) :
    Syn.subst σ (right k N a C E T M) = right (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [right]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (k N t A R M : PTm n) :
    (source k N t A R M).subst σ = source (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ t)
      (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ M) := by
  simp [source,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (s k N E T M : PTm n) :
    Syn.subst σ (numerator s k N E T M) = numerator (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ N)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (s k E T M : PTm n) :
    Syn.subst σ (denominator s k E T M) = denominator (Syn.subst σ s) (Syn.subst σ k)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [denominator]

/-- Both actual endpoint numerators are positive and below M, even if
both absolute cuts coincide. -/
theorem native_endpoints (k N a C E T M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) : Γ ⊢[PRAAx]
    le one (start k N a C E T M) ⋏ lt (start k N a C E T M+count k N a C E T M) M := by
  have hl := GaussianEulerUnitSubstitutionFloorCuts.original_cut_source zero k N a C E T M hs
  have hr := GaussianEulerUnitSubstitutionFloorCuts.original_cut_source N k N a C E T M hs
  exact .andI hl.andE₁.andE₁ (lt_congr
    (GaussianEulerUnitSubstitutionLatticeGeometry.absolute_from_relative N k N a C E T M hs).eqSymm
    (.eqRefl _) hr.andE₁.andE₂)

theorem left_displacement (k N a C E T M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) : Γ ⊢[PRAAx]
    radius (left k N a C E T M) (reverseNode zero (clock k E T) N a C E)
      (two*N*M+unit (clock k E T)) (M*unit (clock k E T)) :=
  GaussianEulerUnitSubstitutionFloorCuts.original_displacement zero k N a C E T M hs (zero_le N)

theorem right_displacement (k N a C E T M : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionFloorCuts.source k N a C E T M) : Γ ⊢[PRAAx]
    radius (right k N a C E T M) (reverseNode N (clock k E T) N a C E)
      (two*N*M+unit (clock k E T)) (M*unit (clock k E T)) := by
  have e := GaussianEulerUnitSubstitutionLatticeGeometry.absolute_from_relative N k N a C E T M hs
  have ef : Γ ⊢[PRAAx] right k N a C E T M ≐ fraction (cut N k N a C E T M) M := by
    simpa [right,count] using Prf.eqCongr1 (fraction (var 0) (Syn.shift M)) e
  exact radius_congr ef.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerUnitSubstitutionFloorCuts.original_displacement N k N a C E T M hs (le_refl N))

private theorem denominator_congr (a b d p : PTm n) (e : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx]
    observation a b p ≐ observation a d p := by
  simpa only [GaussianEulerDecayMesh.subst_observation,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (observation (Syn.shift a) (var 0) (Syn.shift p)) e

theorem original_left_readback (p N t A R : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    reverseNode zero p N one (width t A R) (etaDen t A R) ≐ fstT (leftSample p t A R) := by
  let E := etaDen t A R
  let T := top t A R
  have e := exact_right_endpoint (Γ := Γ) t A R
  have numEq : Γ ⊢[PRAAx] one*N+width t A R*LeanProofs.IPRA.PTm.monus N zero ≐ (T*E)*N := by
    ipra_lc 𝔞 N*natEq e+𝔞 (width t A R)*natEq (monus_zero (Γ := Γ) N)
  have e₁ := observation_numerator_congr _ _ (E*N) p numEq
  have e₂ := observation_rescale (T*E) E N p (GaussianGammaIntegralCutoffs.eta_den_positive t A R) hN
  have e₃ : Γ ⊢[PRAAx] observation (T*E) E p ≐ observation (T*E) (one*E) p :=
    denominator_congr (T*E) E (one*E) p (one_mul E).eqSymm
  have e₄ : Γ ⊢[PRAAx] observation (T*E) (one*E) p ≐ observation T one p :=
    observation_rescale T one E p (le_refl one) (GaussianGammaIntegralCutoffs.eta_den_positive t A R)
  exact congrFst (e₁.eqTrans (e₂.eqTrans (e₃.eqTrans e₄)))

theorem original_right_readback (p N t A R : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    reverseNode N p N one (width t A R) (etaDen t A R) ≐ fstT (rightSample p t A R) := by
  have e : Γ ⊢[PRAAx] one*N+width t A R*LeanProofs.IPRA.PTm.monus N N ≐ one*N :=
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (monus_self N))).eqTrans (by ipra_ring)
  exact congrFst ((observation_numerator_congr _ _ (etaDen t A R*N) p e).eqTrans
    (observation_rescale one (etaDen t A R) N p (GaussianGammaIntegralCutoffs.eta_den_positive t A R) hN))

private theorem scalar_left_endpoint (p s t A R : PTm n)
    (ht : Γ ⊢[PRAAx] le (cutoff s) t) (hp : Γ ⊢[PRAAx] le (cutoff s) p) : Γ ⊢[PRAAx]
    radius (fstT (leftSample p t A R)) (fstT qzero) one (unit s) := by
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (leftSample p t A R) :=
    GaussianRadiusExponentialName.sample_canonical GaussianGammaCanonicalExponent.constantF _ p _
  have hb := GaussianEulerUnitSubstitutionEndpoints.original_left_exhaustion p s t A R ht hp
  have hd : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (leftSample p t A R) qzero one (unit s) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalReconstruction.qsub_zero_right _ hc).eqSymm
      (.eqRefl _) (.eqRefl _) hb
  exact GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ (unit_positive s) hd

theorem original_explicit_endpoints (s k N t A R M : PTm n) (hs : Γ ⊢[PRAAx] source k N t A R M)
    (hA : Γ ⊢[PRAAx] le one A) (ht : Γ ⊢[PRAAx] le (cutoff s) t)
    (hp : Γ ⊢[PRAAx] le (cutoff s) (clock k (etaDen t A R) (top t A R))) : Γ ⊢[PRAAx]
    radius (left k N one (width t A R) (etaDen t A R) (top t A R) M) (fstT qzero)
      (numerator s k N (etaDen t A R) (top t A R) M) (denominator s k (etaDen t A R) (top t A R) M) ⋏
    radius (right k N one (width t A R) (etaDen t A R) (top t A R) M) (fstT qone)
      (numerator s k N (etaDen t A R) (top t A R) M) (denominator s k (etaDen t A R) (top t A R) M) := by
  let E := etaDen t A R
  let T := top t A R
  let p := clock k E T
  have hN := hs.andE₂.andE₁
  have leftEnd := radius_congr (original_left_readback p N t A R hN).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (scalar_left_endpoint p s t A R ht hp)
  have rightEnd := radius_congr (original_right_readback p N t A R hN).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ one (unit s) (unit_positive s)
      (GaussianEulerUnitSubstitutionEndpoints.original_right_exhaustion p s t A R hA ht))
  exact .andI (radius_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring) (by unfold denominator; ipra_ring)
    (radius_triangle _ _ _ _ _ _ _ (left_displacement k N one (width t A R) E T M hs) leftEnd))
    (radius_congr (.eqRefl _) (.eqRefl _) (by unfold numerator; ipra_ring) (by unfold denominator; ipra_ring)
      (radius_triangle _ _ _ _ _ _ _ (right_displacement k N one (width t A R) E T M hs) rightEnd))

def dyadicSource (s k N t A R M : PTm n) : Fm PTm n :=
  source k N t A R M ⋏ (le one A ⋏
    (le (cutoff (cutoff s)) t ⋏
      (le (cutoff (cutoff s)) (clock k (etaDen t A R) (top t A R)) ⋏
        (le (unit (cutoff s)) M ⋏
          le (two*N*unit (cutoff s)) (unit (clock k (etaDen t A R) (top t A R)))))))

@[simp] theorem subst_dyadicSource {m : ℕ} (σ : Fin n → PTm m) (s k N t A R M : PTm n) :
    (dyadicSource s k N t A R M).subst σ = dyadicSource (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ N)
      (Syn.subst σ t) (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ M) := by
  simp [dyadicSource,etaDen,top,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]

theorem endpoint_budget (s k N E T M : PTm n)
    (hM : Γ ⊢[PRAAx] le (unit (cutoff s)) M)
    (hU : Γ ⊢[PRAAx] le (two*N*unit (cutoff s)) (unit (clock k E T))) : Γ ⊢[PRAAx]
    le (numerator (cutoff s) k N E T M*unit s) (denominator (cutoff s) k E T M) := by
  have hS := GaussianEulerUnitSubstitutionEndpoints.requested_budget (Γ := Γ) s
  unfold numerator denominator
  ipra_le 𝔞 (M*unit s)*sl hU+𝔞 (unit (clock k E T)*unit s)*sl hM+
    𝔞 (M*unit (clock k E T))*sl hS

/-- Separate late choices for the original cutoff, original decay query,
lattice denominator and entire tilt give the requested neighborhoods. -/
theorem original_dyadic_endpoints (s k N t A R M : PTm n)
    (hs : Γ ⊢[PRAAx] dyadicSource s k N t A R M) : Γ ⊢[PRAAx]
    radius (left k N one (width t A R) (etaDen t A R) (top t A R) M) (fstT qzero) one (unit s) ⋏
    radius (right k N one (width t A R) (etaDen t A R) (top t A R) M) (fstT qone) one (unit s) := by
  have explicit := original_explicit_endpoints (cutoff s) k N t A R M hs.andE₁ hs.andE₂.andE₁
    hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₁
  have hM := hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have hU := hs.andE₂.andE₂.andE₂.andE₂.andE₂
  have hM1 : Γ ⊢[PRAAx] le one M := le_trans (unit_positive (cutoff s)) hM
  have hd : Γ ⊢[PRAAx] le one (denominator (cutoff s) k (etaDen t A R) (top t A R) M) :=
    positive_product _ _ (positive_product _ _ hM1 (unit_positive _)) (unit_positive _)
  have budget := endpoint_budget s k N (etaDen t A R) (top t A R) M hM hU
  exact .andI (radius_mono _ _ _ _ _ _ hd explicit.andE₁
    (le_congr (.eqRefl _) (one_mul _).eqSymm budget))
    (radius_mono _ _ _ _ _ _ hd explicit.andE₂
      (le_congr (.eqRefl _) (one_mul _).eqSymm budget))

theorem actual_original_rounded_unit_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (dyadicSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      radius (left (var 1) (var 2) one (width (var 3) (var 4) (var 5))
        (etaDen (var 3) (var 4) (var 5)) (top (var 3) (var 4) (var 5)) (var 6)) (fstT qzero) one (unit (var 0)) ⋏
      radius (right (var 1) (var 2) one (width (var 3) (var 4) (var 5))
        (etaDen (var 3) (var 4) (var 5)) (top (var 3) (var 4) (var 5)) (var 6)) (fstT qone) one (unit (var 0))) :=
  closeUniv 7 (.impI (original_dyadic_endpoints _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionRoundedEndpoints

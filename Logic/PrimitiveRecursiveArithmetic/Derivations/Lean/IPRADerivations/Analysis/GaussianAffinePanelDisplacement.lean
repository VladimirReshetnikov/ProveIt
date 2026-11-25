import IPRADerivations.Analysis.GaussianScalarDifferenceEmbedding
import IPRADerivations.Analysis.GaussianCompactRiemannName
import IPRADerivations.Analysis.RationalCubeInfimumIntervals
import IPRADerivations.Core.CertificateTactics

/-!
# Exact displacement geometry for two native affine panels

Both panels retain their common denominator and the actual original grid
encodings. Symmetric native bounds on their two endpoint numerators
bound every common-count node by A/M and the scalar widths by 2A/M.
Starts and widths may be zero; no evaluator or analytic estimate is input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianAffinePanelDisplacement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (grid value)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalValueBounds (radius radius_of_upper radius_congr radius_cancel)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def endpointSource (a C b D A : PTm n) : Fm PTm n :=
  (le a (b+A) ⋏ le b (a+A)) ⋏ (le (a+C) (b+D+A) ⋏ le (b+D) (a+C+A))
@[simp] theorem subst_endpointSource {m : ℕ} (σ : Fin n → PTm m) (a C b D A : PTm n) :
    (endpointSource a C b D A).subst σ = endpointSource (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ b) (Syn.subst σ D) (Syn.subst σ A) := by simp [endpointSource]

theorem convex_upper (j N a C b D A : PTm n) (hj : Γ ⊢[PRAAx] le j N)
    (h0 : Γ ⊢[PRAAx] le a (b+A)) (h1 : Γ ⊢[PRAAx] le (a+C) (b+D+A)) : Γ ⊢[PRAAx]
    le (a*N+C*j) (b*N+D*j+A*N) := by
  have sum := add_le_add₂ (mul_le_mul_right (monus N j) h0) (mul_le_mul_right j h1)
  apply le_congr _ _ sum
  · ipra_lc -(𝔞 a)*natEq (eq_add_of_le hj)
  · ipra_lc -(𝔞 b+𝔞 A)*natEq (eq_add_of_le hj)

theorem grid_native_bounds (j N a C b D A : PTm n) (hj : Γ ⊢[PRAAx] le j N)
    (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    le (a*N+C*j) (b*N+D*j+A*N) ⋏ le (b*N+D*j) (a*N+C*j+A*N) :=
  .andI (convex_upper j N a C b D A hj h.andE₁.andE₁ h.andE₂.andE₁)
    (convex_upper j N b D a C A hj h.andE₁.andE₂ h.andE₂.andE₂)

theorem width_native_bounds (a C b D A : PTm n) (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    le C (D+two*A) ⋏ le D (C+two*A) := by
  exact .andI (by ipra_le sl h.andE₂.andE₁+sl h.andE₁.andE₂)
    (by ipra_le sl h.andE₂.andE₂+sl h.andE₁.andE₁)

theorem common_fraction_upper (x y P M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] le x (y+P)) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fraction x M) (fraction y M) P M := by
  have eq := natEq (eq_add_of_le h)
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat x) (ZT.ofNat y) M M P M hM hM
    (fraction_represents x M hM) (fraction_represents y M hM)
  apply zle_of_toZ (M*M*monus (y+P) x)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -(𝔞 M)^2*eq

theorem common_fraction_radius (x y P M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hxy : Γ ⊢[PRAAx] le x (y+P)) (hyx : Γ ⊢[PRAAx] le y (x+P)) : Γ ⊢[PRAAx]
    radius (fraction x M) (fraction y M) P M :=
  radius_of_upper _ _ _ _ (common_fraction_upper x y P M hM hxy) (common_fraction_upper y x P M hM hyx)

theorem grid_scalar_radius (j N a C b D M A : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le j N) (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    radius (fraction (a*N+C*j) (M*N)) (fraction (b*N+D*j) (M*N)) A M := by
  have native := grid_native_bounds j N a C b D A hj h
  have coarse := common_fraction_radius (a*N+C*j) (b*N+D*j) (A*N) (M*N)
    (positive_product _ _ hM hN) native.andE₁ native.andE₂
  exact radius_cancel _ _ A M N hN
    (radius_congr (.eqRefl _) (.eqRefl _) (mul_comm A N) (mul_comm M N) coarse)

theorem grid_fraction_distance (j N a C b D M A : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le j N) (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.fraction (a*N+C*j) (M*N))
      (GaussianPositiveRationalLogarithm.fraction (b*N+D*j) (M*N)) A M :=
  distance_congr (GaussianEulerDecayOrder.fraction_embedding _ _ (positive_product _ _ hM hN))
    (GaussianEulerDecayOrder.fraction_embedding _ _ (positive_product _ _ hM hN)) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hM (grid_scalar_radius j N a C b D M A hM hN hj h))

/-- Actual original Gaussian grid values, including both endpoint indices. -/
theorem grid_distance (j N a C b D M A : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] le j N) (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    distanceBounded (value (grid j N a C M)) (value (grid j N b D M)) A M :=
  distance_congr (GaussianCompactRiemannName.value_grid j N a C M).eqSymm
    (GaussianCompactRiemannName.value_grid j N b D M).eqSymm (.eqRefl _) (.eqRefl _)
    (grid_fraction_distance j N a C b D M A hM hN hj h)

theorem width_radius (a C b D M A : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    radius (fraction C M) (fraction D M) (two*A) M :=
  common_fraction_radius C D (two*A) M hM (width_native_bounds a C b D A h).andE₁ (width_native_bounds a C b D A h).andE₂

theorem width_distance (a C b D M A : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] endpointSource a C b D A) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.fraction C M) (GaussianPositiveRationalLogarithm.fraction D M) (two*A) M :=
  distance_congr (GaussianEulerDecayOrder.fraction_embedding _ _ hM) (GaussianEulerDecayOrder.fraction_embedding _ _ hM)
    (.eqRefl _) (.eqRefl _) (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hM (width_radius a C b D M A hM h))

theorem actual_same_count_affine_panel_displacement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (((le one (var 6) ⋏ le one (var 1)) ⋏ (le (var 0) (var 1) ⋏ endpointSource (var 2) (var 3) (var 4) (var 5) (var 7))) ⟶
      distanceBounded (value (grid (var 0) (var 1) (var 2) (var 3) (var 6)))
        (value (grid (var 0) (var 1) (var 4) (var 5) (var 6))) (var 7) (var 6)) :=
  closeUniv 8 (.impI (grid_distance _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_affine_panel_scalar_width_displacement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 4) ⋏ endpointSource (var 0) (var 1) (var 2) (var 3) (var 5)) ⟶
      radius (fraction (var 1) (var 4)) (fraction (var 3) (var 4)) (two*var 5) (var 4)) :=
  closeUniv 6 (.impI (width_radius _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianAffinePanelDisplacement

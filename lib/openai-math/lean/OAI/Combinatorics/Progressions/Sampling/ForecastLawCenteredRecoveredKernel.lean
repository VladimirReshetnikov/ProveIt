import OAI.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW
local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

variable {d : ℕ} (e : Fin d ≃ Σ j, J j) (c : (Σ j, J j) → ℝ)

private theorem centeredTagCoordinates_lipschitz :
    LipschitzWith 1 (fun y : Fin d → ℝ => fun a => y (e.symm a) + c a) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  simpa only [dist_add_right] using dist_le_pi_dist y z (e.symm a)

private def centeredTagPullback (f : ((Σ j, J j) → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun y => f (fun a => y (e.symm a) + c a)

private theorem centeredTagPullback_lipschitz {L : ℝ≥0}
    {f : ((Σ j, J j) → ℝ) → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (centeredTagPullback e c f) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  exact (hf.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one, one_mul] using
        (centeredTagCoordinates_lipschitz e c).dist_le_mul y z) L.coe_nonneg)

noncomputable def forecastLawCenteredRecoveredKernel
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) : ℝ :=
  centeredTagPullback e c (kernel v r (fun a => β (e.symm a))) y

local notation "centered" => forecastLawCenteredRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW e c

theorem forecastLawCenteredRecoveredKernel_lift_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) :
    LipschitzWith (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j))))
      (centered v r β) := by
  exact centeredTagPullback_lipschitz e c
    (forecastLawRecoveredKernel_lift_lipschitz B U basis S law density selected sample x
      active Y N volume base physicalN τ o hb bW hR C hC K hK hdensity hcap v r
      (fun a => β (e.symm a)))

theorem forecastLawCenteredRecoveredKernel_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    LipschitzWith (Rcap * (Dlip * ⟨8 / τ, by positivity⟩))
      (fun v => centered v r β y) :=
  forecastLawRecoveredKernel_spatial_lipschitz B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW hτ hdensity hcap r
    (fun a => β (e.symm a)) (fun a => y (e.symm a) + c a)

theorem forecastLawCenteredRecoveredKernel_mem_Icc
    {Dcap Rcap : ℝ≥0} (hdensity : ∀ y, density y ∈ Set.Icc (0 : ℝ) Dcap)
    (hV : 0 ≤ volume) (hcap : ∀ r β, rat r β ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (y : Fin d → ℝ) :
    centered v r β y ∈ Set.Icc (0 : ℝ) (Dcap * Rcap : ℝ≥0) :=
  forecastLawRecoveredKernel_mem_Icc B U basis S law density selected sample x active Y N volume
    base physicalN τ o hb bW hdensity hV hcap v r
    (fun a => β (e.symm a)) (fun a => y (e.symm a) + c a)

theorem forecastLawCenteredRecoveredKernel_recovered_invariant {d' : ℕ}
    (M : Fin d → Fin d' → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (N : ℤ) ∣ M i a)
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) (k : Fin d' → ℤ) :
    centered v r (recoveredIntegerLift M β k) = centered v r β := by
  have heq : (fun a => recoveredIntegerLift M β k (e.symm a)) =
      recoveredLayeredIntegerLift e M (fun a => β (e.symm a)) k := by
    funext a
    change recoveredIntegerLift M β k (e.symm a) =
      recoveredIntegerLift M (fun i => β (e.symm (e i))) k (e.symm a)
    have hb : (fun i => β (e.symm (e i))) = β := by
      funext i
      rw [e.symm_apply_apply]
    rw [hb]
  unfold forecastLawCenteredRecoveredKernel
  rw [heq, forecastLawRecoveredKernel_recovered_invariant B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW e M hcol hdiv]

end Erdos3.VectorPolynomial

end

end OAI

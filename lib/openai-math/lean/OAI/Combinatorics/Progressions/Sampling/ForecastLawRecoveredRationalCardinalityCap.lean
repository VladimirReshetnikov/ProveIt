import OAI.Combinatorics.Progressions.Lattices.RecoveredLatticeMatrixInvariance
import OAI.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators NNReal Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

noncomputable def forecastFrozenIntegerMixedValue
    (z : ∀ j, Fin (n j) → ℤ) (v : (Σ j, J j) → ℝ) :
    ∀ j, (I j → ℝ) × (Fin (n j) → ℤ) :=
  fun j => ((mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
    ((EuclideanSpace.equiv (J j) ℝ).symm (fun i => v ⟨j,i⟩))).1, z j)

private theorem taggedAmbient_lipschitz :
    LipschitzWith 1 (fun v : (Σ j, J j) → ℝ =>
      fun a : JetAmbientIndex (fun _ : Fin m => Unit) J => v ⟨a.1,a.2.2⟩) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).mpr (fun a => dist_le_pi_dist v w ⟨a.1,a.2.2⟩)

theorem forecastFrozenIntegerMixedValue_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (z : ∀ j, Fin (n j) → ℤ) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (fun v => allocatedFullMixedSiteValue (R := R) U b
        (forecastFrozenIntegerMixedValue U b o z v)) := by
  have hf := (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK).comp
    (taggedAmbient_lipschitz (J := J))
  apply LipschitzWith.of_dist_le_mul
  intro v w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, i | i⟩
  · have h := (dist_le_pi_dist _ _ (⟨j, Sum.inl i⟩ : LayerSamplerAxis I n)).trans
      (hf.dist_le_mul v w)
    simpa only [Function.comp_apply, allocatedFullAmbientSiteCoordinates,
      allocatedFullMixedSiteValue, forecastFrozenIntegerMixedValue, Sum.elim_inl,
      mul_one] using h
  · change dist ((z j i : ℝ) / _ / _) ((z j i : ℝ) / _ / _) ≤ _
    simp only [dist_self]
    positivity

theorem forecastFrozenIntegerActiveCoordinates_lipschitz
    (inactive : LayerSamplerAxis I n → Prop)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (z : ∀ j, Fin (n j) → ℤ) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (fun v => forecastNormalizedActiveCoordinates inactive
        (allocatedFullMixedSiteValue (R := R) U b
          (forecastFrozenIntegerMixedValue U b o z v))) := by
  simpa only [one_mul, Function.comp_def] using (forecastNormalizedActiveCoordinates_lipschitz inactive).comp
    (forecastFrozenIntegerMixedValue_lipschitz U b o hR C hC K hK z)

end Erdos3.VectorPolynomial

end

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

noncomputable def forecastRecoveredIntegerLabels (β : (Σ j, J j) → ℤ) :
    ∀ j, Fin (n j) ⊕ Eout j → ℤ :=
  fun j => standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
    (fun i => β ⟨j,i⟩)

noncomputable def forecastLawRecoveredRationalFactor
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) : ℝ :=
  rationalInactiveForecast law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume
    (fun a _ => forecastRecoveredIntegerLabels U basis hb bW β (selected a).1
      (Sum.inl (selected a).2))
    (forecastCongruenceOutput short r
      (fun j i => (forecastRecoveredIntegerLabels U basis hb bW β j i : ZMod N)))

noncomputable def forecastLawRecoveredKernel
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ)
    (y : (Σ j, J j) → ℝ) : ℝ :=
  density (forecastNormalizedSpatialCoordinates base physicalN τ v,
    forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis
        (forecastFrozenIntegerMixedValue U basis o
          (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y))) *
    forecastLawRecoveredRationalFactor B U basis S law selected sample x active Y N volume hb bW r β

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW
local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawRecoveredRationalFactor_nonneg (hV : 0 ≤ volume)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) : 0 ≤ rat r β :=
  rationalInactiveForecast_nonneg _ _ _ _ N hV _ _

theorem forecastLawRecoveredKernel_mem_Icc
    {Dcap Rcap : ℝ≥0} (hdensity : ∀ y, density y ∈ Set.Icc (0 : ℝ) Dcap)
    (hV : 0 ≤ volume) (hcap : ∀ r β, rat r β ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ)
    (y : (Σ j, J j) → ℝ) :
    kernel v r β y ∈ Set.Icc (0 : ℝ) (Dcap * Rcap : ℝ≥0) := by
  exact ⟨mul_nonneg (hdensity _).1
    (forecastLawRecoveredRationalFactor_nonneg B U basis S law selected sample x active Y N
      volume hb bW hV r β),
    mul_le_mul (hdensity _).2 (hcap r β)
      (forecastLawRecoveredRationalFactor_nonneg B U basis S law selected sample x active Y N
        volume hb bW hV r β) Dcap.coe_nonneg⟩

theorem forecastLawRecoveredKernel_lift_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ) :
    LipschitzWith (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j))))
      (kernel v r β) := by
  have hc := forecastFrozenIntegerActiveCoordinates_lipschitz U basis o short hR C hC K hK
    (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i))
  have hpair := (LipschitzWith.const (forecastNormalizedSpatialCoordinates base physicalN τ v)).prodMk hc
  have hd := hdensity.comp hpair
  apply LipschitzWith.of_dist_le_mul
  intro y z
  change |density _ * rat r β - density _ * rat r β| ≤ _
  rw [← sub_mul, abs_mul, mul_comm]
  calc
    _ ≤ (Rcap : ℝ) * |density _ - density _| :=
      mul_le_mul_of_nonneg_right (hcap r β) (abs_nonneg _)
    _ ≤ (Rcap : ℝ) * ((Dlip * (K * ∑ j, C j * Fintype.card (J j)) : ℝ≥0) * dist y z) := by
      apply mul_le_mul_of_nonneg_left _ Rcap.coe_nonneg
      simpa only [Function.comp_apply, zero_max, Real.dist_eq] using hd.dist_le_mul y z
    _ = _ := by simp only [NNReal.coe_mul]; ring

theorem forecastLawRecoveredKernel_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ) :
    LipschitzWith (Rcap * (Dlip * ⟨8 / τ, by positivity⟩)) (fun v => kernel v r β y) := by
  have hc := forecastNormalizedSpatialCoordinates_lipschitz base physicalN hτ
  have hpair := hc.prodMk (LipschitzWith.const
    (forecastNormalizedActiveCoordinates short
      (allocatedFullMixedSiteValue (R := R) U basis
        (forecastFrozenIntegerMixedValue U basis o
          (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y))))
  have hd := hdensity.comp hpair
  apply LipschitzWith.of_dist_le_mul
  intro v w
  change |density _ * rat r β - density _ * rat r β| ≤ _
  rw [← sub_mul, abs_mul, mul_comm]
  calc
    _ ≤ (Rcap : ℝ) * |density _ - density _| :=
      mul_le_mul_of_nonneg_right (hcap r β) (abs_nonneg _)
    _ ≤ (Rcap : ℝ) * ((Dlip * ⟨8 / τ, by positivity⟩ : ℝ≥0) * dist v w) := by
      apply mul_le_mul_of_nonneg_left _ Rcap.coe_nonneg
      simpa only [Function.comp_apply, max_eq_left (show (0 : ℝ≥0) ≤ ⟨8 / τ, by positivity⟩ from bot_le), Real.dist_eq] using hd.dist_le_mul v w
    _ = _ := by simp only [NNReal.coe_mul]; ring

end Erdos3.VectorPolynomial

end

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

local notation "labels" => forecastRecoveredIntegerLabels U basis hb bW
local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW
local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawRecoveredRationalFactor_eq_of_labels
    (β γ : (Σ j, J j) → ℤ)
    (htrans : ∀ j i, labels β j (Sum.inl i) = labels γ j (Sum.inl i))
    (hres : ∀ j i, (labels β j i : ZMod N) = (labels γ j i : ZMod N))
    (r : X → ZMod N) : rat r β = rat r γ := by
  have hg : (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
      labels β (selected a).1 (Sum.inl (selected a).2)) =
      (fun a (_ : (Finset.univ : Finset (Finset Empty))) =>
        labels γ (selected a).1 (Sum.inl (selected a).2)) := by
    funext a t
    exact htrans (selected a).1 (selected a).2
  have hr : (fun j i => (labels β j i : ZMod N)) =
      (fun j i => (labels γ j i : ZMod N)) := by
    funext j i
    exact hres j i
  unfold forecastLawRecoveredRationalFactor
  rw [hg, hr]

theorem forecastLawRecoveredKernel_eq_of_labels
    (β γ : (Σ j, J j) → ℤ)
    (htrans : ∀ j i, labels β j (Sum.inl i) = labels γ j (Sum.inl i))
    (hres : ∀ j i, (labels β j i : ZMod N) = (labels γ j i : ZMod N))
    (v : X → ℝ) (r : X → ZMod N) : kernel v r β = kernel v r γ := by
  have hz : (fun j i => labels β j (Sum.inl i)) =
      (fun j i => labels γ j (Sum.inl i)) := by
    funext j i
    exact htrans j i
  funext y
  unfold forecastLawRecoveredKernel
  rw [hz, forecastLawRecoveredRationalFactor_eq_of_labels B U basis S law selected sample x
    active Y N volume hb bW β γ htrans hres r]

theorem forecastLawRecoveredKernel_recovered_invariant {d d' : ℕ}
    (e : Fin d ≃ Σ j, J j) (M : Fin d → Fin d' → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (N : ℤ) ∣ M i a)
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ) (k : Fin d' → ℤ) :
    kernel v r (recoveredLayeredIntegerLift e M β k) = kernel v r β := by
  apply forecastLawRecoveredKernel_eq_of_labels B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW
  · intro j i
    exact congrFun (recoveredIntegerTransverse_layer_matrix U bW basis hb e M hcol β k j) i
  · intro j i
    exact congrFun (standardLatticeCoordinates_layer_matrix_residue U bW basis hb e M N
      hdiv β k j) i

end Erdos3.VectorPolynomial

end

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

local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW
local notation "labels" => forecastRecoveredIntegerLabels U basis hb bW
local notation "mixed" => forecastFrozenIntegerMixedValue U basis o

theorem forecastLawDensityPhysicalDeckSource_eq_recoveredKernel
    (u : X → ℤ) (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ) :
    forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x active Y N volume
      base physicalN τ u
      (mixed (fun j i => labels β j (Sum.inl i)) y)
      (fun j i => labels β j (Sum.inr i)) =
      (kernel (fun i => (u i : ℝ) / physicalN i) (fun i => (u i : ZMod N)) β y : ℂ) := by
  unfold forecastLawDensityPhysicalDeckSource forecastLawRecoveredKernel
  rw [Complex.ofReal_mul]
  apply congrArg₂ (fun v w : ℝ => (v : ℂ) * (w : ℂ))
  · apply congrArg density
    apply Prod.ext
    · funext a
      exact (forecastNormalizedSpatialCoordinates_eval base u physicalN τ a).symm
    · rfl
  · unfold forecastLawRecoveredRationalFactor
    apply congrArg (rationalInactiveForecast law active
      (forecastInactiveFixedOutput B U basis S selected
        (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
      Y N volume (fun a _ => labels β (selected a).1 (Sum.inl (selected a).2)))
    rw [forecastCongruenceOutput_intCast]
    apply congrArg (forecastCongruenceOutput short (fun i => (u i : ZMod N)))
    funext j i
    cases i <;> rfl

omit [Fintype X] in
theorem forecastRecoveredPhysicalDeck
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ)
    (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ)
    (hpoint : ∀ j i, y ⟨j,i⟩ + (β ⟨j,i⟩ : ℝ) =
      eval (fun i => (u i : ℝ)) (poly j) i) (j : Fin m) :
    normalizedLatticeRepresentative (euclideanSubspace (U j)) (basis j) (hb j)
        (orthonormalMixedChart (o j)
          (forecastFrozenIntegerMixedValue U basis o
            (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y j)) +
        ((bW j).equivFun.symm
          (fun i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inr i))).val =
      physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j := by
  let v : EuclideanSpace ℝ (J j) :=
    (EuclideanSpace.equiv (J j) ℝ).symm (fun i => y ⟨j,i⟩)
  have hv : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val =
      (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).val := by
    ext i
    rw [physicalEuclideanSitePoint_apply]
    exact hpoint j i
  have hm : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val ∈
      euclideanSubspace (U j) := by
    rw [hv]
    exact (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).property
  change normalizedLatticeRepresentative _ _ _
      (orthonormalMixedChart (o j)
        (recoveredMixedCoordinates (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
          (o j) v (fun i => β ⟨j,i⟩))) +
      ((bW j).equivFun.symm
        (recoveredIntegerDeck (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
          (fun i => β ⟨j,i⟩))).val = _
  rw [recoveredMixedCoordinates_deck _ _ _ _ _ _ _ hm]
  apply Subtype.ext
  exact hv

omit [Fintype X] in
theorem forecastRecoveredPhysicalPoint
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ)
    (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ)
    (hpoint : ∀ j i, y ⟨j,i⟩ + (β ⟨j,i⟩ : ℝ) =
      eval (fun i => (u i : ℝ)) (poly j) i) (j : Fin m) :
    normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
        (orthonormalMixedChart (o j)
          (forecastFrozenIntegerMixedValue U basis o
            (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i)) y j)) =
      (EuclideanSpace.equiv (J j) ℝ).symm (fun i => y ⟨j,i⟩) := by
  let v : EuclideanSpace ℝ (J j) :=
    (EuclideanSpace.equiv (J j) ℝ).symm (fun i => y ⟨j,i⟩)
  have hv : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val =
      (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).val := by
    ext i
    rw [physicalEuclideanSitePoint_apply]
    exact hpoint j i
  have hm : v + (standardEuclideanPoint (J j) (fun i => β ⟨j,i⟩)).val ∈
      euclideanSubspace (U j) := by
    rw [hv]
    exact (physicalEuclideanSitePoint U poly hpoly (fun i => (u i : ℝ)) j).property
  exact recoveredMixedCoordinates_point (euclideanSubspace (U j)) (bW j) (basis j) (hb j)
    (o j) v (fun i => β ⟨j,i⟩) hm

theorem forecastLawDensityPhysicalTarget_eq_recoveredKernel
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ)
    (β : (Σ j, J j) → ℤ) (y : (Σ j, J j) → ℝ)
    (hpoint : ∀ j i, y ⟨j,i⟩ + (β ⟨j,i⟩ : ℝ) = eval (fun i => (u i : ℝ)) (poly j) i)
    (hquarter : ∀ a, |y a| ≤ 1 / 4) :
    forecastLawDensityPhysicalTarget B U basis S law density selected sample x active Y N volume
      base physicalN τ o hb bW poly hpoly u =
      (kernel (fun i => (u i : ℝ) / physicalN i) (fun i => (u i : ZMod N)) β y : ℂ) := by
  let w := mixed (fun j i => labels β j (Sum.inl i)) y
  let deck := fun j i => labels β j (Sum.inr i)
  have hdeck := forecastRecoveredPhysicalDeck U basis o hb bW poly hpoly u β y hpoint
  have hsmall (j : Fin m) (i : J j) :
      |normalizedLatticePoint (euclideanSubspace (U j)) (basis j)
        (orthonormalMixedChart (o j) (w j)) i| ≤ 1 / 4 := by
    have hp := forecastRecoveredPhysicalPoint U basis o hb bW poly hpoly u β y hpoint j
    change |normalizedLatticePoint _ _ _ i| ≤ _
    rw [hp]
    exact hquarter ⟨j, i⟩
  exact (forecastLawDensityPhysicalTarget_integer_deck B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW poly hpoly u w deck hdeck hsmall).trans
      (forecastLawDensityPhysicalDeckSource_eq_recoveredKernel B U basis S law density selected
        sample x active Y N volume base physicalN τ o hb bW u β y)

end Erdos3.VectorPolynomial

end

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

theorem forecastLawRecoveredRationalFactor_le_of_decay
    {Icap C P : ℝ} (hV : 0 ≤ volume) (hC : 0 ≤ C)
    (hgrid : ∀ z : A → ℤ,
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun t j => (Y i t j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) :
    rat r β ≤ Icap * (1 + C) := by
  let z : A → ℤ := fun a => forecastRecoveredIntegerLabels U basis hb bW β
    (selected a).1 (Sum.inl (selected a).2)
  exact (rationalInactiveForecast_cap law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N hV hC hP hdecay (fun a _ => z a) _).trans
      (mul_le_mul_of_nonneg_right (hgrid z) (add_nonneg zero_le_one hC))

theorem forecastLawRecoveredRationalFactor_abs_le_of_decay
    {Icap C P : ℝ} (hV : 0 ≤ volume) (hC : 0 ≤ C)
    (hgrid : ∀ z : A → ℤ,
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        (fun a _ => z a) (fun _ => 1) ≤ Icap)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun t j => (Y i t j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) :
    |rat r β| ≤ Icap * (1 + C) := by
  rw [abs_of_nonneg (forecastLawRecoveredRationalFactor_nonneg B U basis S law selected sample x
    active Y N volume hb bW hV r β)]
  exact forecastLawRecoveredRationalFactor_le_of_decay B U basis S law selected sample x
    active Y N volume hb bW hV hC hgrid hP hdecay r β

end Erdos3.VectorPolynomial

end

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

theorem forecastLawRecoveredRationalFactor_le_exp_of_grid_modulus
    {Pgrid Pmod : ℝ} (hV : 0 ≤ volume)
    (hgrid : ∀ z : A → ℤ,
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        (fun a _ => z a) (fun _ => 1) ≤ Real.exp Pgrid)
    (hN : (N : ℝ) ≤ Real.exp Pmod)
    (r : X → ZMod N) (β : (Σ j, J j) → ℤ) :
    rat r β ≤ Real.exp (Pgrid + (Fintype.card Out : ℝ) * Pmod) := by
  have hgridAll (z : A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) :
      volume * law.fiberMean
        (forecastInactiveFixedOutput B U basis S selected
          (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
        z (fun _ => 1) ≤ Real.exp Pgrid := by
    have hz : z = (fun a _ => z a ⟨∅, Finset.mem_univ _⟩) := by
      funext a row
      exact congrArg (z a) (Subsingleton.elim _ _)
    rw [hz]
    exact hgrid (fun a => z a ⟨∅, Finset.mem_univ _⟩)
  exact rationalInactiveForecast_le_exp_of_grid_modulus law active
    (forecastInactiveFixedOutput B U basis S selected
      (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N hV hgridAll hN _ _

end Erdos3.VectorPolynomial

end

end OAI

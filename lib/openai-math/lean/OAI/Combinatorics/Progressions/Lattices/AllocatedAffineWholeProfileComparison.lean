import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedFiniteModelComparison
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineLogEnvelope
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineProfileMeanTransport
import OAI.Combinatorics.Progressions.Lattices.EarlyAllocatedAffineResidueSource
import OAI.Combinatorics.Progressions.Probability.AllocatedProgressionDensityIdentity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "cap" => bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "lip" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap

local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "proxyRadius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedAffineIdeal_finite_reference_l1 (hσ1 : ∀ j, σ j ≤ 1)
    {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω) (F : Ω → (input → ℝ))
    (hF : ∀ v, weights.weight v ≠ 0 → ‖F v‖ ≤ 1)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (center width : input → ℝ) (hw : ∀ i, |center i| + |width i| ≤ 1)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ Cmask) {E : ℝ} :
    let ideal := diagonalImageDensity (fun o : output => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ center width)
    let discrete := fun z => weights.mean (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA (F v) z)
    let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) proxyRadius
    let Ki : ℝ≥0 := ‖(∏ o : output, |R o.1.val.1|)⁻¹‖₊ *
      (affineProductProfileLip output ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
    let select := allocatedLongIntegerSelect B U basis S (O := O)
    (∫ z, |ideal z - discrete z|) ≤ E →
    (∫ z, |allocatedLongProfileDensity B U basis S x rows modulus residue ideal z -
        allocatedLongProfileDensity B U basis S x rows modulus residue discrete z|
      ∂allocatedLongJetReference B U basis S O) ≤
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (E + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : output // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
            ((Ki : ℝ) + lip) * mesh)) := by
  intro ideal discrete radius Ki select he
  have hreg := allocatedFiniteLongJetDensity_regularity B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1 weights F hF
  have hRI (o : output) : |(R o.1.val.1)⁻¹| ≤ Real.exp P := by
    rw [abs_of_pos (inv_pos.mpr (hR o.1.val.1))]
    exact hRi _
  have hIb := activeScaledSlicedIdeal_bounds (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows a.val.1) (fun o : output => R o.1.val.1)
    (C := ⟨Real.exp P, Real.exp_nonneg _⟩) hRI ρ hρ center width
  have hispec := activeAveragedSlicedProfileIdeal_spec (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid (fun a => rows a.val.1) ρ hρ center width
  have hIi : Integrable ideal := diagonalImageDensity_integrable _
    (fun o : output => (hR o.1.val.1).ne') hispec.2.2.1
  have hIs (z : output → ℝ) (hz : radius < ‖z‖) : ideal z = 0 :=
    activeScaledSlicedIdeal_zero_outside (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid (fun a => rows a.val.1) (fun o : output => R o.1.val.1)
      (fun o => (hR o.1.val.1).ne') (Real.exp_nonneg P)
      (fun o => by simpa only [abs_of_pos (hR o.1.val.1)] using hRP o.1.val.1)
      (fun a => Nat.succ_le_of_lt a.1.isLt) ρ hρ hρone center width hw z
      ((le_max_left _ _).trans_lt hz)
  have hDs (z : output → ℝ) (hz : radius < ‖z‖) : discrete z = 0 :=
    hreg.2.2.1 z ((le_max_right _ _).trans_lt hz)
  exact allocatedLongReference_l1_comparison B U basis S x rows modulus residue
    ideal discrete ⟨radius, (Real.exp_nonneg _).trans (le_max_right _ _)⟩ hIb.2 hreg.2.1 hIs hDs
    (by positivity) (NNReal.coe_nonneg cap) hIb.1 hreg.1
    (hIi.sub hreg.2.2.2) he hmesh0 hmesh1 hscaleMesh hCmask hmask

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedAffineSourceReferenceError (ρ : ℝ≥0) (P η : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val)
      (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) → ℕ)
    (ε mesh Cmask : ℝ) : ℝ :=
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
      let cap := bound ^ Fintype.card (LayerSamplerAxis I n)
      let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound * cap
      let sourceError := η +
        ((2 * (cap : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
          (lip : ℝ) * 2) * ∑ j, (M j : ℝ) / H j + (lip : ℝ) * ε) *
          (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1)
      let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) (Real.exp (allocatedJetSupportLog (G := G) B α O P))
      let Ki : ℝ≥0 := ‖(∏ o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1), |R o.1.val.1|)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
          (sourceError + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
            ((2 * radius + 2) ^ Fintype.card {o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
              ((Ki : ℝ) + lip) * mesh))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (α : Type*) [Fintype α] [DecidableEq α] (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Outputs" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)

theorem allocatedAffineSourceReferenceError_small
    (ρ : ℝ≥0) (P : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬grid a} => B a.val)
      (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) → ℕ)
    {D L target η ε mesh Cmask : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hP : P ≤ L)
    (hdensity : allocatedDensityLog (G := G) B α O P ≤ L)
    (hsupport : allocatedJetSupportLog (G := G) B α O P ≤ L)
    (hideal : partitionedIdealRadius α m + 1 ≤ Real.exp L)
    (hKi : ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ *
      ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P) ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α))
    (hb : scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L)
    (ha : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (ho : (Fintype.card Outputs : ℝ) ≤ D)
    (hu : (Fintype.card (UnselectedColumn select) : ℝ) ≤ D)
    (hi : (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} : ℝ) ≤ D)
    (hη0 : 0 ≤ η) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hη : η ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hratio : (∑ j, (M j : ℝ) / H j) ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hε : ε ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4))) :
    allocatedAffineSourceReferenceError B U basis S α O ρ P η M H ε mesh Cmask ≤ Real.exp (-target) := by
  let cap := Real.exp (allocatedDensityLog (G := G) B α O P) ^ Fintype.card (LayerSamplerAxis I n)
  let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) * cap
  let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) (Real.exp (allocatedJetSupportLog (G := G) B α O P))
  let Ki := ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ * ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P)
  let vol := (2 * radius) ^ Fintype.card (UnselectedColumn select) *
    (2 * radius + 2) ^ Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o}
  have hc := affineReferenceCoefficient_bounds hD hL hdensity hsupport hP hideal hKi hCmask0 hCmask hb0 hb
    (Fintype.card (LayerSamplerAxis I n)) (Fintype.card Outputs)
    (Fintype.card (UnselectedColumn select))
    (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o}) ha ho hu hi
  have hc' : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (2 * cap * (scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α)) + lip * 2) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) * lip *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) * vol * (Ki + lip) ≤ Real.exp (affineReferenceCoefficientLog D L) := by
    refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
    convert hc.2.2.2 using 1
    dsimp only [vol, Ki, lip, cap, radius]
    ring
  have herr := affineReferenceError_accuracy hη0 (by positivity : 0 ≤ ∑ j, (M j : ℝ) / H j)
    hε0 hmesh0 hc' hη hratio hε hmesh
  let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
  let capNN : ℝ≥0 := bound ^ Fintype.card (LayerSamplerAxis I n)
  let lipNN : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound * capNN
  let KiNN : ℝ≥0 := ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖₊ *
    (affineProductProfileLip Outputs ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
  have hcapNN : (capNN : ℝ) = cap := rfl
  have hlipNN : (lipNN : ℝ) = lip := by
    simp only [lipNN, NNReal.coe_mul, NNReal.coe_natCast, hcapNN]
    rfl
  have hKiNN : (KiNN : ℝ) = Ki := rfl
  convert herr using 1
  change Cmask ^ Fintype.card (LayerSamplerAxis I n) *
    (η + ((2 * (capNN : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + (lipNN : ℝ) * 2) *
      (∑ j, (M j : ℝ) / H j) + (lipNN : ℝ) * ε) *
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs +
      (2 * radius) ^ Fintype.card (UnselectedColumn select) *
        ((2 * radius + 2) ^ Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
          ((KiNN : ℝ) + lipNN) * mesh)) = _
  rw [hcapNN, hlipNN, hKiNN]
  dsimp only [vol]
  ring

theorem allocatedAffineSourceReferenceError_small_separated
    (ρ : ℝ≥0) (P : ℝ)
    (M H : PrincipalTupleIndex
      (fun a : {a // ¬grid a} => B a.val)
      (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) → ℕ)
    {D L target η ε mesh Cmask earlyMaskLog : ℝ}
    (hearlyMask : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp earlyMaskLog)
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hP : P ≤ L)
    (hdensity : allocatedDensityLog (G := G) B α O P ≤ L)
    (hsupport : allocatedJetSupportLog (G := G) B α O P ≤ L)
    (hideal : partitionedIdealRadius α m + 1 ≤ Real.exp L)
    (hKi : ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ *
      ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P) ≤ Real.exp L)
    (hCmask0 : 0 ≤ Cmask) (hCmask : Cmask ≤ Real.exp L)
    (hb0 : 0 ≤ scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α))
    (hb : scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L)
    (ha : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (ho : (Fintype.card Outputs : ℝ) ≤ D)
    (hu : (Fintype.card (UnselectedColumn select) : ℝ) ≤ D)
    (hi : (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} : ℝ) ≤ D)
    (hη0 : 0 ≤ η) (hε0 : 0 ≤ ε) (hmesh0 : 0 ≤ mesh)
    (hη : η ≤ Real.exp (-(target + earlyMaskLog + 4)))
    (hratio : (∑ j, (M j : ℝ) / H j) ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hε : ε ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4)))
    (hmesh : mesh ≤ Real.exp (-(target + affineReferenceCoefficientLog D L + 4))) :
    allocatedAffineSourceReferenceError B U basis S α O ρ P η M H ε mesh Cmask ≤ Real.exp (-target) := by
  let cap := Real.exp (allocatedDensityLog (G := G) B α O P) ^ Fintype.card (LayerSamplerAxis I n)
  let lip := (Fintype.card (LayerSamplerAxis I n) : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) * cap
  let radius := max (Real.exp P * (partitionedIdealRadius α m + 1)) (Real.exp (allocatedJetSupportLog (G := G) B α O P))
  let Ki := ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖ * ((affineProductProfileLip Outputs ρ : ℝ) * Real.exp P)
  let vol := (2 * radius) ^ Fintype.card (UnselectedColumn select) *
    (2 * radius + 2) ^ Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o}
  have hc := affineReferenceCoefficient_bounds hD hL hdensity hsupport hP hideal hKi hCmask0 hCmask hb0 hb
    (Fintype.card (LayerSamplerAxis I n)) (Fintype.card Outputs)
    (Fintype.card (UnselectedColumn select))
    (Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o}) ha ho hu hi
  have hc' : Cmask ^ Fintype.card (LayerSamplerAxis I n) ≤ Real.exp earlyMaskLog ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (2 * cap * (scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α)) + lip * 2) *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) * lip *
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs ≤ Real.exp (affineReferenceCoefficientLog D L) ∧
      Cmask ^ Fintype.card (LayerSamplerAxis I n) * vol * (Ki + lip) ≤ Real.exp (affineReferenceCoefficientLog D L) := by
    refine ⟨hearlyMask, hc.2.1, hc.2.2.1, ?_⟩
    convert hc.2.2.2 using 1
    dsimp only [vol, Ki, lip, cap, radius]
    ring
  have herr := affineReferenceError_accuracy_separated hη0 (by positivity : 0 ≤ ∑ j, (M j : ℝ) / H j)
    hε0 hmesh0 hc' hη hratio hε hmesh
  let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), Real.exp_nonneg _⟩
  let capNN : ℝ≥0 := bound ^ Fintype.card (LayerSamplerAxis I n)
  let lipNN : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound * capNN
  let KiNN : ℝ≥0 := ‖(∏ o : Outputs, |R o.1.val.1|)⁻¹‖₊ *
    (affineProductProfileLip Outputs ρ * ⟨Real.exp P, Real.exp_nonneg _⟩)
  have hcapNN : (capNN : ℝ) = cap := rfl
  have hlipNN : (lipNN : ℝ) = lip := by
    simp only [lipNN, NNReal.coe_mul, NNReal.coe_natCast, hcapNN]
    rfl
  have hKiNN : (KiNN : ℝ) = Ki := rfl
  convert herr using 1
  change Cmask ^ Fintype.card (LayerSamplerAxis I n) *
    (η + ((2 * (capNN : ℝ) * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + (lipNN : ℝ) * 2) *
      (∑ j, (M j : ℝ) / H j) + (lipNN : ℝ) * ε) *
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P)) ^ Fintype.card Outputs +
      (2 * radius) ^ Fintype.card (UnselectedColumn select) *
        ((2 * radius + 2) ^ Fintype.card {o : Outputs // allocatedLongIntegerCoordinate B U basis S (O := O) o} *
          ((KiNN : ℝ) + lipNN) * mesh)) = _
  rw [hcapNN, hlipNN, hKiNN]
  dsimp only [vol]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineReferenceComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) : Prop :=
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (_hR : ∀ j, 0 < R j) (_hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      (∀ j, σ j ≤ t) →
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      ∀ (L step H M : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ℕ) (residue : ∀ j i, ZMod (modulus j i))
        (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
        (hsize : ∀ j, (Fintype.card α + 1) * M j ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (outputModulus : ℕ)
        (outputResidue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod outputModulus))
        {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j outputModulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j outputModulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let discrete := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
          (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      (∫ z, |allocatedLongProfileDensity B U basis S x rows outputModulus outputResidue ideal z -
          allocatedLongProfileDensity B U basis S x rows outputModulus outputResidue discrete z|
        ∂allocatedLongJetReference B U basis S O) ≤
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η M H ε mesh Cmask

include hrows hcard in
theorem exists_early_allocated_affine_reference_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineReferenceComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_residue_source_with_scales (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  unfold AllocatedAffineReferenceComparison
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L step H M c hL hstep hH hsubset hdense modulus residue hm hmM hsize hsmall ε hε hmesh
    outputModulus outputResidue mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal discrete
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have he := hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    L step H M c hL hstep hH hsubset hdense modulus residue hm hmM hsize hsmall hε hmesh
  let weights := FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) (M j)
    (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))
  let V := fun (v : ∀ j, IntegerScalarCubeBox α (H j)) => principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
    (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)
  have hV (v) (hv : weights.weight v ≠ 0) : ‖V v‖ ≤ 1 := by
    apply (principalTupleFlatten_norm_apply_le _ _ _ _).trans
    apply progressionTuple_norm_le L step H c hH
      (fun j => (progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
        (hsubset j) (hdense j)).2.2.1) v
    intro j
    exact scalarCubeResidueWeights_cube_support α (H j) (M j) (by have := hH j; omega)
      (modulus j) (residue j) (hm j) (hmM j) (hsize j) (v j)
      (FiniteProbabilityWeights.pi_weight_pos_component _ v
        (lt_of_le_of_ne (weights.nonneg v) (Ne.symm hv)) j)
  have hwidth := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  exact allocatedAffineIdeal_finite_reference_l1 B U basis hR hσ S x rows s hA
    hMk hi hP hMkP hRP hRi hσi hcount u hσ1 weights V hV (ρ (allocatedGridAxis (I := I) U basis S.value))
    (hρmin.trans_le (hρ (allocatedGridAxis (I := I) U basis S.value)).1) (hρ (allocatedGridAxis (I := I) U basis S.value)).2 center width (fun i => (hwidth i).2.2)
    outputModulus outputResidue hmesh0 hmesh1 hscaleMesh hCmask hmask he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineCoefficient_from_reference_l1
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1) :
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_ : 0 < Mk)
        (_ : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_ : 0 ≤ P) (_ : (Mk : ℝ) ≤ Real.exp P)
        (_ : ∀ j, R j ≤ Real.exp P) (_ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_ : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_ : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (_ : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_ : 0 ≤ ε) (_ : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (_ : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (_ : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (_ : 0 ≤ e) (_ : 0 < εcoef) (_ : εcoef⁻¹ ≤ Real.exp e)
        (_ : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (_ : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (_ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (_ : 0 ≤ mesh) (_ : mesh ≤ 1)
        (_ : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (_ : 1 ≤ Cmask)
        (_ : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      let proxy := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) modulus
          (lt_of_lt_of_le (by decide : 0 < 2) (hH j)) (fun _ => modulus) (residue j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      (∫ z, |allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z -
        allocatedLongProfileDensity B U basis S x rows modulus outputResidue proxy z|
        ∂allocatedLongJetReference B U basis S O) ≤
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask →
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law proxy href
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hw := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hg := allocatedAffineIdeal_profile_integrable B U basis hR S x rows hRP hRi
    (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρpos _) (hρone _)
    center width (fun i => (hw i).2.2) modulus outputResidue hCmask hmask
  have hlong := allocatedSlicedLongJet_ideal_transfer B U basis hR hσ S x rows
    hMk selection hx hq hrows hcard hσ1 hP he hεcoef hMkP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u H step c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset hm residue hsize
    v₀ hv₀ (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal)
    hg (Eref := allocatedAffineSourceReferenceError B U basis S α O
      (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask) href
  exact hlong

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

 theorem exists_quantitative_early_affine_reference_source
    (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a) (hblock : ∀ a, Function.Injective (block a))
    {δ η E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hηE : η⁻¹ ≤ Real.exp E) (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, 0 < ρ P ∧ ρ P ≤ 1 ∧
        (ρ P : ℝ)⁻¹ ≤ Real.exp (allocatedAffineRadiusLog (O := O) (α := α) B A T E F)) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        Real.log t⁻¹ ≤ allocatedAffineToleranceLog (G := G) (O := O) (α := α) B A T E F ∧
        AllocatedAffineReferenceComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_reference_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  have hδhalf : δ / 2 ≤ 1 := by linarith
  refine ⟨ρ, ?_, t, ht, htone, ?_, hs⟩
  · intro P
    refine ⟨hρmin.trans_le (hρ P).1, (hρ P).2, ?_⟩
    rw [hρeq P]
    exact allocatedAffineSourceRadius_inverse_bound B A T (half_pos hδ) hδhalf hη hE hF hηE hδF P
  · rw [hteq]
    exact allocatedAffineSourceTolerance_log_bound B A T (half_pos hδ) hδhalf hη hE hF hηE hδF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineCoefficientComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

include hrows hcard in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineCoefficientComparison_of_reference
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineReferenceComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t) :
    AllocatedAffineCoefficientComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  unfold AllocatedAffineCoefficientComparison
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have href := hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    L step H (fun _ => modulus) c hL hstep hH hsubset hdense (fun _ _ => modulus) residue
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize hsmall hε hmesh
    modulus outputResidue hmesh0 hmesh1 hscaleMesh hCmask hmask
  with_reducible
    refine allocatedAffineCoefficient_from_reference_l1 B rows hrows hcard hδ ρ hρpos hρone t htone
      U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
      H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
      selection hx hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask ?_
  exact href

include hrows hcard in
theorem exists_early_allocated_affine_coefficient_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineCoefficientComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_reference_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  exact allocatedAffineCoefficientComparison_of_reference B rows hrows hcard hδ ρ
    (fun P => hρmin.trans_le (hρ P).1) (fun P => (hρ P).2) t htone hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

def AllocatedAffineCoveredComparison
    (δ η : ℝ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (_ : t ≤ 1) : Prop :=
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (hMk : 0 < Mk)
        (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
        (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (hq : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
        (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (hv₀ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
        (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (hCmask : 1 ≤ Cmask)
        (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      ∀ (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
        (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)
        (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1),
      ‖(∫ p, law.complexMean (fun v => F (((allocatedCoefficientSplit B U basis S) p.1).1,
          euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v))
            (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin (allocatedGridAxis (I := I) U basis S.value) u v)) rows
            (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
          ∂(allocatedCoefficientSource B U basis hR hσ S).prod
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).toMeasure) -
        ∫ a₀, ∫ z, (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z : ℂ) *
          allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d F a₀ z
          ∂allocatedLongJetReference B U basis S O ∂allocatedFrozenCoefficientSource B U basis hR hσ S‖ ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask

omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineCoveredComparison_of_coefficient
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoefficientComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t htone) :
    AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  unfold AllocatedAffineCoveredComparison
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law Q _ hb o bW d _ F hF hFbound
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hc := hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
    selection hx hq he hεcoef hεe hlarge hperiod v₀ hv₀
    hmesh0 hmesh1 hscaleMesh hCmask hmask
  have hw := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hg := allocatedAffineIdeal_profile_integrable B U basis hR S x rows hRP hRi
    (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρpos _) (hρone _)
    center width (fun i => (hw i).2.2) modulus outputResidue hCmask hmask
  exact allocatedSlicedPhysicalCovered_test_comparison_of_l1 B U basis hR hσ S x u v₀ rows
    Q hb o bW d s hA hσ1 modulus hperiod F H step c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j))
    hsubset hm residue hsize hv₀ _ hg hc hF hFbound

include hrows hcard in
theorem exists_early_allocated_affine_covered_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_coefficient_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  exact allocatedAffineCoveredComparison_of_coefficient B rows hδ ρ
    (fun P => hρmin.trans_le (hρ P).1) (fun P => (hρ P).2) t htone hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d F
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineWholeCovered_comparison
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (_ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, O a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let outputResidue := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ‖actual - FiniteProbabilityWeights.complexMean gridLaw (fun u => ∫ a₀, ∫ z,
      (allocatedLongProfileDensity B U basis S x rows modulus (outputResidue u) ideal z : ℂ) *
        allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d F a₀ z
      ∂reference ∂frozenSource)‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro center width ideal outputResidue
  let f := fun (p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
      (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)) =>
    F (((allocatedCoefficientSplit B U basis S) p.1).1,
      euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
        (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2))
  have hf (y) : Integrable (fun p => f p y) ((source).prod (deck).toMeasure) :=
    allocatedProgressionCoveredIntegrand_integrable B U basis hR hσ S rows x Q hb o bW d F y hF hFbound
  apply containedSupportedProgressionLaw_integral_comparison B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
    ((source).prod (deck).toMeasure) f hf
  intro u hu
  have heq := containedSupportedProgressionAxisLaw_eq_of_size B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus hm r₀ hcell
    (fun a => ¬grid a) hsize
  rw [heq]
  exact hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
    selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask (hmask u)
    Q hb o bW d F hF hFbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_bounded_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ target maskLog F D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htarget : 0 ≤ target) (hmaskLog : 0 ≤ maskLog) (hF : 0 ≤ F)
    (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let radiusLog := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let toleranceLog := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, 0 < ρ P ∧ ρ P ≤ 1 ∧ Real.exp (-radiusLog) ≤ ρ P) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
        (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp toleranceLog ∧
        t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone := by
  intro E η radiusLog toleranceLog
  have hη : 0 < η := Real.exp_pos _
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hηE : η⁻¹ ≤ Real.exp E := by
    dsimp [η]
    rw [← Real.exp_neg]
    simp only [neg_neg, le_refl]
  have hδhalf : δ / 2 ≤ 1 := by linarith
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_covered_source.{uJ,uQ} (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  have hρpos (P) : 0 < ρ P := hρmin.trans_le (hρ P).1
  have hfloor := allocatedAffineSourceRadius_uniform_floor (O := O) (α := α)
    B A T (half_pos hδ) hδhalf hη hE hF hηE hδF ρ hρpos hρeq
  have htlog := allocatedAffineSourceTolerance_log_bound (G := G) (O := O) (α := α)
    B A T (half_pos hδ) hδhalf hη hE hF hηE hδF
  rw [← hteq] at htlog
  have hlogs := allocatedAffine_log_costs_le_envelope B A T hdim hE hF
  refine ⟨ρ, fun P => ⟨hρpos P, (hρ P).2,
    (Real.exp_le_exp.mpr (neg_le_neg hlogs.1)).trans (hfloor P)⟩,
    hρeq, t, ht, htone, ?_, hteq, hs⟩
  exact (Real.log_le_iff_le_exp (inv_pos.mpr ht)).mp (htlog.trans hlogs.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (s : ∀ j : Fin m, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound (O := O j)
  S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (Mk : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => O
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d (fun p => F (Prod.snd p))
  H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include hR hσ hMk hi hP hMkP hRP hRi hσi hcount in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineWholeProfile_comparison
    {δ η : ℝ} (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid) (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j) (hH : ∀ j : Tuple, 2 ≤ H j)
    (hδ : 0 < δ)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hm : 0 < modulus)
    (hsize : ∀ j : Tuple, (Fintype.card α + 1) * modulus ≤ H j)
    (hsmall : ∀ j : Tuple, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) <
      volume.real (scalarCubeDomain α))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j : Tuple, (step j : ℝ) / L j ≤ ε)
    (selection : α ↪ G)
    (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (hq : Fintype.card α ≤ m + 1)
    {e εcoef : ℝ} (he : 0 ≤ e) (hεcoef : 0 < εcoef) (hεe : εcoef⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α jetRows P e) ≤ S.value)
    (hperiod : ∀ j : Fin m, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree L H step c positiveLengths
      (fun j : Tuple => hH₀ (embed j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0)
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hscaleMesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hCmask : 1 ≤ Cmask)
    (hmask : ∀ (u : GridTuples) j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ∧ allocatedIntegerKernelMask B U basis S x rows j
      modulus
      (integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus) z ≤ Cmask)
    (T : Fin m → ℝ) (hT : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    let center := principalProgressionSliceCenter (α := α) activeB activeDegree L c
    let width := principalProgressionSliceWidth (α := α) activeB activeDegree L H step
    let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬grid a}, O a.val.1) => R o.1.val.1)
      (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
        (layerSamplerDegree I n) grid (fun a => rows a.val.1) (ρ grid) center width)
    let _ := fun (u : GridTuples) j => integerResidueMatrix
      (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
    ‖actual - (∫ y, ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile
      B U basis hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) modulus ideal y) : ℂ) * F y
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j)))‖ ≤
      (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (Fintype.card {a // ¬grid a} * εcoef *
          (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
            Fintype.card {a // ¬grid a}) +
      allocatedAffineSourceReferenceError B U basis S α O (ρ grid) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro center width ideal outputResidue
  have hw := principalProgressionSlice_parameters (α := α) activeB activeDegree
    L H step c positiveLengths hstep hH hδ hsubset hdense
  have ht := allocatedAffineCoveredProfile_mean_test_integral B U basis S rows x hR (ρ grid)
    center width hσ v₀ Q hb o bW d ν hρ hρ1 (fun i => (hw i).2.2) hRP hRi
    modulus gridLaw outputResidue hCmask hmask (fun j => (hσsmall j).trans htone)
    T hT hsource C hC hchart hbudget F hF hFbound
  have hc := allocatedAffineWholeCovered_comparison B U basis hR hσ S rows x s hA hMk hi
    hP hMkP hRP hRi hσi hcount Q hb o bW d (fun p => F (Prod.snd p))
    H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell ρ t htone hs hσsmall hstep hH hδ hdense
    hm hsize hsmall hε hmesh selection hgood hq he hεcoef hεe hlarge hperiod v₀ hv₀
    hmesh0 hmesh1 hscaleMesh hCmask hmask (hF.comp measurable_snd) (fun p => hFbound p.2)
  change ‖actual - (gridLaw).complexMean (fun u => ∫ a₀, ∫ z,
    (allocatedLongProfileDensity B U basis S x rows modulus (outputResidue u) ideal z : ℂ) *
      allocatedCoveredFixedTest B U basis S x u v₀ rows Q hb o bW d (fun p => F (Prod.snd p)) a₀ z
        ∂reference ∂frozenSource)‖ ≤ _ at hc
  rw [ht] at hc
  simpa only [allocatedWholeMaskedCoveredProfile_join] using hc

end Erdos3.VectorPolynomial

end

end OAI

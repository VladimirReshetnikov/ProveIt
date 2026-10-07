/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Probability.AllocatedLongJetMixture

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

noncomputable def allocatedLongJetOutputScale : {a // ¬grid a} → ℝ
  | ⟨⟨_, .inl _⟩, _⟩ => 1
  | ⟨⟨j, .inr i⟩, _⟩ => (basisAxisScale (basis j) i : ℝ)^Fintype.card (O j)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetOutputScale_pos (a : {a // ¬grid a}) :
    0 < allocatedLongJetOutputScale B U basis S (O := O) a := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact zero_lt_one
  | inr i => exact pow_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)) _

noncomputable def allocatedLongJetTarget
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨j, .inl i⟩, _⟩ => allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
  | ⟨⟨j, .inr i⟩, _⟩ => fun z => allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y
      (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))

noncomputable def allocatedLongJetMask (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    ∀ a : {a // ¬grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨_, .inl _⟩, _⟩ => fun _ => 1
  | ⟨⟨j, .inr _⟩, _⟩ => allocatedIntegerKernelMask B U basis S x rows j modulus (residue j)

include hR hσ in
theorem allocatedLongJetTarget_row_bounds (hσ1 : ∀ j, σ j ≤ 1) (a : {a // ¬grid a}) :
    ∃ C K : ℝ≥0, ∀ z : CoefficientJetAxisRow O a.val,
      (∀ y, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ C) ∧
      LipschitzOnWith K (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z)
        (Metric.closedBall 0 1) := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i =>
    exact ⟨_, _, fun z => allocatedContinuousKernelDensity_bounds B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j) z⟩
  | inr i =>
    exact ⟨_, _, fun z => allocatedIntegerKernelDensity_bounds B U basis hR hσ S j i x u
      (rows j) (s j) (hA j) (hσ1 j) (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))⟩

include hR hσ in
theorem allocatedLongJetTarget_uniform_bounds (hσ1 : ∀ j, σ j ≤ 1) :
    ∃ C K : ℝ≥0, 1 ≤ C ∧
      (∀ y a z, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ C) ∧
      (∀ a z, LipschitzOnWith K
        (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z) (Metric.closedBall 0 1)) := by
  classical
  choose C K h using allocatedLongJetTarget_row_bounds B U basis hR hσ S x u rows s hA hσ1
  have hC (a) : C a ≤ 1 + ∑ a, C a :=
    (Finset.single_le_sum (fun b _ => show 0 ≤ C b from zero_le) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hK (a) : K a ≤ ∑ a, K a :=
    Finset.single_le_sum (fun b _ => show 0 ≤ K b from zero_le) (Finset.mem_univ a)
  refine ⟨1 + ∑ a, C a, ∑ a, K a, le_add_of_nonneg_right (by positivity), ?_, ?_⟩
  · intro y a z
    exact ((h a z).1 y).trans (by exact_mod_cast hC a)
  · intro a z
    exact (h a z).2.weaken (hK a)

theorem allocatedLongJet_scaled_density
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hσ1 : ∀ j, σ j ≤ 1) (z : AllocatedLongJetRows B U basis S O) :
    (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
      allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z =
    ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a *
      allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a) := by
  simp only [allocatedLongJetDensity, Finset.prod_mul_distrib]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (modulus : ℕ) (hmodulus : 0 < modulus)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
variable (hsize : ∀ d, (Fintype.card α+1)*modulus ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
    (allocatedPrincipalSides B U basis S) d)

noncomputable def allocatedLongResidueWeights :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) := by
  exact principalResidueWeights (fun a : {a // ¬grid a} => B a.val)
    (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) lengths
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩)
    modulus hmodulus r hsize

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "weights" => allocatedLongResidueWeights B U basis S modulus hmodulus r hsize

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedLongResidueWeights_matrix
    (ref : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℤ)
    (href : integerResidueMap _ modulus ref = principalTupleResidues r)
    (j : Fin m) (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv : (weights).weight v ≠ 0) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus =
      integerResidueMatrix (integerMappedJetMatrix (allocatedNonkernelExponent B j)
        (partitionedPrincipalInput grid (fun g a => (g, a)))
        (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
        (rows j) ref) modulus :=
  principalResidueWeights_matrix (fun a : {a // ¬grid a} => B a.val)
    (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) lengths
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩)
    modulus hmodulus r hsize _ _ _ _ ref href v hv

theorem allocatedLongJet_principal_comparison
    (hsmall : ∀ d, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/lengths d) <
      volume.real (scalarCubeDomain α))
    (C K : ℝ≥0) (hC : 1 ≤ C) {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hcap : ∀ y a z, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ C)
    (hLip : ∀ a z, LipschitzOnWith K
      (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z) (Metric.closedBall 0 1))
    (hmask : ∀ j i, S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i → ∀ z,
      0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ M)
    (herror : ∀ v, (weights).weight v ≠ 0 → ∀ j i
      (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) z,
      |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
          (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
          allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
            (principalTupleNormalized lengths v) (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε)
    (z : AllocatedLongJetRows B U basis S O) :
    |(weights).mean (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
        allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
      (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        (∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
          ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))| ≤
      Fintype.card {a // ¬grid a} * ε * (1+M*C+ε)^Fintype.card {a // ¬grid a} +
        M^Fintype.card {a // ¬grid a} * jointTupleQuadratureError (α := α)
          (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
          (Fintype.card {a // ¬grid a}) C K lengths modulus := by
  have hm (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a (z a) ∧
        allocatedLongJetMask B U basis S x rows modulus residue a (z a) ≤ M := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => exact ⟨zero_le_one, hM⟩
    | inr i => exact hmask j i (Nat.lt_of_not_ge ha) _
  have he (v) (hv : (weights).weight v ≠ 0) (a : {a // ¬grid a}) :
      |allocatedLongJetOutputScale B U basis S (O := O) a *
          allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a) -
        allocatedLongJetMask B U basis S x rows modulus residue a (z a) *
          allocatedLongJetTarget B U basis S x u rows s hA (principalTupleNormalized lengths v) a (z a)| ≤ ε := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => simpa only [allocatedLongJetOutputScale, allocatedLongJetFactor,
        allocatedLongJetMask, allocatedLongJetTarget, sub_self, abs_zero] using hε
    | inr i => exact herror v hv j i (Nat.lt_of_not_ge ha) _
  have hquad := sharedTupleProduct_riemann (fun a : {a // ¬grid a} => B a.val)
    (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) lengths
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩)
    modulus hmodulus r hsize hsmall
    (fun a y => allocatedLongJetTarget B U basis S x u rows s hA y a (z a)) C K hC
    (fun a => hLip a (z a)) (fun a y => hcap y a (z a))
  have hm0 : 0 ≤ ∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a) :=
    Finset.prod_nonneg (fun a _ => (hm a).1)
  have hmM : (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) ≤
      M^Fintype.card {a // ¬grid a} := by
    calc
      _ ≤ ∏ _a : {a // ¬grid a}, M := Finset.prod_le_prod₀ (fun a _ => (hm a).1) (fun a _ => (hm a).2)
      _ = _ := by simp
  apply finiteMean_masked_comparison_of_support weights _ _ hm0 hmM ((abs_nonneg _).trans hquad) _ hquad
  intro v hv
  rw [allocatedLongJet_scaled_density]
  exact masked_product_error _ _ _ C.coe_nonneg (zero_le_one.trans hM) hε
    (fun a => hcap _ a (z a)) (fun a => by rw [abs_of_nonneg (hm a).1]; exact (hm a).2) (he v hv)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (modulus : ℕ) (hmodulus : 0 < modulus)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
variable (hsize : ∀ d, (Fintype.card α+1)*modulus ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
    (allocatedPrincipalSides B U basis S) d)

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable (kernelModulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod kernelModulus))

local notation "weights" => allocatedLongResidueWeights B U basis S modulus hmodulus r hsize

theorem allocatedLongJet_refined_principal_comparison
    (hsmall : ∀ d, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/lengths d) <
      volume.real (scalarCubeDomain α))
    (C K : ℝ≥0) (hC : 1 ≤ C) {M ε : ℝ} (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hcap : ∀ y a z, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ C)
    (hLip : ∀ a z, LipschitzOnWith K
      (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z) (Metric.closedBall 0 1))
    (hmask : ∀ j i, S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i → ∀ z,
      0 ≤ allocatedIntegerKernelMask B U basis S x rows j kernelModulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j kernelModulus (residue j) z ≤ M)
    (herror : ∀ v, (weights).weight v ≠ 0 → ∀ j i
      (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) z,
      |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
          (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
        allocatedIntegerKernelMask B U basis S x rows j kernelModulus (residue j) z *
          allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
            (principalTupleNormalized lengths v) (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε)
    (z : AllocatedLongJetRows B U basis S O) :
    |(weights).mean (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
        allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
      (∏ a, allocatedLongJetMask B U basis S x rows kernelModulus residue a (z a)) *
        (∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
          ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))| ≤
      Fintype.card {a // ¬grid a} * ε * (1+M*C+ε)^Fintype.card {a // ¬grid a} +
        M^Fintype.card {a // ¬grid a} * jointTupleQuadratureError (α := α)
          (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
          (Fintype.card {a // ¬grid a}) C K lengths modulus := by
  have hm (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows kernelModulus residue a (z a) ∧
        allocatedLongJetMask B U basis S x rows kernelModulus residue a (z a) ≤ M := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => exact ⟨zero_le_one, hM⟩
    | inr i => exact hmask j i (Nat.lt_of_not_ge ha) _
  have he (v) (hv : (weights).weight v ≠ 0) (a : {a // ¬grid a}) :
      |allocatedLongJetOutputScale B U basis S (O := O) a *
          allocatedLongJetFactor B U basis hR hσ S x u v rows s hA hσ1 a (z a) -
        allocatedLongJetMask B U basis S x rows kernelModulus residue a (z a) *
          allocatedLongJetTarget B U basis S x u rows s hA (principalTupleNormalized lengths v) a (z a)| ≤ ε := by
    rcases a with ⟨⟨j, a⟩, ha⟩
    cases a with
    | inl i => simpa only [allocatedLongJetOutputScale, allocatedLongJetFactor,
        allocatedLongJetMask, allocatedLongJetTarget, sub_self, abs_zero] using hε
    | inr i => exact herror v hv j i (Nat.lt_of_not_ge ha) _
  have hquad := sharedTupleProduct_riemann (fun a : {a // ¬grid a} => B a.val)
    (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val) lengths
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩)
    modulus hmodulus r hsize hsmall
    (fun a y => allocatedLongJetTarget B U basis S x u rows s hA y a (z a)) C K hC
    (fun a => hLip a (z a)) (fun a y => hcap y a (z a))
  have hm0 : 0 ≤ ∏ a, allocatedLongJetMask B U basis S x rows kernelModulus residue a (z a) :=
    Finset.prod_nonneg (fun a _ => (hm a).1)
  have hmM : (∏ a, allocatedLongJetMask B U basis S x rows kernelModulus residue a (z a)) ≤
      M^Fintype.card {a // ¬grid a} := by
    calc
      _ ≤ ∏ _a : {a // ¬grid a}, M := Finset.prod_le_prod₀ (fun a _ => (hm a).1) (fun a _ => (hm a).2)
      _ = _ := by simp
  apply finiteMean_masked_comparison_of_support weights _ _ hm0 hmM ((abs_nonneg _).trans hquad) _ hquad
  intro v hv
  rw [allocatedLongJet_scaled_density]
  exact masked_product_error _ _ _ C.coe_nonneg (zero_le_one.trans hM) hε
    (fun a => hcap _ a (z a)) (fun a => by rw [abs_of_nonneg (hm a).1]; exact (hm a).2) (he v hv)

end Erdos3.VectorPolynomial

end

end OAI

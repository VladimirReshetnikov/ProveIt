import OAI.Combinatorics.Progressions.Geometry.AllocatedRefinedSpatialData

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

theorem allocatedGoodKernel_stride_refined_spatial_data {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E
      ((m+1 : ℕ)*P + Fintype.card X*T)) ≤ S.value) :
    ∃ (modulus : ℕ) (_hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (q : X → ℕ), (∀ d, 0 < q d) → (∀ d, (q d : ℝ) ≤ Real.exp T) →
      let refined := residueRefinedPeriod modulus q
      ∃ hRefined : 0 < refined,
      (∀ d, q d * modulus ∣ refined) ∧
      (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*P + Fintype.card X*T) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*refined ≤ lengths d,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined),
      ∃ (reference : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        principalResidueLabel refined reference = r ∧
        (∀ v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue j) ∧
        ∀ z : AllocatedLongJetRows B U b S O,
        |(allocatedLongResidueWeights B U b S refined hRefined r hsize).mean
            (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
              allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
          allocatedLongJetProxy B U b S x u rows s hA modulus residue z| ≤ η := by
  have hbudget : 0 ≤ (m+1 : ℕ)*(P : ℝ) + Fintype.card X*T := by positivity
  obtain ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, hdata⟩ :=
    allocatedGoodKernel_refined_spatial_data B U b hR hσ S x rows hM selection hx
      hq hinj hrows hσ1 hP hE hbudget hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  refine ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, ?_⟩
  intro q hqpos hqbound
  dsimp only
  have hRefined := residueRefinedPeriod_pos hm q hqpos
  have hmod : (modulus : ℝ) ≤ Real.exp ((m+1 : ℕ)*P) := by
    calc
      _ ≤ (M : ℝ)^(m+1) := by exact_mod_cast hmB
      _ ≤ Real.exp P ^ (m+1) := pow_le_pow_left₀ (Nat.cast_nonneg M) hMP _
      _ = _ := (Real.exp_nat_mul P (m+1)).symm
  have hbound := residueRefinedPeriod_exp_bound modulus q hmod hqbound
  have hdiv : modulus ∣ residueRefinedPeriod modulus q :=
    ⟨∏ d, q d, rfl⟩
  exact ⟨hRefined, stride_mul_dvd_residueRefinedPeriod modulus q, hbound,
    hdata _ hRefined hdiv hbound⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

def allocatedStrideRefinedStatement (M : ℕ) (selection : α ↪ G)
    (hσ1 : ∀ j, σ j ≤ 1) (P T η : ℝ) : Prop :=
    ∃ (modulus : ℕ) (_hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (q : X → ℕ), (∀ d, 0 < q d) → (∀ d, (q d : ℝ) ≤ Real.exp T) →
      let refined := residueRefinedPeriod modulus q
      ∃ hRefined : 0 < refined,
      (∀ d, q d * modulus ∣ refined) ∧
      (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*P + Fintype.card X*T) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*refined ≤ lengths d,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined),
      ∃ (reference : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        principalResidueLabel refined reference = r ∧
        (∀ v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue j) ∧
        ∀ z : AllocatedLongJetRows B U b S O,
        |(allocatedLongResidueWeights B U b S refined hRefined r hsize).mean
            (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
              allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
          allocatedLongJetProxy B U b S x u rows s hA modulus residue z| ≤ η

theorem allocatedStrideRefinedStatement_of_data {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E
      ((m+1 : ℕ)*P + Fintype.card X*T)) ≤ S.value) :
    allocatedStrideRefinedStatement B U b hR hσ S x rows X M selection hσ1 P T η := by
  exact allocatedGoodKernel_stride_refined_spatial_data B U b hR hσ S x rows X
    hM selection hx hq hinj hrows hσ1 hP hE hT hη hη1 hMP hRP hRi hσi hcount hηE hlarge

end Erdos3.VectorPolynomial

end

end OAI

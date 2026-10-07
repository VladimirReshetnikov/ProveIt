import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison

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

theorem allocatedGoodKernel_refined_spatial_data {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E T) ≤ S.value) :
    ∃ (modulus : ℕ) (_hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (refined : ℕ) (hRefined : 0 < refined), modulus ∣ refined →
      (refined : ℝ) ≤ Real.exp T →
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
  have hcoefficient : Real.exp (allocatedKernelReplacementLog (G := G) B α O P
      (allocatedJointAccuracyLog (G := G) B α O P E)) ≤ S.value :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans hlarge
  obtain ⟨hε, _, hεe⟩ := allocatedJointAccuracy_spec (G := G) B α O hP hMP hη hη1 hηE
  have he := allocatedJointAccuracyLog_nonneg (G := G) B α O hP hE
  obtain ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, hcompare⟩ :=
    allocatedGoodKernel_refined_principal_comparison B U b hR hσ S x rows hM selection hx
      hq hinj hrows hσ1 hP he hε hMP hRP hRi hσi hcount hεe hcoefficient
  refine ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, ?_⟩
  intro refined hRefined hdiv hbound
  have htuple := (allocatedRefinedJointLengthLog_spec (G := G) B α O
    hP hE hT hbound hMP hη hηE hlarge).2
  obtain ⟨hsize, hsmall, herror⟩ :=
    allocatedRefinedJointTupleCutoff_spec B U b S O hP hM hη hη1 (le_refl refined) htuple
  refine ⟨hsize, ?_⟩
  intro u r
  obtain ⟨reference, href⟩ := exists_allocatedLongResidueReference B U b S refined hRefined r hsize
  obtain ⟨residue, hr, he⟩ := hcompare refined hRefined hdiv u r hsize hsmall
  exact ⟨reference, residue, href, hr, fun z => (he z).trans herror⟩

end Erdos3.VectorPolynomial

end

end OAI

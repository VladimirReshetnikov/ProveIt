import OAI.Combinatorics.Progressions.Probability.AllocatedDensityParameterBounds
import OAI.Combinatorics.Progressions.Sampling.PrincipalGridMixture

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
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedGoodKernel_principal_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value) :
    let C : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
    let W : ℝ := layerKernelIndexBound m M
    ∃ (modulus : ℕ) (hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus)
        (hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d),
      (∀ d, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/lengths d) <
        volume.real (scalarCubeDomain α)) →
      ∃ residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus),
        (∀ v, (allocatedLongResidueWeights B U basis S modulus hm r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) ∧
        ∀ z : AllocatedLongJetRows B U basis S O,
        |(allocatedLongResidueWeights B U basis S modulus hm r hsize).mean
            (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
              allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
          (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
            (∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
              ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))| ≤
          Fintype.card {a // ¬grid a} * ε * (1+W*C+ε)^Fintype.card {a // ¬grid a} +
            W^Fintype.card {a // ¬grid a} * jointTupleQuadratureError (α := α)
              (fun a : {a // ¬grid a} => B a.val) (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)
              (Fintype.card {a // ¬grid a}) C C lengths modulus := by
  dsimp only
  obtain ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, herr⟩ :=
    allocatedGoodKernel_replacement B U basis hR hσ S x rows hM selection hx hq hinj hrows hσ1
      hP he hε hMP hRP hRi hσi hcount hεe hlarge
  refine ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, ?_⟩
  intro u r hsize hsmall
  let residue := fun j => integerResidueMatrix
    (integerMappedJetMatrix (allocatedNonkernelExponent B j)
      (partitionedPrincipalInput grid (fun g a => (g, a)))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (rows j) (principalResidueLift modulus r)) modulus
  have hr : ∀ v, (allocatedLongResidueWeights B U basis S modulus hm r hsize).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j := by
    intro v hv j
    exact allocatedLongResidueWeights_matrix B U basis S modulus hm r hsize x u rows
      (principalResidueLift modulus r) (principalResidueLift_spec modulus r) j v hv
  have herror := herr u (allocatedLongResidueWeights B U basis S modulus hm r hsize) residue hr
  obtain ⟨hC, hcap, hLip⟩ := allocatedLongJetTarget_exp_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1
  have hW : (1 : ℝ) ≤ layerKernelIndexBound m M := by
    exact_mod_cast Nat.succ_le_of_lt (show 0 < layerKernelIndexBound m M from pow_pos hM _)
  refine ⟨residue, hr, ?_⟩
  intro z
  exact allocatedLongJet_principal_comparison B U basis hR hσ S modulus hm r hsize x u rows s hA hσ1
    residue hsmall _ _ hC hW hε.le hcap hLip
    (fun j i hj => (herror j i hj).1) (fun v hv j i hj z => (herror j i hj).2 v hv z) z

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AllocatedWholeProfileEnvelope

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Z : ℝ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (p j) e ∈ U j)

local notation "standardRows" => (fun j : Fin m =>
  (Subtype.val : BoundedBooleanJet (Fin dim) (Fin.val j + 1) → Finset (Fin dim)))
local notation "fullRows" => (fun j : Fin m =>
  (Subtype.val : boundedBooleanJetRows (Fin dim) (Fin.val j + 1) → Finset (Fin dim)))

theorem allocatedWholeIdealReference_full_rows (δ : ℝ≥0) :
    allocatedWholeIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x standardRows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells (physicalCubeEuclideanSample U d p hmem) test Z δ =
    allocatedWholeIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x fullRows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells (physicalCubeRowSample U d fullRows p hmem) test Z δ := by
  let P (O : Fin m → Type) [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset (Fin dim)) : Prop :=
    allocatedWholeIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x standardRows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells (physicalCubeEuclideanSample U d p hmem) test Z δ =
    allocatedWholeIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells (physicalCubeRowSample U d rows p hmem) test Z δ
  have hP : P (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1)) standardRows := by
    rfl
  exact boundedBooleanJetRows_family_transport (fun j : Fin m => Fin.val j + 1) P hP
    (fun j => fullBooleanRowSetFintype dim (Fin.val j + 1))

end Erdos3.VectorPolynomial

end

end OAI

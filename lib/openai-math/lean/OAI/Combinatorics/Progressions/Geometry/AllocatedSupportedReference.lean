import OAI.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  sides (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedSupportedWholeReference (modulus : ℕ) :
    (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus) → fullTuple :=
  (whole).supportedFiberReference (principalResidueLabel modulus)

theorem allocatedSupportedWholeReference_label (modulus : ℕ) (y : fullTuple)
    (hy : (whole).weight y ≠ 0) :
    principalResidueLabel modulus (allocatedSupportedWholeReference B U b S modulus
      (principalResidueLabel modulus y)) = principalResidueLabel modulus y :=
  (whole).supportedFiberReference_label (principalResidueLabel modulus) y hy

theorem allocatedSupportedWholeReference_weight (modulus : ℕ)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus) :
    (whole).weight (allocatedSupportedWholeReference B U b S modulus r) ≠ 0 :=
  (whole).supportedFiberReference_weight (principalResidueLabel modulus) r

end Erdos3.VectorPolynomial

end

end OAI

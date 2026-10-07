import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

def allocatedOriginalSampleCongruenceProjection
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (j : Fin m) (a : AllocatedDegreeActiveAxis short j) :
    BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ :=
  match a.val with
  | .inl _ => fun _ => 0
  | .inr i => (sample j).2 i

noncomputable def allocatedOriginalSampleDeckValue
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides)
    (j : Fin m) (e : E j) : ℤ :=
  MvPolynomial.eval (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
    (modularBoundedCoefficientPolynomial (j.val + 1) (fun d => deck j d e))

theorem allocatedOriginalSampleDeckValue_residue
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (q : ℕ) (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides)
    (j : Fin m) :
    coefficientDeckJetMap
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (fun (_ : Fin m) (_ : Unit) => (∅ : Finset Empty)) q
      (fun j d e => (deck j d e : ZMod q)) j () =
      integerResidueMap (E j) q (allocatedOriginalSampleDeckValue B U basis S deck x y j) := by
  funext e
  simp only [coefficientDeckJetMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply,
    boundedCoefficientJetMatrix_empty]
  change (∑ d, (boundedSiteMatrix (j.val + 1)
    (fun _ : Unit => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) () d : ZMod q) *
      (deck j d e : ZMod q)) =
    (allocatedOriginalSampleDeckValue B U basis S deck x y j e : ZMod q)
  simp only [allocatedOriginalSampleDeckValue, modularBoundedCoefficientPolynomial,
    map_sum, MvPolynomial.eval_monomial, Finsupp.prod, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro d _
  exact mul_comm _ _

theorem allocatedOriginalSample_jointResidueOutput_eq_congruence
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (q : ℕ) (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
      (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q y) =
      fun o => (forecastCongruenceOutput (R := ℤ) short
        (base + integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) noise)
        (fun j => Sum.elim
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2
          (allocatedOriginalSampleDeckValue B U basis S deck x y j)) o : ZMod q) := by
  rw [allocatedJointResidueOutput_actual]
  have hroot : Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) =
      allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y := by
    funext v
    simp only [allocatedPhysicalCubeRoot, zero_add]
  rw [hroot]
  funext o
  apply congrArg (fun z : ℤ => (z : ZMod q))
  rcases o with ⟨j, a | e | i⟩
  · exact spatialRankPolynomial_actual_eval base noise a.val _
  · rfl
  · change MvPolynomial.eval _ (modularBoundedCoefficientPolynomial _
      ((sample j).2 i.val)) =
      (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2 i.val
    exact (allocatedOriginalSamplePhysicalMixedValue_integer B U basis S sample x y j i.val).symm

end Erdos3.VectorPolynomial

end

end OAI

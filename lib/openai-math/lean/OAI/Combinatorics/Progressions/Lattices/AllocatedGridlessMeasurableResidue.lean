/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem exists_measurable_fiber_family {A R Y : Type*} [MeasurableSpace Y]
    (F : A → R) (f : A → Y → ℝ) (hf : ∀ a, Measurable (f a))
    (he : ∀ a b, F a = F b → f a = f b) :
    ∃ P : R → Y → ℝ, (∀ r, Measurable (P r)) ∧ ∀ a, f a = P (F a) := by
  let P (r : R) : Y → ℝ := if hr : ∃ a, F a = r then f hr.choose else fun _ => 0
  refine ⟨P, ?_, ?_⟩
  · intro r
    dsimp only [P]
    split_ifs with hr
    · exact hf hr.choose
    · exact measurable_const
  · intro a
    have ha : ∃ b, F b = F a := ⟨a, rfl⟩
    dsimp only [P]
    rw [dite_eq_left ha]
    exact he a ha.choose ha.choose_spec.symm

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedWholeMaskedGridlessProfile_measurable (M : ℕ)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
    (hf : Measurable f) :
    Measurable (allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f) := by
  unfold allocatedWholeMaskedGridlessProfile
  apply allocatedGridlessCoveredProfile_measurable
  exact allocatedLongProfileDensity_measurable B U b S x rows M _ f hf

theorem exists_allocatedWholeMaskedGridlessProfile_measurable_by_residue (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
    (hf : Measurable f) :
    ∃ P : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod M) →
        EuclideanJetLayers U O → ℝ,
      (∀ r, Measurable (P r)) ∧
      ∀ z : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S),
        allocatedWholeMaskedGridlessProfile B U b S x z rows hb o bW d M f =
          P (principalResidueLabel M z) := by
  exact exists_measurable_fiber_family (principalResidueLabel M)
    (fun z => allocatedWholeMaskedGridlessProfile B U b S x z rows hb o bW d M f)
    (fun z => allocatedWholeMaskedGridlessProfile_measurable B U b S x z rows hb o bW d M f hf)
    (fun z w h => allocatedWholeMaskedGridlessProfile_eq B U b S x z w rows hb o bW d M hperiod h f)

end Erdos3.VectorPolynomial

end

end OAI

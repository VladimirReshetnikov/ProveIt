import OAI.Combinatorics.Progressions.Sampling.JointFrozenSamplerLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dependentProductPMF_sigma_curry
    {A : Type*} [Fintype A] {B C : A → Type*}
    [∀ a, Fintype (B a)] [∀ a, Fintype (C a)]
    {X : ∀ a, B a → C a → Type*}
    [∀ a b c, Countable (X a b c)] [∀ a b c, MeasurableSpace (X a b c)]
    [∀ a b c, MeasurableSingletonClass (X a b c)]
    (p : ∀ a b c, PMF (X a b c)) :
    (dependentProductPMF (fun i : Σ a, B a × C a => p i.1 i.2.1 i.2.2)).map
      (fun x a b c => x ⟨a, b, c⟩) =
      dependentProductPMF (fun a => dependentProductPMF (fun b => dependentProductPMF (p a b))) := by
  have hinj : Function.Injective
      (fun (x : ∀ i : Σ a, B a × C a, X i.1 i.2.1 i.2.2) a b c => x ⟨a, b, c⟩) := by
    intro x y h
    funext i
    exact congrFun (congrFun (congrFun h i.1) i.2.1) i.2.2
  ext y
  let x : ∀ i : Σ a, B a × C a, X i.1 i.2.1 i.2.2 := fun i => y i.1 i.2.1 i.2.2
  change (dependentProductPMF (fun i : Σ a, B a × C a => p i.1 i.2.1 i.2.2)).map
    (fun z a b c => z ⟨a, b, c⟩) (fun a b c => x ⟨a, b, c⟩) = _
  rw [pmf_map_injective_at _ _ hinj]
  simp only [dependentProductPMF_apply, Fintype.prod_sigma, Fintype.prod_prod_type, x]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem dependentProductPMF_curry {B C : Type*} [Fintype B] [Fintype C]
    {X : B → C → Type*} [∀ b c, Countable (X b c)] [∀ b c, MeasurableSpace (X b c)]
    [∀ b c, MeasurableSingletonClass (X b c)] (p : ∀ b c, PMF (X b c)) :
    (dependentProductPMF (fun bc : B × C => p bc.1 bc.2)).map
      (fun x b c => x (b, c)) = dependentProductPMF (fun b => dependentProductPMF (p b)) := by
  have hinj : Function.Injective (fun (x : ∀ bc : B × C, X bc.1 bc.2) b c => x (b, c)) := by
    intro x y h
    funext bc
    exact congrFun (congrFun h bc.1) bc.2
  ext y
  let x : ∀ bc : B × C, X bc.1 bc.2 := fun bc => y bc.1 bc.2
  change (dependentProductPMF (fun bc : B × C => p bc.1 bc.2)).map
    (fun z b c => z (b, c)) (fun b c => x (b, c)) = _
  rw [pmf_map_injective_at _ _ hinj]
  simp only [dependentProductPMF_apply, Fintype.prod_prod_type, x]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

variable (a : {a : LayerSamplerAxis I n // allocatedGridAxis (I := I) U basis S.value a})

theorem allocatedFrozenTuple_axis_marginal :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (q : B a.val × Fin (layerSamplerDegree I n a.val)) => u ⟨a, q⟩) =
      dependentProductPMF (fun q : B a.val × Fin (layerSamplerDegree I n a.val) =>
        (integerScalarCubeWeights α (sides ⟨a.val, q⟩)
          (allocatedPrincipalSides_pos B U basis S ⟨a.val, q⟩)).toPMF) := by
  let w := fun k : PrincipalTupleIndex
    (fun d : {d // grid d} => B d.val) (fun d => layerSamplerDegree I n d.val) =>
      integerScalarCubeWeights α (sides ⟨k.1.val, k.2⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨k.1.val, k.2⟩)
  have hp : (allocatedFrozenTupleWeights (α := α) B U basis S).toPMF =
      dependentProductPMF (fun k => (w k).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi w
  exact (congrArg (fun p : PMF (PrincipalAxisTuples (α := α) grid sides) =>
    p.map (fun u (q : B a.val × Fin (layerSamplerDegree I n a.val)) => u ⟨a, q⟩)) hp).trans
      (dependentProductPMF_marginal (fun k => (w k).toPMF) (fun q => ⟨a, q⟩)
        (by intro q r h; simpa using h))

theorem allocatedFrozenTuple_block_marginal :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (b : B a.val) (v : Fin (layerSamplerDegree I n a.val)) => u ⟨a, b, v⟩) =
      dependentProductPMF (fun b : B a.val => dependentProductPMF
        (fun v : Fin (layerSamplerDegree I n a.val) =>
          (integerScalarCubeWeights α (sides ⟨a.val, b, v⟩)
            (allocatedPrincipalSides_pos B U basis S ⟨a.val, b, v⟩)).toPMF)) := by
  have h := congrArg (fun p => p.map (fun z b v => z (b, v)))
    (allocatedFrozenTuple_axis_marginal (α := α) B U basis S a)
  rw [PMF.map_comp] at h
  exact h.trans (dependentProductPMF_curry
    (fun (b : B a.val) (v : Fin (layerSamplerDegree I n a.val)) =>
      (integerScalarCubeWeights α (sides ⟨a.val, b, v⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨a.val, b, v⟩)).toPMF))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedFrozenTuple_full_blocks :
    ((allocatedFrozenTupleWeights (α := α) B U basis S).toPMF).map
      (fun u (a : {a : LayerSamplerAxis I n // grid a}) (b : B a.val)
        (v : Fin (layerSamplerDegree I n a.val)) => u ⟨a, b, v⟩) =
      dependentProductPMF (fun a : {a : LayerSamplerAxis I n // grid a} =>
        dependentProductPMF (fun b : B a.val => dependentProductPMF
          (fun v : Fin (layerSamplerDegree I n a.val) =>
            (integerScalarCubeWeights α (sides ⟨a.val, b, v⟩)
              (allocatedPrincipalSides_pos B U basis S ⟨a.val, b, v⟩)).toPMF))) := by
  let w := fun k : PrincipalTupleIndex
    (fun d : {d // grid d} => B d.val) (fun d => layerSamplerDegree I n d.val) =>
      integerScalarCubeWeights α (sides ⟨k.1.val, k.2⟩)
        (allocatedPrincipalSides_pos B U basis S ⟨k.1.val, k.2⟩)
  have hp : (allocatedFrozenTupleWeights (α := α) B U basis S).toPMF =
      dependentProductPMF (fun k => (w k).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi w
  exact (congrArg (fun p : PMF (PrincipalAxisTuples (α := α) grid sides) =>
    p.map (fun u a b v => u ⟨a, b, v⟩)) hp).trans
      (dependentProductPMF_sigma_curry (fun a b v => (w ⟨a, b, v⟩).toPMF))

end Erdos3.VectorPolynomial

end

end OAI

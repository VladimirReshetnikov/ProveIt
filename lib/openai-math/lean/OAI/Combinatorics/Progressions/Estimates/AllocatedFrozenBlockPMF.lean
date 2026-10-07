import OAI.Combinatorics.Progressions.Probability.AllocatedFrozenJetDensity
import OAI.Combinatorics.Progressions.Sampling.AllocatedWeightedGridMixture

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedFrozenBlockPMF :
    ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val)
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ =>
      (independentProductPMF (allocatedLayerIntegerPMFs B U b hR hσ S j i)).map
        (fun c t => booleanCoefficient (fun _ => c (constantCoefficientSlot _ _)) (rows j t) +
          ∑ q : B ⟨j, Sum.inr i⟩,
            c (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ q) *
              integerBooleanBlockJet
                (fun v r => (u ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, v⟩ r : ℤ)) (rows j t))

omit [∀ j, Fintype (O j)] in
theorem allocatedGridJetFactor_frozen_blocks
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedGridJetFactor B U b hR hσ S x u v rows a z =
      (allocatedFrozenBlockPMF B U b hR hσ S u rows a z).toReal := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · have h := allocatedPhysicalGridJetPMF_blocks B U b hR hσ S j i ha x
      (principalAxisJoin grid u v) (rows j)
    have hjoin (q : B ⟨j, Sum.inr i⟩) (w : Fin (j.val + 1)) :
        principalAxisJoin grid u v ⟨⟨j, Sum.inr i⟩, q, w⟩ =
          u ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, w⟩ := by
      exact congrFun (principalAxisRestrict_join_left grid u v) ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, w⟩
    unfold allocatedGridJetFactor allocatedFrozenBlockPMF
    apply congrArg (fun p : PMF (O j → ℤ) => (p z).toReal)
    rw [h]
    congr 1
    funext c t
    apply congrArg (fun a : ℤ =>
      booleanCoefficient (fun _ => c (constantCoefficientSlot _ _)) (rows j t) + a)
    apply Finset.sum_congr rfl
    intro q _
    apply congrArg (fun a : ℤ => c (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ q) * a)
    apply congrArg (fun w => integerBooleanBlockJet w (rows j t))
    funext w r
    exact congrArg (fun y => (y r : ℤ)) (hjoin q w)

omit [∀ j, Fintype (O j)] in
theorem allocatedGridJetDensity_frozen_blocks
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridJetDensity B U b hR hσ S x u v rows z =
      ∏ a, (allocatedFrozenBlockPMF B U b hR hσ S u rows a (z a)).toReal := by
  unfold allocatedGridJetDensity
  exact Finset.prod_congr rfl (fun a _ =>
    allocatedGridJetFactor_frozen_blocks B U b hR hσ S u rows x v a (z a))

end Erdos3.VectorPolynomial

end

end OAI

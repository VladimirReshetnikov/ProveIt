import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m d : ℕ} {X : Type*} {J : Fin m → Type*}

noncomputable def fullTaggedBufferedCoordinates (e : Fin d ≃ Σ j, J j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) : Fin d → ℝ :=
  fun i => eval (fun a => (x a : ℝ)) (poly (e i).1) (e i).2 - c (e i).1 (e i).2

theorem fullTaggedPhysicalIntegerPoint_eq_nearest
    (e : Fin d ≃ Σ j, J j) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) :
    fullTaggedPhysicalIntegerPoint J poly c x =
      Sum.elim x (fun a => nearestIntegerLift (fullTaggedBufferedCoordinates e poly c x)
        (e.symm a)) := by
  funext v
  rcases v with a | a
  · rfl
  · simp only [fullTaggedPhysicalIntegerPoint, Sum.elim_inr, nearestIntegerLift,
      fullTaggedBufferedCoordinates]
    rw [e.apply_symm_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem fullTaggedBufferedCoordinates_close_on_slice
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) (i : Fin tagCount) :
    |fullTaggedBufferedCoordinates e poly (fun j => (C.centerLift j).val) (C.physical u) i -
      (nearestIntegerLift
        (fullTaggedBufferedCoordinates e poly (fun j => (C.centerLift j).val)
          (C.physical u)) i : ℝ)| ≤ 1 / 8 := by
  have hj : (e i).1.val + 1 ≤ m + 1 := by omega
  have hr := C.low_residual_on_slice hσ1 H hH hchart hsmall hp (m + 1) u hu
    (lowTaggedSlot J (m + 1) (e i).1 hj (e i).2)
  rw [lowTaggedPolynomial_eval] at hr
  simp only [integerSampledLowTags] at hr
  rw [lowTaggedIndex_slot] at hr
  change |eval (fun x => (C.physical u x : ℝ)) (poly (e i).1) (e i).2 -
    (C.centerLift (e i).1).val (e i).2 -
    (C.chartValues u (Sum.inr (e i)) : ℝ)| ≤ 1 / 8 at hr
  rw [C.chartValues_tag_eq_round hσ1 H hH hchart hsmall hp u
    (C.slice.integerPoints_subset_integerBox hu) (e i).1 (e i).2] at hr
  exact hr

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem siteLaw_fullTaggedBufferedCoordinates_close
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (z : out.retained) (site : A.Site) (hsite : (out.siteLaw z).weight site ≠ 0)
    (i : Fin tagCount) :
    |fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
        (A.physical z.val site) i -
      (nearestIntegerLift
        (fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
          (A.physical z.val site)) i : ℝ)| ≤ 1 / 8 := by
  have hpos : 0 < (out.siteLaw z).weight site :=
    lt_of_le_of_ne ((out.siteLaw z).nonneg site) (Ne.symm hsite)
  obtain ⟨u, _, hu, _, hphysical⟩ := out.siteLaw_support z site hpos
  rw [hphysical]
  have h := (P.chart ⟨z.val, out.subset z.property⟩).fullTaggedBufferedCoordinates_close_on_slice
    hσ1 H hH hchart hsmall hp e u hu i
  rw [P.chart_centerLift] at h
  exact h

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

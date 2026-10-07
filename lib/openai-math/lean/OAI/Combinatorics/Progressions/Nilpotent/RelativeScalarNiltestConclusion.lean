import OAI.Combinatorics.Progressions.Lattices.RelativePhysicalResiduePatch

namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem physicalResidueMean_sub_mul_re (h g : (X → ℤ) → ℂ)
    (target : ℝ) (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) :
    (physicalResidueMean (fun x => h x - (target : ℂ) * g x) lo H M a).re =
      (physicalResidueMean h lo H M a).re -
        target * (physicalResidueMean g lo H M a).re := by
  simp only [physicalResidueMean, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

theorem physicalResidueMean_scalar_patch_difference {s d : ℕ}
    (f : (X → ℤ) → ℝ) (P : PolynomialPatch X s d)
    (h g : (X → ℤ) → ℂ)
    (hg : ∀ x, g x = (P.value (fun i => (x i : ℝ)) : ℂ))
    (hh : ∀ x, h x = (f x : ℂ) * g x)
    (target : ℝ) (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) :
    (physicalResidueMean h lo H M a).re -
        target * (physicalResidueMean g lo H M a).re =
      (physicalResidueMean (fun x =>
        (((f x - target) * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) lo H M a).re := by
  have hpoint : (fun x => h x - (target : ℂ) * g x) =
      (fun x => (((f x - target) * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)) := by
    funext x
    rw [hh, hg, Complex.ofReal_mul, Complex.ofReal_sub, sub_mul]
  rw [← physicalResidueMean_sub_mul_re, hpoint]

theorem relativePatchSliceConclusion_of_scalar_patch_transfer {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (P : PolynomialPatch X s d)
    (h g : (X → ℤ) → ℂ)
    (hg : ∀ x, g x = (P.value (fun i => (x i : ℝ)) : ℂ))
    (hh : ∀ x, h x = (f x : ℂ) * g x)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity P ≤ cost)
    (hscore : Real.exp (-cost) < (physicalResidueMean h lo H M a).re -
      target * (physicalResidueMean g lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost := by
  apply relativePatchSliceConclusion_of_nonempty_physicalResidueMean
    N f P lo H M a target cost hM hbox hne hcost hcomplexity
  rw [← physicalResidueMean_scalar_patch_difference f P h g hg hh]
  exact hscore.le

theorem relativePatchSliceConclusion_of_scalarNiltest
    {V : Type*} [LieRing V] [LieAlgebra ℚ V]
    [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
    {s d d₀ : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (P : PolynomialPatch X s d)
    (g : nilmanifold.Niltest (fun _ : X => 1)) (h : (X → ℤ) → ℂ)
    (hg : ∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ))
    (hh : ∀ x, h x = (f x : ℂ) * g.eval x)
    (lo : X → ℤ) (H : X → ℕ) (M : ℕ) (a : X → ℤ) (target cost : ℝ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : Nonempty (IntegerResidueBox lo (fun i => lo i + H i) (fun _ => (M : ℤ)) a))
    (hcost : ResidueSliceLogCostLE N lo H M a cost)
    (hcomplexity : relativePatchComplexity P ≤ cost)
    (hscore : Real.exp (-cost) < (physicalResidueMean h lo H M a).re -
      target * (physicalResidueMean g.eval lo H M a).re) :
    RelativePatchSliceConclusion s N f target d cost :=
  relativePatchSliceConclusion_of_scalar_patch_transfer N f P h g.eval hg hh
    lo H M a target cost hM hbox hne hcost hcomplexity hscore

end Erdos3

end

end OAI

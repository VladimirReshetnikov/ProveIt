import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredStagedModelProductiveGood
import OAI.Combinatorics.Progressions.Estimates.RelativePatchSourceTestFinBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem relativePatchSourceTest_expect_physical
    {X Ω : Type*} [Fintype X] [Fintype Ω] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (physical : Ω → X → ℤ) (hphysical : ∀ u, physical u ∈ integerBox N) :
    (𝔼 u, relativePatchSourceTest N f a A (fun x => (physical u x : ℝ))) =
      𝔼 u, (f (physical u) - a) * A.value (fun x => (physical u x : ℝ)) := by
  apply Finset.expect_congr rfl
  intro u _
  rw [relativePatchSourceTest_integer, relativeBoxInput_eq N f (hphysical u)]

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {N : Fin nX → ℕ}
    {widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ}
    {bases : Finset (Fin nX → ℤ)}
    {f : (Fin nX → ℤ) → ℝ} {a gain : ℝ}
    {s d : ℕ} {A : PolynomialPatch (Fin nX) s d}
    {z : bases × rectangularWeightIndices 0 widths 1}

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

namespace AllocatedPathProductivity

theorem relativePatch_child_mem
    (hprod : AllocatedPathProductivity B U b S N widths bases
      (relativePatchSourceTest N f a A) gain z) :
    ∀ u ∈ integerBox sides,
      jointIntegerPhysicalSite u (z.1.val, z.2.val) ∈ integerBox N := by
  intro u hu
  exact hprod.2.2 ⟨u, hu⟩

theorem relativePatch_child_score
    (hprod : AllocatedPathProductivity B U b S N widths bases
      (relativePatchSourceTest N f a A) gain z) :
    gain / 2 ≤ 𝔼 u : integerBox sides,
      (f (jointIntegerPhysicalSite u.val (z.1.val, z.2.val)) - a) *
        A.value (fun x => (jointIntegerPhysicalSite u.val (z.1.val, z.2.val) x : ℝ)) := by
  have hscore : gain / 2 ≤ 𝔼 u : integerBox sides,
      relativePatchSourceTest N f a A
        (fun x => (jointIntegerPhysicalSite u.val (z.1.val, z.2.val) x : ℝ)) := hprod.2.1
  exact hscore.trans_eq (relativePatchSourceTest_expect_physical N f a A
    (fun u : integerBox sides => jointIntegerPhysicalSite u.val (z.1.val, z.2.val))
    (fun u => by simpa only [mem_integerBox] using hprod.2.2 u))

theorem relativePatch_child_unitInterval
    (hprod : AllocatedPathProductivity B U b S N widths bases
      (relativePatchSourceTest N f a A) gain z)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ u ∈ integerBox sides,
      f (jointIntegerPhysicalSite u (z.1.val, z.2.val)) ∈ Set.Icc (0 : ℝ) 1 := by
  intro u hu
  exact hf _ (hprod.2.2 ⟨u, hu⟩)

end AllocatedPathProductivity
end Erdos3.VectorPolynomial

end

end OAI

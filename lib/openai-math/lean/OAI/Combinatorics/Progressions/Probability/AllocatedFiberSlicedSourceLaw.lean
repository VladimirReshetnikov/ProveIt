import OAI.Combinatorics.Progressions.Estimates.AllocatedActiveContainedTupleMap
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineFixedPathRationalReference
import OAI.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex B degree
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

include hlen hfixed in
theorem allocatedFiberActiveProgression_contained (j : ActiveInput) :
    integerProgressionSupport (slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr ⟨j.1.val, j.2⟩) : ℤ)
      (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩)) ⊆
        Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  apply integerProgressionSupport_subset_of_fin
  intro t
  have hi := slice.fiberPrincipalParameter_inside hlen fixed hfixed ⟨j.1.val, j.2⟩ t
  simpa only [allocatedPrincipalSides_not_short B U basis S j.1 j.2] using hi

theorem allocatedFiberSliceLaw_sliced_source_complexMean
    (φ : (G → IntegerScalarCubeBox Empty S.value) →
      PrincipalIntegerTuples B degree Empty sides → ℂ) :
    let H := fun j : Input => slice.fiberParameterLength (Sum.inr j)
    let step := fun j : Input => ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr j)
    let start := fun j : Input => slice.fiberParameterStart fixed (Sum.inr j)
    let inside := slice.fiberPrincipalParameter_inside hlen fixed hfixed
    let pos := fun j : Input => slice.fiberParameterLength_pos hlen (Sum.inr j)
    let Hactive := principalAxisLength (fun a => ¬short a) H
    let stepActive := principalAxisLength (fun a => ¬short a) step
    let cActive := fun j : ActiveInput => start ⟨j.1.val, j.2⟩
    let hsubset := allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed
    let kernel := FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty
      (slice.length ⟨Sum.inl g, hkernel g⟩) (hlen ⟨Sum.inl g, hkernel g⟩))
    let active := FiniteProbabilityWeights.pi (fun j : ActiveInput =>
      integerScalarCubeWeights Empty (Hactive j) (pos ⟨j.1.val, j.2⟩))
    let embed := fun (x : ∀ g, IntegerScalarCubeBox Empty (slice.length ⟨Sum.inl g, hkernel g⟩)) g =>
      containedProgressionCubeMap Empty S.value (slice.length ⟨Sum.inl g, hkernel g⟩)
        q (slice.start ⟨Sum.inl g, hkernel g⟩) S.positive
        (slice.fiberKernelProgression_contained hkernel g) (x g)
    (slice.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      φ (kernelZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)
        (principalZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos).complexMean (fun u =>
        kernel.complexMean (fun x => active.complexMean (fun v =>
          φ (embed x) (principalAxisJoin short u
            (allocatedActiveContainedProgression B U basis S stepActive Hactive cActive hsubset v))))) := by
  intro H step start inside pos Hactive stepActive cActive hsubset kernel active embed
  rw [slice.fiberSliceLaw_kernel_principal_source_complexMean hlen fixed hfixed hkernel
    (fun _ => S.positive)]
  have hsubset' (j : ActiveInput) : integerProgressionSupport (cActive j) (stepActive j : ℤ)
      (Hactive j) ⊆ Finset.Ico (0 : ℤ) (principalAxisLength (fun a => ¬short a) sides j : ℤ) := by
    simpa only [cActive, stepActive, Hactive, start, step, H, principalAxisLength,
      allocatedPrincipalSides_not_short B U basis S j.1 j.2]
      using hsubset j
  have hfactor (x : ∀ g, IntegerScalarCubeBox Empty (slice.length ⟨Sum.inl g, hkernel g⟩)) :
      (principalAffineIntervalLaw B degree sides H step start inside pos).complexMean (φ (embed x)) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos).complexMean (fun u =>
        active.complexMean (fun v => φ (embed x) (principalAxisJoin short u
          (allocatedActiveContainedProgression B U basis S stepActive Hactive cActive hsubset v)))) := by
    have hh := principalAffineIntervalLaw_axis_contained_complexMean B degree sides H step start
      inside pos short (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)
      hsubset' (φ (embed x))
    rw [allocatedActiveContainedTupleMap_eq B U basis S stepActive Hactive cActive hsubset] at hh
    exact hh
  change kernel.complexMean (fun x =>
    (principalAffineIntervalLaw B degree sides H step start inside pos).complexMean (φ (embed x))) = _
  simp_rw [hfactor]
  exact FiniteProbabilityWeights.complexMean_commute kernel
    (allocatedInactiveAffineIntervalLaw B U basis S H step start inside pos) _

end Erdos3.VectorPolynomial

end

end OAI

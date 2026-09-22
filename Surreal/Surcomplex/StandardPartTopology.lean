import Surreal.Foundations.SignSequenceStandardPartTopology
import Surreal.Surcomplex.StandardPart
import Surreal.Surcomplex.TopologicalField
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Clopen monads in the actual surcomplex fine topology

This proves `a:prop:clopen` of `docs/surcomplex/analysis/article.tex`
for the constructed surcomplex field. Finite and infinitesimal elements
form clopen sets, all infinitesimal cosets are clopen, and nonzero affine
images of both sets are clopen. Native total separatedness, hence total
disconnectedness, follows by pulling back scalar clopen separators along
the two coordinates of the existing product topology.

The standard-part homomorphism on the finite subring is locally constant
and continuous. These statements concern the fine topology and ordinary
complex standard parts; they do not identify Hahn exponents or coefficients.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Set

noncomputable section

/-- Finiteness in the actual surcomplex field is clopen in its native fine topology. -/
theorem isClopen_setOf_isFinite : IsClopen {z : Surcomplex.{u} | IsFinite z} :=
  (SignSequence.isClopen_setOf_isFinite.preimage continuous_re).inter
    (SignSequence.isClopen_setOf_isFinite.preimage continuous_im)

/-- Infinitesimality is clopen in the actual product topology. -/
theorem isClopen_setOf_isInfinitesimal :
    IsClopen {z : Surcomplex.{u} | IsInfinitesimal z} :=
  (SignSequence.isClopen_setOf_isInfinitesimal.preimage continuous_re).inter
    (SignSequence.isClopen_setOf_isInfinitesimal.preimage continuous_im)

/-- Every infinitesimal coset is clopen, with no finiteness condition on its center. -/
theorem isClopen_monad (c : Surcomplex.{u}) :
    IsClopen {z : Surcomplex.{u} | IsInfinitesimal (z - c)} :=
  isClopen_setOf_isInfinitesimal.preimage (continuous_id.sub continuous_const)

/-- Nonzero affine maps are homeomorphisms for the already constructed fine topology. -/
theorem isClopen_affine_image {s : Set Surcomplex.{u}} (hs : IsClopen s)
    (b r : Surcomplex.{u}) (hr : r ≠ 0) :
    IsClopen ((fun z => b + r * z) '' s) := by
  let e := (Homeomorph.mulLeft₀ r hr).trans (Homeomorph.addLeft b)
  exact ⟨e.isClosedMap s hs.isClosed, e.isOpenMap s hs.isOpen⟩

/-- Every affine finite class `b + r O` is clopen for nonzero `r`. -/
theorem isClopen_affine_finite (b r : Surcomplex.{u}) (hr : r ≠ 0) :
    IsClopen ((fun z => b + r * z) '' {z : Surcomplex.{u} | IsFinite z}) :=
  isClopen_affine_image isClopen_setOf_isFinite b r hr

/-- Every scaled monad `b + r m` is clopen for nonzero `r`. -/
theorem isClopen_affine_infinitesimal (b r : Surcomplex.{u}) (hr : r ≠ 0) :
    IsClopen ((fun z => b + r * z) '' {z : Surcomplex.{u} | IsInfinitesimal z}) :=
  isClopen_affine_image isClopen_setOf_isInfinitesimal b r hr

/-- The normalized-difference description of a scaled monad is exact for nonzero scales. -/
theorem affine_infinitesimals_eq (b r : Surcomplex.{u}) (hr : r ≠ 0) :
    (fun z => b + r * z) '' {z : Surcomplex.{u} | IsInfinitesimal z} =
      {z | IsInfinitesimal ((z - b) / r)} := by
  ext z
  constructor
  · rintro ⟨ε, hε, rfl⟩
    simpa [hr] using hε
  · intro hz
    refine ⟨(z - b) / r, hz, ?_⟩
    dsimp only
    rw [mul_div_cancel₀ _ hr]
    simp

/-- Coordinate clopen separators distinguish every pair of actual surcomplex numbers. -/
theorem exists_isClopen_separating {z w : Surcomplex.{u}} (hzw : z ≠ w) :
    ∃ s : Set Surcomplex.{u}, IsClopen s ∧ z ∈ s ∧ w ∉ s := by
  by_cases hre : z.re = w.re
  · have him : z.im ≠ w.im := fun h => hzw (QuadraticAlgebra.ext hre h)
    obtain ⟨s, hs, hz, hw⟩ := SignSequence.exists_isClopen_separating him
    exact ⟨(fun x : Surcomplex.{u} => x.im) ⁻¹' s, hs.preimage continuous_im, hz, hw⟩
  · obtain ⟨s, hs, hz, hw⟩ := SignSequence.exists_isClopen_separating hre
    exact ⟨(fun x : Surcomplex.{u} => x.re) ⁻¹' s, hs.preimage continuous_re, hz, hw⟩

/-- The native fine topology is totally separated. -/
instance surcomplexTotallySeparatedSpace : TotallySeparatedSpace Surcomplex.{u} :=
  totallySeparatedSpace_iff_exists_isClopen.mpr
    (fun _ _ hzw => exists_isClopen_separating hzw)

/-- In particular, the fine topology is totally disconnected, as in `a:prop:clopen`. -/
theorem totallyDisconnectedSpace : TotallyDisconnectedSpace Surcomplex.{u} := inferInstance

/-- A complex standard-part fiber, restricted to finite elements, is exactly its monad. -/
theorem finite_standardPart_fiber_eq_monad (a : ℂ) :
    {z : Surcomplex.{u} | IsFinite z ∧ standardPart z = a} =
      {z | IsInfinitesimal (z - ofComplex a)} := by
  ext z
  constructor
  · rintro ⟨hz, ha⟩
    exact (infinitesimal_sub_ofComplex_iff hz).mpr ha
  · intro hz
    have hf : IsFinite z := by
      have hsum := finiteSubring.add_mem (finite_of_infinitesimal hz) (finite_ofComplex a)
      simpa only [sub_add_cancel, mem_finiteSubring] using hsum
    exact ⟨hf, (infinitesimal_sub_ofComplex_iff hf).mp hz⟩

/-- Each guarded standard-part fiber is clopen in the full surcomplex fine topology. -/
theorem isClopen_standardPart_fiber (a : ℂ) :
    IsClopen {z : Surcomplex.{u} | IsFinite z ∧ standardPart z = a} := by
  rw [finite_standardPart_fiber_eq_monad]
  exact isClopen_monad (ofComplex a)

/-- Standard part on its genuine finite domain is locally constant in the fine topology. -/
theorem isLocallyConstant_standardPartHom :
    IsLocallyConstant (standardPartHom : finiteSubring.{u} → ℂ) := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro a
  convert (isClopen_monad (ofComplex a)).isOpen.preimage
    (continuous_subtype_val : Continuous (fun z : finiteSubring.{u} => z.1)) using 1
  ext z
  exact (infinitesimal_sub_ofComplex_iff z.2).symm

/-- The standard-part ring homomorphism is continuous into ordinary `ℂ`. -/
theorem continuous_standardPartHom :
    Continuous (standardPartHom : finiteSubring.{u} → ℂ) :=
  isLocallyConstant_standardPartHom.continuous

end

end Surreal.Surcomplex

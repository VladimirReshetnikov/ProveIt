import Surreal.Surcomplex.StandardPartTopology

/-!
# Halos, punctures, and the ordinary boundary

This realizes `a:def:halo`, `a:rem:puncture`, and `a:rem:halonotball`
on the actual surcomplex field. A halo is the finite standard-part
preimage of an ordinary complex set. It is the union of precisely the
corresponding infinitesimal monads and is clopen for the fine topology.
Deleting an ordinary point removes its entire monad. The explicit point
`1 - ω⁻¹` is inside the full fine unit ball but outside the halo of the
ordinary unit disk, because its standard part is the boundary point one.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Set

noncomputable section

/-- The halo retains the genuine finite domain of standard part. -/
def halo (U : Set ℂ) : Set Surcomplex.{u} := {z | IsFinite z ∧ standardPart z ∈ U}

@[simp] theorem mem_halo {U : Set ℂ} {z : Surcomplex.{u}} :
    z ∈ halo U ↔ IsFinite z ∧ standardPart z ∈ U := Iff.rfl

@[simp] theorem ofComplex_mem_halo_iff {U : Set ℂ} {a : ℂ} :
    (ofComplex a : Surcomplex.{u}) ∈ halo U ↔ a ∈ U := by simp [finite_ofComplex]

@[simp] theorem halo_empty : halo.{u} ∅ = ∅ := by ext z; simp

@[simp] theorem halo_univ : halo.{u} Set.univ = {z | IsFinite z} := by ext z; simp

theorem halo_union (U V : Set ℂ) : halo.{u} (U ∪ V) = halo U ∪ halo V := by
  ext z
  simp only [mem_halo, mem_union]
  tauto

theorem halo_inter (U V : Set ℂ) : halo.{u} (U ∩ V) = halo U ∩ halo V := by
  ext z
  simp only [mem_halo, mem_inter_iff]
  tauto

theorem halo_sdiff (U V : Set ℂ) : halo.{u} (U \ V) = halo U \ halo V := by
  ext z
  simp only [mem_halo, mem_sdiff]
  tauto

/-- A singleton lifts to its entire infinitesimal monad. -/
theorem halo_singleton (a : ℂ) :
    halo.{u} {a} = {z | IsInfinitesimal (z - ofComplex a)} := by
  simpa only [halo, mem_singleton_iff] using finite_standardPart_fiber_eq_monad a

@[simp] theorem halo_singleton_zero : halo.{u} {0} = {z | IsInfinitesimal z} := by
  simpa using halo_singleton (0 : ℂ)

/-- Puncturing an ordinary domain deletes the whole infinitesimal monad. -/
theorem halo_punctured (U : Set ℂ) :
    halo.{u} (U \ {0}) = halo U \ {z | IsInfinitesimal z} := by
  rw [halo_sdiff, halo_singleton_zero]

/-- The halo consists precisely of monads centered at the ordinary points in the set. -/
theorem halo_eq_iUnion_monads (U : Set ℂ) :
    halo.{u} U = ⋃ a ∈ U, {z | IsInfinitesimal (z - ofComplex a)} := by
  simp_rw [← halo_singleton]
  ext z
  simp only [mem_halo, mem_singleton_iff, mem_iUnion]
  constructor
  · rintro ⟨hz, ha⟩
    exact ⟨standardPart z, ha, hz, rfl⟩
  · rintro ⟨a, ha, hz, rfl⟩
    exact ⟨hz, ha⟩

/-- The displayed constant-plus-infinitesimal description of a halo. -/
theorem mem_halo_iff_exists {U : Set ℂ} {z : Surcomplex.{u}} :
    z ∈ halo U ↔ ∃ a ∈ U, ∃ ε : Surcomplex.{u}, IsInfinitesimal ε ∧ z = ofComplex a + ε := by
  rw [halo_eq_iUnion_monads]
  simp only [mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, hε⟩
    exact ⟨a, ha, z - ofComplex a, hε, by simp⟩
  · rintro ⟨a, ha, ε, hε, rfl⟩
    exact ⟨a, ha, by simpa using hε⟩

/-- Every nonzero scale chart has the normalized-coordinate membership from the definition. -/
theorem affine_halo_eq (U : Set ℂ) (b r : Surcomplex.{u}) (hr : r ≠ 0) :
    (fun z => b + r * z) '' halo U = {z | (z - b) / r ∈ halo U} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [hr] using hw
  · intro hz
    refine ⟨(z - b) / r, hz, ?_⟩
    dsimp only
    rw [mul_div_cancel₀ _ hr]
    simp

/-- The actual surcomplex infinitesimal monad contains nonzero points. -/
theorem exists_nonzero_infinitesimal : ∃ z : Surcomplex.{u}, z ≠ 0 ∧ IsInfinitesimal z := by
  refine ⟨ofReal (SignSequence.ofOrdinal Ordinal.omega0)⁻¹,
    (map_ne_zero ofReal).mpr SignSequence.inv_omega0_pos.ne',
    SignSequence.infinitesimal_inv_omega0, SignSequence.infinitesimal_zero⟩

/-- If the ordinary domain contains zero, removing its monad really differs from removing a point. -/
theorem halo_punctured_ne_remove_zero {U : Set ℂ} (hU : 0 ∈ U) :
    halo.{u} (U \ {0}) ≠ halo U \ {0} := by
  obtain ⟨z, hz, hε⟩ := exists_nonzero_infinitesimal.{u}
  have hf := finite_of_infinitesimal hε
  have hs : standardPart z = 0 := (standardPart_eq_zero_iff hf).mpr hε
  have hmem : z ∈ halo U \ {0} := ⟨⟨hf, hs ▸ hU⟩, hz⟩
  intro heq
  rw [← heq, halo_punctured] at hmem
  exact hmem.2 hε

/-- Even arbitrary ordinary subsets give fine-open halos. -/
theorem isOpen_halo (U : Set ℂ) : IsOpen (halo.{u} U) := by
  rw [halo_eq_iUnion_monads]
  exact isOpen_iUnion fun a => isOpen_iUnion fun _ => (isClopen_monad (ofComplex a)).isOpen

/-- The finite ring and the complementary standard-part fibers also make every halo closed. -/
theorem isClopen_halo (U : Set ℂ) : IsClopen (halo.{u} U) := by
  refine ⟨?_, isOpen_halo U⟩
  have heq : halo.{u} U = {z | IsFinite z} \ halo Uᶜ := by
    ext z
    simp only [mem_halo, mem_sdiff, mem_compl_iff, mem_setOf_eq]
    tauto
  rw [heq]
  exact isClopen_setOf_isFinite.isClosed.sdiff (isOpen_halo Uᶜ)

/-- All nonzero affine scale charts of halos are clopen in the same fine topology. -/
theorem isClopen_affine_halo (U : Set ℂ) (b r : Surcomplex.{u}) (hr : r ≠ 0) :
    IsClopen ((fun z => b + r * z) '' halo U) :=
  isClopen_affine_image (isClopen_halo U) b r hr

/-- The explicit point just inside the ordinary unit boundary. -/
def unitDiskBoundaryWitness : Surcomplex.{u} :=
  ofReal (1 - (SignSequence.ofOrdinal Ordinal.omega0)⁻¹)

theorem standardPart_unitDiskBoundaryWitness :
    standardPart unitDiskBoundaryWitness.{u} = 1 := by
  have hε := SignSequence.infinitesimal_inv_omega0.{u}
  have hf := SignSequence.finite_of_infinitesimal hε
  apply Complex.ext
  · change SignSequence.standardPart (1 - (SignSequence.ofOrdinal Ordinal.omega0)⁻¹) = 1
    rw [SignSequence.standardPart_sub SignSequence.finite_one hf,
      SignSequence.standardPart_one, (SignSequence.standardPart_eq_zero_iff hf).mpr hε,
      sub_zero]
  · exact SignSequence.standardPart_zero

theorem modulus_unitDiskBoundaryWitness_lt_one : modulus unitDiskBoundaryWitness.{u} < 1 := by
  have hpos := SignSequence.inv_omega0_pos.{u}
  have hlt : (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u})⁻¹ < 1 := by
    simpa using SignSequence.inv_omega0_lt_ofReal (1 : ℝ) zero_lt_one
  rw [unitDiskBoundaryWitness, modulus_ofReal, abs_of_pos (sub_pos.mpr hlt)]
  exact sub_lt_self 1 hpos

theorem unitDiskBoundaryWitness_not_mem_halo_unitDisk :
    unitDiskBoundaryWitness.{u} ∉ halo {a : ℂ | norm a < 1} := by
  intro hz
  have h := hz.2
  rw [standardPart_unitDiskBoundaryWitness] at h
  change norm (1 : ℂ) < 1 at h
  norm_num [Complex.norm_def, Complex.normSq_apply] at h

/-- The halo of the ordinary open disk differs from the full fine open unit ball. -/
theorem halo_unitDisk_ne_fineBall :
    halo.{u} {a : ℂ | norm a < 1} ≠ fineBall 0 1 := by
  intro heq
  apply unitDiskBoundaryWitness_not_mem_halo_unitDisk.{u}
  rw [heq, fineBall_eq_modulus 0 zero_lt_one]
  simpa using modulus_unitDiskBoundaryWitness_lt_one.{u}

end

end Surreal.Surcomplex

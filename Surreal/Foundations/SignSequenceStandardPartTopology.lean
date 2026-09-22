import Surreal.Foundations.SignSequenceStandardPart
import Surreal.Foundations.SignSequenceUniformity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Clopen finite and infinitesimal sets in the actual sign field

This proves the real-coordinate version of `a:prop:clopen` in
`docs/surcomplex/analysis/article.tex`. The native order topology makes
the finite-element additive subgroup and the infinitesimal additive
subgroup clopen, as well as their translates and their affine images
under nonzero scales. Scaled infinitesimal cosets separate every pair of
distinct points, giving native total separatedness and hence total
disconnectedness.

The open neighborhood of zero is witnessed by the already constructed
positive infinitesimal `ω⁻¹`. No real-valued metric, Hahn normal-form
identification, or smallness hypothesis on the whole carrier is used.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

open Set Filter Topology

theorem infinitesimal_add {x y : SignSequence.{u}}
    (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) : IsInfinitesimal (x + y) :=
  (lt_min hx hy).trans_le (ArchimedeanClass.min_le_mk_add x y)

theorem infinitesimal_neg {x : SignSequence.{u}} (hx : IsInfinitesimal x) :
    IsInfinitesimal (-x) := by
  simpa only [IsInfinitesimal, ArchimedeanClass.mk_neg] using hx

theorem infinitesimal_of_abs_le {x y : SignSequence.{u}} (hxy : |x| ≤ |y|)
    (hy : IsInfinitesimal y) : IsInfinitesimal x := by
  apply (isInfinitesimal_iff_forall_nat_abs_lt x).mpr
  intro n hn
  exact hxy.trans_lt ((isInfinitesimal_iff_forall_nat_abs_lt y).mp hy n hn)

/-- The positive infinitesimal that supplies an open neighborhood inside the ideal. -/
theorem infinitesimal_inv_omega0 :
    IsInfinitesimal ((ofOrdinal Ordinal.omega0 : SignSequence.{u})⁻¹) := by
  apply (isInfinitesimal_iff_forall_real_abs_lt _).mpr
  intro r hr
  rw [abs_of_pos inv_omega0_pos]
  exact inv_omega0_lt_ofReal r hr

/-- The additive subgroup of all finite sign-field elements. -/
def finiteAddSubgroup : AddSubgroup SignSequence.{u} where
  carrier := {x | IsFinite x}
  zero_mem' := finite_zero
  add_mem' := finite_add
  neg_mem' := finite_neg

/-- The additive subgroup of all infinitesimal sign-field elements. -/
def infinitesimalAddSubgroup : AddSubgroup SignSequence.{u} where
  carrier := {x | IsInfinitesimal x}
  zero_mem' := infinitesimal_zero
  add_mem' := infinitesimal_add
  neg_mem' := infinitesimal_neg

/-- A ball with positive infinitesimal radius lies inside the infinitesimals. -/
theorem infinitesimals_mem_nhds_zero :
    {x : SignSequence.{u} | IsInfinitesimal x} ∈ 𝓝 0 := by
  apply Filter.mem_of_superset
    ((nhds_hasBasis_abs_sub (0 : SignSequence.{u})).mem_of_mem inv_omega0_pos)
  intro x hx
  apply infinitesimal_of_abs_le (y := (ofOrdinal Ordinal.omega0)⁻¹) _ infinitesimal_inv_omega0
  have hx' : |x| < (ofOrdinal Ordinal.omega0)⁻¹ := by simpa using hx
  simpa only [abs_of_pos inv_omega0_pos] using hx'.le

theorem isOpen_setOf_isInfinitesimal :
    IsOpen {x : SignSequence.{u} | IsInfinitesimal x} :=
  infinitesimalAddSubgroup.isOpen_of_mem_nhds infinitesimals_mem_nhds_zero

/-- The infinitesimals are clopen in the native order topology. -/
theorem isClopen_setOf_isInfinitesimal :
    IsClopen {x : SignSequence.{u} | IsInfinitesimal x} :=
  ⟨infinitesimalAddSubgroup.isClosed_of_isOpen isOpen_setOf_isInfinitesimal,
    isOpen_setOf_isInfinitesimal⟩

theorem isOpen_setOf_isFinite : IsOpen {x : SignSequence.{u} | IsFinite x} :=
  AddSubgroup.isOpen_mono (H₁ := infinitesimalAddSubgroup) (H₂ := finiteAddSubgroup)
    (fun _ hx => finite_of_infinitesimal hx) isOpen_setOf_isInfinitesimal

/-- The entire finite-element valuation ring is clopen. -/
theorem isClopen_setOf_isFinite : IsClopen {x : SignSequence.{u} | IsFinite x} :=
  ⟨finiteAddSubgroup.isClosed_of_isOpen isOpen_setOf_isFinite, isOpen_setOf_isFinite⟩

/-- Every infinitesimal coset is clopen, regardless of whether its center is finite. -/
theorem isClopen_monad (c : SignSequence.{u}) :
    IsClopen {x : SignSequence.{u} | IsInfinitesimal (x - c)} :=
  isClopen_setOf_isInfinitesimal.preimage (continuous_id.sub continuous_const)

/-- Nonzero affine changes of coordinates preserve clopen subsets. -/
theorem isClopen_affine_image {s : Set SignSequence.{u}} (hs : IsClopen s)
    (b r : SignSequence.{u}) (hr : r ≠ 0) :
    IsClopen ((fun x => b + r * x) '' s) := by
  let e := (Homeomorph.mulLeft₀ r hr).trans (Homeomorph.addLeft b)
  exact ⟨e.isClosedMap s hs.isClosed, e.isOpenMap s hs.isOpen⟩

/-- The finite-ring affine classes `b + r O` are clopen for every nonzero scale. -/
theorem isClopen_affine_finite (b r : SignSequence.{u}) (hr : r ≠ 0) :
    IsClopen ((fun x => b + r * x) '' {x : SignSequence.{u} | IsFinite x}) :=
  isClopen_affine_image isClopen_setOf_isFinite b r hr

/-- The scaled monads `b + r m` are clopen for every nonzero scale. -/
theorem isClopen_affine_infinitesimal (b r : SignSequence.{u}) (hr : r ≠ 0) :
    IsClopen ((fun x => b + r * x) '' {x : SignSequence.{u} | IsInfinitesimal x}) :=
  isClopen_affine_image isClopen_setOf_isInfinitesimal b r hr

/-- A coordinate description of a scaled monad; the nonzero guard makes it
exactly the affine image appearing in the source. -/
theorem affine_infinitesimals_eq (b r : SignSequence.{u}) (hr : r ≠ 0) :
    (fun x => b + r * x) '' {x : SignSequence.{u} | IsInfinitesimal x} =
      {x | IsInfinitesimal ((x - b) / r)} := by
  ext x
  constructor
  · rintro ⟨ε, hε, rfl⟩
    simpa [hr] using hε
  · intro hx
    refine ⟨(x - b) / r, hx, ?_⟩
    dsimp only
    rw [mul_div_cancel₀ _ hr]
    simp

/-- Distinct points are separated by a clopen scaled infinitesimal coset. -/
theorem exists_isClopen_separating {x y : SignSequence.{u}} (hxy : x ≠ y) :
    ∃ s : Set SignSequence.{u}, IsClopen s ∧ x ∈ s ∧ y ∉ s := by
  refine ⟨{z | IsInfinitesimal ((z - x) / (y - x))},
    isClopen_setOf_isInfinitesimal.preimage
      ((continuous_id.sub continuous_const).div_const (y - x)),
    ?_, ?_⟩
  · simp
  · change ¬ IsInfinitesimal ((y - x) / (y - x))
    rw [div_self (sub_ne_zero.mpr hxy.symm)]
    simp [IsInfinitesimal]

/-- Native total separatedness, which also supplies total disconnectedness. -/
instance signSequenceTotallySeparatedSpace : TotallySeparatedSpace SignSequence.{u} :=
  totallySeparatedSpace_iff_exists_isClopen.mpr
    (fun _ _ hxy => exists_isClopen_separating hxy)

theorem totallyDisconnectedSpace : TotallyDisconnectedSpace SignSequence.{u} := inferInstance

end

end Surreal.Foundations.SignSequence

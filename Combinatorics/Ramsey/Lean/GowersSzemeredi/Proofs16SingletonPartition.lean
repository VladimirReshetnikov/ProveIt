import GowersSzemeredi.Proofs05BoxPartition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The singleton branch of the Section 16 local partition construction

`section16_local_linearity_singletons` is in `Proofs16SingletonPartitionSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A genuine length-one box at a point, with no inflated formal lengths. -/
def pointSingletonBox {N d : Nat} (x : Point N d) : Box N d where
  axis i := { start := x i, step := 1, length := 1 }
  commonDiff := 1
  axis_step _ := rfl

@[simp] theorem pointSingletonBox_axis_carrier {N d : Nat} (x : Point N d) (i : Fin d) :
    ((pointSingletonBox x).axis i).carrier = {x i} := by
  simp [pointSingletonBox, ModAP.carrier]

@[simp] theorem pointSingletonBox_carrier {N d : Nat} [NeZero N] (x : Point N d) :
    (pointSingletonBox x).carrier = {x} := by
  ext y
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and,
    pointSingletonBox_axis_carrier, Finset.mem_singleton]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

theorem pointSingletonBox_isProper {N d : Nat} (x : Point N d) :
    (pointSingletonBox x).IsProper := by
  intro i
  change ((pointSingletonBox x).axis i).carrier.card = 1
  rw [pointSingletonBox_axis_carrier]
  simp

@[simp] theorem pointSingletonBox_width {N d : Nat} (hd : 0 < d) (x : Point N d) :
    (pointSingletonBox x).width = 1 := by
  apply le_antisymm
  · exact (pointSingletonBox x).width_le_axis_length ⟨0, hd⟩
  · exact (pointSingletonBox x).le_width_of_le_axis hd (fun _ => le_rfl)

/-- Partition any box into its points, retaining actual width one in
positive dimension and allowing the empty partition for the empty box. -/
theorem box_singleton_partition {N d : Nat} [NeZero N] (P : Box N d) :
    ∃ M : Nat, ∃ x : Fin M → Point N d,
      IsBoxPartition (fun j => pointSingletonBox (x j)) P := by
  let e := Fintype.equivFin {x // x ∈ P.carrier}
  refine ⟨Fintype.card {x // x ∈ P.carrier}, fun j => (e.symm j).val, ?_⟩
  constructor
  · intro x
    simp only [pointSingletonBox_carrier, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
  · intro i j hij
    simp only [pointSingletonBox_carrier, Finset.disjoint_singleton]
    exact fun h => (bne_iff_ne.mp hij) (e.symm.injective (Subtype.ext h))

/-- Every map is affine when restricted to a subset of a singleton. -/
theorem LinearOn.of_subset_singleton {N : Nat} (A : Finset (ZMod N))
    (f : ZMod N → ZMod N) (y : ZMod N) (hA : A ⊆ {y}) : LinearOn A f := by
  refine ⟨0, f y, ?_⟩
  intro x hx
  have hxy : x = y := Finset.mem_singleton.mp (hA hx)
  simp [hxy]

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16OrientedPartitions
import GowersSzemeredi.Proofs16ProductGeometry

/-! # Tiling products after a change of common difference

A base box in a short unit-step index interval determines a small signed
step. Partitioning a sufficiently long unit-step final axis at that step
makes their Cartesian product a union of genuine common-step boxes.

`box_product_tiling_of_short_axis` is in `Proofs16ProductTilingSide`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Append a final axis with the same common difference. -/
def boxAppend {N k : Nat} (R : Box N k) (I : ModAP N)
    (hstep : I.step = R.commonDiff) : Box N (k + 1) where
  axis := Fin.snoc R.axis I
  commonDiff := R.commonDiff
  axis_step i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hstep
    · simpa only [Fin.snoc_castSucc] using R.axis_step j

theorem boxAppend_isProper {N k : Nat} (R : Box N k) (I : ModAP N)
    (hstep : I.step = R.commonDiff) (hR : R.IsProper) (hI : I.IsProper) :
    (boxAppend R I hstep).IsProper := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [boxAppend, Fin.snoc_last] using hI
  · simpa only [boxAppend, Fin.snoc_castSucc] using hR j

theorem boxAppend_width_ge {N k w : Nat} (R : Box N k) (I : ModAP N)
    (hstep : I.step = R.commonDiff) (hR : w ≤ R.width) (hI : w ≤ I.length) :
    w ≤ (boxAppend R I hstep).width := by
  apply Box.le_width_of_le_axis _ (by omega)
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [boxAppend, Fin.snoc_last] using hI
  · simpa only [boxAppend, Fin.snoc_castSucc] using hR.trans (R.width_le_axis_length j)

/-- Appending a matching axis realizes the displayed Cartesian product. -/
theorem boxAppend_product {N k : Nat} [NeZero N] (R : Box N k) (I : ModAP N)
    (hstep : I.step = R.commonDiff) :
    IsLastCoordinateBoxProduct (boxAppend R I hstep) R I := by
  refine ⟨?_, rfl, hstep⟩
  ext x
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    exact ⟨fun i => by simpa only [boxAppend, Fin.snoc_castSucc, section16Init] using hx i.castSucc,
      by simpa only [boxAppend, Fin.snoc_last, section16Last] using hx (Fin.last k)⟩
  · intro hx i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [boxAppend, Fin.snoc_last, section16Last] using hx.2
    · simpa only [boxAppend, Fin.snoc_castSucc, section16Init] using hx.1 j

/-- Partitioning only the last factor partitions the entire product, even
when the unpartitioned product has no common-step box presentation. -/
theorem boxAppend_partition {N k M : Nat} [NeZero N]
    (R : Box N k) (I : ModAP N) (J : Fin M → ModAP N)
    (hstep : ∀ j, (J j).step = R.commonDiff)
    (hpart : IsPartition (fun j => (J j).carrier) I.carrier) :
    IsPartition (fun j => (boxAppend R (J j) (hstep j)).carrier)
      (Finset.univ.filter (fun x : Point N (k + 1) =>
        section16Init x ∈ R.carrier ∧ section16Last x ∈ I.carrier)) := by
  have hmem (j : Fin M) (x : Point N (k + 1)) :
      x ∈ (boxAppend R (J j) (hstep j)).carrier ↔
        section16Init x ∈ R.carrier ∧ section16Last x ∈ (J j).carrier := by
    rw [(boxAppend_product R (J j) (hstep j)).1]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
    constructor
    · rintro ⟨hx, hy⟩
      obtain ⟨j, hj⟩ := (hpart.1 _).mp hy
      exact ⟨j, hx, hj⟩
    · rintro ⟨j, hx, hj⟩
      exact ⟨hx, (hpart.1 _).mpr ⟨j, hj⟩⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact Finset.disjoint_left.mp (hpart.2 i j hij) ((hmem i x).mp hi).2 ((hmem j x).mp hj).2

end LeanProofs.GowersSzemeredi

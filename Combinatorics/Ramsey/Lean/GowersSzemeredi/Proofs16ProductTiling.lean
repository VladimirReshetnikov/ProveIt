import GowersSzemeredi.Proofs16OrientedPartitions
import GowersSzemeredi.Proofs16ProductGeometry

/-! # Tiling products after a change of common difference

A base box in a short unit-step index interval determines a small signed
step. Partitioning a sufficiently long unit-step final axis at that step
makes their Cartesian product a union of genuine common-step boxes.
-/
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
  classical
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

/-- Short containment of one base axis supplies a tiling at the base's
common difference. All final axes have length v-1 or v; all boxes are proper. -/
theorem box_product_tiling_of_short_axis {N k n v : Nat} [NeZero N]
    (R : Box N k) (I : ModAP N) (i : Fin k)
    (hR : R.IsProper) (hI : I.IsProper) (hIstep : I.step = 1)
    (hn : 2 * n ≤ N) (hsub : (R.axis i).carrier ⊆ (modInterval N 0 n).carrier)
    (hL : n ≤ I.length) (hv : 1 ≤ v) (hfit : v ^ 2 ≤ R.width - 1) :
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier)
        (Finset.univ.filter (fun x : Point N (k + 1) =>
          section16Init x ∈ R.carrier ∧ section16Last x ∈ I.carrier)) ∧
      (∀ j, (S j).IsProper ∧ v - 1 ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) R (J j)) ∧
      ∀ j, 0 < (J j).length ∧ ((J j).length = v - 1 ∨ (J j).length = v) := by
  have haxis := R.width_le_axis_length i
  obtain ⟨M, J, hpart, hprop, hstep⟩ :=
    (R.axis i).partition_at_short_interval_step I (hR i) hI hn hsub hL hv
      (hfit.trans (Nat.sub_le_sub_right haxis 1))
  have hstep' (j : Fin M) : (J j).step = R.commonDiff := by
    rw [hstep j, hIstep, mul_one, R.axis_step]
  refine ⟨M, fun j => boxAppend R (J j) (hstep' j), J,
    boxAppend_partition R I J hstep' hpart, ?_, ?_, ?_⟩
  · intro j
    refine ⟨boxAppend_isProper R (J j) (hstep' j) hR (hprop j).1,
      boxAppend_width_ge R (J j) (hstep' j) ?_ ?_⟩
    · have hv2 : v ≤ v ^ 2 := by nlinarith
      omega
    · rcases (hprop j).2.2 with h | h <;> omega
  · intro j
    exact boxAppend_product R (J j) (hstep' j)
  · intro j
    exact (hprop j).2

end LeanProofs.GowersSzemeredi

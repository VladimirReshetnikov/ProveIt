import GowersSzemeredi.Proofs16Slicing
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Small common-difference products via a multilinear lift and slice

`lemma_16_1_holds`, `proper_lemma_16_1`, `section16K_eq_multilinear`,
`section16RecurrenceExponent_eq_multilinear` and
`section16WidthThreshold_eq_multilinear` are in `Proofs16Lemma1Side`, outside
the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Multiplication by a new variable preserves multilinearity. -/
theorem IsMultilinear.mul_new_coordinate {N k : Nat}
    {mu : Point N k → ZMod N} (hmu : IsMultilinear mu) :
    IsMultilinear (fun z : Point N (k + 1) => mu (Fin.tail z) * z 0) := by
  obtain ⟨c, hc⟩ := hmu
  refine ⟨fun e => if e 0 then c (Fin.tail e) else 0, ?_⟩
  intro z
  dsimp only
  rw [hc, ← (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail, Finset.mul_sum, mul_comm, mul_left_comm]

/-- A diameter estimate for the lifted function bounds its first-coordinate
increment, even when the selected slice lies at the final progression index. -/
theorem lifted_diameter_commonDiff {N k : Nat} [NeZero N]
    (Q : Box N (k + 1)) (mu : Point N k → ZMod N) (s : Real)
    (hdiam : diameterAtMostReal
      (Q.carrier.image (fun z => mu (Fin.tail z) * z 0)) s)
    (hwidth : 2 ≤ Q.width) (y : ZMod N) (hy : y ∈ (Q.axis 0).carrier)
    (x : Point N k) (hx : x ∈ (boxTail Q).carrier) :
    (centeredAbs (mu x * Q.commonDiff) : Real) ≤ s := by
  have hbase : mu x * y ∈ Q.carrier.image (fun z => mu (Fin.tail z) * z 0) := by
    refine Finset.mem_image.mpr ⟨Fin.cons y x, (mem_boxTail_cons _ _ _).mpr ⟨hy, hx⟩, ?_⟩
    simp
  obtain hnext | hprev := (Q.axis 0).adjacent_mem (hwidth.trans (Q.width_le_axis_length 0)) hy
  · have hnext' : mu x * (y + Q.commonDiff) ∈
        Q.carrier.image (fun z => mu (Fin.tail z) * z 0) := by
      refine Finset.mem_image.mpr ⟨Fin.cons (y + (Q.axis 0).step) x,
        (mem_boxTail_cons _ _ _).mpr ⟨hnext, hx⟩, ?_⟩
      simp [Q.axis_step]
    have h := hdiam.centeredAbs_sub_le hnext' hbase
    convert h using 2
    congr 1
    ring
  · have hprev' : mu x * (y - Q.commonDiff) ∈
        Q.carrier.image (fun z => mu (Fin.tail z) * z 0) := by
      refine Finset.mem_image.mpr ⟨Fin.cons (y - (Q.axis 0).step) x,
        (mem_boxTail_cons _ _ _).mpr ⟨hprev, hx⟩, ?_⟩
      simp [Q.axis_step]
    have h := hdiam.centeredAbs_sub_le hbase hprev'
    convert h using 2
    congr 1
    ring

end LeanProofs.GowersSzemeredi

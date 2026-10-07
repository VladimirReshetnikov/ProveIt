import GowersSzemeredi.Proofs13EdgeDensity

/-! Vertical Freiman structure gives constant edge differences on each
single-column cell, without a Fourier or Bohr-radius budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_vertical_difference_same_column {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) {v w : Pair N}
    (hv : v ∈ verticalEdgeDomain S.A h) (hw : w ∈ verticalEdgeDomain S.A h)
    (hx : v.1 = w.1) :
    verticalPhiDifference S.phi h v = verticalPhiDifference S.phi h w := by
  classical
  obtain ⟨x, y⟩ := v
  obtain ⟨x', z⟩ := w
  simp only at hx
  subst x'
  have hv' := (Finset.mem_filter.mp hv).2
  have hw' := (Finset.mem_filter.mp hw).2
  have hf := (S.separately_freiman.1 x).mono (by norm_num : 2 ≤ 8)
  have hy : y ∈ verticalSection S.A x := by simpa [verticalSection] using hv'.1
  have hyh : y + h ∈ verticalSection S.A x := by simpa [verticalSection] using hv'.2
  have hz : z ∈ verticalSection S.A x := by simpa [verticalSection] using hw'.1
  have hzh : z + h ∈ verticalSection S.A x := by simpa [verticalSection] using hw'.2
  have heq := hf.add_eq_add hyh hz hzh hy (show y + h + z = z + h + y by ring)
  dsimp only [verticalPhiDifference]
  linear_combination heq

theorem section13_single_column_linear {N : Nat} [NeZero N]
    (S : Section13Context N) (h x : ZMod N) :
    LinearOnDomain ((verticalEdgeDomain S.A h).filter fun z => z.1 = x)
      (fun z : Pair N => z.1) (verticalPhiDifference S.phi h) := by
  classical
  let A := (verticalEdgeDomain S.A h).filter fun z => z.1 = x
  by_cases hA : A.Nonempty
  · obtain ⟨v, hv⟩ := hA
    refine ⟨0, verticalPhiDifference S.phi h v, ?_⟩
    intro w hw
    simp only [zero_mul, zero_add]
    exact section13_vertical_difference_same_column S h
      (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hv).1
      ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hv).2.symm)
  · refine ⟨0, 0, ?_⟩
    intro w hw
    exact (hA ⟨w, hw⟩).elim

end LeanProofs.GowersSzemeredi

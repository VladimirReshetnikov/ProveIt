import OAI.Combinatorics.Progressions.Lattices.RectangularLatticeCells

namespace OAI

section

namespace Erdos3

theorem rectangularLatticeCell_disjoint {I : Type*}
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Pairwise (fun k l => Disjoint (rectangularLatticeCell a S k) (rectangularLatticeCell a S l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hkl (((rectangularLatticeCell_iff a S hS x k).mp hx).symm.trans
    ((rectangularLatticeCell_iff a S hS x l).mp hy))

theorem rectangularLatticePoint_mem_cell {I : Type*}
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (k : I → ℤ) :
    rectangularLatticePoint a S k ∈ rectangularLatticeCell a S k := by
  intro i _
  change ((k i : ℝ) - a i) / S i ∈
    Set.Ico (((k i : ℝ) - a i) / S i) (((k i : ℝ) + 1 - a i) / S i)
  exact ⟨le_rfl, (div_lt_div_iff_of_pos_right (hS i)).mpr (by linarith)⟩

theorem rectangularLatticeCell_point_distance {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmesh : ∀ i, 1 / S i ≤ δ) (k : I → ℤ) (x : I → ℝ)
    (hx : x ∈ rectangularLatticeCell a S k) :
    ‖x - rectangularLatticePoint a S k‖ ≤ δ := by
  have h := rectangularLatticeSample_error a S hS hδ hmesh x
  have hk := (rectangularLatticeCell_iff a S hS x k).mp hx
  rw [rectangularLatticeSample, hk, norm_sub_rev] at h
  exact h

theorem integerBoxCell_unit_bound {I : Type*} (L : ℕ) (hL : 0 < L) (k : I → ℤ)
    (hk : ∀ i, -(L : ℤ) ≤ k i ∧ k i < L) (x : I → ℝ)
    (hx : x ∈ rectangularLatticeCell (fun _ => 0) (fun _ => (L : ℝ)) k) :
    ∀ i, |x i| ≤ 1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  intro i
  have hi := hx i (Set.mem_univ i)
  change ((k i : ℝ) - 0) / (L : ℝ) ≤ x i ∧
    x i < ((k i : ℝ) + 1 - 0) / (L : ℝ) at hi
  simp only [sub_zero] at hi
  have hlo : -(L : ℝ) ≤ (k i : ℝ) := by exact_mod_cast (hk i).1
  have hhi : (k i : ℝ) + 1 ≤ L := by exact_mod_cast (show k i + 1 ≤ (L : ℤ) by have := (hk i).2; omega)
  have h1 := (div_le_iff₀ hL').mp hi.1
  have h2 := (lt_div_iff₀ hL').mp hi.2
  apply abs_le.mpr
  constructor <;> nlinarith

end Erdos3

end

end OAI

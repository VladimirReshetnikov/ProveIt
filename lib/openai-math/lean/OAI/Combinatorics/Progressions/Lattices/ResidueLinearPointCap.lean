import OAI.Combinatorics.Progressions.Geometry.CoordinateProductCap
import OAI.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerArrayLinearForm {D : Type*} [Fintype D] (c z : D → ℤ) : ℤ := ∑ d, c d * z d

theorem integerArrayLinearForm_affine_join {D : Type*} [Fintype D] [DecidableEq D]
    (c a q : D → ℤ) (j : D) (tail : {d : D // d ≠ j} → ℤ) (x : ℤ) :
    integerArrayLinearForm c (fun d => a d + q d * coordinateJoin j tail x d) =
      c j * (a j + q j * x) + ∑ d : {d : D // d ≠ j}, c d.val * (a d.val + q d.val * tail d) := by
  rw [integerArrayLinearForm, Fintype.sum_eq_add_sum_subtype_ne _ j]
  simp only [coordinateJoin_pivot, coordinateJoin_other]

theorem integerArrayLinearForm_pivot_injective {D : Type*} [Fintype D] [DecidableEq D]
    (c a q : D → ℤ) (j : D) (hc : c j ≠ 0) (hq : q j ≠ 0)
    (tail : {d : D // d ≠ j} → ℤ) :
    Function.Injective (fun x => integerArrayLinearForm c
      (fun d => a d + q d * coordinateJoin j tail x d)) := by
  intro x y h
  simp only [integerArrayLinearForm_affine_join] at h
  exact mul_left_cancel₀ hq (add_left_cancel (mul_left_cancel₀ hc (add_right_cancel h)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSmoothPMF_linear_cap {K I : Type*} [Fintype K] [Fintype I]
    (c residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus W))
    (j : K × I) (hc : c j ≠ 0)
    (hscale : 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W j) (y : ℤ) :
    ((residueSmoothPMF residue modulus hmodulus W hW hZ).map (integerArrayLinearForm c) y).toReal ≤
      2*(modulus j.2 : ℝ)/W j := by
  rw [residueSmoothPMF, PMF.map_comp, residueSmoothIndexPMF]
  have hq : (modulus j.2 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hmodulus j.2))
  have h := shiftedSmoothProductPMF_coordinate_cap (residueProfileCenter residue modulus)
    (residueProfileWidth modulus W) (residueProfileWidth_pos modulus W hmodulus hW) hZ j
    (integerArrayLinearForm c ∘ residueLatticeArray residue modulus)
    (integerArrayLinearForm_pivot_injective c residue (fun d => (modulus d.2 : ℤ)) j hc hq)
    hscale y
  simpa only [residueProfileWidth, div_div_eq_mul_div] using h

theorem selectedResidueSmoothPMF_linear_cap {K I : Type*} [Fintype K] [Fintype I]
    (c : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern K I modulus)) (hT : T.Nonempty)
    (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    (j : K × I) (hc : c j ≠ 0) (y : ℤ) :
    ((selectedResidueSmoothPMF modulus T W hW hZ).map (integerArrayLinearForm c) y).toReal ≤
      2*(modulus j.2 : ℝ)/W j := by
  have hcell (r : T) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus W) := shiftedSmoothProductMass_pos_of_scales _ _ hscale
  obtain ⟨_, h⟩ := selectedResidueSmoothPMF_bound_of_cells (ε := 2*(modulus j.2 : ℝ)/W j)
    modulus hmodulus T hT W hW hcell
    (fun z => if integerArrayLinearForm c z = y then (1 : ℂ) else 0)
    (by
      intro r
      exact (pmf_point_indicator_norm _ (integerArrayLinearForm c) y).trans_le
        (residueSmoothPMF_linear_cap c (columnResidueRepresentative modulus r.val)
          modulus hmodulus W hW (hcell r) j hc (hscale j) y))
  exact (pmf_point_indicator_norm _ (integerArrayLinearForm c) y).symm.trans_le h

end Erdos3

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.ResiduePhysicalCap

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]
variable (root : K → ℤ) (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
variable (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
variable (hc : ∀ r : T, 0 < shiftedSmoothProductMass
  (residueProfileCenter (columnResidueRepresentative modulus r.val) modulus) (residueProfileWidth modulus W))
variable (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W (none,i))

include hmodulus hT hc hbase in
theorem selectedResidueSmoothPMF_physical_cap (y : I → ℝ) :
    ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal ≤
      ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  obtain ⟨_, h⟩ := selectedResidueSmoothPMF_bound_of_cells (ε := ∏ i, 2*(modulus i : ℝ)/W (none,i))
    modulus hmodulus T hT W hW hc
    (fun z => if physicalAffineSite root z = y then (1 : ℂ) else 0)
    (by
      intro r
      exact (pmf_point_indicator_norm _ (physicalAffineSite root) y).trans_le
        (residueSmoothPMF_physical_cap root (columnResidueRepresentative modulus r.val)
          modulus hmodulus W hW (hc r) hbase y))
  exact (pmf_point_indicator_norm _ (physicalAffineSite root) y).symm.trans_le h

include hmodulus hT hc hbase in
theorem selectedResidueSmoothPMF_physical_finite_event (E : Finset (I → ℝ)) :
    (∑ y ∈ E, ((selectedResidueSmoothPMF modulus T W hW hZ).map (physicalAffineSite root) y).toReal) ≤
      (E.card : ℝ) * ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  calc
    _ ≤ ∑ _y ∈ E, ∏ i, 2*(modulus i : ℝ)/W (none,i) :=
      Finset.sum_le_sum (fun y _ => selectedResidueSmoothPMF_physical_cap
        root modulus hmodulus T hT W hW hZ hc hbase y)
    _ = _ := by simp

end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

theorem spatialBaseCap_volume_bound {I : Type*} [Fintype I]
    (modulus : I → ℕ) (W H : I → ℝ) (hW : ∀ i, 0 < W i) (hH : ∀ i, 0 ≤ H i)
    {S ρ : ℝ} (hρ : 0 < ρ) (hS : 0 ≤ S) (hmodulus : ∀ i, (modulus i : ℝ) ≤ S)
    (hwidth : ∀ i, ρ*H i ≤ W i) :
    (∏ i, H i) * (∏ i, 2*(modulus i : ℝ)/W i) ≤ (2*S/ρ)^Fintype.card I := by
  have hi (i : I) : H i * (2*(modulus i : ℝ)/W i) ≤ 2*S/ρ := by
    have hr : H i / W i ≤ 1/ρ :=
      (div_le_div_iff₀ (hW i) hρ).mpr (by simpa only [one_mul, mul_one, mul_comm] using hwidth i)
    calc
      _ = 2*(modulus i : ℝ)*(H i/W i) := by ring
      _ ≤ 2*S*(1/ρ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hmodulus i) (by norm_num)) hr
          (div_nonneg (hH i) (hW i).le) (mul_nonneg (by norm_num) hS)
      _ = _ := by ring
  rw [← Finset.prod_mul_distrib]
  calc
    _ ≤ ∏ _i : I, 2*S/ρ := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (hH i)
        (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hW i).le)) (fun i _ => hi i)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI

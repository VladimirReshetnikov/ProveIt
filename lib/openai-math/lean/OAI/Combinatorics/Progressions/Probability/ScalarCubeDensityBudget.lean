import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
import OAI.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scalarCubeInnerBox (I : Type*) [Fintype I] : Set (Option I → ℝ) :=
  Set.Icc (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1)))
    (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1)))

theorem scalarCubeInnerBox_subset (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeInnerBox I ⊆ scalarCubeDomain I := by
  intro x hx t
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have hn : ‖x-scalarCubeCenter I‖ ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |x i-scalarCubeCenter I i| ≤ _
    exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
  have hb := scalarCubeValue_sub_bound x (scalarCubeCenter I) hr hn t
  rw [scalarCubeValue_center] at hb
  have he : ((Fintype.card I : ℝ)+1)*(1/(4*((Fintype.card I : ℝ)+1))) = 1/4 := by
    field_simp
  rw [he] at hb
  have ha := abs_le.mp hb
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

theorem scalarCubeInnerBox_volume (I : Type*) [Fintype I] :
    volume.real (scalarCubeInnerBox I) = (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have ho : (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) ≤
      (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))) := fun i => by linarith
  have he (i : Option I) : scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))-
      (scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) = 1/(2*((Fintype.card I : ℝ)+1)) := by
    field_simp
    ring
  simp only [measureReal_def, scalarCubeInnerBox, Real.volume_Icc_pi_toReal ho, he,
    Finset.prod_const, Finset.card_univ, Fintype.card_option]

theorem scalarCubeDomainDensity_le_power (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by
  have hv := measureReal_mono (scalarCubeInnerBox_subset I) (scalarCubeDomain_volume_lt_top I).ne
  rw [scalarCubeInnerBox_volume] at hv
  have hp : 0 < (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by positivity
  have hi := one_div_le_one_div_of_le hp hv
  simpa only [scalarCubeDomainDensity, one_div, inv_pow, inv_inv] using hi

theorem scalarCubeDomainDensity_le_exp (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ Real.exp (((Fintype.card I : ℝ)+1)^2) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hb : 2*((Fintype.card I : ℝ)+1) ≤ Real.exp ((Fintype.card I : ℝ)+1) := by
    calc
      _ ≤ Real.exp 1*Real.exp (Fintype.card I) := by gcongr; exact Real.add_one_le_exp _
      _ = _ := by rw [← Real.exp_add, add_comm]
  calc
    _ ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := scalarCubeDomainDensity_le_power I
    _ ≤ (Real.exp ((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; congr 1; ring

end Erdos3

end

end OAI

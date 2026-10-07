/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_one {K I : Type*} [Fintype K] [Fintype I]
    (W : K × I → ℝ) (z : K × I → ℤ) :
    selectedResidueSmoothWeight (fun _ => 1) {0} W z =
      rectangularWeight (smoothProductProfile (K × I)) 0 W z := by
  have hp : columnResiduePattern (fun _ : I => 1) z = 0 := Subsingleton.elim _ _
  simp only [selectedResidueSmoothWeight, hp, Finset.mem_singleton, ite_true,
    rectangularWeight, rectangularLatticePoint_zero_origin]

theorem selectedResidueSmoothMass_one {K I : Type*} [Fintype K] [Fintype I]
    (W : K × I → ℝ) :
    (∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} W z) =
      shiftedSmoothProductMass 0 W := by
  simp only [selectedResidueSmoothWeight_one, shiftedSmoothProductMass]

theorem selectedResidueSmoothPMF_one {K I : Type*} [Fintype K] [Fintype I]
    (W : K × I → ℝ) (hW : ∀ t, 0 < W t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} W z) :
    selectedResidueSmoothPMF (fun _ => 1) {0} W hW hZ =
      shiftedSmoothProductPMF 0 W hW ((selectedResidueSmoothMass_one W) ▸ hZ) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [selectedResidueSmoothPMF_toReal, shiftedSmoothProductPMF_toReal,
    selectedResidueSmoothWeight_one, selectedResidueSmoothMass_one]

theorem independentProductPMF_slopes {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    (independentProductPMF p).map (fun z => fun t : K × I => z (some t.1,t.2)) =
      independentProductPMF (fun t : K × I => p (some t.1,t.2)) := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp only [PMF.map_comp]
  have hconst (tail : K × I → X) :
      (independentProductPMF (fun i => p (none,i))).map
        ((fun z => fun t : K × I => z (some t.1,t.2)) ∘ baseArrayJoin tail) =
      PMF.pure tail := by
    have he : ((fun z => fun t : K × I => z (some t.1,t.2)) ∘ baseArrayJoin tail) =
        Function.const (I → X) tail := by
      funext z t
      rcases t with ⟨k,i⟩
      rfl
    rw [he, PMF.map_const]
  simp only [hconst, PMF.bind_pure]

theorem shiftedSmoothProductPMF_slopes_cap {K I : Type*} [Fintype K] [Fintype I]
    (a W : Option K × I → ℝ) (hW : ∀ t, 0 < W t)
    (hZ : 0 < shiftedSmoothProductMass a W)
    (hlarge : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ W (some t.1,t.2))
    (y : K × I → ℤ) :
    (((shiftedSmoothProductPMF a W hW hZ).map
      (fun z => fun t : K × I => z (some t.1,t.2))) y).toReal ≤
      ∏ t : K × I, 2 / W (some t.1,t.2) := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_slopes,
    independentProductPMF_toReal]
  exact Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg)
    (fun t _ => shiftedSmoothCoefficientPMF_le (a (some t.1,t.2)) (hlarge t) (y t))

theorem selectedResidueFiniteLaw_one_slopes_cap {K I : Type*} [Fintype K] [Fintype I]
    (W : Option K × I → ℝ) (hW : ∀ t, 0 < W t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} W z)
    (hlarge : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ W (some t.1,t.2))
    (y : K → I → ℤ) :
    (selectedResidueFiniteLaw (fun _ => 1) {0} W hW hZ).mean
      (fun z => if (fun k i => z.val (some k,i)) = y then 1 else 0) ≤
      ∏ t : K × I, 2 / W (some t.1,t.2) := by
  have he (z : Option K × I → ℤ) :
      ((fun k i => z (some k,i)) = y) ↔
      ((fun t : K × I => z (some t.1,t.2)) = fun t => y t.1 t.2) := by
    simp only [funext_iff, Prod.forall]
  simp_rw [he]
  rw [selectedResidueFiniteLaw_mean (fun _ => 1) {0} W hW hZ
    (fun z => if (fun t : K × I => z (some t.1,t.2)) = (fun t => y t.1 t.2) then 1 else 0),
    ← pmf_map_toReal_indicator, selectedResidueSmoothPMF_one]
  exact shiftedSmoothProductPMF_slopes_cap 0 W hW _ hlarge (fun t => y t.1 t.2)

end Erdos3

end

end OAI

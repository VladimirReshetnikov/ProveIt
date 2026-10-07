import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem constantObservable_memberNets
    {Z Y : Type*} (box : Finset Z) (hbox : box.Nonempty)
    (F : Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : Z // x ∈ box},
        ∀ x ∈ box, ∃ i, ∀ y,
          ‖(fun (_ : Z) => F) x y - (fun (_ : Z) => F) (oc i).val y‖ ≤ η := by
  intro η hη hηone
  have hlog : 0 ≤ Real.log (1 / η) :=
    Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa using hηone))
  have hpower : 0 ≤ (p + Real.log (1 / η) + (e : ℝ)) ^ e :=
    pow_nonneg (add_nonneg (add_nonneg hp hlog) (Nat.cast_nonneg e)) e
  obtain ⟨z, hz⟩ := hbox
  refine ⟨1, (by simpa using Real.one_le_exp_iff.mpr hpower), (fun _ => ⟨z, hz⟩), ?_⟩
  intro x hx
  exact ⟨0, fun y => by simpa using hη.le⟩

theorem constantObservable_integerBox_memberNets
    {X Y : Type*} [Fintype X] (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (F : Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖(fun (_ : X → ℤ) => F) x y - (fun (_ : X → ℤ) => F) (oc i).val y‖ ≤ η := by
  have hzero : (0 : X → ℤ) ∈ integerBox N := by
    apply (mem_integerBox N 0).mpr
    intro x
    exact ⟨le_rfl, by change (0 : ℤ) < N x; exact_mod_cast hN x⟩
  exact constantObservable_memberNets (integerBox N) ⟨0, hzero⟩ F hp e

end Erdos3

end

end OAI

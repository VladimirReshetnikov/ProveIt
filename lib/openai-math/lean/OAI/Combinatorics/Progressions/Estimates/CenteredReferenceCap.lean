import OAI.Combinatorics.Progressions.Lattices.IntegerBoxObservedMean

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem image_mean_eq_sum {X Y : Type*} [Fintype X] [DecidableEq Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (T : Finset Y)
    (hF : ∀ x, F x ∈ T) (g : Y → ℝ) :
    p.mean (fun x => g (F x)) =
      ∑ y ∈ T, p.mean (fun x => if F x = y then 1 else 0) * g y := by
  simp only [mean, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [hF x, eq_comm]

theorem image_mean_le_uniform {X Y : Type*} [Fintype X] [DecidableEq Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (T : Finset Y)
    (hF : ∀ x, F x ∈ T) {B : ℝ}
    (hB : ∀ y, p.mean (fun x => if F x = y then 1 else 0) ≤ B)
    (g : Y → ℝ) (hg : ∀ y ∈ T, 0 ≤ g y) :
    p.mean (fun x => g (F x)) ≤ B * (T.card : ℝ) * (𝔼 y ∈ T, g y) := by
  rw [image_mean_eq_sum p F T hF g]
  calc
    _ ≤ ∑ y ∈ T, B * g y := Finset.sum_le_sum
      (fun y hy => mul_le_mul_of_nonneg_right (hB y) (hg y hy))
    _ = B * ∑ y ∈ T, g y := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [mul_assoc, Finset.card_mul_expect]

end Erdos3.FiniteProbabilityWeights

namespace Erdos3

theorem pmf_map_injective_toReal_cap {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ x, (p x).toReal ≤ C) (y : Y) : (p.map f y).toReal ≤ C := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    rw [pmf_map_injective_at p f hf]
    exact hp x
  · rw [pmf_map_zero_off_range p f y hy, ENNReal.toReal_zero]
    exact hC

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

theorem pmf_centeredPhysicalSite_cap {K I : Type*} [Fintype K]
    (p : PMF (Option K × I → ℤ)) (root : K → ℤ) (N : I → ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hp : ∀ y, ((p.map (physicalAffineSite root)) y).toReal ≤ C)
    (y : I → ℤ) : ((p.map (centeredIntegerPhysicalSite root N)) y).toReal ≤ C := by
  let cast : (I → ℤ) → (I → ℝ) := fun x i => (x i : ℝ)
  let shift : (I → ℝ) → (I → ℝ) := fun x => (fun i => (integerBoxCenter N i : ℝ)) + x
  have hcast : Function.Injective cast := by
    intro x y he
    funext i
    have hi : (x i : ℝ) = (y i : ℝ) := congrFun he i
    exact_mod_cast hi
  have hshift : Function.Injective shift := by
    intro x y he
    exact add_left_cancel he
  have hlaw : (p.map (centeredIntegerPhysicalSite root N)).map cast =
      (p.map (physicalAffineSite root)).map shift := by
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext z
    exact centeredIntegerPhysicalSite_cast root N z
  calc
    _ = (((p.map (centeredIntegerPhysicalSite root N)).map cast) (cast y)).toReal :=
      congrArg ENNReal.toReal (pmf_map_injective_at _ cast hcast y).symm
    _ = (((p.map (physicalAffineSite root)).map shift) (cast y)).toReal := by rw [hlaw]
    _ ≤ C := pmf_map_injective_toReal_cap _ shift hshift hC hp (cast y)

end Erdos3.BooleanCubeKernel

end

end OAI

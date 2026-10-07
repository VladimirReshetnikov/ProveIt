import OAI.Combinatorics.Progressions.Estimates.AnnihilatorIntervalBound
import OAI.Combinatorics.Progressions.Geometry.FiniteCoordinateSlice
import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerInterval_indicator_expect (a b : ℤ) (hab : a ≤ b) (E : ℤ → Prop)
    [DecidablePred E] :
    (𝔼 x : Finset.Ico a b, if E x then (1 : ℝ) else 0) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (Finset.Ico a b) (fun x : ℤ => if E x then (1 : ℝ) else 0),
    Fintype.card_coe]
  have hcard : ((Finset.Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le a b hab
  rw [hcard]
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem integerBox_character_expect_le {I K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (a b : ℤ) (hab : a < b)
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    (𝔼 x : K → Finset.Ico a b, if χ (fun i => (x (e i) : ℤ)) = 1 then (1 : ℝ) else 0) ≤
      1 / (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) + 1 / ((b - a : ℤ) : ℝ) := by
  classical
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  obtain ⟨i, hi⟩ := exists_annihilating_coordinate_bound χ hχ
  apply expect_le_of_coordinate_slices (e i)
  intro x
  have hupdate (y : Finset.Ico a b) :
      (fun j => (Function.update x (e i) y (e j) : ℤ)) =
        Function.update (fun j => (x (e j) : ℤ)) i (y : ℤ) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, he.ne hji]
  simp_rw [hupdate]
  rw [integerInterval_indicator_expect a b hab.le
    (fun y => χ (Function.update (fun j => (x (e j) : ℤ)) i y) = 1)]
  exact hi _ a b hab

theorem integerBox_character_probability_le {I K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (a b : ℤ) (hab : a < b)
    (p : FiniteProbabilityWeights (K → Finset.Ico a b)) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x, p.weight x ≤ C * (Fintype.card (K → Finset.Ico a b) : ℝ)⁻¹)
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    p.eventProbability (fun x => χ (fun i => (x (e i) : ℤ)) = 1) ≤
      C * (1 / (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) + 1 / ((b - a : ℤ) : ℝ)) := by
  classical
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  let u := FiniteProbabilityWeights.uniform (K → Finset.Ico a b)
  have h := p.eventProbability_le_of_weight_le u C hw
    (fun x => χ (fun i => (x (e i) : ℤ)) = 1)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.uniform_mean]
  exact integerBox_character_expect_le e he a b hab χ hχ

end Erdos3

end

end OAI

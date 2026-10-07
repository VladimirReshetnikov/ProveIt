import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Estimates.UniformHomFiberWeights

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).mean g := by
  calc
    _ = ∑ y : H, (FiniteProbabilityWeights.uniform G).mean
        (fun x => if f x = y then (1 : ℝ) else 0) * g y := by
      unfold FiniteProbabilityWeights.mean
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [mul_ite, ite_mul]
    _ = ∑ y : H, (Fintype.card H : ℝ)⁻¹ * g y := by
      simp_rw [uniform_mean_surjective_hom_fiber f hf]
    _ = _ := rfl

theorem expect_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (𝔼 x : G, g (f x)) = 𝔼 y : H, g y := by
  simpa only [FiniteProbabilityWeights.uniform_mean] using
    uniform_mean_surjective_hom f hf g

noncomputable def nestedTupleResidueReduction {I : Type*} (n : ℕ)
    {M N : ℕ} (hMN : M ∣ N) :
    (Fin n → I → ZMod N) →+ (Fin n → I → ZMod M) where
  toFun x a i := ZMod.castHom hMN (ZMod M) (x a i)
  map_zero' := by ext a i; simp
  map_add' := by
    intro x y
    ext a i
    exact map_add (ZMod.castHom hMN (ZMod M)) (x a i) (y a i)

theorem nestedTupleResidueReduction_surjective {I : Type*} (n : ℕ)
    {M N : ℕ} (hMN : M ∣ N) :
    Function.Surjective (nestedTupleResidueReduction (I := I) n hMN) := by
  intro y
  choose x hx using fun a i => ZMod.castHom_surjective hMN (y a i)
  exact ⟨x, funext fun a => funext (hx a)⟩

theorem expect_nestedTupleResidueReduction {I : Type*} [Fintype I]
    (n : ℕ) {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (g : (Fin n → I → ZMod M) → ℝ) :
    (𝔼 x : Fin n → I → ZMod N,
      g (fun a i => ZMod.castHom hMN (ZMod M) (x a i))) =
        𝔼 y : Fin n → I → ZMod M, g y :=
  expect_surjective_hom (nestedTupleResidueReduction n hMN)
    (nestedTupleResidueReduction_surjective n hMN) g

theorem expect_mul_modulus_reduction {I : Type*} [Fintype I]
    (n M d : ℕ) [NeZero M] [NeZero d]
    (g : (Fin n → I → ZMod M) → ℝ) :
    (𝔼 x : Fin n → I → ZMod (M * d),
      g (fun a i => ZMod.castHom (dvd_mul_right M d) (ZMod M) (x a i))) =
        𝔼 y : Fin n → I → ZMod M, g y :=
  expect_nestedTupleResidueReduction n (dvd_mul_right M d) g

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom

namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_coordinate_maps {σ I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    {s : ℕ} {p r : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g)
    (f' : K → (σ → ℤ) → ℂ) (g' : L → (σ → ℤ) → ℂ)
    (a : K → I) (b : L → J)
    (hf : ∀ k x, f' k x = f (a k) x) (hg : ∀ l x, g' l x = g (b l) x)
    (hK : (Fintype.card K : ℝ) ≤ Real.exp r) (hL : (Fintype.card L : ℝ) ≤ Real.exp r)
    (hpr : p ≤ r) : NativeIntegerVectorEquivalence s r f' g' := by
  refine ⟨hK, hL, fun k l => ?_⟩
  obtain ⟨R⟩ := E.expansion (a k) (b l)
  have heq : (fun x => f (a k) x * star (g (b l) x)) =
      (fun x => f' k x * star (g' l x)) := by
    funext x
    rw [hf, hg]
  exact ⟨heq ▸ R.mono hpr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI

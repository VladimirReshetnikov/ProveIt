import OAI.Combinatorics.Progressions.Fourier.SelectedDensityAmbientProductFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def layerSamplerIntegerBox : Finset (LayerSamplerVariables G I n B → ℤ) :=
  integerBox (layerSamplerSides B U b R S.value)

theorem layerSamplerIntegerBox_nonempty : (layerSamplerIntegerBox B U b S).Nonempty := by
  refine ⟨0, (mem_integerBox _ _).mpr ?_⟩
  intro v
  change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) < layerSamplerSides B U b R S.value v
  exact ⟨le_rfl, by exact_mod_cast layerSamplerSides_pos B U b R S.positive v⟩

theorem layerSamplerIntegerBox_abs_bound {x : LayerSamplerVariables G I n B → ℤ}
    (hx : x ∈ layerSamplerIntegerBox B U b S) (v : LayerSamplerVariables G I n B) :
    |(x v : ℝ)| ≤ layerSamplerBox B U b S v := by
  have h := (mem_integerBox _ _).mp hx v
  have h0 : (0 : ℝ) ≤ x v := by exact_mod_cast h.1
  rw [abs_of_nonneg h0]
  change (x v : ℝ) ≤ (layerSamplerSides B U b R S.value v : ℝ)
  exact_mod_cast h.2.le

theorem layerSamplerIntegerBox_root_bound {M : ℝ} (hM : (S.value : ℝ) ≤ M)
    {x : LayerSamplerVariables G I n B → ℤ} (hx : x ∈ layerSamplerIntegerBox B U b S)
    (v : LayerSamplerVariables G I n B) : |(x v : ℝ)| ≤ M :=
  (layerSamplerIntegerBox_abs_bound B U b S hx v).trans ((layerSamplerBox_le B U b S v).trans hM)

theorem layerSamplerSides_free (g : G) :
    layerSamplerSides B U b R S.value (.inl g) = S.value := rfl

theorem layerSamplerSides_attains_scale [Nonempty G] :
    ∃ v : LayerSamplerVariables G I n B, layerSamplerSides B U b R S.value v = S.value :=
  ⟨.inl (Classical.choice inferInstance), rfl⟩

end Erdos3.VectorPolynomial

end

end OAI

import DiophantineConsistency.PRABndRewriting
set_option autoImplicit false
namespace DiophantineConsistency.PRARewritingWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

theorem rew_bound_with {k n : ℕ} (φ : ArithmeticSemisentence k) (bound : (Fin k → V) → V)
    (hφ : ∀ g, φ.Evalb g → (bnd φ).Evalb (Fin.snoc g (bound g)))
    (ω : Rew ℒₒᵣ Empty k Empty n) (e : Fin n → V) (w : V)
    (hw : bound (fun i => (ω #i).val e Empty.elim) ≤ w) :
    (ω ▹ φ).Evalb e → (bnd (ω ▹ φ)).Evalb (Fin.snoc e w) := by
  intro h
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  simp only [Semiformula.eval_rew] at h
  rw [hf] at h
  apply (PRABndRewriting.natural φ ω e w).mpr
  exact eval_bnd_mono φ _ (Empty.elim : Empty → V) hw (hφ _ h)

theorem ternary_rew_bound_with (φ : ArithmeticSemisentence 3) (bound : V → V → V → V)
    (hφ : ∀ x y z, φ.Evalb ![x,y,z] → (bnd φ).Evalb ![x,y,z,bound x y z])
    {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) (w : V)
    (hw : bound ((ω #0).val e Empty.elim) ((ω #1).val e Empty.elim)
      ((ω #2).val e Empty.elim) ≤ w) :
    (ω ▹ φ).Evalb e → (bnd (ω ▹ φ)).Evalb (Fin.snoc e w) := by
  apply rew_bound_with φ (fun g => bound (g 0) (g 1) (g 2)) ?_ ω e w hw
  intro g h
  have hv : ![g 0,g 1,g 2] = g := by funext i; revert i; simp [Fin.forall_fin_succ]
  have hs : Fin.snoc g (bound (g 0) (g 1) (g 2)) = ![g 0,g 1,g 2,bound (g 0) (g 1) (g 2)] := by
    funext i; revert i; simp [Fin.forall_fin_succ, Fin.snoc]
  rw [hs]
  exact hφ (g 0) (g 1) (g 2) (by simpa [hv] using h)

end DiophantineConsistency.PRARewritingWitnessBound

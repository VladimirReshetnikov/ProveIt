import DiophantineConsistency.PRARewritingWitnessBound
set_option autoImplicit false
namespace DiophantineConsistency.PRAUnaryRewritingBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- Transport a unary witness bound through rewriting and monotonicity. -/
theorem rew_bound_with (φ : ArithmeticSemisentence 1) (bound : M → M)
    (hφ : ∀ x : M, φ.Evalb ![x] → (bnd φ).Evalb ![x,bound x])
    {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → M) (w : M)
    (hw : bound ((ω #0).val e Empty.elim) ≤ w) :
    (ω ▹ φ).Evalb e → (bnd (ω ▹ φ)).Evalb (Fin.snoc e w) := by
  apply PRARewritingWitnessBound.rew_bound_with φ (fun g => bound (g 0)) ?_ ω e w hw
  intro g h
  have hv : ![g 0] = g := by funext i; revert i; simp
  have hs : Fin.snoc g (bound (g 0)) = ![g 0,bound (g 0)] := by
    funext i; revert i; simp [Fin.forall_fin_succ, Fin.snoc]
  rw [hs]
  exact hφ (g 0) (by simpa [hv] using h)

/-- Transport a unary successor bound through rewriting and a larger witness bound. -/
theorem rew_bound_at (φ : ArithmeticSemisentence 1)
    (hφ : ∀ x : M, φ.Evalb ![x] → (bnd φ).Evalb ![x,x+1])
    {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → M) (w : M)
    (hw : (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ φ).Evalb e → (bnd (ω ▹ φ)).Evalb (Fin.snoc e w) :=
  rew_bound_with φ (fun x => x+1) hφ ω e w hw
end DiophantineConsistency.PRAUnaryRewritingBound

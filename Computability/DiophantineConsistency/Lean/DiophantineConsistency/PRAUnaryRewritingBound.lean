import DiophantineConsistency.PRABndRewriting
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
  intro h
  let g : Fin 1 → M := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0] = g := by funext i; revert i; simp
  have hs : Fin.snoc g (bound (g 0)) = ![g 0,bound (g 0)] := by
    funext i; revert i; simp [Fin.forall_fin_succ, Fin.snoc]
  have hb := hφ (g 0) (by simpa [hv] using h)
  have hb' : (bnd φ).Evalb (Fin.snoc g w) := by
    apply eval_bnd_mono φ g (Empty.elim : Empty → M) hw
    rw [hs]
    exact hb
  exact (PRABndRewriting.natural φ ω e w).mpr hb'
/-- Transport a unary successor bound through rewriting and a larger witness bound. -/
theorem rew_bound_at (φ : ArithmeticSemisentence 1)
    (hφ : ∀ x : M, φ.Evalb ![x] → (bnd φ).Evalb ![x,x+1])
    {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → M) (w : M)
    (hw : (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ φ).Evalb e → (bnd (ω ▹ φ)).Evalb (Fin.snoc e w) :=
  rew_bound_with φ (fun x => x+1) hφ ω e w hw
end DiophantineConsistency.PRAUnaryRewritingBound

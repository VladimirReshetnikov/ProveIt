import DiophantineConsistency.StrictSigmaOneInduction
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace DiophantineConsistency.PRABndRewriting
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
variable {M : Type} [ORingStructure M]

/-- Bounding commutes semantically with arbitrary rewriting of a closed
formula's bound variables, retaining the same distinguished final bound. -/
theorem natural : ∀ {n m : ℕ} (φ : ArithmeticSemisentence n)
    (ω : Rew ℒₒᵣ Empty n Empty m) (e : Fin m → M) (w : M),
    (bnd (ω ▹ φ)).Evalb (Fin.snoc e w) ↔
      (bnd φ).Evalb (Fin.snoc (fun i => (ω (#i)).val e Empty.elim) w)
  | _, _, ⊤, _, _, _ => by simp [bnd]
  | _, _, ⊥, _, _, _ => by simp [bnd]
  | _, _, .rel r v, ω, e, w => by
      rw [Semiformula.rew_rel_eq_comp]
      simp only [bnd]
      rw [eval_bnd_atom, eval_bnd_atom]
      rw [← Semiformula.rew_rel_eq_comp, Semiformula.eval_rew]
      have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
      rw [hf]
      rfl
  | _, _, .nrel r v, ω, e, w => by
      rw [Semiformula.rew_nrel_eq_comp]
      simp only [bnd]
      rw [eval_bnd_atom, eval_bnd_atom]
      rw [← Semiformula.rew_nrel_eq_comp, Semiformula.eval_rew]
      have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
      rw [hf]
      rfl
  | _, _, φ ⋏ ψ, ω, e, w => by simp [bnd, natural φ ω e w, natural ψ ω e w]
  | _, _, φ ⋎ ψ, ω, e, w => by simp [bnd, natural φ ω e w, natural ψ ω e w]
  | _, _, ∀⁰ φ, ω, e, w => by
      simp only [Rewriting.app_all, bnd, Semiformula.eval_all]
      apply forall_congr'
      intro x
      have hv : (fun i => (ω.q (#i)).val (x :> e) Empty.elim) =
          (x :> fun i => (ω (#i)).val e Empty.elim) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      have h := natural φ ω.q (x :> e) w
      simpa only [cons_snoc, hv] using h
  | _, _, ∃⁰ φ, ω, e, w => by
      simp only [Rewriting.app_exs, bnd, Semiformula.eval_bexs]
      apply exists_congr
      intro x
      have hv : (fun i => (ω.q (#i)).val (x :> e) Empty.elim) =
          (x :> fun i => (ω (#i)).val e Empty.elim) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp
      have h := natural φ ω.q (x :> e) w
      have h' : (bnd (ω.q ▹ φ)).Evalb (x :> Fin.snoc e w) ↔
          (bnd φ).Evalb (x :> Fin.snoc (fun i => (ω (#i)).val e Empty.elim) w) := by
        simpa only [cons_snoc, hv] using h
      simpa [val_lastVar] using (fun (_ : x < w) => h')
end DiophantineConsistency.PRABndRewriting

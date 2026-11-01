import DiophantineConsistency.ParsonsFreshOpen
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsGuardPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsBlock ParsonsStructure ParsonsRule ParsonsInductionCase

inductive Guard : Proposition ℒₒᵣ → Prop
  | sigma {P} : Hierarchy 𝚺 1 P → Guard P
  | all (A : ArithmeticSemiformula ℕ 1) :
      Hierarchy 𝚷 2 (∀⁰ A) → Guard A.free → Guard (∀⁰ A)

theorem Guard.pi {P : Proposition ℒₒᵣ} (h : Guard P) : Hierarchy 𝚷 2 P := by
  cases h with
  | sigma h => exact h.strict_mono _ (by decide)
  | all A h _ => exact h

/-- The precise strong induction assumption needed by the local case. -/
def Below (H : ℕ) : Prop :=
  ∀ (es : List Mark) (d : Derivation (es.map Mark.formula)),
    Derivation.IsCutFree d → d.height < H →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin (es.map Mark.output)))

/-- A finite universal prefix ending in Σ₁ can be opened structurally.  The
only recursion on derivations is the explicit strong hypothesis `Below H`. -/
theorem counter_prefix (G : Proposition ℒₒᵣ) (hg : Guard G) :
    ∀ (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
      (B : ArithmeticSemiformula ℕ 1) (hs : State φ (∃⁰ B))
      (es : List Mark) (t : SyntacticTerm ℒₒᵣ)
      (d : Derivation (B/[t] :: G :: es.map Mark.formula)),
      Derivation.IsCutFree d → Hierarchy 𝚺 1 (disjoin (es.map Mark.output)) →
      ∀ H : ℕ, d.exs.height ≤ H → Below H →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ 0 (∃⁰ B) hs ::
        Mark.side G hg.pi :: es).map Mark.output))) := by
  induction hg with
  | @sigma P hG =>
      intro φ hφ B hs es t d hc hE H hd ih
      have hside : Hierarchy 𝚺 1 (disjoin ((Mark.side P (hG.strict_mono _ (by decide)) :: es).map Mark.output)) := by
        simp only [List.map_cons, Mark.output, disjoin, Hierarchy.or_iff]
        exact ⟨hG,hE⟩
      apply counter_case φ hφ B hs (Mark.side P (hG.strict_mono _ (by decide)) :: es) t d hc hside
      · intro f eq e he ht; exact ih _ e he (lt_of_lt_of_le ht hd)
      · intro f eq e he ht; exact ih _ e he (lt_of_lt_of_le ht hd)
      · intro f eq e he ht; exact ih _ e he (lt_of_lt_of_le ht hd)
  | all A hA hg ihGuard =>
      intro φ hφ B hs es t d hc hE H hd ih
      have hS : State φ (∃⁰ (Rew.shift ▹ B)) := by
        simpa using ParsonsShift.state_shift φ (∃⁰ B) hs
      have hEs : Hierarchy 𝚺 1 (disjoin ((es.map Mark.shift).map Mark.output)) := by
        rw [shift_outputs, ParsonsShift.disjoin_shift]
        exact Hierarchy.rew Rew.shift hE
      obtain ⟨e, he, ht⟩ := ParsonsFreshOpen.fresh_open A B t (es.map Mark.formula) d hc
      have hsub : Rewriting.shift (B/[t]) = (Rew.shift ▹ B)/[Rew.shift t] := by
        have hr : Rew.rewrite (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) = (@Rew.shift ℒₒᵣ 0) := by
          ext i <;> simp
        simpa [hr, ← Rew.q_rewrite] using
          (LawfulSyntacticRewriting.rewrite_subst_eq (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) t B)
      have heq : (Rewriting.shift (B/[t]) :: A.free :: (es.map Mark.formula)⁺) =
          ((Rew.shift ▹ B)/[Rew.shift t]) :: A.free :: (es.map Mark.shift).map Mark.formula := by
        simp only [shift_formulas, hsub]
      let e' := e.cast heq
      have hc' : Derivation.IsCutFree e' := by simpa [e'] using he
      have hh : e'.exs.height ≤ H := by
        simp only [e', Derivation.height_exs, Derivation.height_cast] at *
        omega
      have hp := ihGuard φ hφ (Rew.shift ▹ B) hS (es.map Mark.shift) (Rew.shift t) e' hc' hEs H hh ih
      have hp' : Proof 𝗣𝗔⁻ (⊥ ⋎ (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output)))) := by
        simpa only [List.map_cons, Mark.output, disjoin, shift_outputs, ParsonsShift.disjoin_shift] using hp.some
      have hdrop : Proof 𝗣𝗔⁻ ((⊥ ⋎ (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output)))) 🡒
          (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output)))) :=
        ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa using hf)
      have hu := ParsonsLogicalCases.universal A (disjoin (es.map Mark.output)) (Proof.mp hdrop hp')
      have hswap : Proof 𝗣𝗔⁻ ((disjoin (es.map Mark.output) ⋎ (∀⁰ A)) 🡒
          (⊥ ⋎ ((∀⁰ A) ⋎ disjoin (es.map Mark.output)))) :=
        ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa [or_comm] using hf)
      simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hswap hu)
end DiophantineConsistency.ParsonsGuardPrefix

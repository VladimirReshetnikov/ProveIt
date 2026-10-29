import DiophantineConsistency.ParsonsFreshOpen
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsCounterFresh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsUnified ParsonsBlock ParsonsStructure ParsonsRule ParsonsInductionCase

/-- Opening one strict universal guard in the counter-witness case.  The
remaining guard must already be Σ₁, and all three smaller cases are explicit. -/
theorem counter_one_universal
    (φ : ArithmeticSemiformula ℕ 1) (hφ : Hierarchy 𝚺 1 φ)
    (B : ArithmeticSemiformula ℕ 1) (hs : State φ (∃⁰ B))
    (A : ArithmeticSemiformula ℕ 1) (hA : Hierarchy 𝚺 1 A)
    (es : List Mark) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation (B/[t] :: (∀⁰ A) :: es.map Mark.formula))
    (hc : Derivation.IsCutFree d)
    (hE : Hierarchy 𝚺 1 (disjoin (es.map Mark.output)))
    (ihBase : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ)
      (_heq : (Rew.shift ▹ B) = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((baseMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) ::
        Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift).map Mark.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((baseMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) ::
        Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift).map Mark.output))))
    (ihStep : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ)
      (_heq : (Rew.shift ▹ B) = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((stepMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) ::
        Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift).map Mark.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((stepMark ((Rew.rewrite f).q ▹ φ) (Hierarchy.rew _ hφ) ::
        Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift).map Mark.output))))
    (ihNeg : ∀ (f : ℕ → SyntacticTerm ℒₒᵣ)
      (_heq : (Rew.shift ▹ B) = matrix ((Rew.rewrite f).q ▹ φ))
      (e : Derivation ((negativeMark ((Rew.rewrite f).q ▹ φ) (Rew.shift t) (Hierarchy.rew _ hφ) ::
        Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift).map Mark.formula)),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((negativeMark ((Rew.rewrite f).q ▹ φ) (Rew.shift t) (Hierarchy.rew _ hφ) ::
        Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift).map Mark.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Mark.block φ hφ 0 (∃⁰ B) hs ::
      Mark.side (∀⁰ A) (by exact Hierarchy.all (hA.strict_mono _ (by decide))) :: es).map Mark.output))) := by
  let es' : List Mark := Mark.side A.free ((Hierarchy.rew Rew.free hA).strict_mono _ (by decide)) :: es.map Mark.shift
  have hS : State φ (∃⁰ (Rew.shift ▹ B)) := by
    simpa using ParsonsShift.state_shift φ (∃⁰ B) hs
  have hSg : Hierarchy 𝚺 1 (disjoin (es'.map Mark.output)) := by
    dsimp [es']
    simp only [Mark.output, disjoin, shift_outputs, ParsonsShift.disjoin_shift]
    exact Hierarchy.or_iff.mpr ⟨Hierarchy.rew Rew.free hA, Hierarchy.rew Rew.shift hE⟩
  obtain ⟨e, he, ht⟩ := ParsonsFreshOpen.fresh_open A B t (es.map Mark.formula) d hc
  have hsub : Rewriting.shift (B/[t]) = (Rew.shift ▹ B)/[Rew.shift t] := by
    have hr : Rew.rewrite (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) = (@Rew.shift ℒₒᵣ 0) := by
      ext i <;> simp
    simpa [hr, ← Rew.q_rewrite] using
      (LawfulSyntacticRewriting.rewrite_subst_eq (fun x : ℕ => (&(x+1) : SyntacticTerm ℒₒᵣ)) t B)
  have heq : (Rewriting.shift (B/[t]) :: A.free :: (es.map Mark.formula)⁺) =
      ((Rew.shift ▹ B)/[Rew.shift t]) :: es'.map Mark.formula := by
    simp only [es', List.map_cons, Mark.formula, shift_formulas, hsub]
  let e' := e.cast heq
  have hc' : Derivation.IsCutFree e' := by simpa [e'] using he
  have hh : e'.exs.height ≤ d.exs.height := by
    simp only [e', Derivation.height_exs, Derivation.height_cast] at *
    omega
  have hp := counter_case φ hφ (Rew.shift ▹ B) hS es' (Rew.shift t) e' hc' hSg
    (by intro f eq q hq hqheight; exact ihBase f eq q hq (by omega))
    (by intro f eq q hq hqheight; exact ihStep f eq q hq (by omega))
    (by intro f eq q hq hqheight; exact ihNeg f eq q hq (by omega))
  have hp' : Proof 𝗣𝗔⁻ (⊥ ⋎ (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output)))) := by
    simpa only [List.map_cons, Mark.output, disjoin, shift_outputs, ParsonsShift.disjoin_shift, es'] using hp.some
  have hdrop : Proof 𝗣𝗔⁻ ((⊥ ⋎ (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output)))) 🡒
      (A.free ⋎ Rewriting.shift (disjoin (es.map Mark.output)))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa using hf)
  have hu := ParsonsLogicalCases.universal A (disjoin (es.map Mark.output)) (Proof.mp hdrop hp')
  have hswap : Proof 𝗣𝗔⁻ ((disjoin (es.map Mark.output) ⋎ (∀⁰ A)) 🡒
      (⊥ ⋎ ((∀⁰ A) ⋎ disjoin (es.map Mark.output)))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f hf; simpa [or_comm] using hf)
  simpa [Mark.output, disjoin] using Nonempty.intro (Proof.mp hswap hu)
end DiophantineConsistency.ParsonsCounterFresh

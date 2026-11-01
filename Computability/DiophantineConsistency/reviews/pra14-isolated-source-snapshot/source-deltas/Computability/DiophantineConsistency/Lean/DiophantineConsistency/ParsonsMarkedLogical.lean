import DiophantineConsistency.ParsonsShift
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsMarkedLogical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsInvariant ParsonsStructure ParsonsRule ParsonsLogicalCases

set_option linter.flexible false in
theorem pi_body_of_exists {n : ℕ} (A : ArithmeticSemiformula ℕ (n+1)) :
    Hierarchy 𝚷 2 (∃⁰ A) → Hierarchy 𝚷 2 A := by
  generalize hr : ∃⁰ A = r
  generalize hb : (𝚷 : Polarity) = Γ
  intro H
  cases H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
  case bexs => rcases hr with rfl; simpa
  case exs => rcases hr with rfl; simpa
  case sigma hp => rcases hr with rfl; exact hp.accum _
  case dummy_pi hp => rcases hr with rfl; exact hp.accum _

theorem orLeft (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋎ Q)) : Hierarchy 𝚷 2 P :=
  (Hierarchy.or_iff.mp h).1

theorem orRight (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋎ Q)) : Hierarchy 𝚷 2 Q :=
  (Hierarchy.or_iff.mp h).2

theorem andLeft (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋏ Q)) : Hierarchy 𝚷 2 P :=
  (Hierarchy.and_iff.mp h).1

theorem andRight (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋏ Q)) : Hierarchy 𝚷 2 Q :=
  (Hierarchy.and_iff.mp h).2

theorem existsInstance (A : ArithmeticSemiformula ℕ 1) (t : SyntacticTerm ℒₒᵣ)
    (h : Hierarchy 𝚷 2 (∃⁰ A)) : Hierarchy 𝚷 2 (A/[t]) :=
  Hierarchy.rew (Rew.subst ![t]) (pi_body_of_exists A h)

/-- Principal disjunction with an arbitrary marked nonprincipal context. -/
theorem marked_or (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋎ Q))
    (es : List Entry) (d : Derivation (P :: Q :: es.map Entry.formula))
    (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Entry.side P (orLeft P Q h) :: Entry.side Q (orRight P Q h) :: es).map Entry.formula),
      Derivation.IsCutFree e → e.height < d.or.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side P (orLeft P Q h) :: Entry.side Q (orRight P Q h) :: es).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side (P ⋎ Q) h :: es).map Entry.output))) := by
  have hh : d.height < d.or.height := by simp
  have hp : Proof 𝗣𝗔⁻ (P ⋎ (Q ⋎ disjoin (es.map Entry.output))) := by
    simpa [Entry.formula, Entry.output, disjoin] using (ih d hc hh).some
  simpa [Entry.output, disjoin] using Nonempty.intro (disjunction P Q _ hp)

/-- Principal conjunction with two strictly smaller marked premises. -/
theorem marked_and (P Q : Proposition ℒₒᵣ) (h : Hierarchy 𝚷 2 (P ⋏ Q))
    (es : List Entry) (dP : Derivation (P :: es.map Entry.formula))
    (dQ : Derivation (Q :: es.map Entry.formula))
    (hcP : Derivation.IsCutFree dP) (hcQ : Derivation.IsCutFree dQ)
    (ihP : ∀ e : Derivation ((Entry.side P (andLeft P Q h) :: es).map Entry.formula),
      Derivation.IsCutFree e → e.height < (dP.and dQ).height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side P (andLeft P Q h) :: es).map Entry.output))))
    (ihQ : ∀ e : Derivation ((Entry.side Q (andRight P Q h) :: es).map Entry.formula),
      Derivation.IsCutFree e → e.height < (dP.and dQ).height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side Q (andRight P Q h) :: es).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side (P ⋏ Q) h :: es).map Entry.output))) := by
  have hp : dP.height < (dP.and dQ).height := by simp
  have hq : dQ.height < (dP.and dQ).height := by simp
  have hP : Proof 𝗣𝗔⁻ (P ⋎ disjoin (es.map Entry.output)) := by
    simpa [Entry.formula, Entry.output, disjoin] using (ihP dP hcP hp).some
  have hQ : Proof 𝗣𝗔⁻ (Q ⋎ disjoin (es.map Entry.output)) := by
    simpa [Entry.formula, Entry.output, disjoin] using (ihQ dQ hcQ hq).some
  simpa [Entry.output, disjoin] using Nonempty.intro (conjunction P Q _ hP hQ)

/-- Principal ordinary existential, with the arbitrary marked context unchanged. -/
theorem marked_exs (A : ArithmeticSemiformula ℕ 1) (h : Hierarchy 𝚷 2 (∃⁰ A))
    (es : List Entry) (t : SyntacticTerm ℒₒᵣ)
    (d : Derivation ((A/[t]) :: es.map Entry.formula)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Entry.side (A/[t]) (existsInstance A t h) :: es).map Entry.formula),
      Derivation.IsCutFree e → e.height < d.exs.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side (A/[t]) (existsInstance A t h) :: es).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side (∃⁰ A) h :: es).map Entry.output))) := by
  have hh : d.height < d.exs.height := by simp
  have hp : Proof 𝗣𝗔⁻ ((A/[t]) ⋎ disjoin (es.map Entry.output)) := by
    simpa [Entry.formula, Entry.output, disjoin] using (ih d hc hh).some
  have he := existential A (disjoin (es.map Entry.output)) t hp
  have hs : Proof 𝗣𝗔⁻ ((disjoin (es.map Entry.output) ⋎ (∃⁰ A)) 🡒
      ((∃⁰ A) ⋎ disjoin (es.map Entry.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f h; simp at h ⊢; tauto)
  simpa [Entry.output, disjoin] using Nonempty.intro (Proof.mp hs he)

end DiophantineConsistency.ParsonsMarkedLogical

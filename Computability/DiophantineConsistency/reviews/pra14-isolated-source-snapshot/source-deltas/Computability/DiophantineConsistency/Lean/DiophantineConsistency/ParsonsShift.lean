import DiophantineConsistency.ParsonsInvariant
import DiophantineConsistency.ParsonsLogicalCases
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsBlock ParsonsOpened ParsonsInvariant ParsonsStructure ParsonsRule

/-- The frozen parameter body has no free variables: `fixitr` binds every
free variable that occurs in the counterexample matrix. -/
theorem normalized_closed (φ : ArithmeticSemiformula ℕ 1) (x : ℕ) :
    ¬(normalizedBody φ).FVar? x := by
  intro h
  rcases Semiformula.fvar?_rew h with ⟨i, hi⟩ | ⟨z, hz, hx⟩
  · exact Fin.elim0 i
  · have hzlt : z < (succInd φ).fvSup :=
      Semiformula.lt_fvSup_of_fvar? (counterexample_support φ z hz)
    simp [Rew.fixitr_fvar, hzlt] at hx

theorem state_shift (φ : ArithmeticSemiformula ℕ 1) {n : ℕ}
    (A : ArithmeticSemiformula ℕ n) (h : State φ A) :
    State φ (Rew.shift ▹ A) := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨fun i => Rew.shift (v i), ?_⟩
  simp only [Rewriting.subst, ← TransitiveRewriting.comp_app]
  apply Semiformula.rew_eq_of_funEqOn
  · simp [Rew.comp_app]
  · intro x hx
    exact False.elim (normalized_closed φ x hx)

theorem shift_closure {n : ℕ} (A : ArithmeticSemiformula ℕ n) :
    (∃⁰* (Rew.shift ▹ A)) = Rew.shift ▹ (∃⁰* A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [exsClosure_succ]
    simpa using ih (∃⁰ A)

def Entry.shift : Entry → Entry
  | .side P hp => .side (Rewriting.shift P) (Hierarchy.rew Rew.shift hp)
  | .base σ h => .base σ h
  | .block φ hφ n A hs => .block φ hφ n (Rew.shift ▹ A) (state_shift φ A hs)

theorem shift_formula (e : Entry) : (Entry.shift e).formula = Rewriting.shift e.formula := by
  cases e with
  | side P h => rfl
  | base σ h => simp [Entry.shift, Entry.formula]
  | block φ hφ n A hs => simp [Entry.shift, Entry.formula, shift_closure]

theorem shift_output (e : Entry) : (Entry.shift e).output = Rewriting.shift e.output := by
  cases e <;> simp [Entry.shift, Entry.output]

theorem shift_formulas (es : List Entry) :
    (es.map Entry.shift).map Entry.formula = (es.map Entry.formula)⁺ := by
  simp [Rewriting.shifts, List.map_map, Function.comp_def, shift_formula]

theorem shift_outputs (es : List Entry) :
    (es.map Entry.shift).map Entry.output = (es.map Entry.output)⁺ := by
  simp [Rewriting.shifts, List.map_map, Function.comp_def, shift_output]

theorem disjoin_shift (Γ : Sequent ℒₒᵣ) : disjoin Γ⁺ = Rewriting.shift (disjoin Γ) := by
  induction Γ with
  | nil => simp [disjoin, Rewriting.shifts]
  | cons P Γ ih => simp [disjoin, Rewriting.shifts, ← ih]

/-- Opening a Π₂ universal preserves Π₂ classification at the eigenvariable. -/
theorem opened_pi_two (A : ArithmeticSemiformula ℕ 1)
    (hA : Hierarchy 𝚷 2 (∀⁰ A)) : Hierarchy 𝚷 2 A.free :=
  Hierarchy.rew Rew.free (Hierarchy.pi_of_pi_all hA)

/-- The ordinary universal rule with an arbitrary marked nonprincipal
context. Every entry, including partially opened induction blocks, is shifted
coherently before invoking the strictly smaller premise. -/
theorem marked_universal (A : ArithmeticSemiformula ℕ 1)
    (hA : Hierarchy 𝚷 2 (∀⁰ A)) (es : List Entry)
    (d : Derivation (A.free :: (es.map Entry.formula)⁺)) (hc : Derivation.IsCutFree d)
    (ih : ∀ e : Derivation ((Entry.side A.free (opened_pi_two A hA) :: es.map Entry.shift).map Entry.formula),
      Derivation.IsCutFree e → e.height < d.all.height →
      Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side A.free (opened_pi_two A hA) :: es.map Entry.shift).map Entry.output)))) :
    Nonempty (Proof 𝗣𝗔⁻ (disjoin ((Entry.side (∀⁰ A) hA :: es).map Entry.output))) := by
  have heq : A.free :: (es.map Entry.formula)⁺ =
      (Entry.side A.free (opened_pi_two A hA) :: es.map Entry.shift).map Entry.formula := by
    simp only [List.map_cons, Entry.formula]
    rw [shift_formulas]
  let e := d.cast heq
  have he : Derivation.IsCutFree e := by simpa [e] using hc
  have hh : e.height < d.all.height := by simp [e]
  have hp : Proof 𝗣𝗔⁻ (A.free ⋎ Rewriting.shift (disjoin (es.map Entry.output))) := by
    simpa only [List.map_cons, Entry.output, disjoin, shift_outputs, disjoin_shift] using (ih e he hh).some
  have hu := ParsonsLogicalCases.universal A (disjoin (es.map Entry.output)) hp
  have hs : Proof 𝗣𝗔⁻ ((disjoin (es.map Entry.output) ⋎ (∀⁰ A)) 🡒
      ((∀⁰ A) ⋎ disjoin (es.map Entry.output))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by intro M _ _ f h; simp at h ⊢; tauto)
  simpa [Entry.output, disjoin] using Nonempty.intro (Proof.mp hs hu)

end DiophantineConsistency.ParsonsShift

import DiophantineConsistency.ParsonsCollection
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenexAll
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuard ParsonsRule ParsonsCollection
variable {L : Language} [L.ORing]

omit [L.ORing] in
theorem guard_free (Q : Semiproposition L 1) (E : Proposition L) :
    (guard Q E).free = Q.free ⋎ Rewriting.shift E := by
  simp [ParsonsGuard.guard, ← TransitiveRewriting.comp_app]

def disjunction_to_all (Q : Semiproposition L 1) (E : Proposition L) :
    Derivation [(E ⋎ (∀⁰ Q)) 🡒 (∀⁰ guard Q E)] := by
  have h0 : Derivation [Q.free, Rewriting.shift E, ∼Q.free] :=
    Derivation.close Q.free (by simp) (by simp)
  have h1 : Derivation [∼Q.free, (guard Q E).free] := by
    simpa [guard_free] using h0.or.contra (Γ := [∼Q.free, Q.free ⋎ Rewriting.shift E]) (by simp)
  have h2 := all_mono Q (guard Q E) h1
  have h3 : Derivation [∼E, ∀⁰ guard Q E] := by
    have h4 : Derivation ((guard Q E).free :: [∼E]⁺) := by
      have h5 : Derivation [Q.free, Rewriting.shift E, ∼Rewriting.shift E] :=
        Derivation.close (Rewriting.shift E) (by simp) (by simp)
      simpa [guard_free, Rewriting.shifts] using h5.or
    exact h4.all.contra (by simp)
  have h4 : Derivation [∼E ⋏ ∼(∀⁰ Q), ∀⁰ guard Q E] := h3.and h2
  simpa [Semiformula.imp_eq] using h4.or

def all_to_disjunction (Q : Semiproposition L 1) (E : Proposition L) :
    Derivation [(∀⁰ guard Q E) 🡒 (E ⋎ (∀⁰ Q))] := by
  have h1 : Derivation [∼Q.free, Q.free, Rewriting.shift E] :=
    Derivation.close Q.free (by simp) (by simp)
  have h2 : Derivation [∼Rewriting.shift E, Q.free, Rewriting.shift E] :=
    Derivation.close (Rewriting.shift E) (by simp) (by simp)
  have h3 : Derivation [∼(guard Q E).free, Q.free, Rewriting.shift E] := by
    simpa [guard_free] using h1.and h2
  have h4 : Derivation [(∼(Rewriting.shift (guard Q E)))/[&0], Q.free, Rewriting.shift E] := by
    simpa using h3
  have h5 : Derivation [∃⁰ ∼(Rewriting.shift (guard Q E)), Q.free, Rewriting.shift E] := h4.exs
  have h6 : Derivation (Q.free :: [∼(∀⁰ guard Q E), E]⁺) := by
    simpa [Rewriting.shifts] using h5.contra
      (Γ := [Q.free, ∃⁰ ∼(Rewriting.shift (guard Q E)), Rewriting.shift E]) (by simp)
  have h7 : Derivation [∀⁰ Q, ∼(∀⁰ guard Q E), E] := h6.all
  have h8 : Derivation [E, ∀⁰ Q, ∼(∀⁰ guard Q E)] := h7.contra (by simp)
  have h9 : Derivation [E ⋎ (∀⁰ Q), ∼(∀⁰ guard Q E)] := h8.or
  simpa [Semiformula.imp_eq] using (h9.contra
    (Γ := [∼(∀⁰ guard Q E), E ⋎ (∀⁰ Q)]) (by simp)).or

def prove_disjunction_to_all {T : Theory L} (Q : Semiproposition L 1) (E : Proposition L)
    (h : Proof T (E ⋎ (∀⁰ Q))) : Proof T (∀⁰ guard Q E) :=
  .mp (.logical (disjunction_to_all Q E)) h

def prove_all_to_disjunction {T : Theory L} (Q : Semiproposition L 1) (E : Proposition L)
    (h : Proof T (∀⁰ guard Q E)) : Proof T (E ⋎ (∀⁰ Q)) :=
  .mp (.logical (all_to_disjunction Q E)) h

theorem provability_equiv {T : Theory L} (Q : Semiproposition L 1) (E : Proposition L) :
    Nonempty (Proof T (E ⋎ (∀⁰ Q))) ↔ Nonempty (Proof T (∀⁰ guard Q E)) := by
  constructor
  · rintro ⟨h⟩; exact ⟨prove_disjunction_to_all Q E h⟩
  · rintro ⟨h⟩; exact ⟨prove_all_to_disjunction Q E h⟩

end DiophantineConsistency.ParsonsPrenexAll

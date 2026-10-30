import DiophantineConsistency.ParsonsRule
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuard ParsonsRule
variable {L : Language} [L.ORing]

/-- Lift a pointwise logical implication through existential quantification. -/
def exists_mono (A B : Semiproposition L 1)
    (d : Derivation [∼A.free, B.free]) : Derivation [∼(∃⁰ A), ∃⁰ B] := by
  have h0 : Derivation [(Rewriting.shift B)/[&0], ∼A.free] := by
    simpa using d.contra (Γ := [B.free, ∼A.free]) (by simp)
  have h1 : Derivation [∃⁰ Rewriting.shift B, ∼A.free] := h0.exs
  have h2 : Derivation ((∼A).free :: [∃⁰ B]⁺) := by
    simpa [Rewriting.shifts] using h1.contra
      (Γ := [∼A.free, ∃⁰ Rewriting.shift B]) (by simp)
  have h3 := h2.all
  simpa using h3

/-- The existential of `guard Q E` is a strict outer existential for the
    disjunction of E with the existential formula `∃Q`. -/
def disjunction_to_exs (Q : Semiproposition L 1) (E : Proposition L) :
    Derivation [(E ⋎ (∃⁰ Q)) 🡒 (∃⁰ guard Q E)] := by
  have h0 : Derivation [Q.free, ∼Q.free, Rewriting.shift E] :=
    Derivation.close Q.free (by simp) (by simp)
  have h1 : Derivation [(guard Q E).free, ∼Q.free] := by
    have h0' : Derivation [Q.free, Rewriting.shift E, ∼Q.free] := h0.contra (by simp)
    have he : (guard Q E).free = Q.free ⋎ Rewriting.shift E := by
      simp [ParsonsGuard.guard, ← TransitiveRewriting.comp_app]
    simpa [he] using h0'.or
  have h2 : Derivation [∼(∃⁰ Q), ∃⁰ guard Q E] := by
    exact exists_mono Q (guard Q E) (h1.contra (by simp))
  have h3 : Derivation [∼E, ∃⁰ guard Q E] := by
    have ht : Derivation [(guard Q E)/[‘0’], ∼E] := by
      simp only [guard_subst]
      have h : Derivation [E, Q/[‘0’], ∼E] := Derivation.close E (by simp) (by simp)
      exact (h.contra (Γ := [Q/[‘0’], E, ∼E]) (by simp)).or
    exact ht.exs.contra (by simp)
  have h4 : Derivation [∼E ⋏ ∼(∃⁰ Q), ∃⁰ guard Q E] := h3.and h2
  simpa [Semiformula.imp_eq] using h4.or

/-- The reverse implication, also a pure LK derivation. -/
def exs_to_disjunction (Q : Semiproposition L 1) (E : Proposition L) :
    Derivation [(∃⁰ guard Q E) 🡒 (E ⋎ (∃⁰ Q))] := by
  have h0 : Derivation [(Rewriting.shift Q)/[&0], ∼Q.free, Rewriting.shift E] := by
    simpa using Derivation.close Q.free (Δ := [Q.free, ∼Q.free, Rewriting.shift E])
      (by simp) (by simp)
  have h1 : Derivation [∼Q.free, Rewriting.shift E, Rewriting.shift (∃⁰ Q)] := by
    simpa using h0.exs.contra
      (Γ := [∼Q.free, Rewriting.shift E, ∃⁰ Rewriting.shift Q]) (by simp)
  have h2 : Derivation [∼Rewriting.shift E, Rewriting.shift E, Rewriting.shift (∃⁰ Q)] :=
    Derivation.close (Rewriting.shift E) (by simp) (by simp)
  have hg : (guard Q E).free = Q.free ⋎ Rewriting.shift E := by
    simp [ParsonsGuard.guard, ← TransitiveRewriting.comp_app]
  have h3 : Derivation ((∼(guard Q E)).free :: [E, ∃⁰ Q]⁺) := by
    simpa [hg, Rewriting.shifts] using h1.and h2
  have h4 : Derivation [∼(∃⁰ guard Q E), E, ∃⁰ Q] := by simpa using h3.all
  have h5 : Derivation [E, ∃⁰ Q, ∼(∃⁰ guard Q E)] := h4.contra (by simp)
  have h6 : Derivation [E ⋎ (∃⁰ Q), ∼(∃⁰ guard Q E)] := h5.or
  simpa [Semiformula.imp_eq] using (h6.contra (Γ := [∼(∃⁰ guard Q E), E ⋎ (∃⁰ Q)]) (by simp)).or

/-- Any existing rule proof of the side disjunction gives a proof of its
    existentially prefixed version. -/
def prove_disjunction_to_exs {T : Theory L} (Q : Semiproposition L 1) (E : Proposition L)
    (h : Proof T (E ⋎ (∃⁰ Q))) : Proof T (∃⁰ guard Q E) :=
  .mp (.logical (disjunction_to_exs Q E)) h

def prove_exs_to_disjunction {T : Theory L} (Q : Semiproposition L 1) (E : Proposition L)
    (h : Proof T (∃⁰ guard Q E)) : Proof T (E ⋎ (∃⁰ Q)) :=
  .mp (.logical (exs_to_disjunction Q E)) h

/-- The two shapes have rule proofs over exactly the same theory. -/
theorem provability_equiv {T : Theory L} (Q : Semiproposition L 1) (E : Proposition L) :
    Nonempty (Proof T (E ⋎ (∃⁰ Q))) ↔ Nonempty (Proof T (∃⁰ guard Q E)) := by
  constructor
  · rintro ⟨h⟩; exact ⟨prove_disjunction_to_exs Q E h⟩
  · rintro ⟨h⟩; exact ⟨prove_exs_to_disjunction Q E h⟩

/-- If the inputs are bounded, the introduced existential has bounded
matrix, i.e. this instance is genuinely strict Σ₁. -/
theorem strict_matrix (Q : Semiproposition L 1) (E : Proposition L)
    (hQ : Hierarchy 𝚺 0 Q) (hE : Hierarchy 𝚺 0 E) :
    Hierarchy 𝚺 0 (guard Q E) := by
  simp only [ParsonsGuard.guard, Hierarchy.or_iff]
  exact ⟨hQ, by simpa using hE⟩

end DiophantineConsistency.ParsonsPrenex

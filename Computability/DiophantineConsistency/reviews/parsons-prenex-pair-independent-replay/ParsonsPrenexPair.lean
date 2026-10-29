import DiophantineConsistency.ParsonsPrenex
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPrenexPair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuard ParsonsRule ParsonsPrenex
variable {L : Language} [L.ORing]

def matrix (Q R : Semiproposition L 1) : Semiproposition L 2 :=
  (Rew.bShift.q ▹ R) ⋎ (Rew.bShift ▹ Q)

def body (Q R : Semiproposition L 1) : Semiproposition L 1 := ∃⁰ matrix Q R

omit [L.ORing] in
theorem guard_free (Q R : Semiproposition L 1) :
    (guard Q (∃⁰ R)).free = Q.free ⋎ (∃⁰ (Rew.shift.q ▹ R)) := by
  have he : (@Rew.free L 1).comp (@Rew.bShift L ℕ 0).q = Rew.shift := by
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app]
    · simp [Rew.comp_app]
  simp [ParsonsGuard.guard, ← TransitiveRewriting.comp_app, he]

omit [L.ORing] in
theorem body_free (Q R : Semiproposition L 1) :
    (body Q R).free = ∃⁰ (guard (Rew.shift.q ▹ R) Q.free) := by
  have he : (@Rew.free L 1).comp (@Rew.bShift L ℕ 0).q = Rew.shift := by
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app]
    · simp [Rew.comp_app]
  have hf : (@Rew.free L 1).comp (@Rew.bShift L ℕ 1) =
      (@Rew.bShift L ℕ 0).comp (@Rew.free L 0) := by
    ext i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      change (@Rew.free L 1) (#(Fin.last 1)) = &0
      exact Rew.free_bvar_last
    · simp [Rew.comp_app]
  simp [body, matrix, ParsonsGuard.guard, ← TransitiveRewriting.comp_app, he, hf]

/-- Turn an LK implication proof into the corresponding sequent. -/
def sequentize (P Q : Proposition L) (d : Derivation [P 🡒 Q]) : Derivation [∼P, Q] := by
  have h1 : Derivation [P, ∼P, Q] := Derivation.close P (by simp) (by simp)
  have h2 : Derivation [∼Q, ∼P, Q] := Derivation.close Q (by simp) (by simp)
  have h3 : Derivation [∼(P 🡒 Q), ∼P, Q] := by
    simpa [Semiformula.imp_eq] using h1.and h2
  simpa using d.cut h3

def pair_forward_pointwise (Q R : Semiproposition L 1) :
    Derivation [∼(guard Q (∃⁰ R)).free, (body Q R).free] := by
  simpa [guard_free, body_free] using
    sequentize (Q.free ⋎ (∃⁰ (Rew.shift.q ▹ R)))
      (∃⁰ (guard (Rew.shift.q ▹ R) Q.free))
      (disjunction_to_exs (Rew.shift.q ▹ R) Q.free)

def pair_backward_pointwise (Q R : Semiproposition L 1) :
    Derivation [∼(body Q R).free, (guard Q (∃⁰ R)).free] := by
  simpa [guard_free, body_free] using
    sequentize (∃⁰ (guard (Rew.shift.q ▹ R) Q.free))
      (Q.free ⋎ (∃⁰ (Rew.shift.q ▹ R)))
      (exs_to_disjunction (Rew.shift.q ▹ R) Q.free)

/-- Move both witnesses into an explicit two-variable existential block. -/
def pair_forward {T : Theory L} (Q R : Semiproposition L 1)
    (h : Proof T ((∃⁰ R) ⋎ (∃⁰ Q))) : Proof T (∃⁰ body Q R) := by
  have h1 : Proof T (∃⁰ guard Q (∃⁰ R)) := prove_disjunction_to_exs Q (∃⁰ R) h
  have h2 : Derivation [(∃⁰ guard Q (∃⁰ R)) 🡒 (∃⁰ body Q R)] := by
    simpa [Semiformula.imp_eq] using (exists_mono _ _ (pair_forward_pointwise Q R)).or
  exact .mp (.logical h2) h1

def pair_backward {T : Theory L} (Q R : Semiproposition L 1)
    (h : Proof T (∃⁰ body Q R)) : Proof T ((∃⁰ R) ⋎ (∃⁰ Q)) := by
  have h2 : Derivation [(∃⁰ body Q R) 🡒 (∃⁰ guard Q (∃⁰ R))] := by
    simpa [Semiformula.imp_eq] using (exists_mono _ _ (pair_backward_pointwise Q R)).or
  exact prove_exs_to_disjunction Q (∃⁰ R) (.mp (.logical h2) h)

theorem pair_strict_matrix (Q R : Semiproposition L 1)
    (hQ : Hierarchy 𝚺 0 Q) (hR : Hierarchy 𝚺 0 R) :
    Hierarchy 𝚺 0 (matrix Q R) := by
  simp [matrix, hQ, hR]

end DiophantineConsistency.ParsonsPrenexPair

import DiophantineConsistency.FoundationHAOrderTrichotomy
import DiophantineConsistency.FoundationHAOrderIrreflexive

/-! # Decidability of the interpreted strict order inside HA

Plain trichotomy, proved earlier by actual HA formula induction, gives three
cases. Equality and reverse order each refute strict order by Leibniz
transport or transitivity and irreflexivity. All proofs below are HA
derivations, with arbitrary free terms and explicit finite open contexts.

The resulting stability is for `ltFormula` only. No general double-negation
rule, bounded-matrix normalization, or consistency-checker comparison is
asserted here.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderDecidable
open SetTheory.PA HA FoundationPAHFSyntax
open FoundationHAOrderIrreflexive FoundationHAOrderWitnesses

/-- The fresh hole is slot zero; the entire left parameter is shifted outside
it before equality elimination, including parameters already using slot zero. -/
theorem transport_right {G : List Formula} {s t u : Term}
    (h : Relative Formula.Ax_s G (ltFormula s t))
    (he : Relative Formula.Ax_s G (.eq t u)) :
    Relative Formula.Ax_s G (ltFormula s u) := by
  have h₀ : Relative Formula.Ax_s G (Formula.subst (Formula.instTerm t)
      (ltFormula (Term.rename Nat.succ s) (.var 0))) := by
    simpa only [subst_ltFormula, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ] using h
  have h₁ := Relative.eq_elim (ltFormula (Term.rename Nat.succ s) (.var 0)) he h₀
  simpa only [subst_ltFormula, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using h₁

theorem not_lt_of_eq {G : List Formula} {s t : Term}
    (he : Relative Formula.Ax_s G (.eq s t)) :
    Relative Formula.Ax_s G (neg (ltFormula s t)) := by
  apply Relative.imp_intro
  exact ((lt_irrefl s).weaken (by simp)).mp
    (transport_right (Relative.hypothesis List.mem_cons_self) (he.eq_symm.prepend _))

theorem not_lt_of_reverse {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (ltFormula t s)) :
    Relative Formula.Ax_s G (neg (ltFormula s t)) := by
  apply Relative.imp_intro
  exact ((lt_irrefl s).weaken (by simp)).mp
    (lt_trans (Relative.hypothesis List.mem_cons_self) (h.prepend _))

/-- A genuine object-language decision disjunction, not Lean `Decidable`
on a model interpretation and not just a translated excluded-middle formula. -/
theorem lt_decidable (s t : Term) :
    Proves (.or (ltFormula s t) (neg (ltFormula s t))) := by
  apply Relative.or_elim (FoundationHAOrderTrichotomy.trichotomy s t)
  · exact Relative.or_intro_left _ (Relative.hypothesis List.mem_cons_self)
  · apply Relative.or_elim (Relative.hypothesis List.mem_cons_self)
    · exact Relative.or_intro_right _ (not_lt_of_eq (Relative.hypothesis List.mem_cons_self))
    · exact Relative.or_intro_right _ (not_lt_of_reverse (Relative.hypothesis List.mem_cons_self))

/-- Order-specific double-negation elimination follows from that proved
decision formula using intuitionistic disjunction elimination. -/
theorem lt_stable (s t : Term) :
    Proves (.imp (doubleNeg (ltFormula s t)) (ltFormula s t)) := by
  apply Relative.imp_intro
  apply Relative.or_elim ((lt_decidable s t).weaken (by simp))
  · exact Relative.hypothesis List.mem_cons_self
  · have hn : Relative Formula.Ax_s
        [neg (ltFormula s t), doubleNeg (ltFormula s t)] (neg (ltFormula s t)) :=
      Relative.hypothesis List.mem_cons_self
    have hnn : Relative Formula.Ax_s
        [neg (ltFormula s t), doubleNeg (ltFormula s t)] (doubleNeg (ltFormula s t)) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨L,hL,h⟩ := hnn.mp hn
    exact ⟨L,hL,.botE _ _ h⟩

theorem recover {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (doubleNeg (ltFormula s t))) :
    Relative Formula.Ax_s G (ltFormula s t) :=
  ((lt_stable s t).weaken (by simp)).mp h

end DiophantineConsistency.FoundationHAOrderDecidable

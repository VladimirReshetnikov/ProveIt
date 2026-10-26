import DiophantineConsistency.HADeduction

set_option Elab.async false
namespace DiophantineConsistency.HADeductionChecks
open SetTheory.PA HA

/-- The two premises may use different finite axiom lists. -/
theorem distinct_axiom_mp (a b : Formula) :
    Relative (fun x => x = a ∨ x = .imp a b) [] b :=
  Relative.mp (relative_axiom (Or.inr rfl)) (relative_axiom (Or.inl rfl))

theorem context_permutation (a b : Formula) :
    Relative (fun _ => False) [b, a, b] a := by
  have h : Relative (fun _ => False) [a] a :=
    relative_of_derives (.ass _ _ List.mem_cons_self)
  exact h.weaken (by intro x hx; simp only [List.mem_singleton] at hx; simp [hx])

theorem axiom_weakening (a b : Formula) :
    Relative (fun x => x = a ∨ x = b) [] a := by
  have h : Relative (fun x => x = a) [] a := relative_axiom rfl
  exact h.mono_axioms (fun _ hx => Or.inl hx)

/-- Implication introduction moves the assumption past the finite axiom list. -/
theorem implication_with_axiom (a b : Formula) :
    Relative (fun x => x = .imp a b) [] (.imp a b) := by
  apply Relative.imp_intro
  exact Relative.mp (relative_axiom rfl)
    (relative_of_derives (.ass _ a List.mem_cons_self))

theorem object_composition (a b c : Formula) :
    Relative (fun x => x = .imp a b ∨ x = .imp b c) [] (.imp a c) :=
  Relative.imp_trans (relative_axiom (Or.inl rfl)) (relative_axiom (Or.inr rfl))

theorem conjunction_proof (a : Formula) :
    Proves (.and (.imp a a) (.imp a a)) :=
  Proves.and_intro (proves_identity a) (proves_identity a)

theorem actual_induction_projection (a : Formula) :
    Proves (Formula.sealPA (Formula.inductionForm a)) :=
  Proves.and_left (Proves.and_intro (induction_axiom a) (proves_identity a))

#print axioms Relative.combine
#print axioms Relative.mp
#print axioms Relative.imp_intro
#print axioms Relative.imp_trans
#print axioms Proves.mp
#print axioms distinct_axiom_mp
#print axioms context_permutation
#print axioms actual_induction_projection

end DiophantineConsistency.HADeductionChecks

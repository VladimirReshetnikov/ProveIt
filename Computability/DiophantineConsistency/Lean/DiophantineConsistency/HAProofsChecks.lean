import DiophantineConsistency.HAProofs

/-! Focused checks of the actual HA proof relation, including its binders. -/
set_option Elab.async false
namespace DiophantineConsistency.HA.Checks
open SetTheory.PA

theorem six_arithmetic_axioms :
    Proves (Formula.sealPA Formula.succInj) ∧
    Proves (Formula.sealPA Formula.zeroNotSucc) ∧
    Proves (Formula.sealPA Formula.addZero) ∧
    Proves (Formula.sealPA Formula.addSucc) ∧
    Proves (Formula.sealPA Formula.mulZero) ∧
    Proves (Formula.sealPA Formula.mulSucc) :=
  ⟨proves_axiom Formula.Ax_s_succInj, proves_axiom Formula.Ax_s_zeroNotSucc,
   proves_axiom Formula.Ax_s_addZero, proves_axiom Formula.Ax_s_addSucc,
   proves_axiom Formula.Ax_s_mulZero, proves_axiom Formula.Ax_s_mulSucc⟩

theorem every_formula_induction (a : Formula) :
    Proves (Formula.sealPA (Formula.inductionForm a)) := induction_axiom a

/-- The old parameter is shifted from variable 0 to variable 1. -/
theorem universal_eigenvariable_shift :
    Derives [.eq (.var 0) (.var 0)] (.all (.eq (.var 1) (.var 1))) :=
  .allI _ _ (.ass _ _ (by decide))

/-- Under `∀ x`, choose the same x as the existential witness y. -/
theorem universal_reflexive_witness :
    Derives [] (.all (.ex (.eq (.var 1) (.var 0)))) :=
  .allI [] _ (.exI [] _ (.var 0) (.eqRefl [] (.var 0)))

/-- The existential body's target and the entire old context are shifted. -/
theorem existential_elimination_signature (G : List Formula) (a c : Formula)
    (hex : Derives G (.ex a))
    (hbody : Derives (a :: G.map (Formula.rename Nat.succ))
      (Formula.rename Nat.succ c)) : Derives G c :=
  .exE G a c hex hbody

theorem equality_symmetry :
    Derives [.eq (.var 0) (.var 1)] (.eq (.var 1) (.var 0)) :=
  .eqElim _ (.var 0) (.var 1) (.eq (.var 0) (.var 1))
    (.ass _ _ (by decide)) (.eqRefl _ (.var 0))

theorem explosion (a : Formula) : Derives [.bot] a :=
  .botE _ a (.ass _ .bot (by simp))

theorem relative_identity_without_axioms (B : Formula → Prop) (a : Formula) :
    Relative B [] (.imp a a) := relative_of_derives (Derives.identity [] a)

/-- The sole calculus comparison is in the safe direction. -/
theorem classical_audit (a : Formula) (h : Proves a) :
    Formula.BProv Formula.Ax_s [] a := to_classical h

end DiophantineConsistency.HA.Checks

#print axioms DiophantineConsistency.HA.Derives.erase
#print axioms DiophantineConsistency.HA.Derives.weaken
#print axioms DiophantineConsistency.HA.induction_axiom
#print axioms DiophantineConsistency.HA.to_classical
#print axioms DiophantineConsistency.HA.Checks.six_arithmetic_axioms
#print axioms DiophantineConsistency.HA.Checks.universal_eigenvariable_shift
#print axioms DiophantineConsistency.HA.Checks.universal_reflexive_witness
#print axioms DiophantineConsistency.HA.Checks.existential_elimination_signature
#print axioms DiophantineConsistency.HA.Checks.equality_symmetry
#print axioms DiophantineConsistency.HA.Checks.explosion

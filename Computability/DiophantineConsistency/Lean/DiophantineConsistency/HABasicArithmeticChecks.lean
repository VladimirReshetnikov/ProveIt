import DiophantineConsistency.HABasicArithmetic

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HABasicArithmeticChecks
open SetTheory.PA DiophantineConsistency.HA

/-- Equality elimination respects ambient variables in a one-hole context. -/
theorem nested_term_congruence {G : List Formula} {s t : Term}
    (h : Derives G (.eq s t)) :
    Derives G (.eq (.mul (.add s (.var 3)) (.succ s))
      (.mul (.add t (.var 3)) (.succ t))) := by
  simpa only [Term.subst, Formula.instTerm, Term.rename] using
    h.eq_congr_term (.mul (.add (.var 0) (.var 4)) (.succ (.var 0)))

example {G : List Formula} {s t u : Term}
    (h : Derives G (.eq s t)) (h' : Derives G (.eq u t)) : Derives G (.eq s u) :=
  h.eq_trans h'.eq_symm

/-- Both terms can contain unrelated free parameters; neither quantifier captures them. -/
example : Proves (.eq
    (.add (.mul (.var 0) (.var 4)) (.succ (.add (.var 3) (.var 1))))
    (.succ (.add (.mul (.var 0) (.var 4)) (.add (.var 3) (.var 1))))) :=
  Arithmetic.add_succ (.mul (.var 0) (.var 4)) (.add (.var 3) (.var 1))

example (s t : Term) : Proves (.imp (.eq (.succ s) (.succ t)) (.eq s t)) :=
  Arithmetic.succ_inj s t
example (t : Term) : Proves (.imp (.eq (.succ t) .zero) .bot) := Arithmetic.succ_ne_zero t
example (t : Term) : Proves (.eq (.add t .zero) t) := Arithmetic.add_zero t
example (t : Term) : Proves (.eq (.mul t .zero) .zero) := Arithmetic.mul_zero t
example (s t : Term) : Proves (.eq (.mul s (.succ t)) (.add (.mul s t) s)) :=
  Arithmetic.mul_succ s t

/-- Induction variable zero and parameter one, underneath another quantifier. -/
def parameterBody : Formula := .all (.eq (.add (.var 1) (.var 2)) (.add (.var 1) (.var 2)))

theorem parameter_zero : Formula.subst Formula.substZero parameterBody =
    .all (.eq (.add .zero (.var 1)) (.add .zero (.var 1))) := rfl

theorem parameter_succ : Formula.subst Formula.substSuccVar parameterBody =
    .all (.eq (.add (.succ (.var 1)) (.var 2)) (.add (.succ (.var 1)) (.var 2))) := rfl

/-- A complete instance of the derived HA induction rule with a genuine free parameter. -/
theorem parameter_induction : Proves (.all parameterBody) := by
  apply Arithmetic.induction parameterBody
  · rw [parameter_zero]
    apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    exact Relative.eq_refl (.add .zero (.var 1))
  · apply Relative.all_intro Formula.Ax_s_sentences (G := [])
    apply Relative.imp_intro
    rw [parameter_succ]
    apply Relative.all_intro Formula.Ax_s_sentences
    exact Relative.eq_refl (.add (.succ (.var 1)) (.var 2))

/-- Reopening a closure preserves the nested bound variable and all free parameters. -/
theorem reopen_parameter (h : Proves (Formula.closeN 2 parameterBody)) :
    Proves (.all (.eq (.add (.var 4) (.var 5)) (.add (.var 4) (.var 5)))) := by
  have hf : ∀ n, Formula.Free n parameterBody → n < 2 := by
    intro n hn
    change (n+1 = 1 ∨ n+1 = 2) ∨ (n+1 = 1 ∨ n+1 = 2) at hn
    omega
  have hp := Relative.open_rename 2 parameterBody (fun n => n+3) hf h
  exact hp

/-- Zero outer closures are handled only when the formula has no free indices. -/
example (h : Proves (.all (.eq (.var 0) (.var 0)))) :
    Proves (Formula.rename (fun _ => 19) (.all (.eq (.var 0) (.var 0)))) := by
  apply Relative.open_rename 0 _ (fun _ => 19) _ h
  intro n hn
  change n+1 = 0 ∨ n+1 = 0 at hn
  omega

example (n : Nat) (t : Term) : Proves (Formula.closeN n (.eq (.add .zero t) t)) :=
  Arithmetic.reclose n (Arithmetic.zero_add t)

example (t : Term) : Proves (.eq (.add t (.succ .zero)) (.succ t)) := Arithmetic.add_one t

#print axioms Derives.eq_symm
#print axioms Derives.eq_trans
#print axioms Derives.eq_congr_term
#print axioms Relative.all_intro
#print axioms Relative.open_rename
#print axioms Arithmetic.axiom_body
#print axioms Arithmetic.succ_inj
#print axioms Arithmetic.succ_ne_zero
#print axioms Arithmetic.add_zero
#print axioms Arithmetic.add_succ
#print axioms Arithmetic.mul_zero
#print axioms Arithmetic.mul_succ
#print axioms Arithmetic.induction
#print axioms Arithmetic.zero_add_all
#print axioms Arithmetic.zero_add
#print axioms Arithmetic.add_one
#print axioms nested_term_congruence
#print axioms parameter_induction
#print axioms reopen_parameter
end DiophantineConsistency.HABasicArithmeticChecks

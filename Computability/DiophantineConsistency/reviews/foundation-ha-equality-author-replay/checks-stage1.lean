import DiophantineConsistency.FoundationHAEquality

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAEqualityChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAEquality
open SetTheory.PA HA

private def e (s t : SyntacticTerm ℒₒᵣ) : Proposition ℒₒᵣ := .rel .eq ![s,t]
private def inputs : Proposition ℒₒᵣ :=
  e (.fvar 0) (.fvar 2) ⋏ (e (.fvar 1) (.fvar 3) ⋏ ⊤)

/-- These are definitional checks against the actual source, including its
trailing true conjunct and the reversed bound-variable ordering. -/
theorem literal_refl : sentence (Theory.Eq.refl ℒₒᵣ)ᴺ =
    Formula.closeN 1 (doubleNeg (.eq (.var 0) (.var 0))) := rfl

theorem literal_symm : sentence (Theory.Eq.symm ℒₒᵣ)ᴺ =
    Formula.closeN 2 (formula (e (.fvar 1) (.fvar 0) 🡒 e (.fvar 0) (.fvar 1))ᴺ) := rfl

theorem literal_trans : sentence (Theory.Eq.trans ℒₒᵣ)ᴺ =
    Formula.closeN 3 (formula (e (.fvar 2) (.fvar 1) 🡒
      (e (.fvar 1) (.fvar 0) 🡒 e (.fvar 2) (.fvar 0)))ᴺ) := rfl

theorem literal_zero : sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .zero)ᴺ =
    formula ((⊤ : Proposition ℒₒᵣ) 🡒
      e (.func .zero Fin.elim0) (.func .zero Fin.elim0))ᴺ := rfl

theorem literal_one : sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .one)ᴺ =
    formula ((⊤ : Proposition ℒₒᵣ) 🡒
      e (.func .one Fin.elim0) (.func .one Fin.elim0))ᴺ := rfl

theorem literal_add : sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .add)ᴺ =
    Formula.closeN 4 (formula (inputs 🡒
      e (.func .add ![.fvar 0,.fvar 1]) (.func .add ![.fvar 2,.fvar 3]))ᴺ) := rfl

theorem literal_mul : sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .mul)ᴺ =
    Formula.closeN 4 (formula (inputs 🡒
      e (.func .mul ![.fvar 0,.fvar 1]) (.func .mul ![.fvar 2,.fvar 3]))ᴺ) := rfl

theorem literal_eq : sentence (Theory.Eq.relExt (L := ℒₒᵣ) .eq)ᴺ =
    Formula.closeN 4 (formula (inputs 🡒
      (e (.fvar 0) (.fvar 1) 🡒 e (.fvar 2) (.fvar 3)))ᴺ) := rfl

theorem literal_lt : sentence (Theory.Eq.relExt (L := ℒₒᵣ) .lt)ᴺ =
    Formula.closeN 4 (formula (inputs 🡒
      ((Semiformula.rel .lt ![.fvar 0,.fvar 1] : Proposition ℒₒᵣ) 🡒
       (Semiformula.rel .lt ![.fvar 2,.fvar 3] : Proposition ℒₒᵣ)))ᴺ) := rfl

/-- Omitting the nullary antecedent changes the literal translated formula. -/
theorem zero_antecedent_not_erased :
    sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .zero)ᴺ ≠ doubleNeg (.eq .zero .zero) := by
  intro h
  cases h

/-- Free zero and free seven survive the order witness binder distinctly. -/
theorem literal_parameterized_order :
    ltFormula (.add (.var 0) (.succ (.var 7))) (.mul (.var 7) (.var 0)) =
    .ex (.eq (.add (.add (.var 1) (.succ (.var 8))) (.succ (.var 0)))
      (.mul (.var 8) (.var 1))) := rfl

theorem parameterized_stability : Proves (.imp
    (doubleNeg (.eq (.mul (.var 7) (.var 0)) (.succ (.var 0))))
    (.eq (.mul (.var 7) (.var 0)) (.succ (.var 0)))) :=
  equality_stable _ _

/-- The actual implication adapter works under an undischarged arbitrary
assumption, rather than silently treating that assumption as an HA axiom. -/
theorem open_context_imp (φ ψ : Proposition ℒₒᵣ) :
    Relative Formula.Ax_s [.imp (formula φᴺ) (formula ψᴺ)] (formula (φ 🡒 ψ)ᴺ) :=
  translated_imp φ ψ (Relative.hypothesis List.mem_cons_self)

theorem scoped_lt_transport (s t u v : Term) :
    Proves (.imp (.eq s u) (.imp (.eq t v)
      (.imp (doubleNeg (ltFormula s t)) (doubleNeg (ltFormula u v))))) := by
  apply Relative.imp_intro
  apply Relative.imp_intro
  apply Relative.imp_intro
  exact lt_transport
    (Relative.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    (Relative.hypothesis List.mem_cons_self)

theorem nested_parameterized_lt : Proves (Formula.closeN 2
    (.imp (.eq (.var 7) (.succ (.var 1)))
      (.imp (.eq (.add (.var 0) (.var 7)) (.var 1))
        (.imp (doubleNeg (ltFormula (.var 7) (.add (.var 0) (.var 7))))
          (doubleNeg (ltFormula (.succ (.var 1)) (.var 1))))))) :=
  Arithmetic.reclose 2 (scoped_lt_transport _ _ _ _)

theorem actual_lt_case : Proves (sentence (Theory.Eq.relExt (L := ℒₒᵣ) .lt)ᴺ) :=
  equality_axiom (.relExt .lt)

theorem actual_zero_case : Proves (sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .zero)ᴺ) :=
  equality_axiom (.funcExt .zero)

#print axioms equality_stable
#print axioms translated_imp
#print axioms FoundationHAEquality.refl
#print axioms FoundationHAEquality.symm
#print axioms FoundationHAEquality.trans
#print axioms funcZero
#print axioms funcOne
#print axioms funcAdd
#print axioms funcMul
#print axioms relEq
#print axioms lt_transport
#print axioms relLt
#print axioms equality_axiom
#print axioms literal_refl
#print axioms literal_symm
#print axioms literal_trans
#print axioms literal_zero
#print axioms literal_one
#print axioms literal_add
#print axioms literal_mul
#print axioms literal_eq
#print axioms literal_lt
#print axioms zero_antecedent_not_erased
#print axioms literal_parameterized_order
#print axioms parameterized_stability
#print axioms open_context_imp
#print axioms scoped_lt_transport
#print axioms nested_parameterized_lt
#print axioms actual_lt_case
#print axioms actual_zero_case

end DiophantineConsistency.FoundationHAEqualityChecks

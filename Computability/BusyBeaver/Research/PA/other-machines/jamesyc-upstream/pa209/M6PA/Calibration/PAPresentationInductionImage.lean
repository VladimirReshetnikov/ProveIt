module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationBinders
public import M6PA.Calibration.PAPresentationAxioms
public import Foundation.FirstOrder.Arithmetic.Schemata
@[expose] public section

/-! The exact image of Foundation's induction schema. Its additive step is
not silently identified with primitive successor induction. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

def additiveInductionFormula (p : Semiproposition language 1) : Proposition language :=
  implies (Semiformula.rewAux (Rew.subst ![zero]) p)
    (implies (.all (implies p
      (Semiformula.rewAux (Rew.subst ![add (.bvar 0) (succ zero)]) p))) (.all p))

theorem formula_one_substitution {ξ : Type} {m : Nat}
    (p : ArithmeticSemiformula ξ 1) (t : ArithmeticSemiterm ξ m) :
    formula (p/[t]) = (formula p)/[term t] := by
  have hv : term ∘ (![t] : Fin 1 → ArithmeticSemiterm ξ m) = ![term t] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  change formula (Semiformula.rewAux (Rew.subst ![t]) p) =
    Semiformula.rewAux (Rew.subst ![term t]) (formula p)
  rw [formula_subst,hv]

/-- Syntax equality only. A uniform PAeq derivation of the right-hand side
still requires the proved arithmetic step equation and formula congruence. -/
theorem formula_succInd (p : ArithmeticSemiproposition 1) :
    formula (Arithmetic.succInd p) = additiveInductionFormula (formula p) := by
  have hz : term ((0 : Nat) : ArithmeticSemiterm Nat 0) = (zero : Semiterm language Nat 0) := rfl
  have hs : term (‘(#0 + 1)’ : ArithmeticSemiterm Nat 1) =
      add (.bvar 0) (succ zero) := rfl
  have hi : (formula p)/[(Semiterm.bvar 0 : Semiterm language Nat 1)] = formula p :=
    @Rewriting.subst1_bvar0_eq language Nat (Semiformula language Nat) _ _ _ (formula p)
  simp only [Arithmetic.succInd,additiveInductionFormula,implies,formula,
    formula_neg,formula_one_substitution]
  change ((formula p)/[(term ((0 : Nat) : ArithmeticSemiterm Nat 0))]).neg.or
    (((((formula p)/[(Semiterm.bvar 0 : Semiterm language Nat 1)]).neg.or
      ((formula p)/[term (‘(#0 + 1)’ : ArithmeticSemiterm Nat 1)])).all).neg.or
      (((formula p)/[(Semiterm.bvar 0 : Semiterm language Nat 1)]).all)) = _
  rw [hz,hs,hi]
  rfl

#print axioms formula_succInd
end M6.PA.Presentation

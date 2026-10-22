import Init

/-!
A finite obstruction to weakening dominated rho8 to the diagonal guard u = a.
This is a countermodel to the proposed abstract inference, not a model of ZFC.
All statements are closed and use only Init.
-/
namespace ProofSimplification.DiagonalCountermodel

inductive Val where
  | zero | one | two
  deriving DecidableEq, Repr

open Val

def imp : Val → Val → Val
  | zero, zero => zero
  | zero, one => one
  | zero, two => one
  | one, _ => zero
  | two, zero => zero
  | two, one => zero
  | two, two => one

abbrev Designated (a : Val) : Prop := a = zero

def rho8 (a b c u : Val) : Val :=
  imp (imp (imp c u) a) (imp (imp a c) (imp b c))

theorem mp (a b : Val) :
    Designated (imp a b) → Designated a → Designated b := by
  cases a <;> cases b <;> decide

theorem diagonal (a b c : Val) : Designated (rho8 a b c a) := by
  cases a <;> cases b <;> cases c <;> decide

theorem unrestricted_fails : ¬ Designated (rho8 one zero two two) := by
  decide

/-- No abstract rule with only MP and diagonal rows can recover every row. -/
theorem diagonal_does_not_suffice :
    ¬ (∀ (A : Type) (i : A → A → A) (T : A → Prop),
      (∀ a b, T (i a b) → T a → T b) →
      (∀ a b c, T (i (i (i c a) a) (i (i a c) (i b c)))) →
      ∀ a b c u, T (i (i (i c u) a) (i (i a c) (i b c)))) := by
  intro h
  exact unrestricted_fails (h Val imp Designated mp diagonal one zero two two)

#print axioms mp
#print axioms diagonal
#print axioms unrestricted_fails
#print axioms diagonal_does_not_suffice
end ProofSimplification.DiagonalCountermodel

/-
An implementation audit of one abbreviated modal axiom list.

Source: Hajnal Andreka and Istvan Nemeti, "Formalizing set theory in weak
logics, searching for the weakest logic with Godel's incompleteness
property", arXiv:1111.0995v1, Section 2, displayed modal list B,K,S5,C1,C2.
https://arxiv.org/html/1111.0995v1

Interpret every box as the constant true operator, and every diamond as
the constant false operator.  With ordinary Boolean propositional
connectives, K, the displayed S5 (the 5 axiom), C1 and C2 all evaluate true.
Modus ponens and necessitation preserve truth.  But T, box p -> p, fails
when p is false.  Consequently the abbreviated list, read literally,
does not axiomatize reflexive S5 modalities.

This checks a transcription/implementation trap, not the paper's main
translation theorem.  The paper's earlier axiom (3), p -> diamond p, and
its equational D1 both fail in this interpretation and supply the missing
reflexivity condition.  Those original presentations are not refuted.

The scope of the file is a Boolean valuation certificate.  It does not
claim to formalize the paper's full syntactic translation or a complete
modal soundness theorem.
-/

namespace ProveIt.ModalBasisAudit

def implies (p q : Bool) : Bool := (!p) || q

def box (_i : Nat) (_p : Bool) : Bool := true

def diamond (_i : Nat) (_p : Bool) : Bool := false

theorem duality (i : Nat) (p : Bool) :
    diamond i p = !(box i (!p)) := rfl

def schemaK (i : Nat) (p q : Bool) : Bool :=
  implies (box i (implies p q)) (implies (box i p) (box i q))

def schema5 (i : Nat) (p : Bool) : Bool :=
  implies (diamond i p) (box i (diamond i p))

def schemaC1 (i j : Nat) (p : Bool) : Bool :=
  implies (diamond i (diamond j p)) (diamond j (diamond i p))

def schemaC2 (i j : Nat) (p : Bool) : Bool :=
  implies (diamond i (box j p)) (box j (diamond i p))

/-- All listed non-propositional schemas hold under the degenerate
    Boolean interpretation, for every choice of indices and truth values. -/
theorem abbreviated_schemata (i j : Nat) (p q : Bool) :
    schemaK i p q = true ∧
    schema5 i p = true ∧
    schemaC1 i j p = true ∧
    schemaC2 i j p = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A Boolean tautology, understood semantically, is true on every
    assignment, including the assignments given to modal subformulas. -/
def BooleanTautology (f : (Nat → Bool) → Bool) : Prop :=
  ∀ valuation, f valuation = true

theorem propositional_tautologies_hold
    (f : (Nat → Bool) → Bool)
    (hf : BooleanTautology f)
    (valuation : Nat → Bool) :
    f valuation = true :=
  hf valuation

theorem modus_ponens {p q : Bool}
    (hp : p = true) (hpq : implies p q = true) : q = true := by
  cases p with
  | false => cases hp
  | true => exact hpq

theorem necessitation (i : Nat) (p : Bool) (_hp : p = true) :
    box i p = true := rfl

theorem T_fails (i : Nat) :
    implies (box i false) false = false := rfl

theorem T_not_valid (i : Nat) :
    ¬ (∀ p : Bool, implies (box i p) p = true) := by
  intro h
  have impossible : false = true := h false
  cases impossible

/-- The earlier, unabbreviated axiom (3) excludes this interpretation. -/
theorem original_axiom_three_fails (i : Nat) :
    implies true (diamond i true) = false := rfl

/-- So does the earlier equational D1, x + F(x) = F(x). -/
theorem equational_D1_fails (i : Nat) :
    (true || diamond i true) ≠ diamond i true := by
  intro h
  cases h

end ProveIt.ModalBasisAudit

#print axioms ProveIt.ModalBasisAudit.abbreviated_schemata
#print axioms ProveIt.ModalBasisAudit.propositional_tautologies_hold
#print axioms ProveIt.ModalBasisAudit.modus_ponens
#print axioms ProveIt.ModalBasisAudit.necessitation
#print axioms ProveIt.ModalBasisAudit.T_not_valid
#print axioms ProveIt.ModalBasisAudit.original_axiom_three_fails
#print axioms ProveIt.ModalBasisAudit.equational_D1_fails

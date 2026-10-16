import BusyBeaver.ZFC.Kalmar
import BusyBeaver.ZFC.TarskiCalculus
import BusyBeaver.ZFC.Lukasiewicz

/-!
# The falsity bridge for the substitution-free Tarski calculus

The pure implicational Lukasiewicz row can supply K, S and Peirce's law.
It cannot by itself supply ex falso for a designated primitive falsity.
This file derives ex falso from K, S and the existing `rho6` row, and then
assembles precisely the `Kalmar.Classical` hypothesis of `TarskiComplete`.

No new inference rule or machine row is added. The generic bridge first keeps
K, S and Peirce explicit, then discharges them using the explicit reconstructed
Lukasiewicz proof. `classical_from_rows` has no propositional assumptions.

Checked against the dependencies at ProveIt commit
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7` with Lean 4.32.0.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF

variable {Ax : NF → Prop}

/-- K and S, together with the existing `rho6`, give ex falso.
For `q = ∀i (∀i a → ⊥)`, compose `⊥ → (q → ⊥)` with `(q → ⊥) → a`.
The first formula is K; the second is exactly `rho6 i a`. -/
theorem efq_of_k_s
    (hK : ∀ a b : NF, Thm Ax (imp a (imp b a)))
    (hS : ∀ a b c : NF,
      Thm Ax (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (i : Nat) (a : NF) : Thm Ax (imp NF.bot a) := by
  let q : NF := all i (imp (all i a) NF.bot)
  have h6 : Thm Ax (imp (imp q NF.bot) a) := Thm.rho6 i a
  have h6lift : Thm Ax (imp NF.bot (imp (imp q NF.bot) a)) :=
    Thm.mp (hK (imp (imp q NF.bot) a) NF.bot) h6
  exact Thm.mp (Thm.mp (hS NF.bot (imp q NF.bot) a) h6lift) (hK NF.bot q)

/-- The exact classicality interface required by the existing derived rules
and conditional completeness theorem. Only implicational derivations remain
as inputs; the primitive-falsity component is supplied by `rho6`. -/
theorem classical_of_implicational
    (hK : ∀ a b : NF, Thm Ax (imp a (imp b a)))
    (hS : ∀ a b c : NF,
      Thm Ax (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (hP : ∀ a b : NF, Thm Ax (imp (imp (imp a b) a) a)) :
    Kalmar.Classical NF.imp NF.bot (Thm Ax) where
  mp := Thm.mp
  k := hK
  s := hS
  peirce := hP
  efq := efq_of_k_s hK hS 0

/-- K from the machine's original pure implicational row. -/
theorem k_from_rho8 (a b : NF) : Thm Ax (imp a (imp b a)) :=
  Lukasiewicz.impsingle_ax1 NF.imp (Thm Ax) Thm.mp Thm.rho8 a b

/-- S from the same row, through the reconstructed Tarski--Bernays basis. -/
theorem s_from_rho8 (a b c : NF) :
    Thm Ax (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) :=
  Lukasiewicz.tarski_bernays_ax2 NF.imp (Thm Ax) Thm.mp Thm.rho8 a b c

/-- Peirce's law from the same row. -/
theorem peirce_from_rho8 (a b : NF) : Thm Ax (imp (imp (imp a b) a) a) :=
  Lukasiewicz.impsingle_peirce NF.imp (Thm Ax) Thm.mp Thm.rho8 a b

/-- Full primitive-falsity classicality from the actual emitted rows.
The implicational part uses `rho8`; ex falso additionally uses `rho6`. -/
theorem classical_from_rows : Kalmar.Classical NF.imp NF.bot (Thm Ax) :=
  classical_of_implicational k_from_rho8 s_from_rho8 peirce_from_rho8

/-! Pure implication has no way to distinguish a named constant from an atom.
The following Boolean countervaluation makes the boundary precise. -/

private def bImp (a b : Bool) : Bool := !a || b

private def bLuk (c u a b : Bool) : Bool :=
  bImp (bImp (bImp c u) a) (bImp (bImp a c) (bImp b c))

/-- Every valuation validates the pure Lukasiewicz row. -/
theorem luk_boolean_valid (c u a b : Bool) : bLuk c u a b = true := by
  cases c <;> cases u <;> cases a <;> cases b <;> decide

/-- Material modus ponens preserves Boolean validity. -/
theorem boolean_mp {a b : Bool} (hAB : bImp a b = true) (hA : a = true) :
    b = true := by
  cases a with
  | false => cases hA
  | true => exact hAB

/-- Interpreting the primitive constant as true refutes ex falso to a false
atom. Hence the constant's intended meaning must enter through another row. -/
theorem efq_fails_when_bot_true : bImp true false = false := rfl

/-- The pure implicational row, MP and even theorem generalization. -/
inductive LukOnly : NF → Prop
  | row (c u a b : NF) : LukOnly (luk c u a b)
  | mp {a b : NF} : LukOnly (imp a b) → LukOnly a → LukOnly b
  | gen (i : Nat) {a : NF} : LukOnly a → LukOnly (all i a)

/-- A syntactic counterinterpretation, not the ordinary Tarski semantics:
the primitive constant is true, atoms are false, and quantifiers are identity. -/
def lukCounterValue : NF → Bool
  | rel _ _ => false
  | NF.eq _ _ => false
  | NF.bot => true
  | imp a b => bImp (lukCounterValue a) (lukCounterValue b)
  | all _ a => lukCounterValue a

theorem lukOnly_countervalue_sound {a : NF} (h : LukOnly a) :
    lukCounterValue a = true := by
  induction h with
  | row c u a b =>
    exact luk_boolean_valid (lukCounterValue c) (lukCounterValue u)
      (lukCounterValue a) (lukCounterValue b)
  | mp _ _ ih1 ih2 => exact boolean_mp ih1 ih2
  | gen _ _ ih => exact ih

/-- The claim that `rho8` alone supplies primitive-Bottom ex falso is false,
even if MP and generalization are included. -/
theorem efq_not_from_rho8 : ¬ LukOnly (imp NF.bot (rel 0 0)) := by
  intro h
  have bad : false = true := lukOnly_countervalue_sound h
  cases bad

#print axioms efq_of_k_s
#print axioms classical_of_implicational
#print axioms k_from_rho8
#print axioms s_from_rho8
#print axioms peirce_from_rho8
#print axioms classical_from_rows
#print axioms luk_boolean_valid
#print axioms boolean_mp
#print axioms efq_fails_when_bot_true
#print axioms lukOnly_countervalue_sound
#print axioms efq_not_from_rho8

end SetTheory.BusyBeaver.ZFC.Tarski

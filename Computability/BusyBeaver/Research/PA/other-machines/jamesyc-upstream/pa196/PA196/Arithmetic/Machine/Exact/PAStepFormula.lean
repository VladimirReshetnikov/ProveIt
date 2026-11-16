module
/- Exact PA196 arithmetic semantics, with literal working labels 0..195. -/
public import PA196.Arithmetic.Machine.Exact.PATheory
public import PA196.Arithmetic.Machine.Exact.PANatTape
@[expose] public section

/-! An explicit six-place arithmetic formula for the 392 literal PA196 rows.
Working controls are exactly 0..195 and state code 196 is reserved for halting.
This public transition formula has no auxiliary padding states. -/
namespace PA196.Arithmetic.Machine.Exact.PA.StepFormula
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def controlCode : Control → Nat
  | none => 196
  | some q => q.val

def rowRelation (src : WorkingState) (read : Bool)
    (q l r q' l' r' : Nat) : Prop :=
  let a := row src read
  q = src.val ∧ q' = controlCode a.next ∧
    if a.right then
      ∃ t, r = 2 * t + read.toNat ∧ l' = 2 * l + a.write.toNat ∧ r' = t
    else
      ∃ t u e, (e = 0 ∨ e = 1) ∧ l = 2 * u + e ∧
        r = 2 * t + read.toNat ∧ l' = u ∧ r' = 2 * (2 * t + a.write.toNat) + e

def rowFormula (src : WorkingState) (read : Bool) : ArithmeticSemisentence 6 :=
  let a := row src read
  if a.right then
    “q l r q' l' r'. q = ↑src.val ∧ q' = ↑(controlCode a.next) ∧
      ∃ t, r = (1 + 1) * t + ↑read.toNat ∧
        l' = (1 + 1) * l + ↑a.write.toNat ∧ r' = t”
  else
    “q l r q' l' r'. q = ↑src.val ∧ q' = ↑(controlCode a.next) ∧
      ∃ t u e, (e = 0 ∨ e = 1) ∧ l = (1 + 1) * u + e ∧
        r = (1 + 1) * t + ↑read.toNat ∧ l' = u ∧
        r' = (1 + 1) * ((1 + 1) * t + ↑a.write.toNat) + e”

theorem rowFormula_correct (src : WorkingState) (read : Bool)
    (q l r q' l' r' : Nat) :
    (Nat ⊧/![q,l,r,q',l',r'] (rowFormula src read)) ↔
      rowRelation src read q l r q' l' r' := by
  cases hd : (row src read).right <;> simp [rowFormula, rowRelation, hd]; aesop

def rows : List (WorkingState × Bool) :=
  (List.finRange 196).flatMap fun q => [(q, false), (q, true)]

set_option maxRecDepth 2000 in
theorem rows_length : rows.length = 392 := by decide

def disjoin : List (WorkingState × Bool) → ArithmeticSemisentence 6
  | [] => ⊥
  | (q,b)::rs => rowFormula q b ⋎ disjoin rs

def formula : ArithmeticSemisentence 6 := disjoin rows

def relation (q l r q' l' r' : Nat) : Prop :=
  ∃ src read, rowRelation src read q l r q' l' r'

theorem disjoin_correct (rs : List (WorkingState × Bool))
    (q l r q' l' r' : Nat) :
    (Nat ⊧/![q,l,r,q',l',r'] (disjoin rs)) ↔
      ∃ p ∈ rs, rowRelation p.1 p.2 q l r q' l' r' := by
  induction rs with
  | nil => simp [disjoin]
  | cons p rs ih =>
    rcases p with ⟨src, read⟩
    simp [disjoin, rowFormula_correct, ih]

theorem formula_correct (q l r q' l' r' : Nat) :
    (Nat ⊧/![q,l,r,q',l',r'] formula) ↔ relation q l r q' l' r' := by
  rw [formula, disjoin_correct]
  simp [relation, rows]

#print axioms rowFormula_correct
#print axioms formula_correct
end PA196.Arithmetic.Machine.Exact.PA.StepFormula


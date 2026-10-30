import BusyBeaver.ZFC.KZip

/-!
Literal transition tables for the K-family, and agreement of two tables on a set of states.

Every K-family candidate keeps K230's engine, so a proof about the engine is written once for any
table that agrees with K230 on the engine states it reads (`Agree M tm230 S`). For a concrete table
the agreement is a finite check (`agreeB`).
-/

namespace SetTheory.BusyBeaver.ZFC.KTableCore

open KZip

/-- One table entry: `some (write, moveRight, next)`, or `none` (no row). -/
abbrev Row := Option (Bool × Bool × Nat)

def tmOf (t : List (Row × Row)) : TMN := fun q b =>
  match t[q]? with
  | some p => if b then p.2 else p.1
  | none => none

def Agree (M N : TMN) (S : List Nat) : Prop := ∀ q ∈ S, ∀ b, M q b = N q b

def agreeB (M N : TMN) (S : List Nat) : Bool :=
  S.all fun q => decide (M q false = N q false) && decide (M q true = N q true)

theorem Agree.row {M N : TMN} {S : List Nat} (h : Agree M N S) {q : Nat} {b : Bool}
    {r : Option (Bool × Bool × Nat)} (hq : q ∈ S) (e : N q b = r) : M q b = r :=
  (h q hq b).trans e

end SetTheory.BusyBeaver.ZFC.KTableCore

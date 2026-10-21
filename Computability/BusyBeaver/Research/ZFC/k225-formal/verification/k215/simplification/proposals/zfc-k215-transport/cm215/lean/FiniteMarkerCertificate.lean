import MarkerTransport

namespace FiniteMarkerCertificate

open MarkerTransport

def checkOuter (old new : Table) (q : State) (b : Bool) : Bool :=
  decide (q ≠ 52 → q ≠ 176 →
    new (phi q) b = (old q b).map renameRow)

def checkStopped (old new : Table) (q : State) (b : Bool) : Bool :=
  decide (old q b = none → new (phi q) b = none)

def check52 (old : Table) (q : State) (b : Bool) : Bool :=
  match old q b with
  | none => true
  | some r => decide (r.next = 52 → r.write = true ∧ r.right = true)

def check156 (old : Table) (q : State) (b : Bool) : Bool :=
  match old q b with
  | none => true
  | some r => decide (r.next = 156 → r.write = true ∧ r.right = false)

def check176 (old : Table) (q : State) (b : Bool) : Bool :=
  match old q b with
  | none => true
  | some r => decide (r.next = 176 →
      (r.write = false ∧ r.right = true) ∨
      (q = 156 ∧ b = true ∧ r.write = true ∧ r.right = true))

def checkRow (old new : Table) (q : State) (b : Bool) : Bool :=
  checkOuter old new q b &&
    (checkStopped old new q b &&
      (check52 old q b && (check156 old q b && check176 old q b)))

/-- A linear finite scan; the proof term need not expand a dependent universal quantifier. -/
def check (old new : Table) : Bool :=
  (List.finRange 303).all fun q => checkRow old new q false && checkRow old new q true

theorem check52_sound {old : Table} {q : State} {b : Bool}
    (h : check52 old q b = true) :
    match old q b with
    | none => True
    | some r => r.next = 52 → r.write = true ∧ r.right = true := by
  cases hr : old q b with
  | none => trivial
  | some r => exact of_decide_eq_true (by simpa [check52, hr] using h)

theorem check156_sound {old : Table} {q : State} {b : Bool}
    (h : check156 old q b = true) :
    match old q b with
    | none => True
    | some r => r.next = 156 → r.write = true ∧ r.right = false := by
  cases hr : old q b with
  | none => trivial
  | some r => exact of_decide_eq_true (by simpa [check156, hr] using h)

theorem check176_sound {old : Table} {q : State} {b : Bool}
    (h : check176 old q b = true) :
    match old q b with
    | none => True
    | some r => r.next = 176 →
      (r.write = false ∧ r.right = true) ∨
      (q = 156 ∧ b = true ∧ r.write = true ∧ r.right = true) := by
  cases hr : old q b with
  | none => trivial
  | some r => exact of_decide_eq_true (by simpa [check176, hr] using h)

theorem row_checked {old new : Table} (hc : check old new = true)
    (q : State) (b : Bool) : checkRow old new q b = true := by
  have hq := List.all_eq_true.mp hc q (List.mem_finRange q)
  have hb : checkRow old new q false = true ∧ checkRow old new q true = true := by
    simpa only [Bool.and_eq_true] using hq
  cases b with
  | false => exact hb.1
  | true => exact hb.2

/-- The remaining literal row equations, independently small kernel computations. -/
structure LocalRows (old new : Table) : Prop where
  old52zero : old 52 false = some ⟨false, true, 154⟩
  old52one : old 52 true = some ⟨true, true, 150⟩
  old176zero : old 176 false = some ⟨false, true, 168⟩
  old176one : old 176 true = some ⟨true, true, 150⟩
  new52zero : new 52 false = some ⟨false, false, 176⟩
  new52one : new 52 true = some ⟨true, true, 150⟩
  new176zero : new 176 false = some ⟨false, true, 185⟩
  new176one : new 176 true = some ⟨true, true, 129⟩
  new185zero : new 185 false = some ⟨false, true, 168⟩
  new129zero : new 129 false = some ⟨false, true, 154⟩

/-- Soundness of the finite Boolean certificate for the universal machine theorem. -/
theorem certificate (old new : Table) (hc : check old new = true)
    (rows : LocalRows old new) : MarkerTransport.Certificate old new := by
  have allRows := row_checked hc
  constructor
  · intro q b
    have h := allRows q b
    simp only [checkRow, Bool.and_eq_true] at h
    exact of_decide_eq_true h.1
  · intro q b
    have h := allRows q b
    simp only [checkRow, Bool.and_eq_true] at h
    exact of_decide_eq_true h.2.1
  · intro q b
    have h := allRows q b
    simp only [checkRow, Bool.and_eq_true] at h
    exact check52_sound h.2.2.1
  · intro q b
    have h := allRows q b
    simp only [checkRow, Bool.and_eq_true] at h
    exact check156_sound h.2.2.2.1
  · intro q b
    have h := allRows q b
    simp only [checkRow, Bool.and_eq_true] at h
    exact check176_sound h.2.2.2.2
  · exact rows.old52zero
  · exact rows.old52one
  · exact rows.old176zero
  · exact rows.old176one
  · exact rows.new52zero
  · exact rows.new52one
  · exact rows.new176zero
  · exact rows.new176one
  · exact rows.new185zero
  · exact rows.new129zero

theorem all_tape_halts_iff (old new : Table) (hc : check old new = true)
    (rows : LocalRows old new) (h : Int) (t : Tape) :
    PositiveStuttering.Halts (step old) ⟨0, h, t⟩ ↔
      PositiveStuttering.Halts (step new) ⟨0, h, t⟩ :=
  MarkerTransport.all_tape_halts_iff (certificate old new hc rows) h t

#print axioms certificate
#print axioms all_tape_halts_iff

end FiniteMarkerCertificate

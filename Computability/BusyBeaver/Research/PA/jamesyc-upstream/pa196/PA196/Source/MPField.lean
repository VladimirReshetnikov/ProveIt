module
public import PA196.Source.Readers
public import PA196.Program
/-! Arithmetic proof adapted from M6.Source.MPField; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace PA196.Source.MPField
open M6.Source

def rename (r : Fin 9) : Fin 9 :=
  if r = 2 then 8 else if r = 8 then 2 else if r = 4 then 5 else if r = 5 then 4 else r

def relocation : UnpairRelocation :=
  ⟨rename,by decide,3693,3707⟩

/-- All14 literal MP field-reader rows, including the nonzero D accumulator. -/
private theorem row0 : resolveAt Program.sites 3693 = some (relocation.instruction unpairExpected[0]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row1 : resolveAt Program.sites 3694 = some (relocation.instruction unpairExpected[1]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row2 : resolveAt Program.sites 3695 = some (relocation.instruction unpairExpected[2]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row3 : resolveAt Program.sites 3696 = some (relocation.instruction unpairExpected[3]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row4 : resolveAt Program.sites 3697 = some (relocation.instruction unpairExpected[4]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row5 : resolveAt Program.sites 3698 = some (relocation.instruction unpairExpected[5]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row6 : resolveAt Program.sites 3699 = some (relocation.instruction unpairExpected[6]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row7 : resolveAt Program.sites 3700 = some (relocation.instruction unpairExpected[7]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row8 : resolveAt Program.sites 3701 = some (relocation.instruction unpairExpected[8]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row9 : resolveAt Program.sites 3702 = some (relocation.instruction unpairExpected[9]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row10 : resolveAt Program.sites 3703 = some (relocation.instruction unpairExpected[10]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row11 : resolveAt Program.sites 3704 = some (relocation.instruction unpairExpected[11]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row12 : resolveAt Program.sites 3705 = some (relocation.instruction unpairExpected[12]) := by
  rw [Program.resolve_tree]
  rfl
private theorem row13 : resolveAt Program.sites 3706 = some (relocation.instruction unpairExpected[13]) := by
  rw [Program.resolve_tree]
  rfl

#check row13
theorem bound : Readers.Bound Program.sites relocation := by
  intro ⟨j,hj⟩
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13


#check bound

def registers (l d : Nat) (f : Registers) : Registers := fun r =>
  if r = 8 then l else if r = 4 then d else if r = 6 ∨ r = 7 then 0 else f r

private theorem register_bridge (l d : Nat) (f : Registers) :
    relocation.regs (Unpair.registers ⟨l,d,0,0,relocation.regs f⟩) = registers l d f := by
  funext j
  simp only [UnpairRelocation.regs,Unpair.registers,registers,
    relocation.rename_eq_iff,relocation.involution]
  by_cases h6 : j = 6 <;> by_cases h7 : j = 7 <;>
    simp_all [relocation,rename]

/-- Actual source3693–3706 consumes the next right-nested field and adds its
head to the OLD D. N,T,W,A,H are arbitrary and preserved; X,Y end clean. -/
theorem read (l d : Nat) (f : Registers) :
    ∃ m, 0 < m ∧ m ≤ Unpair.loopCost l (0,0) +
      (3*(Cantor.decode l).2+1) + (3*(Cantor.decode l).1+1) ∧
      Steps Program.sites m ⟨.at 3693,registers l d f⟩
        ⟨.at 3707,registers (Cantor.decode l).2 (d+(Cantor.decode l).1) f⟩ := by
  have h := Readers.unpair_add relocation bound l d (relocation.regs f)
  simpa only [UnpairRelocation.embed,Unpair.configAt,Unpair.exitAt,
    UnpairRelocation.control,register_bridge,
    show relocation.base = 3693 from rfl, show relocation.exitPort = 3707 from rfl,
    Nat.sub_self,Nat.add_zero] using h

#print axioms bound
#print axioms read
end PA196.Source.MPField


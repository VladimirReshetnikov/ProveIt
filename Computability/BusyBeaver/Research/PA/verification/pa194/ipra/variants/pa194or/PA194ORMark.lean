import PA194ORPhysical
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace PA194ORMark
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed
open PA194ORData

def control (n : Nat) : Nat := [106,89,66,107,91,69,100,82,59].getD n 106

def returnControl (n : Nat) : Nat := if n = 0 then 15 else 17

private theorem markEntry : findRow table 106 0 = some ⟨106,0,0,true,14⟩ := by rfl
private theorem markWrite : findRow table 14 1 = some ⟨14,1,0,false,15⟩ := by rfl
private theorem markBack : findRow table 15 0 = some ⟨15,0,0,false,15⟩ := by rfl
private theorem skipRow (n : Nat) (hn : n < 8) :
    findRow table (control (n+1)) 0 = some ⟨control (n+1),0,0,true,control n⟩ := by
  interval_cases n <;> rfl
private theorem skipLoop (n : Nat) (hn : n < 8) :
    findRow table (control n) 1 = some ⟨control n,1,1,true,control n⟩ := by
  interval_cases n <;> rfl
private theorem backEntry (n : Nat) :
    findRow table (returnControl n) 1 = some ⟨returnControl n,1,1,false,16⟩ := by
  by_cases hn : n = 0 <;> simp only [returnControl,hn,if_true,if_false] <;> rfl
private theorem backLoop : findRow table 16 1 = some ⟨16,1,1,false,16⟩ := by rfl
private theorem backExit : findRow table 16 0 = some ⟨16,0,0,false,17⟩ := by rfl

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def block (n r : V) : V := push false (bitPrefix true (n+1) r)
noncomputable def marked (n r : V) : V := push false (push false (bitPrefix true n r))

noncomputable def file (registers : List V) (tail : V) : V :=
  registers.foldr block tail

theorem delimiter (n l r : V) :
    Reach1 table (scanFrame true 106 l (block n r)) (scanFrame false 15 (marked n r) l) := by
  have first := rightRow table 106 14 false false l (push true (bitPrefix true n r)) markEntry
  have second := leftRow table 14 15 true false (push false l) (bitPrefix true n r) markWrite
  have third := one (scanStep table false false false 15 15
      (push false (bitPrefix true n r)) l markBack)
  change Reach1 table (scanFrame false 15 (push false (bitPrefix true n r)) (push false l))
    (scanFrame false 15 (marked n r) l) at third
  have first' : Reach1 table (scanFrame true 106 l (block n r))
      (scanFrame true 14 (push false l) (push true (bitPrefix true n r))) := by
    simpa only [block,bitPrefix_succ,push] using first
  exact positiveTrans first' (trans (reachable second) (reachable third))

theorem skipBlock (i : Nat) (hi : i < 8) (n l r : V) :
    Reach1 table (scanFrame true (control (i+1)) l (block n r))
      (scanFrame true (control i) (bitPrefix true (n+1) (push false l)) r) := by
  have first := rightRow table (control (i+1)) (control i) false false l
      (bitPrefix true (n+1) r) (skipRow i hi)
  exact positiveTrans first ⟨n+1, scan table true true true (control i) (n+1)
    (push false l) r (skipLoop i hi)⟩

theorem returnBlock (i : Nat) (n l r : V) :
    Reach1 table
      (scanFrame false (returnControl i) r (bitPrefix true (n+1) (push false l)))
      (scanFrame false 17 (block n r) l) := by
  have first := one (scanStep table false true true (returnControl i) 16
    r (bitPrefix true n (push false l)) (backEntry i))
  change Reach1 table (scanFrame false (returnControl i) r (push true
    (bitPrefix true n (push false l))))
    (scanFrame false 16 (push true r) (bitPrefix true n (push false l))) at first
  have middle := scan table false true true 16 n (push true r) (push false l) backLoop
  have last := one (scanStep table false false false 16 17
    (bitPrefix true n (push true r)) l backExit)
  change Reach1 table (scanFrame false 16 (bitPrefix true n (push true r)) (push false l))
    (scanFrame false 17 (push false (bitPrefix true n (push true r))) l) at last
  have first' : Reach1 table
      (scanFrame false (returnControl i) r (bitPrefix true (n+1) (push false l)))
      (scanFrame false 16 (push true r) (bitPrefix true n (push false l))) := by
    simpa only [bitPrefix_succ,push] using first
  have onesCommute : bitPrefix true n (push true r) = bitPrefix true (n+1) r :=
    bitPrefix_push true n r
  have middleReach :
      Reach table (scanFrame false 16 (push true r) (bitPrefix true n (push false l)))
        (scanFrame false 16 (bitPrefix true n (push true r)) (push false l)) := ⟨n,middle⟩
  have last' : Reach1 table (scanFrame false 16 (bitPrefix true n (push true r)) (push false l))
      (scanFrame false 17 (block n r) l) := by
    simpa only [block,onesCommute] using last
  exact positiveTrans first' (trans middleReach (reachable last'))

/-- The exact variant rows mark any of the first nine register blocks,
    allowing each preceding block and the target block a model-valued length. -/
theorem mark (previous : List V) (bound : previous.length < 9) (n l r : V) :
    Reach1 table (scanFrame true (control previous.length) l (file previous (block n r)))
      (scanFrame false (returnControl previous.length) (file previous (marked n r)) l) := by
  induction previous generalizing l with
  | nil => exact delimiter n l r
  | cons a previous later =>
    have shorter : previous.length < 8 := by
      simp only [List.length_cons] at bound
      omega
    have first := skipBlock previous.length shorter a l (file previous (block n r))
    have mid := later (by omega) (bitPrefix true (a + 1) (push false l))
    have last := returnBlock previous.length a l (file previous (marked n r))
    exact positiveTrans first (trans (reachable mid) (reachable last))

#print axioms mark
end models
end PA194ORMark

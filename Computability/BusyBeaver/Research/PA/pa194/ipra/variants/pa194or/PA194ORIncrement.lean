import PA194ORDecrement

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace PA194ORIncrement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed
open PA194ORData
open PA194ORMark (block marked file)
open PA194ORDecrement (rightStep leftScanStep blockShape carried forwardBlock backPositive)

private theorem row0_0 : findRow table 0 0 = some ⟨0,0,1,true,1⟩ := rfl
private theorem row0_1 : findRow table 0 1 = some ⟨0,1,1,true,2⟩ := rfl
private theorem row1_1 : findRow table 1 1 = some ⟨1,1,1,true,1⟩ := rfl
private theorem row2_0 : findRow table 2 0 = some ⟨2,0,0,true,0⟩ := rfl
private theorem row2_1 : findRow table 2 1 = some ⟨2,1,1,true,2⟩ := rfl
private theorem row6_0 : findRow table 6 0 = some ⟨6,0,0,false,7⟩ := rfl
private theorem row6_1 : findRow table 6 1 = some ⟨6,1,1,false,6⟩ := rfl
private theorem row7_1 : findRow table 7 1 = some ⟨7,1,1,false,6⟩ := rfl

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def prefixWord (n l : V) : V := bitPrefix true (n+1) (push false l)

private theorem grow (n l : V) :
    bitPrefix true n (push true (push false l)) = prefixWord n l :=
  bitPrefix_push true n (push false l)

private theorem advance (n l r : V) :
    Reach table (scanFrame true 2 l (block n r)) (scanFrame true 2 (prefixWord n l) r) := by
  rw [blockShape]
  have h1 := rightStep 2 0 false false l (push true (bitPrefix true n r)) row2_0
  have h2 := rightStep 0 2 true true (push false l) (bitPrefix true n r) row0_1
  have h3 := scan table true true true 2 n (push true (push false l)) r row2_1
  rw [grow] at h3
  exact Compressed.trans h1 (Compressed.trans h2 ⟨n,h3⟩)

private theorem pick (n l r : V) :
    Reach table (scanFrame true 2 l (marked n r)) (scanFrame true 1 (prefixWord n l) r) := by
  rw [marked]
  have h1 := rightStep 2 0 false false l (push false (bitPrefix true n r)) row2_0
  have h2 := rightStep 0 1 false true (push false l) (bitPrefix true n r) row0_0
  have h3 := scan table true true true 1 n (push true (push false l)) r row1_1
  rw [grow] at h3
  exact Compressed.trans h1 (Compressed.trans h2 ⟨n,h3⟩)

private theorem restore (n l r : V) :
    Reach table (scanFrame false 7 r (prefixWord n l))
      (scanFrame false 7 (block n r) l) := by
  have h1 := leftScanStep 7 6 true true r (bitPrefix true n (push false l)) row7_1
  have h1' : Reach table (scanFrame false 7 r (prefixWord n l))
      (scanFrame false 6 (push true r) (bitPrefix true n (push false l))) := by
    simpa only [prefixWord,bitPrefix_succ,push] using h1
  have h2 := scan table false true true 6 n (push true r) (push false l) row6_1
  rw [show bitPrefix true n (push true r) = bitPrefix true (n+1) r from bitPrefix_push true n r] at h2
  have h3 := leftScanStep 6 7 false false (bitPrefix true (n+1) r) l row6_0
  exact Compressed.trans h1' (Compressed.trans ⟨n,h2⟩ h3)

private theorem follow (following : List V) (l oldTail newTail : V)
    (tailRoute : ∀ left, Reach table (scanFrame true 1 left oldTail)
      (scanFrame true 7 left (push true newTail))) :
    Reach table (scanFrame true 1 l (file following oldTail))
      (scanFrame true 7 l (push true (file following newTail))) := by
  induction following generalizing l with
  | nil => exact tailRoute l
  | cons a following ih =>
    have h1 := forwardBlock a l (file following oldTail)
    have h2 := ih (carried a l)
    have h3 := backPositive a l (file following newTail)
    exact Compressed.trans h1 (Compressed.trans h2 h3)

private theorem incrementSelected (n l : V) (following : List V) (oldTail newTail : V)
    (tailRoute : ∀ left, Reach table (scanFrame true 1 left oldTail)
      (scanFrame true 7 left (push true newTail))) :
    Reach table (scanFrame true 2 l (marked n (file following oldTail)))
      (scanFrame false 7 (block (n+1) (file following newTail)) l) := by
  have h1 := pick n l (file following oldTail)
  have h2 := follow following (prefixWord n l) oldTail newTail tailRoute
  have hshape : push true (prefixWord n l) = prefixWord (n+1) l := by
    simp only [prefixWord,bitPrefix_succ,push]
  have h3 := restore (n+1) l (file following newTail)
  rw [← hshape, turnRight] at h3
  exact Compressed.trans h1 (Compressed.trans h2 h3)

/-- Exact increment of a marked register, conditional only on the tail
    traversal that appends one spare. Earlier and later registers are arbitrary. -/
theorem increment (previous following : List V) (n l oldTail newTail : V)
    (tailRoute : ∀ left, Reach table (scanFrame true 1 left oldTail)
      (scanFrame true 7 left (push true newTail))) :
    Reach table (scanFrame true 2 l (file previous (marked n (file following oldTail))))
      (scanFrame false 7 (file previous (block (n+1) (file following newTail))) l) := by
  induction previous generalizing l with
  | nil => exact incrementSelected n l following oldTail newTail tailRoute
  | cons a previous ih =>
    have h1 := advance a l (file previous (marked n (file following oldTail)))
    have h2 := ih (prefixWord a l)
    have h3 := restore a l (file previous (block (n+1) (file following newTail)))
    exact Compressed.trans h1 (Compressed.trans h2 h3)

#print axioms increment
end models
end PA194ORIncrement

import ConPAMachineGenericDecrement

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace ConPA.Machine.GenericIncrement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine.Compressed
open GenericMark (block marked file)
open GenericDecrement (rightStep leftScanStep blockShape carried forwardBlock backPositive)

/-- Literal rows used to find and increment the marked block. The carry and
    return rows are shared with the decrement routine. -/
structure Rows (T : Table) (D : GenericDecrement.Rows T) where
  start : Nat
  afterSeparator : Nat
  enterBlock : findRow T start 0 = some ⟨start,0,0,true,afterSeparator⟩
  scanOnce : findRow T start 1 = some ⟨start,1,1,true,start⟩
  skipOrdinary : findRow T afterSeparator 1 = some ⟨afterSeparator,1,1,true,start⟩
  foundMark : findRow T afterSeparator 0 = some ⟨afterSeparator,0,1,true,D.scanRight⟩

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Table} {D : GenericDecrement.Rows T} (S : Rows T D)

noncomputable def prefixWord (n l : V) : V := bitPrefix true (n+1) (push false l)

private theorem grow (n l : V) :
    bitPrefix true n (push true (push false l)) = prefixWord n l :=
  bitPrefix_push true n (push false l)

private theorem advance (n l r : V) :
    Reach T (scanFrame true S.start l (block n r)) (scanFrame true S.start (prefixWord n l) r) := by
  rw [blockShape]
  have h1 := rightStep T S.start S.afterSeparator false false l (push true (bitPrefix true n r)) S.enterBlock
  have h2 := rightStep T S.afterSeparator S.start true true (push false l) (bitPrefix true n r) S.skipOrdinary
  have h3 := scan T true true true S.start n (push true (push false l)) r S.scanOnce
  rw [grow] at h3
  exact Compressed.trans h1 (Compressed.trans h2 ⟨n,h3⟩)

private theorem pick (n l r : V) :
    Reach T (scanFrame true S.start l (marked n r)) (scanFrame true D.scanRight (prefixWord n l) r) := by
  rw [marked]
  have h1 := rightStep T S.start S.afterSeparator false false l (push false (bitPrefix true n r)) S.enterBlock
  have h2 := rightStep T S.afterSeparator D.scanRight false true (push false l) (bitPrefix true n r) S.foundMark
  have h3 := scan T true true true D.scanRight n (push true (push false l)) r D.scanRightOne
  rw [grow] at h3
  exact Compressed.trans h1 (Compressed.trans h2 ⟨n,h3⟩)

private theorem restore (n l r : V) :
    Reach T (scanFrame false D.returnPositive r (prefixWord n l))
      (scanFrame false D.returnPositive (block n r) l) := by
  have h1 := leftScanStep T D.returnPositive D.scanBack true true r (bitPrefix true n (push false l)) D.enterPositiveBlock
  have h1' : Reach T (scanFrame false D.returnPositive r (prefixWord n l))
      (scanFrame false D.scanBack (push true r) (bitPrefix true n (push false l))) := by
    simpa only [prefixWord,bitPrefix_succ,push] using h1
  have h2 := scan T false true true D.scanBack n (push true r) (push false l) D.scanBackOne
  rw [show bitPrefix true n (push true r) = bitPrefix true (n+1) r from bitPrefix_push true n r] at h2
  have h3 := leftScanStep T D.scanBack D.returnPositive false false (bitPrefix true (n+1) r) l D.finishPositiveBlock
  exact Compressed.trans h1' (Compressed.trans ⟨n,h2⟩ h3)

private theorem follow (following : List V) (l oldTail newTail : V)
    (tailRoute : ∀ left, Reach T (scanFrame true D.scanRight left oldTail)
      (scanFrame true D.returnPositive left (push true newTail))) :
    Reach T (scanFrame true D.scanRight l (file following oldTail))
      (scanFrame true D.returnPositive l (push true (file following newTail))) := by
  induction following generalizing l with
  | nil => exact tailRoute l
  | cons a following ih =>
    have h1 := forwardBlock D a l (file following oldTail)
    have h2 := ih (carried a l)
    have h3 := backPositive D a l (file following newTail)
    exact Compressed.trans h1 (Compressed.trans h2 h3)

private theorem incrementSelected (n l : V) (following : List V) (oldTail newTail : V)
    (tailRoute : ∀ left, Reach T (scanFrame true D.scanRight left oldTail)
      (scanFrame true D.returnPositive left (push true newTail))) :
    Reach T (scanFrame true S.start l (marked n (file following oldTail)))
      (scanFrame false D.returnPositive (block (n+1) (file following newTail)) l) := by
  have h1 := pick S n l (file following oldTail)
  have h2 := follow (D := D) following (prefixWord n l) oldTail newTail tailRoute
  have hshape : push true (prefixWord n l) = prefixWord (n+1) l := by
    simp only [prefixWord,bitPrefix_succ,push]
  have h3 := restore (D := D) (n+1) l (file following newTail)
  rw [← hshape, turnRight] at h3
  exact Compressed.trans h1 (Compressed.trans h2 h3)

/-- Exact increment of a marked register, conditional only on the tail
    traversal that appends one spare. Earlier and later registers are arbitrary. -/
theorem increment (previous following : List V) (n l oldTail newTail : V)
    (tailRoute : ∀ left, Reach T (scanFrame true D.scanRight left oldTail)
      (scanFrame true D.returnPositive left (push true newTail))) :
    Reach T (scanFrame true S.start l (file previous (marked n (file following oldTail))))
      (scanFrame false D.returnPositive (file previous (block (n+1) (file following newTail))) l) := by
  induction previous generalizing l with
  | nil => exact incrementSelected S n l following oldTail newTail tailRoute
  | cons a previous ih =>
    have h1 := advance S a l (file previous (marked n (file following oldTail)))
    have h2 := ih (prefixWord a l)
    have h3 := restore (D := D) a l (file previous (block (n+1) (file following newTail)))
    exact Compressed.trans h1 (Compressed.trans h2 h3)

#print axioms increment
end models
end ConPA.Machine.GenericIncrement

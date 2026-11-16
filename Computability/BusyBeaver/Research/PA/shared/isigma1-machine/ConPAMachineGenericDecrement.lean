import ConPAMachineGenericMark

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace ConPA.Machine.GenericDecrement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine.Compressed
open GenericMark (block marked file)

/-- Literal rows for the two outcomes of decrementing a marked register. -/
structure Rows (T : Table) where
  scanRight : Nat
  testMarker : Nat
  testValue : Nat
  readFollowing : Nat
  scanBack : Nat
  returnPositive : Nat
  clearMarker : Nat
  returnZero : Nat
  enterBlock : findRow T scanRight 0 = some ⟨scanRight,0,1,true,testMarker⟩
  scanRightOne : findRow T scanRight 1 = some ⟨scanRight,1,1,true,scanRight⟩
  enterMarked : findRow T testMarker 0 = some ⟨testMarker,0,0,true,testValue⟩
  skipOrdinary : findRow T testMarker 1 = some ⟨testMarker,1,0,true,scanRight⟩
  readZero : findRow T testValue 0 = some ⟨testValue,0,1,true,readFollowing⟩
  readPositive : findRow T testValue 1 = some ⟨testValue,1,1,false,scanBack⟩
  turnAfterZero : findRow T readFollowing 1 = some ⟨readFollowing,1,1,false,clearMarker⟩
  finishPositiveBlock : findRow T scanBack 0 = some ⟨scanBack,0,0,false,returnPositive⟩
  scanBackOne : findRow T scanBack 1 = some ⟨scanBack,1,1,false,scanBack⟩
  enterPositiveBlock : findRow T returnPositive 1 = some ⟨returnPositive,1,1,false,scanBack⟩
  restoreSeparator : findRow T clearMarker 1 = some ⟨clearMarker,1,0,false,returnZero⟩
  restoreOne : findRow T returnZero 0 = some ⟨returnZero,0,1,false,clearMarker⟩
  scanZeroOne : findRow T returnZero 1 = some ⟨returnZero,1,1,false,returnZero⟩

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Table} (S : Rows T)

noncomputable def carried (n l : V) : V := bitPrefix true n (push false (push true l))

theorem blockShape (n r : V) : block n r = push false (push true (bitPrefix true n r)) := by
  simp only [block,bitPrefix_succ,push]

private theorem markedSucc (n r : V) : marked (n+1) r =
    push false (push false (push true (bitPrefix true n r))) := by
  simp only [marked,bitPrefix_succ,push]

private theorem prefixOne (n r : V) : bitPrefix true n (push true r) = bitPrefix true (n+1) r :=
  bitPrefix_push true n r

theorem rightStep (T : Table) (q q' : Nat) (b w : Bool) (l r : V)
    (h : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,true,q'⟩) :
    Reach T (scanFrame true q l (push b r)) (scanFrame true q' (push w l) r) :=
  reachable (rightRow T q q' b w l r h)

theorem leftStep (T : Table) (q q' : Nat) (b w : Bool) (l r : V)
    (h : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,false,q'⟩) :
    Reach T (scanFrame true q l (push b r)) (scanFrame false q' (push w r) l) :=
  reachable (leftRow T q q' b w l r h)

theorem leftScanStep (T : Table) (q q' : Nat) (b w : Bool) (r l : V)
    (h : findRow T q b.toNat = some ⟨q,b.toNat,w.toNat,false,q'⟩) :
    Reach T (scanFrame false q r (push b l)) (scanFrame false q' (push w r) l) :=
  reachable (one (scanStep T false b w q q' r l h))

theorem forwardBlock (n l r : V) :
    Reach T (scanFrame true S.scanRight l (block n r)) (scanFrame true S.scanRight (carried n l) r) := by
  rw [blockShape]
  let tail := bitPrefix true n r
  have h1 := rightStep T S.scanRight S.testMarker false true l (push true tail) S.enterBlock
  have h2 := rightStep T S.testMarker S.scanRight true false (push true l) tail S.skipOrdinary
  exact Compressed.trans h1 (Compressed.trans h2 ⟨n,scan T true true true S.scanRight n
    (push false (push true l)) r S.scanRightOne⟩)

private theorem positiveCell (n l r : V) :
    Reach T (scanFrame true S.scanRight l (marked (n+1) r))
      (scanFrame true S.returnPositive l (push true (block n r))) := by
  rw [markedSucc,← turnRight S.returnPositive true l (block n r),blockShape]
  let tail := bitPrefix true n r
  have h1 := rightStep T S.scanRight S.testMarker false true l (push false (push true tail)) S.enterBlock
  have h2 := rightStep T S.testMarker S.testValue false false (push true l) (push true tail) S.enterMarked
  have h3 := leftStep T S.testValue S.scanBack true true (push false (push true l)) tail S.readPositive
  have h4 := leftScanStep T S.scanBack S.returnPositive false false (push true tail) (push true l) S.finishPositiveBlock
  exact Compressed.trans h1 (Compressed.trans h2 (Compressed.trans h3 h4))

private theorem zeroCell (l tail : V) :
    Reach T (scanFrame true S.scanRight l (marked 0 (push false (push true tail))))
      (scanFrame false S.returnZero (block 0 (push false (push true tail))) l) := by
  simp only [marked,blockShape,bitPrefix_zero]
  have h1 := rightStep T S.scanRight S.testMarker false true l (push false (push false (push true tail))) S.enterBlock
  have h2 := rightStep T S.testMarker S.testValue false false (push true l) (push false (push true tail)) S.enterMarked
  have h3 := rightStep T S.testValue S.readFollowing false true (push false (push true l)) (push true tail) S.readZero
  have h4 := leftStep T S.readFollowing S.clearMarker true true (push true (push false (push true l))) tail S.turnAfterZero
  have h5 := leftScanStep T S.clearMarker S.returnZero true false (push true tail) (push false (push true l)) S.restoreSeparator
  have h6 := leftScanStep T S.returnZero S.clearMarker false true (push false (push true tail)) (push true l) S.restoreOne
  have h7 := leftScanStep T S.clearMarker S.returnZero true false (push true (push false (push true tail))) l S.restoreSeparator
  exact Compressed.trans h1 (Compressed.trans h2 (Compressed.trans h3 (Compressed.trans h4 (Compressed.trans h5 (Compressed.trans h6 h7)))))

theorem backPositive (n l r : V) :
    Reach T (scanFrame true S.returnPositive (carried n l) (push true r))
      (scanFrame true S.returnPositive l (push true (block n r))) := by
  have h1 := leftStep T S.returnPositive S.scanBack true true (carried n l) r S.enterPositiveBlock
  have h2 := scan T false true true S.scanBack n (push true r) (push false (push true l)) S.scanBackOne
  have hm : Reach T (scanFrame false S.scanBack (push true r) (carried n l))
      (scanFrame false S.scanBack (bitPrefix true n (push true r)) (push false (push true l))) := ⟨n,h2⟩
  rw [prefixOne] at hm
  have h3 := leftScanStep T S.scanBack S.returnPositive false false (bitPrefix true (n+1) r) (push true l) S.finishPositiveBlock
  rw [← turnRight S.returnPositive true l (block n r)]
  exact Compressed.trans h1 (Compressed.trans hm h3)

private theorem backZero (n l r : V) :
    Reach T (scanFrame false S.returnZero r (carried n l)) (scanFrame false S.returnZero (block n r) l) := by
  have h1 := scan T false true true S.returnZero n r (push false (push true l)) S.scanZeroOne
  have hm : Reach T (scanFrame false S.returnZero r (carried n l))
      (scanFrame false S.returnZero (bitPrefix true n r) (push false (push true l))) := ⟨n,h1⟩
  have h2 := leftScanStep T S.returnZero S.clearMarker false true (bitPrefix true n r) (push true l) S.restoreOne
  have h3 := leftScanStep T S.clearMarker S.returnZero true false (push true (bitPrefix true n r)) l S.restoreSeparator
  rw [blockShape]
  exact Compressed.trans hm (Compressed.trans h2 h3)

/-- Positive decrement restores the complete arbitrary prefix, replaces the
    marked size n+1 by n, and returns one extra delimiter. -/
theorem positive (previous : List V) (n l r : V) :
    Reach T (scanFrame true S.scanRight l (file previous (marked (n+1) r)))
      (scanFrame false S.returnPositive (file previous (block n r)) (push true l)) := by
  rw [turnRight]
  induction previous generalizing l with
  | nil => exact positiveCell S n l r
  | cons a previous ih =>
    have h1 := forwardBlock S a l (file previous (marked (n+1) r))
    have h2 := ih (carried a l)
    have h3 := backPositive S a l (file previous (block n r))
    exact Compressed.trans h1 (Compressed.trans h2 h3)

/-- Zero decrement unmarks the selected zero register. The immediately
    following ordinary block supplies its two delimiter bits. -/
theorem zero (previous : List V) (l next r : V) :
    Reach T (scanFrame true S.scanRight l (file previous (marked 0 (block next r))))
      (scanFrame false S.returnZero (file previous (block 0 (block next r))) l) := by
  induction previous generalizing l with
  | nil => simpa only [file,List.foldr_nil,blockShape next r] using zeroCell S l (bitPrefix true next r)
  | cons a previous ih =>
    have h1 := forwardBlock S a l (file previous (marked 0 (block next r)))
    have h2 := ih (carried a l)
    have h3 := backZero S a l (file previous (block 0 (block next r)))
    exact Compressed.trans h1 (Compressed.trans h2 h3)

#print axioms positive
#print axioms zero
end models
end ConPA.Machine.GenericDecrement

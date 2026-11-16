import PA194ORMark

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace PA194ORDecrement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed
open PA194ORData
open PA194ORMark (block marked file)

private theorem row1_0 : findRow table 1 0 = some ⟨1,0,1,true,3⟩ := rfl
private theorem row1_1 : findRow table 1 1 = some ⟨1,1,1,true,1⟩ := rfl
private theorem row3_0 : findRow table 3 0 = some ⟨3,0,0,true,4⟩ := rfl
private theorem row3_1 : findRow table 3 1 = some ⟨3,1,0,true,1⟩ := rfl
private theorem row4_0 : findRow table 4 0 = some ⟨4,0,1,true,5⟩ := rfl
private theorem row4_1 : findRow table 4 1 = some ⟨4,1,1,false,6⟩ := rfl
private theorem row5_1 : findRow table 5 1 = some ⟨5,1,1,false,8⟩ := rfl
private theorem row6_0 : findRow table 6 0 = some ⟨6,0,0,false,7⟩ := rfl
private theorem row6_1 : findRow table 6 1 = some ⟨6,1,1,false,6⟩ := rfl
private theorem row7_1 : findRow table 7 1 = some ⟨7,1,1,false,6⟩ := rfl
private theorem row8_1 : findRow table 8 1 = some ⟨8,1,0,false,11⟩ := rfl
private theorem row11_0 : findRow table 11 0 = some ⟨11,0,1,false,8⟩ := rfl
private theorem row11_1 : findRow table 11 1 = some ⟨11,1,1,false,11⟩ := rfl

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def carried (n l : V) : V := bitPrefix true n (push false (push true l))

theorem blockShape (n r : V) : block n r = push false (push true (bitPrefix true n r)) := by
  simp only [block,bitPrefix_succ,push]

private theorem markedSucc (n r : V) : marked (n+1) r =
    push false (push false (push true (bitPrefix true n r))) := by
  simp only [marked,bitPrefix_succ,push]

private theorem prefixOne (n r : V) : bitPrefix true n (push true r) = bitPrefix true (n+1) r :=
  bitPrefix_push true n r

theorem rightStep (q q' : Nat) (b w : Bool) (l r : V)
    (h : findRow table q b.toNat = some ⟨q,b.toNat,w.toNat,true,q'⟩) :
    Reach table (scanFrame true q l (push b r)) (scanFrame true q' (push w l) r) :=
  reachable (rightRow table q q' b w l r h)

theorem leftStep (q q' : Nat) (b w : Bool) (l r : V)
    (h : findRow table q b.toNat = some ⟨q,b.toNat,w.toNat,false,q'⟩) :
    Reach table (scanFrame true q l (push b r)) (scanFrame false q' (push w r) l) :=
  reachable (leftRow table q q' b w l r h)

theorem leftScanStep (q q' : Nat) (b w : Bool) (r l : V)
    (h : findRow table q b.toNat = some ⟨q,b.toNat,w.toNat,false,q'⟩) :
    Reach table (scanFrame false q r (push b l)) (scanFrame false q' (push w r) l) :=
  reachable (one (scanStep table false b w q q' r l h))

theorem forwardBlock (n l r : V) :
    Reach table (scanFrame true 1 l (block n r)) (scanFrame true 1 (carried n l) r) := by
  rw [blockShape]
  let tail := bitPrefix true n r
  have h1 := rightStep 1 3 false true l (push true tail) row1_0
  have h2 := rightStep 3 1 true false (push true l) tail row3_1
  exact Compressed.trans h1 (Compressed.trans h2 ⟨n,scan table true true true 1 n
    (push false (push true l)) r row1_1⟩)

private theorem positiveCell (n l r : V) :
    Reach table (scanFrame true 1 l (marked (n+1) r))
      (scanFrame true 7 l (push true (block n r))) := by
  rw [markedSucc,← turnRight 7 true l (block n r),blockShape]
  let tail := bitPrefix true n r
  have h1 := rightStep 1 3 false true l (push false (push true tail)) row1_0
  have h2 := rightStep 3 4 false false (push true l) (push true tail) row3_0
  have h3 := leftStep 4 6 true true (push false (push true l)) tail row4_1
  have h4 := leftScanStep 6 7 false false (push true tail) (push true l) row6_0
  exact Compressed.trans h1 (Compressed.trans h2 (Compressed.trans h3 h4))

private theorem zeroCell (l tail : V) :
    Reach table (scanFrame true 1 l (marked 0 (push false (push true tail))))
      (scanFrame false 11 (block 0 (push false (push true tail))) l) := by
  simp only [marked,blockShape,bitPrefix_zero]
  have h1 := rightStep 1 3 false true l (push false (push false (push true tail))) row1_0
  have h2 := rightStep 3 4 false false (push true l) (push false (push true tail)) row3_0
  have h3 := rightStep 4 5 false true (push false (push true l)) (push true tail) row4_0
  have h4 := leftStep 5 8 true true (push true (push false (push true l))) tail row5_1
  have h5 := leftScanStep 8 11 true false (push true tail) (push false (push true l)) row8_1
  have h6 := leftScanStep 11 8 false true (push false (push true tail)) (push true l) row11_0
  have h7 := leftScanStep 8 11 true false (push true (push false (push true tail))) l row8_1
  exact Compressed.trans h1 (Compressed.trans h2 (Compressed.trans h3 (Compressed.trans h4 (Compressed.trans h5 (Compressed.trans h6 h7)))))

theorem backPositive (n l r : V) :
    Reach table (scanFrame true 7 (carried n l) (push true r))
      (scanFrame true 7 l (push true (block n r))) := by
  have h1 := leftStep 7 6 true true (carried n l) r row7_1
  have h2 := scan table false true true 6 n (push true r) (push false (push true l)) row6_1
  have hm : Reach table (scanFrame false 6 (push true r) (carried n l))
      (scanFrame false 6 (bitPrefix true n (push true r)) (push false (push true l))) := ⟨n,h2⟩
  rw [prefixOne] at hm
  have h3 := leftScanStep 6 7 false false (bitPrefix true (n+1) r) (push true l) row6_0
  rw [← turnRight 7 true l (block n r)]
  exact Compressed.trans h1 (Compressed.trans hm h3)

private theorem backZero (n l r : V) :
    Reach table (scanFrame false 11 r (carried n l)) (scanFrame false 11 (block n r) l) := by
  have h1 := scan table false true true 11 n r (push false (push true l)) row11_1
  have hm : Reach table (scanFrame false 11 r (carried n l))
      (scanFrame false 11 (bitPrefix true n r) (push false (push true l))) := ⟨n,h1⟩
  have h2 := leftScanStep 11 8 false true (bitPrefix true n r) (push true l) row11_0
  have h3 := leftScanStep 8 11 true false (push true (bitPrefix true n r)) l row8_1
  rw [blockShape]
  exact Compressed.trans hm (Compressed.trans h2 h3)

/-- Positive decrement restores the complete arbitrary prefix, replaces the
    marked size n+1 by n, and returns one extra delimiter. -/
theorem positive (previous : List V) (n l r : V) :
    Reach table (scanFrame true 1 l (file previous (marked (n+1) r)))
      (scanFrame false 7 (file previous (block n r)) (push true l)) := by
  rw [turnRight]
  induction previous generalizing l with
  | nil => exact positiveCell n l r
  | cons a previous ih =>
    have h1 := forwardBlock a l (file previous (marked (n+1) r))
    have h2 := ih (carried a l)
    have h3 := backPositive a l (file previous (block n r))
    exact Compressed.trans h1 (Compressed.trans h2 h3)

/-- Zero decrement unmarks the selected zero register. The immediately
    following ordinary block supplies its two delimiter bits. -/
theorem zero (previous : List V) (l next r : V) :
    Reach table (scanFrame true 1 l (file previous (marked 0 (block next r))))
      (scanFrame false 11 (file previous (block 0 (block next r))) l) := by
  induction previous generalizing l with
  | nil => simpa only [file,List.foldr_nil,blockShape next r] using zeroCell l (bitPrefix true next r)
  | cons a previous ih =>
    have h1 := forwardBlock a l (file previous (marked 0 (block next r)))
    have h2 := ih (carried a l)
    have h3 := backZero a l (file previous (block 0 (block next r)))
    exact Compressed.trans h1 (Compressed.trans h2 h3)

#print axioms positive
#print axioms zero
end models
end PA194ORDecrement

import PA194ORRegisterFile
import PA194ORIncrement
import PA194OneSpareIdentities
import PA194OneSpareRoundTrip

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

namespace PA194ORSpareSweep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed
open PA194ORData
open PA194ORDecrement (rightStep leftStep leftScanStep)
open PA194UnaryRuns PA194OneSpareIterate PA194OneSpareReturn PA194OneSpareIdentities

section generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem progressDef (frame grow consume : V → V → V) (x y n : V)
    (frameDef : 𝚺₁-Function₂ frame) (growDef : 𝚺₁-Function₂ grow)
    (consumeDef : 𝚺₁-Function₂ consume) :
    𝚺₁-Predicate (fun i => n < i ∨ ∃ j, i+j = n ∧
      runFrom table (3*i) (frame x (consume n y)) = frame (grow i x) (consume j y)) := by
  letI := frameDef
  letI := growDef
  letI := consumeDef
  letI := runFrom_definable (V := V) table
  definability

/-- Transfer a model-valued number of identical three-step blocks, with
    independent encodings for the consumed and output blocks. -/
private theorem transfer (frame grow consume : V → V → V) (x y n : V)
    (frameDef : 𝚺₁-Function₂ frame) (growDef : 𝚺₁-Function₂ grow)
    (consumeDef : 𝚺₁-Function₂ consume)
    (growZero : ∀ z, grow 0 z = z) (consumeZero : ∀ z, consume 0 z = z)
    (nextBlock : ∀ i j : V, runFrom table 3 (frame (grow i x) (consume (j+1) y)) =
      frame (grow (i+1) x) (consume j y)) :
    Reach table (frame x (consume n y)) (frame (grow n x) y) := by
  let invariant := fun i : V => n < i ∨ ∃ j, i+j = n ∧
    runFrom table (3*i) (frame x (consume n y)) = frame (grow i x) (consume j y)
  have complete : ∀ i : V, invariant i := by
    intro i
    induction i using ISigma1.sigma1_succ_induction with
    | hP => exact progressDef frame grow consume x y n frameDef growDef consumeDef
    | zero =>
      exact Or.inr ⟨n,zero_add n,by rw [mul_zero,runFrom_zero,growZero]⟩
    | succ i ih =>
      by_cases larger : n < i+1
      · exact Or.inl larger
      have leN : i+1 ≤ n := le_of_not_gt larger
      have prior : ¬ n < i := not_lt_of_ge (le_trans le_self_add leN)
      obtain ⟨r, hr, computation⟩ := ih.resolve_left prior
      rcases zero_or_succ r with hz | ⟨j,hj⟩
      · rw [hz,add_zero] at hr
        rw [← hr] at leN
        exact False.elim (not_le_of_gt (lt_add_of_pos_right i Arithmetic.zero_lt_one) leN)
      · have sum : i+1+j = n := by
          rw [hj] at hr
          simpa only [add_assoc,add_comm (1 : V) j] using hr
        have clock : 3*(i+1) = 3*i+3 := by ring
        exact Or.inr ⟨j,sum,by
          rw [clock,runFrom_add,computation,hj,nextBlock]⟩
  obtain ⟨j, hj, result⟩ := (complete n).resolve_left (Arithmetic.lt_irrefl _)
  have zero : j = 0 := add_left_cancel (hj.trans (add_zero n).symm)
  rw [zero,consumeZero] at result
  exact ⟨3*n,result⟩

private theorem runThree {x y z w : V} (h1 : step table x = y)
    (h2 : step table y = z) (h3 : step table z = w) :
    runFrom table 3 x = w := by
  have clock : (3 : V) = 0+1+1+1 := by norm_num
  rw [clock,runFrom_succ,runFrom_succ,runFrom_succ,runFrom_zero,h1,h2,h3]

private theorem rightFrame_def (q : Nat) : 𝚺₁-Function₂ (scanFrame (V := V) true q) := by
  change 𝚺₁-Function₂ (fun far near : V => ⟪(q : V),far,near⟫)
  definability

private theorem leftFrame_def (q : Nat) : 𝚺₁-Function₂ (scanFrame (V := V) false q) := by
  change 𝚺₁-Function₂ (fun far near : V => ⟪(q : V),near/2,2*far+near%2⟫)
  definability

private theorem row1_0 : findRow table 1 0 = some ⟨1,0,1,true,3⟩ := rfl
private theorem row1_1 : findRow table 1 1 = some ⟨1,1,1,true,1⟩ := rfl
private theorem row3_0 : findRow table 3 0 = some ⟨3,0,0,true,4⟩ := rfl
private theorem row3_1 : findRow table 3 1 = some ⟨3,1,0,true,1⟩ := rfl
private theorem row4_0 : findRow table 4 0 = some ⟨4,0,1,true,5⟩ := rfl
private theorem row5_0 : findRow table 5 0 = some ⟨5,0,1,false,7⟩ := rfl
private theorem row6_0 : findRow table 6 0 = some ⟨6,0,0,false,7⟩ := rfl
private theorem row6_1 : findRow table 6 1 = some ⟨6,1,1,false,6⟩ := rfl
private theorem row7_1 : findRow table 7 1 = some ⟨7,1,1,false,6⟩ := rfl

private theorem toSpare (l r : V) :
    runFrom table 3 (scanFrame true 3 l (push true (push true (push false r)))) =
      scanFrame true 3 (push true (push true (push false l))) r :=
  runThree
    (scanStep table true true false 3 1 l (push true (push false r)) row3_1)
    (scanStep table true true true 1 1 (push false l) (push false r) row1_1)
    (scanStep table true false true 1 3 (push true (push false l)) r row1_0)

private theorem fromSpare (r l : V) :
    runFrom table 3 (scanFrame false 7 r (push true (push true (push false l)))) =
      scanFrame false 7 (push false (push true (push true r))) l :=
  runThree
    (scanStep table false true true 7 6 r (push true (push false l)) row7_1)
    (scanStep table false true true 6 6 (push true r) (push false l) row6_1)
    (scanStep table false false false 6 7 (push true (push true r)) l row6_0)

private theorem addLastSpare (l : V) :
    Reach table (scanFrame true 3 l 0) (scanFrame false 7 (push false (push true (push true 0))) l) := by
  have zeroBit : push false (0 : V) = 0 := by simp [push]
  have h1 := rightStep 3 4 false false l (0 : V) row3_0
  have h2 := rightStep 4 5 false true (push false l) (0 : V) row4_0
  have h3 := leftStep 5 7 false true (push true (push false l)) (0 : V) row5_0
  have h4 := leftScanStep 7 6 true true (push true (0 : V)) (push false l) row7_1
  have h5 := leftScanStep 6 7 false false (push true (push true (0 : V))) l row6_0
  rw [zeroBit] at h1 h2 h3
  exact Compressed.trans h1 (Compressed.trans h2 (Compressed.trans h3 (Compressed.trans h4 h5)))

end generic

section expanded
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194ORRegisterFile
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem pairCode_def (c : Code 2) : 𝚺₁-Function₂ (fun n x : M => F c ![n,x]) := by
  have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F c e) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) c)
  convert h using 1
  funext e
  apply congrArg (fun args : Fin 2 → M => F c args)
  funext i
  fin_cases i <;> rfl

private theorem carriedSpare (n x : M) : F repeatBlock ![n+1,x] =
    push true (push true (push false (F repeatBlock ![n,x]))) := by
  change F repeatBlock ![F addCode ![n,F oneCode Fin.elim0],x] = _
  have two : TableDispatch.modelNumeral M 2 = (0 : M)+1+1 := by
    rw [PA194HalfDiv.modelNumeralCast]
    norm_num
  rw [modelAddOne,modelRepeatSucc,modelOneBlock,modelOnes_eq,two,
    bitPrefix_succ,bitPrefix_succ,bitPrefix_zero]
  simp only [push,Bool.toNat_true,Bool.toNat_false,Nat.cast_one,Nat.cast_zero,add_zero,two_mul]

private theorem restoredSpare (n x : M) : F repeatOutput ![n+1,x] =
    push false (push true (push true (F repeatOutput ![n,x]))) := by
  change F repeatOutput ![F addCode ![n,F oneCode Fin.elim0],x] = _
  rw [modelAddOne,modelOutputSucc,modelOutputBlock,block_eq,PA194ORDecrement.blockShape]
  rw [show (1 : M) = (0 : M)+1 by simp,bitPrefix_succ,bitPrefix_zero]
  rfl

/-- The exact OR tail routine appends one spare to any model-valued
    number of trailing spares and restores the entire left context. -/
theorem roundTrip (count l : M) :
    Reach table (scanFrame true 1 l (F repeatOutput ![count,(0 : M)]))
      (scanFrame true 7 l (push true (F repeatOutput ![count+1,(0 : M)]))) := by
  let u : M → M → M := fun n x => F repeatBlock ![n,x]
  let out : M → M → M := fun n x => F repeatOutput ![n,x]
  have same : out count 0 = push false (u count 0) := by
    unfold out u
    rw [modelSuffixRelation]
    simp only [push,Bool.toNat_false,Nat.cast_zero,add_zero,two_mul]
  let six := push false (push true (push true (0 : M)))
  have shift : out count six = out (count+1) 0 := by
    have hz := restoredSpare (0 : M) (0 : M)
    rw [modelOutputZero,zero_add] at hz
    have hOne : F repeatOutput ![(1 : M),(0 : M)] = F outputBlock (fun _ => (0 : M)) := by
      have h := modelOutputSucc (0 : M) (0 : M)
      rw [modelOutputZero, ← modelAddOne] at h
      change F repeatOutput ![(0 : M)+1,(0 : M)] = _ at h
      simpa only [zero_add] using h
    have hs : six = F outputBlock (fun _ => (0 : M)) := hz.symm.trans hOne
    change F repeatOutput ![count,six] = F repeatOutput ![F addCode ![count,F oneCode Fin.elim0],(0 : M)]
    rw [hs,modelAddOne,modelOutputShift]
  have initial := rightStep 1 3 false true l (u count 0) row1_0
  have across : Reach table (scanFrame true 3 (push true l) (u count 0))
      (scanFrame true 3 (u count (push true l)) 0) := by
    apply transfer (scanFrame true 3) u u (push true l) 0 count
      (rightFrame_def 3) (pairCode_def repeatBlock) (pairCode_def repeatBlock)
      modelRepeatZero modelRepeatZero
    intro i j
    change runFrom table 3 (scanFrame true 3 (F repeatBlock ![i,push true l])
      (F repeatBlock ![j+1,(0 : M)])) = scanFrame true 3
        (F repeatBlock ![i+1,push true l]) (F repeatBlock ![j,(0 : M)])
    rw [carriedSpare j,carriedSpare i]
    exact toSpare _ _
  have atEnd := addLastSpare (u count (push true l))
  have back : Reach table (scanFrame false 7 six (u count (push true l)))
      (scanFrame false 7 (out count six) (push true l)) := by
    apply transfer (scanFrame false 7) out u six (push true l) count
      (leftFrame_def 7) (pairCode_def repeatOutput) (pairCode_def repeatBlock)
      modelOutputZero modelRepeatZero
    intro i j
    change runFrom table 3 (scanFrame false 7 (F repeatOutput ![i,six])
      (F repeatBlock ![j+1,push true l])) = scanFrame false 7
        (F repeatOutput ![i+1,six]) (F repeatBlock ![j,push true l])
    rw [carriedSpare j,restoredSpare i]
    exact fromSpare _ _
  rw [shift,turnRight] at back
  change Reach table (scanFrame true 1 l (out count 0))
    (scanFrame true 7 l (push true (out (count+1) 0)))
  rw [same]
  exact Compressed.trans initial (Compressed.trans across (Compressed.trans atEnd back))

#print axioms roundTrip
end expanded
end PA194ORSpareSweep

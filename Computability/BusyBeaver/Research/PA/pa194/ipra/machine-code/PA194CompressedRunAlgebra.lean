import PA194BidirectionalRunScan

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedRunAlgebra
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRAOpenInduction
open PA194BidirectionalRunScan PA194BidirectionalRow
open PA194GenericRightScan (k app2 valApp2)

def appendBody (b : Bool) : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq
    ![app2 (runCode b) (app2 addCode k (.fvar 0)) (.fvar 1),
      app2 (runCode b) k (app2 (runCode b) (.fvar 0) (.fvar 1))]

def blankBody : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq ![app2 (runCode false) k (.fvar 0),.fvar 0]

theorem appendBody_open (b : Bool) : (appendBody b).Open := by
  simp [appendBody,Semiformula.Open]

theorem blankBody_open : blankBody.Open := by simp [blankBody,Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem appendBody_eval (b : Bool) (x : M) (e : Nat → M) : (appendBody b).Eval ![x] e ↔
    F (runCode b) ![x + e 0,e 1] = F (runCode b) ![x,F (runCode b) ![e 0,e 1]] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (appendBody b) ↔ _
  simp only [appendBody,Semiformula.EvalAux,eqRel]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [k, valApp2, Semiterm.val_bvar, Semiterm.val_fvar]
  rfl

theorem blankBody_eval (x : M) (e : Nat → M) : blankBody.Eval ![x] e ↔
    F (runCode false) ![x,e 0] = e 0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] blankBody ↔ _
  simp only [blankBody,Semiformula.EvalAux,eqRel]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [k, valApp2, Semiterm.val_bvar, Semiterm.val_fvar]

/-- Concatenation of two runs of equal bits, with both lengths model-valued. -/
theorem runAppend (b : Bool) (x y z : M) :
    F (runCode b) ![x+y,z] = F (runCode b) ![x,F (runCode b) ![y,z]] := by
  let e : Nat → M := fun i => if i = 0 then y else z
  have h (u : M) := appendBody_eval b u e
  simp only [e,↓reduceIte, Nat.one_ne_zero] at h
  have main : (appendBody b).Eval ![x] e := by
    apply modelOpenInduction (M := M) (appendBody b) (appendBody_open b) e
    · exact (h 0).mpr (by rw [zero_add,runZero])
    · intro u hu
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      apply (h (u+1)).mpr
      have hsum : (u+1)+y = (u+y)+1 := by ac_rfl
      rw [hsum,runSucc,runSucc,(h u).mp hu]
  exact (h x).mp main

/-- Trailing blank cells encode zero regardless of the model-valued length. -/
theorem blankRun (x : M) : F (runCode false) ![x,(0 : M)] = 0 := by
  let e : Nat → M := fun _ => 0
  have h (u : M) := blankBody_eval u e
  have main : blankBody.Eval ![x] e := by
    apply modelOpenInduction (M := M) blankBody blankBody_open e
    · exact (h 0).mpr (runZero false 0)
    · intro u hu
      have hs : F Code.succ (fun _ => u) = u+1 := (modelAddOne u).symm
      rw [hs]
      apply (h (u+1)).mpr
      rw [runSucc,(h u).mp hu]
      simp [e, PA194BidirectionalRow.push]
  exact (h x).mp main

#print axioms runAppend
#print axioms blankRun
end models
end PA194CompressedRunAlgebra

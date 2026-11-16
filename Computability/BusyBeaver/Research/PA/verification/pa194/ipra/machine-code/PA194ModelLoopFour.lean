import PA194ModelLoopIteration
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelLoopFour
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAOpenInduction PA194ModelLoopIteration PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes TableDispatch

def four (step : Code 1) : Code 1 := unary step (unary step (unary step (unary step (.proj 0))))
def body (step : Code 1) : Semiformula language Nat 1 :=
  let ix : Semiterm language Nat 1 := .bvar 0
  let seed : Semiterm language Nat 1 := .fvar 0
  let plus := PA194ModelLoopIteration.app2 addCode
  let twice := plus ix ix
  .rel Language.ORing.Rel.eq ![
    PA194ModelLoopIteration.app2 (iterCode step) (plus twice twice) seed,
    PA194ModelLoopIteration.app2 (iterCode (four step)) ix seed]
theorem body_open (step : Code 1) : (body step).Open := by simp [body,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem modelFour (step : Code 1) (x : M) :
    F (four step) (fun _ => x) = F step (fun _ => F step (fun _ => F step (fun _ => F step (fun _ => x)))) := by
  simp only [four,modelUnary,modelProjection]
theorem body_eval (step : Code 1) (x : M) (e : Nat → M) :
    (body step).Eval ![x] e ↔ F (iterCode step) ![(x+x)+(x+x),e 0] = F (iterCode (four step)) ![x,e 0] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] (body step) ↔ _
  simp [body,Semiformula.EvalAux,eqRel,PA194ModelLoopIteration.valApp2,Semiterm.val_bvar,Semiterm.val_fvar,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl
theorem groupFour (step : Code 1) (i seed : M) :
    F (iterCode step) ![(i+i)+(i+i),seed] = F (iterCode (four step)) ![i,seed] := by
  classical
  let e : Nat → M := fun _ => seed
  have main : (body step).Eval ![i] e := by
    apply modelOpenInduction (M := M) (body step) (body_open step) e
    · apply (body_eval step (0 : M) e).mpr
      simp only [e,zero_add,modelIterZero]
    · intro u hu
      apply (body_eval step (F Code.succ (fun _ => u)) e).mpr
      have prev := (body_eval step u e).mp hu
      change F (iterCode step) ![(u+u)+(u+u),seed] = F (iterCode (four step)) ![u,seed] at prev
      change F (iterCode step) ![(F Code.succ (fun _ => u)+F Code.succ (fun _ => u))+(F Code.succ (fun _ => u)+F Code.succ (fun _ => u)),seed] = F (iterCode (four step)) ![F Code.succ (fun _ => u),seed]
      rw [show F Code.succ (fun _ => u) = u+1 from (modelAddOne u).symm]
      have ht : ((u+1)+(u+1))+((u+1)+(u+1)) = ((((u+u)+(u+u))+1)+1)+1+1 := by simp only [add_assoc,add_comm,add_left_comm]
      rw [ht]
      let q := (u+u)+(u+u)
      change F (iterCode step) ![(((q+1)+1)+1)+1,seed] = F (iterCode (four step)) ![u+1,seed]
      rw [show (((q+1)+1)+1)+1 = F Code.succ (fun _ => ((q+1)+1)+1) from modelAddOne _,modelIterSucc]
      rw [show ((q+1)+1)+1 = F Code.succ (fun _ => (q+1)+1) from modelAddOne _,modelIterSucc]
      rw [show (q+1)+1 = F Code.succ (fun _ => q+1) from modelAddOne _,modelIterSucc]
      rw [show q+1 = F Code.succ (fun _ => q) from modelAddOne _,modelIterSucc]
      rw [show u+1 = F Code.succ (fun _ => u) from modelAddOne _,modelIterSucc,modelFour,prev]
  have h := (body_eval step i e).mp main
  exact h
#print axioms modelFour
#print axioms groupFour
end models
end PA194ModelLoopFour

import PA194OneSpareReturn
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareIdentities
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero PRAOpenInduction
open PA194OneSpareIterate PA194OneSpareReturn PA194UnaryRuns PA194RegisterFile PA194StateOne PA194BinaryDouble TableDispatch

def ix : Semiterm language Nat 1 := .bvar 0
def zeroT : Semiterm language Nat 1 := .func (.zero 0) Fin.elim0
def app1 (f : Code 1) (a : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a]
def app2 (f : Code 2) (a b : Semiterm language Nat 1) : Semiterm language Nat 1 := .func f ![a,b]
def twice (a : Semiterm language Nat 1) : Semiterm language Nat 1 := app2 addCode a a
def suffixBody : Semiformula language Nat 1 := .rel Language.ORing.Rel.eq
  ![app2 repeatOutput ix zeroT,twice (app2 repeatBlock ix zeroT)]
def shiftBody : Semiformula language Nat 1 := .rel Language.ORing.Rel.eq
  ![app2 repeatOutput ix (app1 outputBlock zeroT),app2 repeatOutput (app1 Code.succ ix) zeroT]
theorem suffixBody_open : suffixBody.Open := by simp [suffixBody,Semiformula.Open,Semiformula.qr]
theorem shiftBody_open : shiftBody.Open := by simp [shiftBody,Semiformula.Open,Semiformula.qr]
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 (x : M) (e : Nat → M) (f : Code 1) (a : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app1 f a) = F f (fun _ => Semiterm.val ![x] e a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 (x : M) (e : Nat → M) (f : Code 2) (a b : Semiterm language Nat 1) :
    Semiterm.val ![x] e (app2 f a b) = F f ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_pair ![x] e a b

theorem suffixEval (x : M) (e : Nat → M) : suffixBody.Eval ![x] e ↔
    F repeatOutput ![x,(0 : M)] = F repeatBlock ![x,(0 : M)]+F repeatBlock ![x,(0 : M)] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] suffixBody ↔ _
  simp only [suffixBody,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := val_pair ![x] e a b
  have hv0 : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [ix,zeroT,twice,valApp2,Matrix.cons_val_zero,Matrix.cons_val_one,Semiterm.val_bvar,Semiterm.val_func,hv0]
  rfl

theorem shiftEval (x : M) (e : Nat → M) : shiftBody.Eval ![x] e ↔
    F repeatOutput ![x,F outputBlock (fun _ => (0 : M))] = F repeatOutput ![F Code.succ (fun _ => x),(0 : M)] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] shiftBody ↔ _
  simp only [shiftBody,Semiformula.EvalAux,eqRel]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![x] e (![a,b] i)) = ![Semiterm.val ![x] e a,Semiterm.val ![x] e b] := val_pair ![x] e a b
  have hv0 : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [ix,zeroT,valApp1,valApp2,Matrix.cons_val_zero,Matrix.cons_val_one,Semiterm.val_bvar,Semiterm.val_func,hv0]
  rfl

theorem modelSuffixRelation (n : M) :
    F repeatOutput ![n,(0 : M)] = F repeatBlock ![n,(0 : M)]+F repeatBlock ![n,(0 : M)] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Nat → M := fun _ => 0
  have h : suffixBody.Eval ![n] e := by
    apply modelOpenInduction (M := M) suffixBody suffixBody_open e
    · apply (suffixEval (0 : M) e).mpr
      rw [modelOutputZero,modelRepeatZero,zero_add]
    · intro u hu
      apply (suffixEval (F Code.succ (fun _ => u)) e).mpr
      have prev := (suffixEval u e).mp hu
      rw [modelOutputSucc,modelRepeatSucc,modelOutputBlock,prev,modelBlock,modelOneBlock]
      have h2 : modelNumeral M 2 = (1 : M)+1 := by rw [←modelNumeralOne,←PA194FiniteControls.modelNumeralAdd]
      rw [h2]
  exact (suffixEval n e).mp h

theorem modelOutputShift (n : M) :
    F repeatOutput ![n,F outputBlock (fun _ => (0 : M))] = F repeatOutput ![F Code.succ (fun _ => n),(0 : M)] := by
  classical
  let e : Nat → M := fun _ => 0
  have h : shiftBody.Eval ![n] e := by
    apply modelOpenInduction (M := M) shiftBody shiftBody_open e
    · apply (shiftEval (0 : M) e).mpr
      rw [modelOutputZero,modelOutputSucc,modelOutputZero]
    · intro u hu
      apply (shiftEval (F Code.succ (fun _ => u)) e).mpr
      have prev := (shiftEval u e).mp hu
      rw [modelOutputSucc,modelOutputSucc,prev]
  exact (shiftEval n e).mp h
#print axioms modelSuffixRelation
#print axioms modelOutputShift
end models
end PA194OneSpareIdentities

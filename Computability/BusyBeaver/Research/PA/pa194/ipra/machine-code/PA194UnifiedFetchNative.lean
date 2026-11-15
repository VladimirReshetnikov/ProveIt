import PA194PositiveFetchNative
import PA194FreshFetchNative
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194UnifiedFetchNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory PRAExhaustion
open TableDispatch PA194SourceControllerCode PA194SchedulerFetchPositive PA194DecoderNative PA194SourceFetchOpen PA194SchedulerCode PA194SchedulerIteration PA194SchedulerPackedFetchPositive
abbrev T := TermN 12
def raw : Fin 11 → T := fun i => .bvar ⟨i.val,by have h:=i.isLt; omega⟩
def args : Fin 11 → T := Function.update raw 6 zero
def n : T := args 0
def l : T := args 8
def chooseCode : Code 3 := choose0 (.proj 0) (.proj 1) (.proj 2)
def choose (t a b : T) : T := .func chooseCode ![t,a,b]
def four : T := app2 addCode (app2 addCode n n) (app2 addCode n n)
def three : T := app2 addCode (app2 addCode n n) n
def freshClock : T := app2 addCode one (app2 addCode (app2 addCode four one) (app2 addCode (app2 addCode three one) one))
def clock : T := choose l freshClock (app2 addCode one one)
def out0 : T := choose l (app2 addCode n one) n
def out8 : T := choose l n (app1 predCode l)
def out : Fin 11 → T := Function.update (Function.update args 0 out0) 8 out8
def lhs : T := app2 PA194SourceControllerCode.run clock (frame 25 args (.bvar 11))
def rhs : T := frame 34 out (.bvar 11)
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem valChoose (e : Fin 12 → M) (t a b : T) :
    Semiterm.val e Empty.elim (choose t a b) =
      if Semiterm.val e Empty.elim t = (0 : M) then Semiterm.val e Empty.elim a else Semiterm.val e Empty.elim b := by
  simp only [choose,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ (![t,a,b] : Fin 3 → T)) =
      ![Semiterm.val e Empty.elim t,Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
    funext i; fin_cases i <;> rfl
  rw [hv,chooseCode,choose0_model]
  simp only [modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rfl

theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  apply (eqClosureModels _ _).mpr
  intro e
  let initial : Fin 11 → M := fun i => Semiterm.val e Empty.elim (args i)
  have h6 : initial 6 = (0 : M) := by simp [initial,args,PA194DecoderNative.valZero]
  have h8 : initial 8 = e 8 := by simp [initial,args,raw,Semiterm.val_bvar]
  by_cases hz : initial 8 = (0 : M)
  · have h := PA194SourceFetchOpen.freshSourceFetch initial (e 11) hz h6
    have he : e 8 = (0 : M) := h8.symm.trans hz
    simp [lhs,rhs,clock,freshClock,four,three,n,l,out0,out8,out,args,raw,valChoose,he,
      PA194DecoderNative.frame,PA194DecoderNative.file,PA194DecoderNative.valApp1,PA194DecoderNative.valApp2,
      PA194DecoderNative.valState,PA194DecoderNative.valZero,PA194DecoderNative.valOne,Semiterm.val_bvar,modelPairCode,
      sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,PA194SourceDrainOpen.four,
      PA194SourceRestoreOpen.three,initial,Function.update] at h ⊢
    convert h using 1 <;> rfl
  · let m := F predCode (fun _ => initial 8)
    have hs : F Code.succ (fun _ => m) = initial 8 := (modelZeroOrSuccPred (initial 8)).resolve_left hz
    have hm : initial 8 = m+1 := hs.symm.trans (modelAddOne m).symm
    have h := (positiveFetchPrefix initial (e 11) m hm).1
    have hrun : F PA194SourceControllerCode.run ![(1 : M)+1,sourceState 25 initial (e 11)] =
        F PA194SourceControllerCode.step ![F PA194SourceControllerCode.step ![sourceState 25 initial (e 11)]] := by
      change F (PA194IteratedSimulation.iterate PA194SourceControllerCode.step) ![(1 : M)+1,sourceState 25 initial (e 11)] = _
      have hz' : (1 : M)+1 = ((0 : M)+1)+1 := by rw [zero_add]
      rw [hz',PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterSucc,PA194DiagonalIteration.iterZero]
    rw [←hrun] at h
    have he : e 8 ≠ (0 : M) := by intro h; apply hz; exact h8.trans h
    have hv : (fun _ : Fin 1 => e 8) = ![e 8] := by funext i; fin_cases i; rfl
    simp [lhs,rhs,clock,freshClock,four,three,n,l,out0,out8,out,args,raw,valChoose,he,
      PA194DecoderNative.frame,PA194DecoderNative.file,PA194DecoderNative.valApp1,PA194DecoderNative.valApp2,
      PA194DecoderNative.valState,PA194DecoderNative.valZero,PA194DecoderNative.valOne,Semiterm.val_bvar,modelPairCode,
      sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,initial,Function.update,m,h8,hv] at h ⊢
    convert h using 1 <;> rfl
end models

theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence

theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194UnifiedFetchNative

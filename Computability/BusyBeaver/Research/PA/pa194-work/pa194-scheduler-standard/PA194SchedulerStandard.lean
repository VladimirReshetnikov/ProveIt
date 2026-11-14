import PA194SchedulerCode
import PA194MachineAXStandard
import PA194MachineShiftMPStandard
import PA194CommandRun
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SchedulerStandard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubReconstruct
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode PA194MachineShiftMPStandard PA194MachineAXStandard PA194SchedulerCode
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language) (M := Nat)

theorem first_code {n : Nat} (a : Code n) (e : Fin n → Nat) :
    F (unary fixedFirst a) e = (M6.Source.Cantor.decode (F a e)).1 := by
  rw [modelUnary]
  have hv : (fun _ : Fin 1 => F a e) = ![F a e] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv,first_standard]

theorem second_code {n : Nat} (a : Code n) (e : Fin n → Nat) :
    F (unary fixedSecond a) e = (M6.Source.Cantor.decode (F a e)).2 := by
  rw [modelUnary]
  have hv : (fun _ : Fin 1 => F a e) = ![F a e] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv,second_standard]

theorem zero_standard : F (Code.zero 0) Fin.elim0 = (0 : Nat) := by rfl

theorem one_standard : F oneCode Fin.elim0 = (1 : Nat) := by
  change eval oneCode (List.Vector.ofFn Fin.elim0) = 1
  decide

theorem pred_standard (x : Nat) : F predCode (fun _ => x) = x-1 := by
  cases x with
  | zero =>
    have h := modelPredZero (M := Nat)
    rw [zero_standard] at h
    simpa using h
  | succ x =>
    have h := modelPredAddOne (M := Nat) x
    have hadd (a b : Nat) := PA194TargetHead1Standard.localAdd_eq (M := Nat) a b
    have hadd' := fun a b => (hadd a b).trans (add_standard a b)
    have hone := PA194TargetHead1Standard.localOne_eq (M := Nat)
    change _ = eval (numeralCode 0 1) (List.Vector.ofFn Fin.elim0) at hone
    have he : eval (numeralCode 0 1) (List.Vector.ofFn Fin.elim0) = 1 := by decide
    rw [he] at hone
    rw [hadd',hone] at h
    simpa using h

theorem pred_code {n : Nat} (a : Code n) (e : Fin n → Nat) :
    F (unary predCode a) e = F a e-1 := by rw [modelUnary,pred_standard]

theorem succ_code {n : Nat} (a : Code n) (e : Fin n → Nat) :
    F (unary .succ a) e = F a e+1 := by
  rw [modelUnary,modelSucc,PA194TargetHead1Standard.localAdd_eq,add_standard]
  rfl

theorem fetchSeed_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (fetchSeed ncode l) e = PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e) := by
  rw [fetchSeed,choose0_model,pred_code]
  simp only [PA194FetchSource.FetchDispatch.seed]
  cases hl : F l e with
  | zero => simp [hl]
  | succ k => simp [hl]

theorem nextN_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (nextN ncode l) e = PA194FetchSource.FetchDispatch.nextN (F ncode e) (F l e) := by
  rw [nextN,choose0_model,succ_code]
  simp only [PA194FetchSource.FetchDispatch.nextN]
  cases hl : F l e with
  | zero => simp [hl]
  | succ k => simp [hl]

theorem head_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (head ncode l) e = (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).1 := by
  rw [head,first_code,fetchSeed_standard]

theorem tail_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (tail ncode l) e = (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).2 := by
  rw [PA194SchedulerCode.tail,second_code,fetchSeed_standard]

theorem yArg_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (yArg ncode l) e = (M6.Source.Cantor.decode (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).2).1 := by
  rw [yArg,first_code,tail_standard]

theorem tail2_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (tail2 ncode l) e = (M6.Source.Cantor.decode (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).2).2 := by
  rw [tail2,second_code,tail_standard]

theorem xArg_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (xArg ncode l) e = (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).2).2).1 := by
  rw [xArg,first_code,tail2_standard]

theorem tail3_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (tail3 ncode l) e = (M6.Source.Cantor.decode (M6.Source.Cantor.decode (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).2).2).2 := by
  rw [tail3,second_code,tail2_standard]

theorem axArg_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (axArg ncode l) e = (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).1 - 2 := by
  rw [axArg,pred_code,pred_code,head_standard]
  omega

theorem choose0_standard {n : Nat} (tag yes no : Code n) (e : Fin n → Nat) :
    F (choose0 tag yes no) e = if F tag e = 0 then F yes e else F no e := by
  rw [choose0_model]
  cases ht : F tag e with
  | zero => simp [ht]
  | succ k => simp [ht]

theorem choose1_standard {n : Nat} (tag yes no : Code n) (e : Fin n → Nat) :
    F (choose1 tag yes no) e = if F tag e = 1 then F yes e else F no e := by
  rw [choose1_model]
  cases ht : F tag e with
  | zero => simp [ht]
  | succ k => cases k <;> simp [ht]

theorem nextL_standard {n : Nat} (ncode l : Code n) (e : Fin n → Nat) :
    F (nextL ncode l) e = (PA194FetchCommand.parse (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).next := by
  rw [nextL,choose0_standard,choose1_standard,head_standard,tail_standard,tail2_standard,tail3_standard]
  cases ht : (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F ncode e) (F l e))).1 with
  | zero => simp [PA194FetchCommand.parse,ht]
  | succ k => cases k with
    | zero => simp [PA194FetchCommand.parse,ht]
    | succ k => simp [PA194FetchCommand.parse,ht]

theorem advance_standard {m : Nat} (n l t w d h : Code m) (e : Fin m → Nat) :
    PA194CommandRun.advance ⟨F n e,F l e,⟨F t e,F w e,F d e,F h e⟩⟩ =
      if F (halt n l t h) e = 1 then none else
        some ⟨F (nextN n l) e,F (nextL n l) e,
          ⟨F (nextTop n l t w d h) e,F (nextStack n l t w d h) e,
            F (nextD n l d) e,F (nextCache n l w) e⟩⟩ := by
  rw [nextN_standard,nextL_standard]
  have hh := head_standard n l e
  cases ht : F (head n l) e with
  | zero =>
    have hsource : (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F n e) (F l e))).1 = 0 := hh.symm.trans ht
    simp only [PA194CommandRun.advance,PA194FetchCommand.parse,hsource]
    rw [shift_code_command]
    simp only [halt,nextTop,nextStack,nextD,nextCache,choose0_standard,ht,if_pos]
    by_cases hs : F (shiftHalt t h) e = 1 <;> simp [hs]
  | succ k => cases k with
    | zero =>
      have hsource : (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F n e) (F l e))).1 = 1 := hh.symm.trans ht
      simp only [PA194CommandRun.advance,PA194FetchCommand.parse,hsource]
      rw [← yArg_standard n l e,mp_code_command]
      simp only [halt,nextTop,nextStack,nextD,nextCache,choose0_standard,choose1_standard,ht,PRAMultiplication.modelZero,zero_standard]
      norm_num
    | succ c =>
      have hsource : (M6.Source.Cantor.decode (PA194FetchSource.FetchDispatch.seed (F n e) (F l e))).1 = c+2 := by simpa using hh.symm.trans ht
      have hc : F (axArg n l) e = c := by rw [axArg_standard,hsource]; omega
      simp only [PA194CommandRun.advance,PA194FetchCommand.parse,hsource]
      rw [← yArg_standard n l e,← xArg_standard n l e,← hc,ax_code_command]
      simp only [halt,nextTop,nextStack,nextD,nextCache,choose0_standard,choose1_standard,ht,PRAMultiplication.modelZero,zero_standard]
      norm_num

#print axioms advance_standard
#print axioms nextL_standard
#print axioms axArg_standard
#print axioms first_code
#print axioms second_code
#print axioms pred_standard
#print axioms fetchSeed_standard
#print axioms nextN_standard
end PA194SchedulerStandard

import BusyBeaver.ZFC.ArithmeticControlDispatch254

set_option autoImplicit false
noncomputable section

/-!
The actual AX parameter read at controls122..135, exiting at136. The
existing internal ReadShape theorem supplies unbounded execution; all
literal edges and resolved successors are bound at this occurrence.
The old cache is retained and augmented by the next PL component. This
read follows the GEN constructor but its contract needs no GEN premise.
No complete AX branch, Enum bridge or internal binary endpoint is claimed.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlRun254 ArithmeticControlFrame254
open ArithmeticControlStep254 ArithmeticControlReadTemplate254
open ArithmeticControlFetch254 (put s1Reg plReg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlDispatch254 (cacheReg)
open FiniteControlTable254 RegisterPath

def entry : Control := ⟨122, by decide⟩
def exit : Control := ⟨136, by decide⟩

theorem entry_source : source entry =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,false,false,false,false], .decnz 8) := by rfl

theorem exit_source : source exit =
    ([true,true,true,false,true,false,false,true,false,false,true,false,true,false,false,false,true,false,false,false,false,false,false], .decnz 1) := by rfl

private def cacheReadShape : ReadShape where
  readEntry := entry
  bodyIncS2 := ⟨123,by decide⟩
  bodyTestS1 := ⟨124,by decide⟩
  bodyBreak := ⟨125,by decide⟩
  bodyMoveTest := ⟨126,by decide⟩
  bodyMoveInc := ⟨127,by decide⟩
  bodyMoveContinue := ⟨128,by decide⟩
  bodyContinue := ⟨129,by decide⟩
  restorePLTest := ⟨130,by decide⟩
  restorePLInc := ⟨131,by decide⟩
  restorePLContinue := ⟨132,by decide⟩
  outputTest := ⟨133,by decide⟩
  outputInc := ⟨134,by decide⟩
  outputContinue := ⟨135,by decide⟩
  nextRead := exit
  targetLogical := 5
  targetIndex := cacheReg
  target_physical := rfl
  target_ne_s1 := by decide
  target_ne_s2 := by decide
  target_ne_pl := by decide
  read_edge := by rfl
  body_inc_edge := by rfl
  body_test_edge := by rfl
  body_break_edge := by rfl
  body_move_test_edge := by rfl
  body_move_inc_edge := by rfl
  body_move_continue_edge := by rfl
  body_continue_edge := by rfl
  restore_test_edge := by rfl
  restore_inc_edge := by rfl
  restore_continue_edge := by rfl
  output_test_edge := by rfl
  output_inc_edge := by rfl
  output_continue_edge := by rfl
  next_read_positive := by rfl
  next_read_zero := by rfl
  next_body_inc := by rfl
  next_body_test_positive := by rfl
  next_body_test_zero := by rfl
  next_body_break := by rfl
  next_body_move_positive := by rfl
  next_body_move_inc := by rfl
  next_body_move_continue := by rfl
  next_body_move_zero := by rfl
  next_body_continue := by rfl
  next_restore_pl_positive := by rfl
  next_restore_pl_inc := by rfl
  next_restore_pl_continue := by rfl
  next_restore_pl_zero := by rfl
  next_output_positive := by rfl
  next_output_inc := by rfl
  next_output_continue := by rfl
  next_output_zero := by rfl

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Consume PL's first Cantor component into the existing cache. -/
def cacheReadFile (file : V) : V :=
  put cacheReg (regValue file cacheReg + first (regValue file plReg))
    (put plReg (second (regValue file plReg)) file)

private theorem read_put_self (file x : V) (p : Fin 9) :
    regValue (put p x file) p = x := write_at file x p

private theorem read_put_other (file x : V) (p q : Fin 9) (h : p ≠ q) :
    regValue (put p x file) q = regValue file q := write_other file x p q h

theorem cacheReadFile_cache (file : V) :
    regValue (cacheReadFile file) cacheReg =
      regValue file cacheReg + first (regValue file plReg) := by
  rw [cacheReadFile, read_put_self]

theorem cacheReadFile_pl (file : V) :
    regValue (cacheReadFile file) plReg = second (regValue file plReg) := by
  rw [cacheReadFile, read_put_other _ _ cacheReg plReg (by decide), read_put_self]

theorem cacheReadFile_other (file : V) (i : Fin 9)
    (hc : i ≠ cacheReg) (hp : i ≠ plReg) :
    regValue (cacheReadFile file) i = regValue file i := by
  rw [cacheReadFile, read_put_other _ _ cacheReg i hc.symm,
    read_put_other _ _ plReg i hp.symm]

/-- All values and the positive runtime belong to the ambient IΣ₁ model. -/
theorem read_cache_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V) (cacheReadFile file) := by
  exact read_shape cacheReadShape file h1 h2

/-- A parameter-stream client, allowing arbitrary old cache and remaining tail. -/
theorem read_cache_pair_run (file x rest : V)
    (hp : regValue file plReg = cantor x rest)
    (h1 : regValue file s1Reg = 0) (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧
      controlRun time (liveValue (number entry : V) file) =
        liveValue (number exit : V)
          (put cacheReg (regValue file cacheReg + x) (put plReg rest file)) := by
  simpa only [cacheReadFile, hp, first_cantor, second_cantor] using
    read_cache_run file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXReadCache254

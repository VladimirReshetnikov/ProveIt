import PA194MachineShiftMPCode
import PA194CommandTransfer
import PA194TargetLeavesStandard
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194MachineShiftMPStandard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PA194PathIterator PA194NumeralCode PA194TargetCantor PA194TargetLeavesStandard
 PA194MachineProjections PA194MachineAXCode PA194MachineShiftMPCode
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

 theorem fn_cantor (a b : Nat) : Structure.func (L := language) fixedCantor ![a,b] = M6.Source.Cantor.pair a b := by
  change eval fixedCantor (List.Vector.ofFn ![a,b]) = _
  rw [ofFn_two]
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using eval_fixedCantor a b

theorem first_standard (p : Nat) :
    Structure.func (L := language) fixedFirst ![p] = (M6.Source.Cantor.decode p).1 := by
  have h := first_machinePair (M := Nat) (M6.Source.Cantor.decode p).1 (M6.Source.Cantor.decode p).2
  rw [fn_cantor,M6.Source.Cantor.pair_decode] at h
  exact h

theorem second_standard (p : Nat) :
    Structure.func (L := language) fixedSecond ![p] = (M6.Source.Cantor.decode p).2 := by
  have h := second_machinePair (M := Nat) (M6.Source.Cantor.decode p).1 (M6.Source.Cantor.decode p).2
  rw [fn_cantor,M6.Source.Cantor.pair_decode] at h
  exact h

theorem add_standard (a b : Nat) : Structure.func (L := language) addCode ![a,b] = a+b := by
  change eval addCode (List.Vector.ofFn ![a,b]) = _
  rw [ofFn_two]
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using eval_addCode a b

theorem shift_code_command {n : Nat} (t w h d : Code n) (e : Fin n → Nat) :
    PA194CommandTransfer.step .shift
      ⟨Structure.func (L := language) t e, Structure.func (L := language) w e,
        Structure.func (L := language) d e,Structure.func (L := language) h e⟩ =
      if Structure.func (L := language) (shiftHalt t h) e = 1 then none else
        some ⟨Structure.func (L := language) h e,Structure.func (L := language) (shiftStack w) e,
          Structure.func (L := language) d e,Structure.func (L := language) (shiftCache w) e⟩ := by
  have hs := shiftHalt_correct (M := Nat) t h e
  have hadd := PA194TargetHead1Standard.localAdd_eq (M := Nat)
    (Structure.func (L := language) t e) (Structure.func (L := language) h e)
  rw [add_standard] at hadd
  rw [hadd] at hs
  have hv : (fun _ : Fin 1 => Structure.func (L := language) w e) = ![Structure.func (L := language) w e] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simp only [PA194CommandTransfer.step,shiftStack,shiftCache,modelUnary,hv,first_standard,second_standard]
  by_cases ht : Structure.func (L := language) t e + Structure.func (L := language) h e = 1
  · have hh := hs.mpr ht
    simp [ht,hh]
  · have hh : Structure.func (L := language) (shiftHalt t h) e ≠ 1 := fun h => ht (hs.mp h)
    simp [ht,hh]

theorem mp_code_command {n : Nat} (t w h d x : Code n) (e : Fin n → Nat) :
    PA194CommandTransfer.step (.mp (Structure.func (L := language) x e))
      ⟨Structure.func (L := language) t e,Structure.func (L := language) w e,
        Structure.func (L := language) d e,Structure.func (L := language) h e⟩ =
    some ⟨Structure.func (L := language) (mpTop t h d x) e,
      Structure.func (L := language) (mpStack t w h d x) e,
      Structure.func (L := language) (mpArg d x) e,0⟩ := by
  have hp (a b : Nat) := modelCantorSelected (M := Nat) fixedCantor fixedCantor_certified a b
  have hpair := fun a b => (hp a b).symm.trans (fn_cantor a b)
  have hadd (a b : Nat) := PA194TargetHead1Standard.localAdd_eq (M := Nat) a b
  have hadd' := fun a b => (hadd a b).trans (add_standard a b)
  simp only [PA194CommandTransfer.step,mpTop_model,mpStack_model,mpArg,add_model,
    hadd', (primitive_standard _ _).1,hpair]
  split <;> rfl
#print axioms first_standard
#print axioms second_standard
#print axioms shift_code_command
#print axioms mp_code_command
end PA194MachineShiftMPStandard

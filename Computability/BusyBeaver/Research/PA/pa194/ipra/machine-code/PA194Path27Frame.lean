import PA194Path27Header
import PA194RegisterFileStandard
import PA194PrimitiveSimulation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path27Frame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194Path27Header PA194RegisterFileStandard PA194ZeroRuns
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem bitsAppend (xs ys : List Bool) :
    PA194Bounded.bits (xs++ys) = word xs (PA194Bounded.bits ys) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.cons_append,PA194Bounded.bits,word,ih]
    omega

theorem zerosNatWord (n t : Nat) :
    F zeros ![n,t] = word (List.replicate n false) t := by
  induction n with
  | zero =>
    have h := modelZerosZero (M := Nat) t
    exact h
  | succ n ih =>
    have h := modelZerosSucc (M := Nat) n t
    change F zeros ![F Code.succ (fun _ => n),t] =
      F addCode ![F zeros ![n,t],F zeros ![n,t]] at h
    rw [natSucc,natAdd] at h
    rw [h,ih]
    simp only [List.replicate_succ,word,Bool.toNat_false,add_zero]
    omega

theorem modelWordNat (xs : List Bool) (t : Nat) :
    modelWord (M := Nat) xs t = word xs t := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false =>
      change F addCode ![modelWord (M := Nat) xs t,modelWord (M := Nat) xs t] = 2 * word xs t + 0
      simp only [ih]
      rw [natAdd]
      omega
    | true =>
      change F addCode ![F addCode ![modelWord (M := Nat) xs t,modelWord (M := Nat) xs t],F oneCode Fin.elim0] = 2 * word xs t + 1
      simp only [ih]
      rw [natAdd,natAdd,natOne]
      omega

#print axioms bitsAppend
#print axioms zerosNatWord
#print axioms modelWordNat

theorem frame_bits_general (path : M6.Source.Path) (n : Nat) (vs : List Nat) :
    PA194Bounded.bits (PA194PrimitiveSimulation.frame path n vs).r =
      modelWord (M := Nat) path
        (F zeros ![n+(48-path.length),1+2*PA194Bounded.bits (M6.Runtime.sepsR vs)]) := by
  rw [PA194PrimitiveSimulation.frame,PA196.Frame.rootFrame_concrete]
  change PA194Bounded.bits (M6.Zip.trim
    (path ++ List.replicate (n+(48-path.length)) false ++ true :: M6.Runtime.sepsR vs)) = _
  rw [PA194Bounded.bits_trim,List.append_assoc,bitsAppend,modelWordNat]
  congr 1
  rw [bitsAppend,←zerosNatWord]
  rfl

theorem path25 : PA194SourceProgram.path 25 = [true,false,false,false,false,false] := by
  decide +kernel

theorem frame25_bits (n : Nat) (vs : List Nat) :
    PA194Bounded.bits (PA194PrimitiveSimulation.frame (PA194SourceProgram.path 25) n vs).r =
      modelWord (M := Nat) (PA194SourceProgram.path 25)
        (F zeros ![n+42,1+2*PA194Bounded.bits (M6.Runtime.sepsR vs)]) := by
  have hp : (PA194SourceProgram.path 25).length = 6 := by rw [path25]; rfl
  have h := frame_bits_general (PA194SourceProgram.path 25) n vs
  simpa only [hp, show (48 : Nat)-6=42 by decide] using h

theorem frame27_bits (n : Nat) (vs : List Nat) :
    PA194Bounded.bits (PA194PrimitiveSimulation.frame (PA194SourceProgram.path 27) n vs).r =
      modelWord (M := Nat) (PA194SourceProgram.path 27)
        (F zeros ![n+41,1+2*PA194Bounded.bits (M6.Runtime.sepsR vs)]) := by
  have hp : (PA194SourceProgram.path 27).length = 7 := by rw [path27]; rfl
  have h := frame_bits_general (PA194SourceProgram.path 27) n vs
  simpa only [hp, show (48 : Nat)-7=41 by decide] using h
#print axioms frame_bits_general
#print axioms path25
#print axioms frame25_bits
#print axioms frame27_bits
end PA194Path27Frame

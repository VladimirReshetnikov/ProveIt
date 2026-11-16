import PA194ZeroThenPositive
import PA194StartupSourceFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedZeroThenPositive
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194BinaryDouble PA194HeaderController BinaryTapeCodes PRAModelIOpenPairing
open PA194StartupSourceFrame PA194ZeroThenPositive PA194Path27Header PA194FiniteControls PA194StateOne
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem seededZeroThenPositive :
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let k : M := modelNumeral M 39
  F PA194Stepper.stepper ![clock27 k e,
    F PA194Stepper.stepper ![clock25 (k+1) e,
      F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0]]] =
    frame 28 ((k+1)+1) (Function.update e 0 (1 : M)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let e : Fin 11 → M := fun i => modelNumeral M (seedArgs i)
  let k : M := modelNumeral M 39
  have hz : e 8 = (0 : M) := by
    change modelNumeral M 0 = (0 : M)
    rfl
  have hp : e 0 = (1 : M)+(1 : M) := by
    change modelNumeral M 2 = (1 : M)+(1 : M)
    rw [←modelNumeralOne,←modelNumeralAdd]
  have hn : ((k+1)+1)+1 = modelNumeral M 42 := by
    dsimp only [k]
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd,←modelNumeralAdd]
  have hstart := PA194StartupSourceFrame.modelDenseStartupSourceFrame (M := M)
  let z : M := (F sourceFileCode e)+(F sourceFileCode e)+1
  have hs (n : Nat) : F zeros ![modelNumeral M (n+1),z] =
      F zeros ![modelNumeral M n,z]+F zeros ![modelNumeral M n,z] := by
    have h := modelZerosSucc (M := M) (modelNumeral M n) z
    change F zeros ![F Code.succ (fun _ => modelNumeral M n),z] = _ at h
    rw [←modelAddOne] at h
    change F zeros ![(modelNumeral M n)+(1 : M),z] = _ at h
    rw [←modelNumeralOne,←modelNumeralAdd] at h
    exact h
  have hword : modelWord (PA194SourceProgram.path 25) (F zeros ![modelNumeral M 42,z]) =
      (F zeros ![modelNumeral M 47,z])+(F zeros ![modelNumeral M 47,z])+1 := by
    rw [PA194Path27Frame.path25]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,hs 46,hs 45,hs 44,hs 43,hs 42]
  have hf : frame 25 (((k+1)+1)+1) e =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
        (F zeros ![modelNumeral M 47,z])+(F zeros ![modelNumeral M 47,z])+1]] := by
    rw [hn]
    unfold frame
    dsimp only
    have ha : (1 : M)+((F sourceFileCode e)+(F sourceFileCode e)) = z := by
      dsimp only [z]
      exact add_comm _ _
    rw [ha,hword]
  change F PA194Stepper.stepper ![modelNumeral M 58154,modelNumeral M 0] = _ at hstart
  rw [modelNumeralOne,←hf] at hstart
  have h := PA194ZeroThenPositive.zeroThenPositive (M := M) k (1 : M) e hz hp
  exact (congrArg (fun x => F PA194Stepper.stepper ![clock27 k e,F PA194Stepper.stepper ![clock25 (k+1) e,x]]) hstart).trans h
#print axioms seededZeroThenPositive
end models
end PA194SeedZeroThenPositive

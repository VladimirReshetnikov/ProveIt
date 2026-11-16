import PA194ModelLoopFrame
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelLoopCost
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PackedDecoderModel TableDispatch

def prev (x : Code 1) : Code 1 := unary predCode x
def k27 : Code 1 := prev (prev gap)
def k29 : Code 1 := prev k27
def nextSuffix : Code 1 := bin repeatOutput (plus1 count) (.zero 1)
def args28 (rs : Fin 9 → Code 1) : Fin 11 → Code 1 :=
  Function.update (PA194ModelLoopFrame.args rs) 0 (prev (PA194ModelLoopFrame.args rs 0))
def args29 (rs : Fin 9 → Code 1) : Fin 11 → Code 1 :=
  Function.update (Function.update (args28 rs) 8 (plus1 (args28 rs 8))) 10 nextSuffix
def inputs27 (rs : Fin 9 → Code 1) : Fin 12 → Code 1 :=
  Fin.cases k27 (Fin.cases (prev (PA194ModelLoopFrame.args rs 0)) (fun i : Fin 10 => PA194ModelLoopFrame.args rs i.succ))
def inputs28 (rs : Fin 9 → Code 1) : Fin 13 → Code 1 := Fin.cases k27 (Fin.cases count (args28 rs))
def inputs29 (rs : Fin 9 → Code 1) : Fin 13 → Code 1 := Fin.cases k29 (Fin.cases (plus1 count) (args29 rs))
def applyCodes {n : Nat} (f : Code n) (es : Fin n → Code 1) : Code 1 := .comp f (PRAFiniteFunctionCodes.pack n es)
def loopCost (c27 : Code 12) (c28 c29 : Code 13) (rs : Fin 9 → Code 1) : Code 1 :=
  bin addCode (bin addCode (bin addCode (applyCodes c27 (inputs27 rs)) (applyCodes c28 (inputs28 rs)))
    (applyCodes c29 (inputs29 rs))) (constantCode 40)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelApplyCodes {n : Nat} (f : Code n) (es : Fin n → Code 1) (x : M) :
    F (applyCodes f es) (fun _ => x) = F f (fun i => F (es i) (fun _ => x)) := by
  rw [applyCodes,modelComposition,getCode_pack]
theorem modelLoopCost (c27 : Code 12) (c28 c29 : Code 13) (rs : Fin 9 → Code 1) (x : M) :
    F (loopCost c27 c28 c29 rs) (fun _ => x) =
      ((F c27 (fun i => F (inputs27 rs i) (fun _ => x)) +
        F c28 (fun i => F (inputs28 rs i) (fun _ => x))) +
        F c29 (fun i => F (inputs29 rs i) (fun _ => x))) + modelNumeral M 40 := by
  simp only [loopCost,modelBin,modelApplyCodes,modelConstant]
  rfl
#print axioms modelApplyCodes
#print axioms modelLoopCost
end models
end PA194ModelLoopCost

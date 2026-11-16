import PA194ModelLoopState
import PA194OneSpareReturn
import PA194Path27Header
import PA194RegisterPermutation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ModelLoopFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopIteration PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194Path27Header BinaryTapeCodes PackedDecoderModel TableDispatch

def reg (rs : Fin 9 → Code 1) (i : Fin 9) : Code 1 := unary (rs i) control
def suffix : Code 1 := bin repeatOutput count (.zero 1)
def args (rs : Fin 9 → Code 1) : Fin 11 → Code 1 :=
  ![reg rs 0,reg rs 1,reg rs 2,reg rs 3,reg rs 4,reg rs 5,reg rs 6,reg rs 7,reg rs 8,spare,suffix]
def nested : (n : Nat) → (Fin (n+1) → Code 1) → Code 1
  | 0, es => es 0
  | n+1, es => bin block (es 0) (nested n (fun i => es i.succ))
def file (rs : Fin 9 → Code 1) : Code 1 := nested 10 (fun i => args rs (inputOrder i))
def double (t : Code 1) : Code 1 := bin addCode t t
def word : List Bool → Code 1 → Code 1
  | [], t => t
  | b::bs, t => let w := double (word bs t); if b then plus1 w else w
def frame (rs : Fin 9 → Code 1) : Code 1 :=
  bin pairCode (constantCode 24)
    (bin pairCode one (word (PA194SourceProgram.path 27)
      (bin zeros gap (plus1 (double (file rs))))))
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem modelNested (n : Nat) (es : Fin (n+1) → Code 1) (x : M) :
    F (nested n es) (fun _ => x) = F (fileCode n) (fun i => F (es i) (fun _ => x)) := by
  induction n with
  | zero =>
    change F (es 0) (fun _ => x) = F (.proj 0) _
    rw [modelProjection]
  | succ n ih =>
    rw [nested,modelBin,ih,modelFileSucc]
theorem modelWordCode (bs : List Bool) (t : Code 1) (x : M) :
    F (word bs t) (fun _ => x) = modelWord bs (F t (fun _ => x)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [word,Bool.false_eq_true,↓reduceIte,modelWord,PA194ModelLoopState.plus1,double,PA194ModelLoopState.one,modelBin,modelConstant,modelNumeralOne,ih] <;> rfl
theorem modelFrame (rs : Fin 9 → Code 1) (g n s c : M) :
    let av : Fin 11 → M := ![F (rs 0) (fun _ => c),F (rs 1) (fun _ => c),F (rs 2) (fun _ => c),F (rs 3) (fun _ => c),F (rs 4) (fun _ => c),F (rs 5) (fun _ => c),F (rs 6) (fun _ => c),F (rs 7) (fun _ => c),F (rs 8) (fun _ => c),s,F repeatOutput ![n,(0 : M)]]
    let f := F sourceFileCode av
    F (frame rs) (fun _ => packed g n s c) =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 27) (F zeros ![g,(1 : M)+(f+f)])]] := by
  dsimp only
  let x := packed g n s c
  let av : Fin 11 → M := ![F (rs 0) (fun _ => c),F (rs 1) (fun _ => c),F (rs 2) (fun _ => c),F (rs 3) (fun _ => c),F (rs 4) (fun _ => c),F (rs 5) (fun _ => c),F (rs 6) (fun _ => c),F (rs 7) (fun _ => c),F (rs 8) (fun _ => c),s,F repeatOutput ![n,(0 : M)]]
  have hfields : (fun i : Fin 11 => F (args rs i) (fun _ => x)) = av := by
    funext i
    fin_cases i <;> simp [av,args,reg,suffix,gap,count,rest,rest2,PA194ModelLoopState.spare,PA194ModelLoopState.control,x,packed,modelBin,modelUnary,modelProjection,modelDecodeLeft,modelDecodeRight,modelPairCode,PRAMultiplication.modelZero,pi₁_pair,pi₂_pair] <;> rfl
  have hfile : F (file rs) (fun _ => x) = F sourceFileCode av := by
    rw [file,modelNested,modelSourceFile]
    congr 1
    funext i
    change (fun j : Fin 11 => F (args rs j) (fun _ => x)) (inputOrder i) = _
    rw [hfields]
    rfl
  simp only [frame,modelBin,modelConstant,PA194ModelLoopState.one,modelNumeralOne,modelWordCode,PA194ModelLoopState.plus1,double,modelProjection]
  simp only [gap,packed,modelDecodeLeft,modelPairCode,pi₁_pair]
  simp only [x,packed,modelPairCode] at hfile
  rw [hfile]
  have hadd (z : M) : F addCode ![F addCode ![z,z],(1 : M)] = (1 : M)+(z+z) := by
    change (z+z)+1 = (1 : M)+(z+z)
    rw [add_comm]
  rw [hadd]
#print axioms modelNested
#print axioms modelWordCode
#print axioms modelFrame
end models
end PA194ModelLoopFrame

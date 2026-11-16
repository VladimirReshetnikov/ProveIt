import PA194SymbolicAuto
import PA194MinimumWidthSafety
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SourceSymbolicEntry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194RegisterPermutation PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls TableDispatch PA194Path27Header PA194SymbolicTrace PA194SymbolicAuto PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem wordAppend (xs ys : List Bool) (x : M) :
    modelWord (xs++ys) x = modelWord xs (modelWord ys x) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp only [List.cons_append,modelWord,Bool.false_eq_true,↓reduceIte,ih]

theorem zerosPrefix (n : Nat) (gap z : M) :
    F zeros ![gap+modelNumeral M n,z] = modelWord (List.replicate n false) (F zeros ![gap,z]) := by
  induction n with
  | zero =>
    change F zeros ![gap+(0 : M),z] = _
    rw [add_zero]
    rfl
  | succ n ih =>
    have hn : modelNumeral M (n+1) = modelNumeral M n + (1 : M) := by
      rw [←modelNumeralOne,←modelNumeralAdd]
    rw [hn,←add_assoc,PA194Site32ZeroPath.zerosSucc,ih]
    rfl

theorem frameEncoding (site n : Nat) (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let base := (1 : M)+(f+f)
    let s : Config := ⟨24,[true],(PA194SourceProgram.path site) ++ List.replicate n false⟩
    encode s (0 : M) (F zeros ![gap,base]) =
      PA194SourceSite31Physical.physicalFrame site (gap+modelNumeral M n) args := by
  dsimp only [PA194SourceSite31Physical.physicalFrame,encode,Config.q,Config.left,Config.right]
  rw [wordAppend,←zerosPrefix]
  simp [modelWord]

theorem runFromSourceFrame (site n fuel : Nat) (gap : M) (args : Fin 11 → M) :
    let f := F sourceFileCode args
    let base := (1 : M)+(f+f)
    let s : Config := ⟨24,[true],(PA194SourceProgram.path site) ++ List.replicate n false⟩
    F PA194Stepper.stepper ![modelNumeral M (PA194SymbolicAuto.run fuel s).1.length,
      PA194SourceSite31Physical.physicalFrame site (gap+modelNumeral M n) args] =
        encode (PA194SymbolicAuto.run fuel s).2 (0 : M) (F zeros ![gap,base]) ∧
      (PA194SymbolicAuto.run fuel s).1.length ≤ fuel := by
  dsimp only
  let f := F sourceFileCode args
  let base := (1 : M)+(f+f)
  let s : Config := ⟨24,[true],(PA194SourceProgram.path site) ++ List.replicate n false⟩
  have h := PA194SymbolicAuto.runCorrect (M := M) fuel s (0 : M) (F zeros ![gap,base])
  rw [frameEncoding] at h
  exact ⟨h,PA194SymbolicAuto.runLength fuel s⟩
#print axioms wordAppend
#print axioms zerosPrefix
#print axioms frameEncoding
#print axioms runFromSourceFrame
end models
end PA194SourceSymbolicEntry

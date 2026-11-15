import PA194OneSpareIdentities
import PA194Site28SeedTail
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareSeed2
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194StandardCodeBridge PA194OneSpareReturn PA194StartupSourceFrame PA194RegisterFile PA194Site28SeedTail PA194StateOne PRAModelIOpenPairing PA194UnaryRuns PA194BinaryDouble PA194FiniteControls
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def values : (n : Nat) → Fin (n+1) → M
 | 0 => fun _ => 0
 | n+1 => Fin.cases 1 (values n)
theorem fileRepeat (n : Nat) : F (fileCode n) (values n) = F repeatOutput ![modelNumeral M n,(0 : M)] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction n with
  | zero =>
    change F (.proj 0) (values 0) = _
    rw [modelProjection,show modelNumeral M 0 = (0 : M) from rfl,modelOutputZero]
    rfl
  | succ n ih =>
    rw [modelFileSucc]
    change F block ![(1 : M),F (fileCode n) (fun i => values (n+1) i.succ)] = _
    have hv : (fun i : Fin (n+1) => values (M := M) (n+1) i.succ) = values (M := M) n := by funext i; rfl
    rw [hv,ih]
    have hn : modelNumeral M (n+1) = F Code.succ (fun _ => modelNumeral M n) := by
      rw [←modelAddOne]
      change modelNumeral M (n+1) = modelNumeral M n+(1 : M)
      rw [←modelNumeralOne,←modelNumeralAdd]
    rw [hn,modelOutputSucc,modelOutputBlock]
theorem modelSeed : F repeatOutput ![modelNumeral M 25,(0 : M)] = modelNumeral M seedTail := by
  rw [←fileRepeat]
  have hv : values 25 = (fun i => modelNumeral M (spareValues i)) := by
    funext i
    fin_cases i <;> first | rfl | exact modelNumeralOne.symm
  rw [hv,modelFileSeedTail]
#print axioms fileRepeat
#print axioms modelSeed
end models
end PA194OneSpareSeed2

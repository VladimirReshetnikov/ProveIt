import PA194SourceControllerCode
import PA194StateOne
import ConfigurationStep
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194SourceControllerBinding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRASelectCode PRAEqualityCode PRABooleanOps PRAModelIOpenPairing
open PackedClock PackedDecoderModel TableDispatch ConfigurationStep PA194StateOne
open PA194SourceControllerCode

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem ordinalTest (n : Nat) (s : M) :
    F (isOrdinal n) ![s] ≠ 0 ↔ F pc ![s] = modelNumeral M n := by
  rw [isOrdinal,modelBin]
  have hv : (![s] : Fin 1 → M) = fun _ => s := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hconst : F (constantCode n) ![s] = modelNumeral M n := by rw [hv,modelConstant]
  rw [hconst]
  have ⟨hb,hc⟩ := modelEqualityCode (F pc ![s]) (modelNumeral M n)
  constructor
  · intro hn
    exact hc.mp (hb.resolve_left hn)
  · intro he hz
    have ho := hc.mpr he
    rw [hz] at ho
    exact (ne_of_lt (Arithmetic.zero_lt_one : (0 : M) < 1)) ho

theorem dispatchCons (n : Nat) (i : Option M6.Source.Instruction)
    (is : List (Option M6.Source.Instruction)) (s : M) :
    F (dispatch n (i::is)) ![s] =
      if F pc ![s] = modelNumeral M n then F (instruction i) ![s]
      else F (dispatch (n+1) is) ![s] := by
  classical
  rw [dispatch,modelSelectAmong,modelSelectAll]
  by_cases he : F pc ![s] = modelNumeral M n
  · have hn := (ordinalTest n s).mpr he
    change F (isOrdinal n) ![s] ≠ F (Code.zero 0) Fin.elim0 at hn
    simp only [he,if_true,hn,if_false]
  · have hz : F (isOrdinal n) ![s] = 0 := by
      classical
      by_contra hn
      exact he ((ordinalTest n s).mp hn)
    change F (isOrdinal n) ![s] = F (Code.zero 0) Fin.elim0 at hz
    simp only [he,if_false,hz,if_true]

/-- Every standard source ordinal selects its actual entry in every model. -/
theorem dispatchAt (base : Nat) (is : List (Option M6.Source.Instruction)) (j : Nat)
    (hj : j < is.length) (s : M) (hs : F pc ![s] = modelNumeral M (base+j)) :
    F (dispatch base is) ![s] = F (instruction is[j]) ![s] := by
  induction is generalizing base j with
  | nil => simp at hj
  | cons i is ih =>
    cases j with
    | zero =>
      rw [dispatchCons]
      simp only [Nat.add_zero] at hs
      simp [hs]
    | succ j =>
      have hn : F pc ![s] ≠ modelNumeral M base := by
        rw [hs]
        exact ne_of_gt (modelNumeralStrict base (base+(j+1)) (by omega))
      rw [dispatchCons,if_neg hn]
      have hj' : j < is.length := by simpa using hj
      have hs' : F pc ![s] = modelNumeral M ((base+1)+j) := by
        convert hs using 1 <;> congr 1 <;> omega
      simpa only [List.getElem_cons_succ] using ih (base+1) j hj' hs'
/-- The finite code selects the instruction resolved from the actual pinned
    PA194 source tree at any standard source ordinal, in every candidate model. -/
theorem selectActual (i : Nat) (hi : i < 3673) (s : M)
    (hs : F pc ![s] = modelNumeral M i) :
    F step ![s] = F (instruction ((M6.Source.PathTrie.nthSite PA194.SourceTree.trie i).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie))) ![s] := by
  have h := dispatchAt 0 program i (by simpa [program] using hi) s (by simpa using hs)
  simpa only [step, program,List.getElem_map,List.getElem_range,Nat.zero_add] using h
#print axioms selectActual
#print axioms ordinalTest
#print axioms dispatchCons
#print axioms dispatchAt
end models
end PA194SourceControllerBinding

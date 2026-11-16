import PA194PathLengthCode
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194PathLengthGlobalBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAExhaustion PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem lookupBound (xs : List Nat) (x : M) (hxs : ∀ a ∈ xs, a ≤ 36) :
    F (lookupCode 0 xs) (fun _ => x) ≤ modelNumeral M 36 := by
  induction xs generalizing x with
  | nil =>
    change F (constantCode 0) (fun _ => x) ≤ _
    rw [modelConstant]
    exact le_of_lt (modelNumeralStrict 0 36 (by decide))
  | cons a as ih =>
    rcases modelZeroOrSuccPred x with hz | hs
    · rw [hz, modelLookupZero, modelConstant]
      have ha := hxs a (by simp)
      by_cases heq : a = 36
      · rw [heq]
      · exact le_of_lt (modelNumeralStrict a 36 (lt_of_le_of_ne ha heq))
    · rw [←hs, modelLookupSucc]
      exact ih _ (fun b hb => hxs b (by simp [hb]))

theorem pathLengthBound (pc : M) :
    F PA194PathLengthCode.pathLengthCode (fun _ => pc) ≤ modelNumeral M 36 := by
  apply lookupBound
  intro a ha
  change a ∈ (List.range 3673).map (fun i => (PA194SourceProgram.path i).length) at ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact PA194SourcePathDepth.sourcePathBound i

theorem widthGapAtLeast21 (pc gap : M)
    (hwidth : gap + F PA194PathLengthCode.pathLengthCode (fun _ => pc) = modelNumeral M 57) :
    modelNumeral M 21 ≤ gap := by
  have hle := pathLengthBound pc
  have h := add_le_add_left hle (modelNumeral M 21)
  have hnum : modelNumeral M 36 + modelNumeral M 21 = modelNumeral M 57 := by rw [←modelNumeralAdd]
  rw [hnum,←hwidth] at h
  have h' : modelNumeral M 21 + F PA194PathLengthCode.pathLengthCode (fun _ => pc) ≤
      gap + F PA194PathLengthCode.pathLengthCode (fun _ => pc) := by
    calc
      _ = F PA194PathLengthCode.pathLengthCode (fun _ => pc) + modelNumeral M 21 := add_comm _ _
      _ ≤ _ := h
  exact le_of_add_le_add_right h'
#print axioms lookupBound
#print axioms pathLengthBound
#print axioms widthGapAtLeast21
end models
end PA194PathLengthGlobalBound

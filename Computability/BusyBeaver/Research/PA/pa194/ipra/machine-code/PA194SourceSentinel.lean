import PA194SourcePCBound
import PA194SourceControllerSites
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSentinel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRASelectCode PRAModelIOpenPairing TableDispatch ConfigurationStep PA194StateOne
open PA194SourceControllerCode PA194SourceControllerBinding PA194SourceControllerSites PA194SourcePCBound
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- If no table ordinal matches, dispatch reaches its explicit default. -/
theorem dispatchAvoid (base : Nat) (is : List (Option M6.Source.Instruction)) (s : M)
    (h : ∀ k : Nat, base ≤ k → k < base + is.length → F pc ![s] ≠ modelNumeral M k) :
    F (dispatch base is) ![s] = F defaultStep ![s] := by
  induction is generalizing base with
  | nil => rfl
  | cons i is ih =>
    rw [dispatchCons,if_neg (h base (by omega) (by simp))]
    apply ih (base+1)
    intro k hk hk'
    apply h k <;> simp only [List.length_cons] at * <;> omega

theorem defaultMalformed (s : M) (hs : F pc ![s] = modelNumeral M 3673) :
    F defaultStep ![s] = s := by
  have hn := (ordinalTest 3673 s).mpr hs
  change F (isOrdinal 3673) ![s] ≠ F (Code.zero 0) Fin.elim0 at hn
  rw [defaultStep,modelSelectAmong,modelSelectAll,if_neg hn,modelProjection]
  rfl

theorem defaultHalted (s : M) (hs : F pc ![s] = modelNumeral M 3674) :
    F defaultStep ![s] = s := by
  have hd : F pc ![s] ≠ modelNumeral M 3673 := by
    rw [hs]
    exact ne_of_gt (modelNumeralStrict 3673 3674 (by decide))
  have hz : F (isOrdinal 3673) ![s] = (0 : M) := by
    classical
    by_contra hn
    exact hd ((ordinalTest 3673 s).mp hn)
  have hn := (ordinalTest 3674 s).mpr hs
  change F (isOrdinal 3673) ![s] = F (Code.zero 0) Fin.elim0 at hz
  change F (isOrdinal 3674) ![s] ≠ F (Code.zero 0) Fin.elim0 at hn
  rw [defaultStep,modelSelectAmong,modelSelectAll,if_pos hz,modelSelectAmong,modelSelectAll,if_neg hn,modelProjection]
  rfl

theorem stepSentinel (n : Nat) (hbound : 3673 ≤ n)
    (s : M) (hs : F pc ![s] = modelNumeral M n) :
    F step ![s] = F defaultStep ![s] := by
  apply dispatchAvoid 0 program s
  intro k _ hk
  have hk' : k < 3673 := by simpa [programLength] using hk
  rw [hs]
  exact ne_of_gt (modelNumeralStrict k n (by omega))

theorem stepMalformed (s : M) (hs : F pc ![s] = modelNumeral M 3673) : F step ![s] = s := by
  rw [stepSentinel 3673 (by omega) s hs,defaultMalformed s hs]
theorem stepHalted (s : M) (hs : F pc ![s] = modelNumeral M 3674) : F step ![s] = s := by
  rw [stepSentinel 3674 (by omega) s hs,defaultHalted s hs]
#print axioms dispatchAvoid
#print axioms stepMalformed
#print axioms stepHalted
end models
end PA194SourceSentinel

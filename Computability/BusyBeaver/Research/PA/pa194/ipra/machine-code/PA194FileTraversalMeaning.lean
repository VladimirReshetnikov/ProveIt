import PA194FileTraversal
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194FileTraversalMeaning
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194RegisterFile PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
/-- The seven scanned physical blocks are present in reverse order on the
left numeric half, followed by its pre-scan tail. -/
theorem leftSevenMeaning (e : Fin 8 → M) (l : M) :
    F (PA194FileTraversal.leftCode 7) (Fin.cases l e) =
    F (fileCode 7) ![e 6,e 5,e 4,e 3,e 2,e 1,e 0,l] := by
  simp only [PA194FileTraversal.modelLeftSucc,PA194FileTraversal.modelLeftZero,
    modelFileSucc,show ∀ e : Fin 1 → M, F (fileCode 0) e = e 0 from fun e => modelProjection 0 e]
  rfl
/-- The final left half is even in every candidate PRA model, so it is not
the numeric code one of the canonical singleton left tape. -/
theorem leftSevenEven (e : Fin 8 → M) (l : M) :
    ∃ z : M, F (PA194FileTraversal.leftCode 7) (Fin.cases l e) = z+z := by
  rw [leftSevenMeaning,modelFileSucc,modelBlock]
  exact ⟨_,rfl⟩
theorem leftSevenNotOne (e : Fin 8 → M) (l : M) :
    F (PA194FileTraversal.leftCode 7) (Fin.cases l e) ≠ (1 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  obtain ⟨z,hz⟩ := leftSevenEven e l
  intro he
  have hp := congrArg (fun x : M => F parityCode (fun _ => x)) (hz.symm.trans he)
  have h1 := (modelOdd (0 : M)).1
  simp only [zero_add] at h1
  rw [(modelDouble z).1,h1] at hp
  exact zero_ne_one hp
#print axioms leftSevenNotOne
#print axioms leftSevenEven
#print axioms leftSevenMeaning
end models
end PA194FileTraversalMeaning

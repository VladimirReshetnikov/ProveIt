import PA194DecoderRoundCode
import PA194ClockInvariantDefinable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194DecoderInvariant3
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194ClockInvariantDefinable PA194IteratedSimulation
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def body (f g : M → M) (initial : Fin 11 → M) (tail limit j : M) : Prop :=
  limit < j ∨ ∃ x y left : M,
    f j = pair (modelNumeral M 34)
      (pair (initial 0) (pair (initial 1) (pair (initial 2) (pair (initial 3) (pair (initial 4)
        (pair (initial 5) (pair x (pair y (pair left tail))))))))) ∧
    left+j = limit ∧ pair x y = g j

theorem bodyDef (f g : M → M) (initial : Fin 11 → M) (tail limit : M)
    (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (body f g initial tail limit) := by
  haveI := hf
  haveI := hg
  unfold body
  definability
#print axioms bodyDef
end models
end PA194DecoderInvariant3

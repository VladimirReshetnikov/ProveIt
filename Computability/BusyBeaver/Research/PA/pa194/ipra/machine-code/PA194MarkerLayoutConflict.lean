import PA194MarkAll
import PA194OnesCommute
/-! An all-model incompatibility between a genuine non-first marking output
and the particular conditional nine-bit increment-dispatch route. -/
set_option autoImplicit false
namespace PA194MarkerLayoutConflict
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble
open PA194ReturnFile PA194OnesCommute PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- A nonempty returned regular prefix has second-lowest bit one. -/
theorem regularPrefixBit (n : Nat) (e : Fin (n+3) → M) :
    F parityCode (fun _ => F halfCode (fun _ => F (returnCode (n+1)) e)) = (1 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelReturnCodeSucc]
  rw [(modelDouble _).2, modelOnesCommute, (modelOdd _).1]

/-- Such a returned prefix cannot begin with two zeros, in any candidate PRA model. -/
theorem regularPrefixNotFour (n : Nat) (e : Fin (n+3) → M) (v : M) :
    F (returnCode (n+1)) e ≠ (v+v)+(v+v) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro heq
  have hp := regularPrefixBit n e
  rw [heq,(modelDouble (v+v)).2,(modelDouble v).1] at hp
  exact _root_.one_ne_zero hp.symm
/-- The returned tape of a non-first marker cannot have the right-hand
prefix required by the particular state-24 to increment path under study. -/
theorem positiveMarkerRightNotRoute (n : Nat) (e : Fin (n+3) → M) (l v : M) :
    let a := F (returnCode (n+1)) e
    let b := (v+v)+(v+v)
    F parityCode (fun _ => l)+a+a ≠ b+b+1 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a := F (returnCode (n+1)) e
  let b := (v+v)+(v+v)
  intro heq
  rcases modelParityBit l with hz | ho
  · change F parityCode (fun _ => l) = (0 : M) at hz
    rw [hz] at heq
    change (0 : M)+a+a = b+b+1 at heq
    rw [zero_add] at heq
    have hp := congrArg (fun x => F parityCode (fun _ => x)) heq
    rw [(modelDouble a).1,(modelOdd b).1] at hp
    exact _root_.zero_ne_one hp
  · change F parityCode (fun _ => l) = (1 : M) at ho
    rw [ho] at heq
    change (1 : M)+a+a = b+b+1 at heq
    have hp := congrArg (fun x => F halfCode (fun _ => x)) heq
    have hleft : (1 : M)+a+a = a+a+1 := by simp only [add_comm,add_left_comm]
    rw [hleft,(modelOdd a).2,(modelOdd b).2] at hp
    exact regularPrefixNotFour n e v hp
/-- This is exactly the right tape half in `modelMarkAllPositive`, for any
non-first position and any values of its parameters. -/
theorem positiveMarkOutputNotRoute (n : Nat) (e : Fin (n+2) → M) (l t v : M) :
    let a := F (returnCode (n+1)) (Fin.cases ((t+t)+(t+t)) e)
    F parityCode (fun _ => l)+a+a ≠ ((v+v)+(v+v))+((v+v)+(v+v))+1 := by
  exact positiveMarkerRightNotRoute n _ l v
#print axioms positiveMarkOutputNotRoute
#print axioms positiveMarkerRightNotRoute
#print axioms regularPrefixBit
#print axioms regularPrefixNotFour
end models
end PA194MarkerLayoutConflict

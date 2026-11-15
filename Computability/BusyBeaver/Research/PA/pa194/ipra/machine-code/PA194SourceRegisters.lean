import PA194SourceControllerBinding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceRegisters
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PackedClock PackedRootModel PackedDecoderModel
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

noncomputable def getSem : Nat → M → M
  | 0, f => pi₁ f
  | n+1, f => getSem n (pi₂ f)

noncomputable def putSem : Nat → M → M → M
  | 0, f, v => pair v (pi₂ f)
  | n+1, f, v => pair (pi₁ f) (putSem n (pi₂ f) v)

theorem getAuxModel (n : Nat) (f : Code 1) (s : M) :
    F (getRegisterAux n f) ![s] = getSem n (F f ![s]) := by
  induction n generalizing f with
  | zero => rw [getRegisterAux,modelUnary,modelDecodeLeft]; rfl
  | succ n ih => rw [getRegisterAux,ih,modelUnary,modelDecodeRight]; rfl

theorem putAuxModel (n : Nat) (f v : Code 1) (s : M) :
    F (putRegisterAux n f v) ![s] = putSem n (F f ![s]) (F v ![s]) := by
  induction n generalizing f with
  | zero => rw [putRegisterAux,modelBin,modelUnary,modelDecodeRight,modelPairCode]; rfl
  | succ n ih =>
    rw [putRegisterAux,modelBin,ih,modelUnary,modelDecodeLeft,modelUnary,modelDecodeRight,modelPairCode]
    rfl

theorem readAfterWrite (n : Nat) (f v : M) : getSem n (putSem n f v) = v := by
  induction n generalizing f with
  | zero => simp [getSem,putSem,pi₁_pair]
  | succ n ih => simp [getSem,putSem,pi₂_pair,ih]

theorem readOtherAfterWrite (n j : Nat) (f v : M) (hne : j ≠ n) :
    getSem j (putSem n f v) = getSem j f := by
  induction n generalizing j f with
  | zero =>
    cases j with
    | zero => exact False.elim (hne rfl)
    | succ j => simp [getSem,putSem,pi₂_pair]
  | succ n ih =>
    cases j with
    | zero => simp [getSem,putSem,pi₁_pair]
    | succ j =>
      simp only [getSem,putSem,pi₂_pair]
      apply ih
      intro he
      exact hne (congrArg Nat.succ he)
#print axioms getAuxModel
#print axioms putAuxModel
#print axioms readAfterWrite
#print axioms readOtherAfterWrite
end models
end PA194SourceRegisters

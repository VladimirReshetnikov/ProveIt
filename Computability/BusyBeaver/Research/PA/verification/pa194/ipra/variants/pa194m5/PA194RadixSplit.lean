import PA194ProgramControl
import PA194ModelCantorWalker

set_option autoImplicit false
set_option maxRecDepth 22000
set_option maxHeartbeats 4500000

namespace PA194RadixSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRASelectCode PRAExhaustion
open PackedClock PackedDecoderModel TableDispatch PA194IteratedSimulation
open PA194ClockInvariantDefinable PA194PathIterator

/-- The packed state has remainder first and quotient second. The largest
    digit of the positive divisor is the parameter `last`. -/
def next (last : Nat) : Code 1 :=
  selectAmong (PA194SourceControllerCode.isOrdinal last)
    (bin pairCode (.zero 1) (PA194PathIterator.unary Code.succ decodeRight))
    (bin pairCode (PA194PathIterator.unary Code.succ decodeLeft) decodeRight)

def splitCode (last : Nat) : Code 1 :=
  .comp (iterate (next last)) (.cons (.proj 0) (.cons (.zero 1) (.nil 1)))

def quotientCode (last : Nat) : Code 1 :=
  PA194PathIterator.unary decodeRight (splitCode last)

def remainderCode (last : Nat) : Code 1 :=
  PA194PathIterator.unary decodeLeft (splitCode last)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelNext (last : Nat) (digit quotient : M) :
    F (next last) ![pair digit quotient] =
      if digit = modelNumeral M last then pair 0 (quotient+1)
      else pair (digit+1) quotient := by
  have singleton : (![pair digit quotient] : Fin 1 → M) = fun _ => pair digit quotient := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hl : F decodeLeft ![pair digit quotient] = digit := by
    rw [singleton,modelDecodeLeft,pi₁_pair]
  have hr : F decodeRight ![pair digit quotient] = quotient := by
    rw [singleton,modelDecodeRight,pi₂_pair]
  rw [next,PA194ProgramControl.selectOrdinal]
  simp only [PA194SourceControllerCode.pc,modelBin,modelUnary,hl,hr,
    PRAMultiplication.modelZero,←modelAddOne,modelPairCode]
  rfl

noncomputable def orbit (last : Nat) (n : M) : M :=
  F (iterate (next last)) ![n,(0 : M)]

def invariant (divisor n state : M) : Prop :=
  divisor*pi₂ state + pi₁ state = n ∧ pi₁ state < divisor

private theorem preserves (last : Nat) (n s : M)
    (h : invariant (modelNumeral M (last+1)) n s) :
    invariant (modelNumeral M (last+1)) (n+1) (F (next last) ![s]) := by
  let divisor : M := modelNumeral M (last+1)
  let digit := pi₁ s
  let quotient := pi₂ s
  have hs : s = pair digit quotient := (pair_unpair s).symm
  change divisor*quotient+digit = n ∧ digit < divisor at h
  have hdiv : divisor = modelNumeral M last+1 := PA194FiniteControls.modelNumeralSucc _
  change invariant divisor (n+1) (F (next last) ![s])
  rw [hs,modelNext]
  by_cases hd : digit = modelNumeral M last
  · rw [if_pos hd]
    simp only [invariant,pi₁_pair,pi₂_pair]
    constructor
    · calc
        divisor*(quotient+1)+0 = divisor*quotient+divisor := by simp [mul_add]
        _ = (divisor*quotient+digit)+1 := by rw [hdiv,hd]; ac_rfl
        _ = n+1 := by rw [h.1]
    · rw [hdiv]
      exact lt_of_le_of_lt zero_le (lt_add_one _)
  · rw [if_neg hd]
    simp only [invariant,pi₁_pair,pi₂_pair]
    constructor
    · rw [←add_assoc,h.1]
    · apply lt_of_le_of_ne (lt_iff_succ_le.mp h.2)
      intro he
      rw [hdiv] at he
      exact hd (add_right_cancel he)

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem orbitInvariant (last : Nat) (n : M) :
    invariant (modelNumeral M (last+1)) n (orbit last n) := by
  have hOrb : 𝚺₁-Function₁ (orbit (M := M) last) :=
    bindBinary _ 0 (binaryCodeDef (iterate (next last)))
  obtain ⟨hLeft,hRight⟩ := PA194ModelCantorWalker.projectionDefs (orbit last) hOrb
  haveI := hLeft
  haveI := hRight
  have hDef : 𝚺₁-Predicate (fun i : M =>
      invariant (modelNumeral M (last+1)) i (orbit last i)) := by
    unfold invariant
    definability
  induction n using ISigma1.sigma1_succ_induction with
  | hP => exact hDef
  | zero =>
    rw [orbit,iterateZero]
    have hzero : pair (0 : M) 0 = 0 := by simp [pair]
    have hd : (0 : M) < modelNumeral M (last+1) := by
      rw [PA194FiniteControls.modelNumeralSucc]
      exact lt_of_le_of_lt zero_le (lt_add_one _)
    have hinit : invariant (modelNumeral M (last+1)) 0 (pair 0 0) := by
      simp [invariant,hd]
    simpa only [hzero] using hinit
  | succ n ih =>
    change invariant (modelNumeral M (last+1)) (n+1)
      (F (iterate (next last)) ![n+1,(0 : M)])
    rw [iterateSucc]
    exact preserves last n (orbit last n) ih

theorem modelSplit (last : Nat) (n : M) :
    let divisor := modelNumeral M (last+1)
    F (splitCode last) ![n] = pair (n%divisor) (n/divisor) := by
  let d := modelNumeral M (last+1)
  let s := orbit last n
  have hi : invariant d n s := orbitInvariant last n
  have hs : F (splitCode last) ![n] = s := by
    rw [splitCode,modelComposition]
    change F (iterate (next last)) (fun i => _) = F (iterate (next last)) ![n,(0 : M)]
    congr 1
    funext i
    fin_cases i
    · exact modelProjection _ _
    · exact PRAMultiplication.modelZero _
  have hr : n%d = pi₁ s := by
    rw [←hi.1,mul_comm d]
    exact mod_mul_add_of_lt _ _ hi.2
  have hq : n/d = pi₂ s := by
    rw [←hi.1]
    exact div_mul_add' _ _ hi.2
  dsimp only
  change F (splitCode last) ![n] = pair (n%d) (n/d)
  rw [hs,hr,hq,pair_unpair]

theorem modelQuotient (last : Nat) (n : M) :
    F (quotientCode last) ![n] = n / modelNumeral M (last+1) := by
  rw [quotientCode,modelUnary,modelSplit,modelDecodeRight,pi₂_pair]

theorem modelRemainder (last : Nat) (n : M) :
    F (remainderCode last) ![n] = n % modelNumeral M (last+1) := by
  rw [remainderCode,modelUnary,modelSplit,modelDecodeLeft,pi₁_pair]

#print axioms modelQuotient
#print axioms modelRemainder
#print axioms modelNext
#print axioms orbitInvariant
#print axioms modelSplit
end models
end PA194RadixSplit

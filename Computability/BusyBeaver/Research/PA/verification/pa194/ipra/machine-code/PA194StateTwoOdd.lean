import PA194StateOne
import PackedIterationModel
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194StateTwoOdd
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls PA194StateOne PA194BinaryDouble PackedIterationModel PRAModelIOpenPairing

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelStateTwoOdd (l r : M) :
    (F nextQ ![modelNumeral M 2,l,r+r+1], F nextL ![modelNumeral M 2,l,r+r+1],
      F nextR ![modelNumeral M 2,l,r+r+1]) = (modelNumeral M 2,l+l+1,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 2 < modelNumeral M 194 := modelNumeralStrict 2 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 2,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelOdd r
  have ha : modelNumeral M 2 + modelNumeral M 2 + F parityCode (fun _ => r+r+1) = modelNumeral M 5 := by
    rw [hr.1, ←modelNumeralOne, ←modelNumeralAdd, ←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 5)  = (1 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 5) = _
    rw [modelWriteNumeral]
    exact modelNumeralOne
  have hd : lookupSem 0 directions (modelNumeral M 5) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 5) = _
    rw [modelDirectionNumeral]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M 5) = modelNumeral M 2 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 5) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 2,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 2,l,r+r+1],F nextL ![modelNumeral M 2,l,r+r+1],
    F nextR ![modelNumeral M 2,l,r+r+1]) = stepSem (modelNumeral M 2) l (r+r+1) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false,add_zero]
theorem modelPackedTwoTransition (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![modelNumeral M 2,F pairCode ![l,(r+r)+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 2,l,(r+r)+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 2,l,(r+r)+1],F nextL ![modelNumeral M 2,l,(r+r)+1],
    F nextR ![modelNumeral M 2,l,(r+r)+1]) = stepSem (modelNumeral M 2) l ((r+r)+1) at hm
  rw [←hm,modelStateTwoOdd]
#print axioms modelStateTwoOdd
end models
end PA194StateTwoOdd

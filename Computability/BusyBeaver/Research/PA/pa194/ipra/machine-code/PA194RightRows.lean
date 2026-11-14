import PA194StateOne
import PA194BinaryDouble
import PackedIterationModel
/-! All-model execution of arbitrary checked right-moving rows of the pinned PA194 table. -/
set_option autoImplicit false
namespace PA194RightRows
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls PA194StateOne PA194BinaryDouble PackedIterationModel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem rightZero (q w dest : Nat) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q) (0,0,194) = (w,1,dest)) (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M dest,F pairCode ![l+l+modelNumeral M w,r]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq' : modelNumeral M q < modelNumeral M 194 := modelNumeralStrict q 194 hq
  have hactive : F ltBitCode ![modelNumeral M q,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq'
  have hr := modelDouble r
  have ha : modelNumeral M q + modelNumeral M q + F parityCode (fun _ => r+r) = modelNumeral M (q+q) := by
    rw [hr.1,add_zero,←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M (q+q)) = modelNumeral M w := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M (q+q)) = _
    rw [modelWriteNumeral,hrow]
  have hd : lookupSem 0 directions (modelNumeral M (q+q)) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M (q+q)) = _
    rw [modelDirectionNumeral,hrow]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M (q+q)) = modelNumeral M dest := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M (q+q)) = _
    rw [modelTargetNumeral,hrow]
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M q,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M q,l,r+r],F nextL ![modelNumeral M q,l,r+r],F nextR ![modelNumeral M q,l,r+r]) = stepSem (modelNumeral M q) l (r+r) at hm
  rw [←hm]
  have hn : (F nextQ ![modelNumeral M q,l,r+r],F nextL ![modelNumeral M q,l,r+r],F nextR ![modelNumeral M q,l,r+r]) = (modelNumeral M dest,l+l+modelNumeral M w,r) := by
    rw [hm]
    simp only [stepSem]
    have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
    simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2]
    have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
      change (1 : M) ≠ 0
      exact _root_.one_ne_zero
    simp only [hone,ite_false]
  rw [hn]

theorem rightOne (q w dest : Nat) (hq : q < 194)
    (hrow : PA194Rows.rows.getD (q+q+1) (0,0,194) = (w,1,dest)) (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M q,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M dest,F pairCode ![l+l+modelNumeral M w,r]] := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq' : modelNumeral M q < modelNumeral M 194 := modelNumeralStrict q 194 hq
  have hactive : F ltBitCode ![modelNumeral M q,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq'
  have hr := modelOdd r
  have ha : modelNumeral M q + modelNumeral M q + F parityCode (fun _ => r+r+1) = modelNumeral M (q+q+1) := by
    rw [hr.1,←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M (q+q+1)) = modelNumeral M w := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M (q+q+1)) = _
    rw [modelWriteNumeral,hrow]
  have hd : lookupSem 0 directions (modelNumeral M (q+q+1)) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M (q+q+1)) = _
    rw [modelDirectionNumeral,hrow]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M (q+q+1)) = modelNumeral M dest := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M (q+q+1)) = _
    rw [modelTargetNumeral,hrow]
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M q,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M q,l,r+r+1],F nextL ![modelNumeral M q,l,r+r+1],F nextR ![modelNumeral M q,l,r+r+1]) = stepSem (modelNumeral M q) l (r+r+1) at hm
  rw [←hm]
  have hn : (F nextQ ![modelNumeral M q,l,r+r+1],F nextL ![modelNumeral M q,l,r+r+1],F nextR ![modelNumeral M q,l,r+r+1]) = (modelNumeral M dest,l+l+modelNumeral M w,r) := by
    rw [hm]
    simp only [stepSem]
    have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
    simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2]
    have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
      change (1 : M) ≠ 0
      exact _root_.one_ne_zero
    simp only [hone,ite_false]
  rw [hn]


#print axioms rightOne
#print axioms rightZero
end models
end PA194RightRows

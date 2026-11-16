import PA194PathLengthGlobalBound
import PA194StartupSentence
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194HeaderWidthGlobalNative
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory PRAEqualityCode
open TableDispatch PackedDecoderModel PackedRootModel PA194StartupSentence

abbrev T := TermN 2
def pc : T := .bvar 0
def gap : T := .bvar 1
def width : T := app2 addCode gap (app1 PA194PathLengthCode.pathLengthCode pc)
def widthOK : T := app2 equalityCode width (state 57)
def gapSmall : T := app2 ltBitCode gap (state 21)
def lhs : T := app2 mulCode widthOK gapSmall
def rhs : T := zero
def sentence : Sentence language := equalClosure lhs rhs

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,widthOK,gapSmall,width,pc,gap,valApp2,valApp1,valState,valZero,Semiterm.val_bvar]
  change F equalityCode ![e 1 + F PA194PathLengthCode.pathLengthCode (fun _ => e 0),modelNumeral M 57] *
      F ltBitCode ![e 1,modelNumeral M 21] = (0 : M)
  by_cases hwidth : e 1 + F PA194PathLengthCode.pathLengthCode (fun _ => e 0) = modelNumeral M 57
  · have hgap := PA194PathLengthGlobalBound.widthGapAtLeast21 (e 0) (e 1) hwidth
    have hz : F ltBitCode ![e 1,modelNumeral M 21] = (0 : M) := (modelLtZero _ _).mpr (not_lt_of_ge hgap)
    rw [hz,mul_zero]
  · have ⟨hb,he⟩ := modelEqualityCode (e 1 + F PA194PathLengthCode.pathLengthCode (fun _ => e 0)) (modelNumeral M 57)
    have hz : F equalityCode ![e 1 + F PA194PathLengthCode.pathLengthCode (fun _ => e 0),modelNumeral M 57] = (0 : M) := by
      rcases hb with hz | ho
      · exact hz
      · exact False.elim (hwidth (he.mp ho))
    rw [hz,zero_mul]
end models

theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence

theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs :=
  nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194HeaderWidthGlobalNative

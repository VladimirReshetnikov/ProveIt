import PA194Site27ZeroClockCodeSplit
import PA194Site27ZeroFile
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
noncomputable section
namespace PA194Site27ZeroClockSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAModelIOpenPairing PA194StartupSentence PA194Path27Header PA194SourceSite25Physical PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194StateOne PackedDecoderModel TableDispatch
abbrev T := TermN 11
def A (a b : T) : T := app2 addCode a b
def twice (a : T) : T := app1 PA194StartupSentence.doubleCode a
def args : Fin 11 → T := Fin.cases zero (fun i : Fin 10 => .bvar i.succ)
def k : T := .bvar 0
def f : T := .func sourceFileCode args
def clockArgs : Fin 12 → T := Fin.cases k args
def wordTerm : List Bool → T → T
  | [], t => t
  | b::bs, t => let x := twice (wordTerm bs t); if b then A x one else x
def right (site : Nat) : T := wordTerm (PA194SourceProgram.path site)
  (app2 zeros (A (A k one) one) (A one (A f f)))
def lhs : T := app2 PA194Stepper.stepper (.func PA194Site27ZeroClockCodeSplit.clockCode clockArgs)
  (PA194StartupSentence.pack (state 24) one (right 27))
def rhs : T := PA194StartupSentence.pack (state 24) one (right 31)
def sentence : Sentence language := equalClosure lhs rhs
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem valWord (e : Fin 11 → M) (xs : List Bool) (t : T) :
    Semiterm.val e Empty.elim (wordTerm xs t) = modelWord (M := M) xs (Semiterm.val e Empty.elim t) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [wordTerm,Bool.false_eq_true,↓reduceIte,modelWord,A,twice,valApp1,valApp2,modelDoubleCode,valOne,ih]
    rfl
theorem modelSentence : M↓[language] ⊧ sentence := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  let es : Fin 11 → M := fun i => Semiterm.val e Empty.elim (args i)
  have hz : es 0 = (0 : M) := by simp [es,args,valZero]
  have hf := PA194Site27ZeroFile.returnedIsSourceFile es hz
  have h := PA194Site27ZeroClockPhysical.zeroBranchWithFile (e 0) es hz hf
  have hc := PA194Site27ZeroClockCodeSplit.modelClock (Fin.cases (e 0) es)
  change F PA194Site27ZeroClockCodeSplit.clockCode (Fin.cases (e 0) es) = PA194Site27ZeroClockPhysical.clock24 (e 0) es at hc
  rw [←hc] at h
  have hv : (fun i : Fin 12 => Semiterm.val e Empty.elim (clockArgs i)) = Fin.cases (e 0) es := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  simp only [lhs,rhs,right,PA194StartupSentence.pack,A,valApp2,valState,valOne,valWord,k,
    Semiterm.val_bvar,f,Semiterm.val_func,Function.comp_def]
  rw [hv]
  exact h
end models
theorem classicalPRA : PRA ⊢ sentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence
theorem nativeIPRA : standardTheory ⊢ equalClosureI lhs rhs := nativeOfClassical lhs rhs classicalPRA
#print axioms modelSentence
#print axioms classicalPRA
#print axioms nativeIPRA
end PA194Site27ZeroClockSentence

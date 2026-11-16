import PA194ModelDenseStartup
import PA194FiniteControls
import PA194StateOne
import PRAEqualityToIPRA
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194StartupSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open TableDispatch PA194FiniteControls PA194StateOne PA194ModelDenseStartup PRAModelIOpenPairing

def app2 {n : Nat} (f : Code 2) (a b : TermN n) : TermN n := .func f ![a,b]
def zero {n : Nat} : TermN n := .func (.zero 0) Fin.elim0
def one {n : Nat} : TermN n := .func oneCode Fin.elim0
/-- A unary primitive-recursive doubling symbol keeps bit terms linear in size. -/
def doubleCode : Code 1 := .comp addCode (.cons (.proj 0) (.cons (.proj 0) (.nil 1)))
def app1 {n : Nat} (f : Code 1) (a : TermN n) : TermN n := .func f ![a]
def state {n : Nat} (q : Nat) : TermN n := .func (constantCode q) ![zero]
def pack {n : Nat} (q l r : TermN n) : TermN n := app2 pairCode q (app2 pairCode l r)
/-- A compact closed arithmetic term for a little-endian binary bit list. -/
def bitsTerm {n : Nat} : List Bool → TermN n
  | [] => zero
  | b :: bs => let t := bitsTerm bs; let d := app1 doubleCode t
      if b then app2 addCode d one else d

def startupClockBits : List Bool := [false,true,false,true,false,true,false,false,true,true,false,false,false,true,true,true]
theorem startupClockBits_value : PA194Bounded.bits startupClockBits = 58154 := by decide +kernel

def lhs : TermN 0 := app2 PA194Stepper.stepper (bitsTerm startupClockBits) zero
def rhs : TermN 0 := pack (state 24) one (bitsTerm PA194StartupData.seedFrame.r)
def sentence : Sentence language := equalClosure lhs rhs

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 {n : Nat} (e : Fin n → M) (f : Code 2) (a b : TermN n) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_term_pair e a b

theorem modelDoubleCode (x : M) : F doubleCode (fun _ => x) = x+x := by
  rw [doubleCode,modelComposition]
  have hv : (fun i => F (getCode (.cons (.proj 0) (.cons (.proj 0) (.nil 1))) i) (fun _ => x)) = ![x,x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection (M := M) 0 _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelProjection (M := M) 0 _
  rw [hv]
  rfl

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 {n : Nat} (e : Fin n → M) (f : Code 1) (a : TermN n) :
    Semiterm.val e Empty.elim (app1 f a) = F f (fun _ => Semiterm.val e Empty.elim a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valZero {n : Nat} (e : Fin n → M) : Semiterm.val e Empty.elim zero = (0 : M) := by
  simp only [zero,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valOne {n : Nat} (e : Fin n → M) : Semiterm.val e Empty.elim one = (1 : M) := by
  simp only [one,Semiterm.val_func]
  congr 1
  exact Subsingleton.elim _ _

theorem valState {n : Nat} (e : Fin n → M) (q : Nat) : Semiterm.val e Empty.elim (state q) = modelNumeral M q := by
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [state,zero,Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ ![(.func (.zero 0) Fin.elim0 : TermN n)]) =
      (fun _ => (0 : M)) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_func,hz]
    rfl
  rw [hv]
  exact modelConstant q _

theorem valBits {n : Nat} (e : Fin n → M) (bs : List Bool) :
    Semiterm.val e Empty.elim (bitsTerm bs) = modelNumeral M (PA194Bounded.bits bs) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  induction bs with
  | nil => exact valZero e
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [bitsTerm, Bool.false_eq_true, ↓reduceIte, valApp1, ih, modelDoubleCode, PA194Bounded.bits, Bool.toNat_false, Nat.zero_add]
      change modelNumeral M (PA194Bounded.bits bs) + modelNumeral M (PA194Bounded.bits bs) = _
      rw [← modelNumeralAdd]
      congr 1
      omega
    | true =>
      simp only [bitsTerm, ↓reduceIte, valApp2, valApp1, valOne, ih, modelDoubleCode, PA194Bounded.bits, Bool.toNat_true]
      change (modelNumeral M (PA194Bounded.bits bs) + modelNumeral M (PA194Bounded.bits bs)) + (1 : M) = _
      rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
      congr 1
      omega

theorem modelSentence : M↓[language] ⊧ sentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [lhs,rhs,pack,valApp2,valState,valOne,valZero,valBits,startupClockBits_value]
  rw [←modelNumeralOne]
  exact modelDenseStartup (M := M)
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
end PA194StartupSentence

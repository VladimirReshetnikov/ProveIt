import PA194GuardModel
import PRAEqualityToIPRA
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194NativeGuard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory
open PRAIsZero PRAExhaustion PRAMultiplication PA194GuardModel

def app2 {n : Nat} (f : Code 2) (a b : TermN n) : TermN n := .func f ![a,b]
def app1 {n : Nat} (f : Code 1) (a : TermN n) : TermN n := .func f ![a]
def guarded {n : Nat} (value test : TermN n) : TermN n :=
  app2 mulCode value (app1 isZeroCode test)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp2 {n : Nat} (e : Fin n → M) (f : Code 2) (a b : TermN n) :
    Semiterm.val e Empty.elim (app2 f a b) = F f ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b] := by
  simp only [app2,Semiterm.val_func]
  congr 1
  exact val_term_pair e a b
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem valApp1 {n : Nat} (e : Fin n → M) (f : Code 1) (a : TermN n) :
    Semiterm.val e Empty.elim (app1 f a) = F f (fun _ => Semiterm.val e Empty.elim a) := by
  simp only [app1,Semiterm.val_func]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i
end models

theorem nativeGuardedOfModels {n : Nat} (a b test : TermN n)
    (hmodel : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA] (e : Fin n → M),
      Semiterm.val e Empty.elim test = Structure.func (L := language) (Code.zero 0) Fin.elim0 →
      Semiterm.val e Empty.elim a = Semiterm.val e Empty.elim b) :
    standardTheory ⊢ equalClosureI (guarded a test) (guarded b test) := by
  apply nativeOfClassical
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [guarded,valApp2,valApp1]
  apply guardEqual
  exact hmodel M e
#print axioms nativeGuardedOfModels
end PA194NativeGuard

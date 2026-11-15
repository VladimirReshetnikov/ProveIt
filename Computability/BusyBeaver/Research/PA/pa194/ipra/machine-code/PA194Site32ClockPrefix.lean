import PA194Site32ClockValuations
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
namespace PA194Site32PositiveClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem valTo4 (e : Fin 12 → M) :
    Semiterm.val e Empty.elim to4Term =
      PA194Site32PositiveClock.to4Clock (e 0) (fun i => e i.succ) := by
  simp only [to4Term,A,oneT,num,succT,twice,k,hv e 0,hv e 1,hv e 2,hv e 3,hv e 4,hv e 5,hv e 6,hv e 7,valCr e,valCarry e,valApp2,valState,valOne,
    Semiterm.val_func,Semiterm.val_bvar,Function.comp_def]
  let v := physicalArgs (fun j : Fin 11 => e j.succ)
  have ht : (![v 9,v 10] : Fin 2 → M) =
      (fun i : Fin 2 => v i.succ.succ.succ.succ.succ.succ.succ.succ.succ) := by
    funext i; fin_cases i <;> rfl
  dsimp only [modelQ]
  change _ = _
  rw [ht]
  rfl
#print axioms valTo4
end models
end PA194Site32PositiveClockCode

import PA194Site28DynamicClock
import PA194StartupSentence
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194Site28ClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194StartupSentence PA194Site28DynamicClock
abbrev T := TermN 13
def A (a b : T) : T := app2 addCode a b
def oneT : T := one
def num (n : Nat) : T := state n
def succT (a : T) : T := A a oneT
def k : T := .bvar 0
def count : T := .bvar 1
def args : Fin 11 → T := fun i => .bvar ⟨i.val+2,by omega⟩
def v : Fin 11 → T := physicalArgs args
def root : T :=
  let r := A (num 4) (succT (A (A (num 5) (num 6)) (num 2)))
  let sc := A (succT (succT (succT k))) (succT (succT (v 0)))
  let bc := A (succT (v 0)) (succT (succT (succT k)))
  let c0 := A (num 16) (A (succT (succT (succT (succT k)))) (succT (succT k)))
  let c1 := A (A (num 4) (num 2)) r
  let c2 := A (A (A (num 9) (A (A sc (num 3)) bc)) (num 7)) r
  let scan := A (A (A k (num 2)) (A (num 1) (v 0))) (num 2)
  let j (i : Fin 7) := A oneT (succT (v ⟨i.val+2,by omega⟩))
  let after := A (A (A (A (A (A (j 0) (j 1)) (j 2)) (j 3)) (j 4)) (j 5)) (j 6)
  let prior := A (A (A (A (A c0 c1) c2) (num 16)) scan) (succT (args 8))
  A prior after

def clockTerm : T :=
  let vals : Fin 8 → T := fun i => v ⟨i.val+2,by omega⟩
  let rc := A (num 4) (succT (A (A (num 5) (num 6)) (num 2)))
  let c := root
  let c := A c (A oneT (succT (args 9)))
  let c := A c (A (A count count) count)
  let c := A c (num 3)
  let c := A c (num 2)
  let c := A c (A (A count count) count)
  let c := A c (succT (succT (args 9)))
  let c := A c (.func (PA194CarryFile.costCode 7) vals)
  let c := A c (succT (succT (succT (args 8))))
  let c := A c (succT (succT (args 2)))
  let c := A c (succT (succT k))
  let c := A c (num 2)
  let c := A c (succT (A (succT (num 2)) k))
  let c := A c (A (A oneT k) (num 3))
  let c := A c oneT
  A c (A (num 2) (A (num 3) rc))
def clockCode : Code 13 := compileTerm clockTerm
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelClock (e : Fin 13 → M) :
    F clockCode e = PA194Site28DynamicClock.clock (e 0) (e 1) (fun i => e ⟨i.val+2,by omega⟩) := by
  rw [clockCode,modelCompile]
  simp only [clockTerm,root,A,oneT,num,succT,k,count,args,v,valApp2,valState,valOne,
    Semiterm.val_func,Semiterm.val_bvar,Function.comp_def]
  rfl
#print axioms modelClock
end models
end PA194Site28ClockCode

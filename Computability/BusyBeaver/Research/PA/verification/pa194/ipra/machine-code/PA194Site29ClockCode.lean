import PA194Site29DynamicClock
import PA194StartupSentence
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site29ClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence PA194Site29DynamicClock
abbrev T := TermN 13
def A (a b : T) : T := app2 addCode a b
def oneT : T := one
def num (n : Nat) : T := state n
def succT (a : T) : T := A a oneT
def k : T := .bvar 0
def count : T := .bvar 1
def args : Fin 11 → T := fun i => .bvar ⟨i.val+2,by omega⟩
def v : Fin 11 → T := physicalArgs args
def rc : T := A (num 4) (succT (A (A (num 5) (num 6)) (num 2)))
def root : T :=
  let a0 := A (A oneT oneT) oneT
  let a1 := A a0 a0
  let a2 := A a1 a1
  let a3 := A a2 a2
  let a4 := succT (A a3 a3)
  let a := A a4 a4
  let bb := succT (A a a)
  let cc := succT (A bb bb)
  let d := A cc cc
  let l := A d d
  let l0 := app2 ones k l
  let l1 := succT (A l0 l0)
  let l2 := succT (A l1 l1)
  let l3 := A l2 l2
  let l4 := app2 ones (succT (v 0)) l3
  let l5 := A l4 l4
  let b0 := app2 ones (v 1) l5
  let base := A (succT (A b0 b0)) (succT (A b0 b0))
  let rev : Fin 6 → T := ![v 6,v 5,v 4,v 3,v 2,base]
  let cscan := A (A (A k (num 3)) (succT (succT (v 0)))) (succT (succT (v 1)))
  let firstClock := A (A (num 19) (A (succT (succT (succT (succT k)))) (succT (succT k)))) (A (num 7) rc)
  let ct6 (i : Fin 6) := succT (succT (v ⟨i.val+2,by omega⟩))
  let c6 := A (A (A (A (A (ct6 0) (ct6 1)) (ct6 2)) (ct6 3)) (ct6 4)) (ct6 5)
  let cr := A (A (num 2) (succT (succT (v 7)))) (.func (PA194CarryFile.costCode 5) rev)
  let ct := A (A (succT (succT (v 1))) (succT (succT (v 0)))) (succT (succT (succT k)))
  let fclock := A (A (v 1) (num 2)) (A (A (v 2) (num 2)) (A (A (v 3) (num 2)) (A (A (v 4) (num 2)) (A (A (v 5) (num 2)) (A (A (v 6) (num 2)) zero)))))
  let scan := A (A (A (A (A k (num 2)) (num 1)) (A (v 0) (num 2))) fclock) (v 7)
  let scan := A scan (num 2)
  A (A (A (A (A (A firstClock (A (num 18) cscan)) (A c6 cr)) ct) (A (num 8) rc)) (num 19)) (A scan (succT (v 8)))
def clockTerm : T :=
  let c := root
  let c := A c (A oneT (succT (v 9)))
  let c := A c (A (A count count) count)
  let c := A c (num 3)
  let c := A c (num 2)
  let c := A c (A (A count count) count)
  let c := A c (succT (succT (v 9)))
  let c := A c (succT (succT (succT (v 8))))
  let c := A c (succT (succT (v 7)))
  let c := A c (succT (succT (v 6)))
  let c := A c (succT (succT (v 5)))
  let c := A c (succT (succT (v 4)))
  let c := A c (succT (succT (v 3)))
  let c := A c (succT (succT (v 2)))
  let c := A c (succT (succT (v 1)))
  let c := A c (succT (succT (v 0)))
  let c := A c (succT (succT k))
  let c := A c (num 2)
  let c := A c (succT (A (succT (num 2)) k))
  let c := A c (A (A oneT k) (num 3))
  let c := A c oneT
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
    F clockCode e = PA194Site29DynamicClock.clock (e 0) (e 1) (fun i => e ⟨i.val+2,by omega⟩) := by
  have hv (i : Fin 11) : Semiterm.val e Empty.elim (v i) =
      physicalArgs (fun j : Fin 11 => e ⟨j.val+2,by omega⟩) i := by
    fin_cases i <;> rfl
  have hv6 (a b c d f g : T) :
      (fun i : Fin 6 => Semiterm.val e Empty.elim (![a,b,c,d,f,g] i)) =
      ![Semiterm.val e Empty.elim a,Semiterm.val e Empty.elim b,Semiterm.val e Empty.elim c,
        Semiterm.val e Empty.elim d,Semiterm.val e Empty.elim f,Semiterm.val e Empty.elim g] := by
    funext i; fin_cases i <;> rfl
  rw [clockCode,modelCompile]
  simp only [clockTerm,root,rc,A,oneT,num,succT,k,count,hv,hv6,valApp2,valState,valOne,valZero,
    Semiterm.val_func,Semiterm.val_bvar,Function.comp_def]
  rfl
#print axioms modelClock
end models
end PA194Site29ClockCode

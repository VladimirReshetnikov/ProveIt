import PA194Site32PositivePathExact
import PA194StartupSentence
import DiophantineConsistency.PRATermCompilation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace PA194Site32PositiveClockCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRATermCompilation
open TableDispatch PA194StateOne PA194ZeroRuns PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194StartupSentence
abbrev T := TermN 12
def A (a b : T) : T := app2 addCode a b
def oneT : T := one
def num (n : Nat) : T := state n
def succT (a : T) : T := A a oneT
def twice (a : T) : T := A a a
def k : T := .bvar 0
def args : Fin 11 → T := fun i => .bvar i.succ
def v : Fin 11 → T := physicalArgs args

def leftSeed : T :=
  let a0 := A (A oneT oneT) oneT
  let a1 := twice a0
  let a2 := twice a1
  let a3 := twice a2
  let a4 := succT (twice a3)
  let a5 := succT (twice a4)
  let a6 := succT (twice a5)
  twice (twice a6)
def baseTerm : T :=
  let l0 := app2 ones k leftSeed
  let l1 := succT (twice l0)
  let l2 := succT (twice l1)
  let l3 := twice l2
  let l4 := app2 ones (succT (v 0)) l3
  let l5 := twice l4
  let b0 := app2 ones (v 1) l5
  twice (succT (twice b0))
def qTerm : T := app2 ones (v 8) (.func (fileCode 1) ![v 9,v 10])

def revTerm : Fin 6 → T := ![v 6,v 5,v 4,v 3,v 2,baseTerm]
def vecTerm : Fin 9 → T := ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,twice (twice qTerm)]
def crTerm : T := A (A (num 2) (succT (succT (v 7)))) (.func (PA194CarryFile.costCode 5) revTerm)
def carryTerm : T := A (A (succT k) (.func (PA194CarryFile.costCode 8) vecTerm)) (num 2)
def to4Term : T :=
  let cscan := A (A (A k (num 3)) (succT (succT (v 0)))) (succT (succT (v 1)))
  let c6 := A (A (A (A (A (succT (succT (v 2))) (succT (succT (v 3)))) (succT (succT (v 4)))) (succT (succT (v 5)))) (succT (succT (v 6)))) (succT (succT (v 7)))
  let cr := crTerm
  let ct := A (A (succT (succT (v 1))) (succT (succT (v 0)))) (succT (succT (succT k)))
  let rc := A (num 4) (succT (A (A (num 5) (num 6)) (num 2)))
  let c12 := A (A (num 8) (num 3)) oneT
  let c := A (succT (succT (succT (succT k)))) (succT (succT k))
  let firstClock := A (A (A c12 (num 2)) c) (A (num 3) (A (num 3) rc))
  let c13 := A c12 oneT
  let cR := A (num 4) (A (num 3) rc)
  let c14 := A c12 (num 2)
  let carryClock := carryTerm
  let to4 := A (A (A (A (A (A firstClock (A c13 cscan)) (A c6 cr)) ct) cR) c14) carryClock
  to4

def clockTerm : T :=
  let rc := A (num 4) (succT (A (A (num 5) (num 6)) (num 2)))
  let ret := A (num 1) (A (A (A (A (A (A (A (A oneT (succT (v 7))) (A oneT (succT (v 6)))) (A oneT (succT (v 5)))) (A oneT (succT (v 4)))) (A oneT (succT (v 3)))) (A oneT (succT (v 2)))) (A oneT (succT (v 1)))) (A oneT (succT (v 0))))
  let header12 := A (A oneT (succT (succT k))) (num 3)
  let scan14 := succT (A (succT (num 2)) (succT k))
  let header16 := A (A oneT (succT k)) (num 3)
  let return24 := A (num 3) (A (num 3) rc)
  A (A (A (A (A to4Term ret) header12) scan14) header16) return24

def clockCode : Code 12 := compileTerm clockTerm
end PA194Site32PositiveClockCode

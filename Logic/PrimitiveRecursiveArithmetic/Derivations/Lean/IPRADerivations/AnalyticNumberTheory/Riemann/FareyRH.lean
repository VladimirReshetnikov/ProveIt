import IPRADerivations.AnalyticNumberTheory.Riemann.DivisorMatrices
import IPRADerivations.AnalyticNumberTheory.Riemann.SmokePR

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`FareyRH.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Integer rank discrepancies for ordinary and progression-filtered Farey
fractions. The comparison is by cross multiplication, including the endpoint
1/1 whenever its denominator is admitted. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.FareyRH
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices

/-- Arguments range over positive a ≤ q in the sums below. -/
def eligible : PR 4 := program ["m","b","q","a"] <|
  eqB (modE (v "q") (v "m")) (v "b") *
    call reduced [v "q", modE (v "a") (v "q")]

/-- Number of admitted fractions no greater than u/v. -/
def rank : PR 5 := program ["n","m","b","u","v"] <|
  sumTo "d" (v "n") <| sumTo "e" (v "d"+1) <|
    call eligible [v "m",v "b",v "d"+1,v "e"+1] *
    leB ((v "e"+1)*v "v") ((v "d"+1)*v "u")

def factorial : PR 1 := program ["n"] <| prodTo "i" (v "n") (v "i"+1)

def sizeAtLeastOne : PR 3 := program ["n","m","b"] <|
  call maxR [1, call rank [v "n",v "m",v "b",1,1]]

def scale : PR 3 := program ["n","m","b"] <|
  call factorial [v "n"] * call sizeAtLeastOne [v "n",v "m",v "b"]

/-- Numerator of |a/q − rank(a/q)/N| with scale max(1,N) n!. -/
def displacement : PR 5 := program ["n","m","b","a","q"] <|
  let fac := call factorial [v "n"]
  let left := v "a" * divE fac (v "q") * call sizeAtLeastOne [v "n",v "m",v "b"]
  let right := call rank [v "n",v "m",v "b",v "a",v "q"] * fac
  (left-right)+(right-left)

def moment (squared : Bool) : PR 3 := program ["n","m","b"] <|
  sumTo "d" (v "n") <| sumTo "e" (v "d"+1) <|
    call eligible [v "m",v "b",v "d"+1,v "e"+1] *
    powE (call displacement [v "n",v "m",v "b",v "e"+1,v "d"+1])
      (if squared then 2 else 1)

def error (squared : Bool) : PR 5 := program ["n","m","b","k","c"] <|
  let r := v "k"+1
  let T := call (moment squared) [v "n",v "m",v "b"]
  let W := call scale [v "n",v "m",v "b"]
  if squared then powE (v "n") (v "k") * powE T r - v "c" * powE W (2*r)
  else powE T (2*r) - v "c" * powE W (2*r) * powE (v "n") (r+1)

/-- squared = true gives Franel's criterion, false gives Landau's. -/
def RH (squared : Bool) : Fm PTm 0 :=
  allN (ctx := []) "k" <| exN "c" <| allN "x" <| zeroTest <|
    call (error squared) [v "x"+1,1,0,v "k",v "c"]

/-- Denominators in a reduced progression; constants may depend on m,b,k. -/
def GRH (squared : Bool) : Fm PTm 0 :=
  allN (ctx := []) "m0" <| allN "b" <| allN "k" <| exN "c" <| allN "x" <|
    zeroTest <| call reduced [v "m0"+1,v "b"] *
      call (error squared) [v "x"+1,v "m0"+1,v "b",v "k",v "c"]

-- At order 3 the unfiltered list is 1/3, 1/2, 2/3, 1; W=24.
-- At order 2 in the residue class 2 mod 3 there is only 1/2; W=2.
#guard RiemannIPRA.Smoke.vecEval (moment false) #v[3,1,0] == 4
#guard RiemannIPRA.Smoke.vecEval (moment true) #v[3,1,0] == 8
#guard RiemannIPRA.Smoke.vecEval (moment true) #v[2,3,2] == 1
#guard RiemannIPRA.Smoke.vecEval (moment false) #v[1,3,2] == 0

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.FareyRH

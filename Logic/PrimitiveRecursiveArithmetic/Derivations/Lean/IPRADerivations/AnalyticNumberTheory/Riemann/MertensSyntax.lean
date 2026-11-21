import IPRADerivations.AnalyticNumberTheory.Riemann.DivisorMatrices
import IPRADerivations.AnalyticNumberTheory.Riemann.SmokePR

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`MertensSyntax.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Direct reciprocal-coefficient formulas in the ProveIt object language.
Every polynomial argument uses the four-word code of the primary statements. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.MertensSyntax
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices

/-- Count distinct monic irreducible divisors, optionally weighted by degree. -/
def factorCount (weighted : Bool) : PR 3 := program ["p","e","g"] <|
  sumTo "i" (v "e") <| (if weighted then v "i"+1 else 1) *
    (sumTo "z" (powE (v "p") (v "i"+1)) <|
      call PacketPolynomial.irred [v "p",v "i"+1,v "z"] *
      call PacketPolynomial.divides [v "p",v "i"+1,v "z",v "e",v "g"])

/-- Enumerate squarefree monic polynomial divisors supported on f. -/
def inversePart (odd : Bool) : PR 4 := program ["p","e","d","f"] <|
  sumTo "g" (powE (v "p") (v "e")) <|
    let a := [v "p",v "e",v "g"]
    call supported [v "p",v "e",v "g",v "d",v "f"] *
    eqB (call (factorCount true) a) (v "e") *
    eqB (modE (call (factorCount false) a) 2) (if odd then 1 else 0)

/-- Absolute value or negative-sign bit of a local reciprocal coefficient. -/
def localValue (sign : Bool) : PR 6 := program ["d","H","u","v","p","n"] <|
  let p := v "p"
  let n := v "n"
  let a := [p,call valuation [p,n],v "d",call PacketPolynomial.residueWord [v "d",v "H",v "u",v "v",p]]
  let pos := call (inversePart false) a
  let neg := call (inversePart true) a
  iteE (call primeCode [p] * eqB (modE n p) 0)
    (if sign then leB (pos+1) neg else (pos-neg)+(neg-pos)) (if sign then 0 else 1)

def fieldPart (odd : Bool) : PR 5 := program ["d","H","u","v","n"] <|
  let fieldArgs := [v "d",v "H",v "u",v "v",v "p",v "n"]
  let signCount := sumTo "p" (v "n"+1) (call (localValue true) fieldArgs)
  let amplitude := prodTo "p" (v "n"+1) (call (localValue false) fieldArgs)
  eqB (modE signCount 2) (if odd then 1 else 0) * amplitude

def mobiusPart (odd : Bool) : PR 1 := program ["n"] <|
  let squarefree := allTo "p" (v "n"+1) <|
    1 - call primeCode [v "p"] * eqB (modE (v "n") (powE (v "p") 2)) 0
  let omega := sumTo "p" (v "n"+1) <|
    call primeCode [v "p"] * eqB (modE (v "n") (v "p")) 0
  leB 1 (v "n") * squarefree * eqB (modE omega 2) (if odd then 1 else 0)

def prefixPart (field odd : Bool) : PR 7 := program ["d","H","u","v","q","a","N"] <|
  sumTo "i" (v "N") <|
    let n := v "i"+1
    eqB (modE n (v "q")) (v "a") *
      (if field then call (fieldPart odd) [v "d",v "H",v "u",v "v",n]
       else call (mobiusPart odd) [n])

private def growth {ctx} (field : Bool) (d H u v' q a k c N : E ctx) : E ctx :=
  let xs := [d,H,u,v',q,a,N]
  let pos := call (prefixPart field false) xs
  let neg := call (prefixPart field true) xs
  powE ((pos-neg)+(neg-pos)) (2*(k+1)) - c * powE N (k+2)

def RH : Fm PTm 0 := allN (ctx := []) "k" <| exN "c" <| allN "N" <| zeroTest <|
  growth false 1 0 0 1 1 0 (v "k") (v "c") (v "N")

def progressionGRH : Fm PTm 0 := allN (ctx := []) "k" <| exN "c" <| allN "q" <| allN "a" <|
  allN "N" <| zeroTest <| call reduced [v "q",v "a"] *
    growth false 1 0 0 1 (v "q") (v "a") (v "k") (v "c") (v "N")

def cyclotomicGRH : Fm PTm 0 := allN (ctx := []) "s" <| allN "k" <| exN "c" <|
  allN "N" <| zeroTest <| growth true (v "s"+1) 0 0 1 1 0 (v "k") (v "c") (v "N")

def ERH : Fm PTm 0 := allN (ctx := []) "s" <| allN "H" <| allN "u" <| allN "v" <|
  allN "k" <| exN "c" <| allN "N" <| zeroTest <|
    growth true (v "s"+1) (v "H") (v "u") (v "v") 1 0 (v "k") (v "c") (v "N")

open RiemannIPRA.Smoke in
#guard vecEval (mobiusPart true) #v[3] == 1
open RiemannIPRA.Smoke in
#guard vecEval (inversePart true) #v[2,1,2,1] == 1

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.MertensSyntax

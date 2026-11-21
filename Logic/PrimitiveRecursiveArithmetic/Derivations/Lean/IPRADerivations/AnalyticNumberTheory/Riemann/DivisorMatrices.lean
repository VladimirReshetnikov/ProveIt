import IPRADerivations.AnalyticNumberTheory.Riemann.Hypotheses

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`DivisorMatrices.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Closed first-order witness sentences using finite divisibility matrices.
The absolute value of the determinant is calculated from its two nonnegative
Leibniz sums. Parameter functions build fixed ProveIt syntax trees in Lean. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.DivisorMatrices
open LeanProofs.ConciseIPRA PacketLanguage

/-- Whether every monic irreducible divisor of the degree-e candidate g also
divides the degree-d polynomial f. At a prime p this recognizes exactly the
monomials in the distinct irreducible factors of f, allowing repetition. -/
def supported : PR 5 := program ["p","e","g","d","f"] <|
  allTo "j" (v "e") <| allTo "z" (powE (v "p") (v "j"+1)) <|
    leB (call PacketPolynomial.irred [v "p",v "j"+1,v "z"] *
         call PacketPolynomial.divides [v "p",v "j"+1,v "z",v "e",v "g"])
        (call PacketPolynomial.divides [v "p",v "j"+1,v "z",v "d",v "f"])

def localCount : PR 4 := program ["p","e","d","f"] <|
  sumTo "g" (powE (v "p") (v "e"))
    (call supported [v "p",v "e",v "g",v "d",v "f"])

def valuation : PR 2 := program ["p","n"] <|
  maxTo "j" (v "n"+1)
    (v "j" * eqB (modE (v "n") (powE (v "p") (v "j"))) 0)

/-- Coefficients of the direct polynomial Euler product. -/
def eulerCount : PR 5 := program ["d","H","u","v","n"] <|
  prodTo "p" (v "n"+1) (iteE
    (call primeCode [v "p"] * eqB (modE (v "n") (v "p")) 0)
    (call localCount [v "p",call valuation [v "p",v "n"],v "d",
      call PacketPolynomial.residueWord [v "d",v "H",v "u",v "v",v "p"]]) 1)

def permOK : PR 2 := program ["n","w"] <|
  allTo "i" (v "n") <| allTo "j" (v "i") <|
    1 - eqB (digitE (v "w") (v "n") (v "i")) (digitE (v "w") (v "n") (v "j"))

def inversions : PR 2 := program ["n","w"] <|
  sumTo "i" (v "n") <| sumTo "j" (v "i") <|
    leB (digitE (v "w") (v "n") (v "i")+1) (digitE (v "w") (v "n") (v "j"))

/-- The integer entries use one-based indices. Column one holds a progression
indicator. To disable filtering take q=1,a=0. -/
def entry (fieldWeights : Bool) : PR 8 := program ["d","H","u","v","q","a","i","j"] <|
  iteE (eqB (v "j") 1) (eqB (modE (v "i") (v "q")) (v "a"))
    (eqB (modE (v "j") (v "i")) 0 *
      (if fieldWeights then call eulerCount [v "d",v "H",v "u",v "v",divE (v "j") (v "i")]
       else 1))

def permWeight (fieldWeights : Bool) : PR 8 := program ["d","H","u","v","q","a","n","w"] <|
  prodTo "i" (v "n")
    (call (entry fieldWeights) [v "d",v "H",v "u",v "v",v "q",v "a",v "i"+1,
      digitE (v "w") (v "n") (v "i")+1])

def leibnizPart (fieldWeights odd : Bool) : PR 7 := program ["d","H","u","v","q","a","n"] <|
  sumTo "w" (powE (v "n") (v "n"))
    (call permOK [v "n",v "w"] *
     eqB (modE (call inversions [v "n",v "w"]) 2) (if odd then 1 else 0) *
     call (permWeight fieldWeights) [v "d",v "H",v "u",v "v",v "q",v "a",v "n",v "w"])

def absDet (fieldWeights : Bool) : PR 7 := program ["d","H","u","v","q","a","n"] <|
  let pos := call (leibnizPart fieldWeights false) [v "d",v "H",v "u",v "v",v "q",v "a",v "n"]
  let neg := call (leibnizPart fieldWeights true) [v "d",v "H",v "u",v "v",v "q",v "a",v "n"]
  (pos-neg)+(neg-pos)

def reduced : PR 2 := program ["q","a"] <|
  leB 1 (v "q") * leB (v "a"+1) (v "q") *
  (allTo "j" (v "q"-1) <|
    1 - eqB (modE (v "q") (v "j"+2)) 0 * eqB (modE (v "a") (v "j"+2)) 0)

abbrev SentenceAt (ctx : List String) := Fm PTm ctx.length
def allN {ctx} (name : String) (A : SentenceAt (name::ctx)) : SentenceAt ctx := .all A
def exN {ctx} (name : String) (A : SentenceAt (name::ctx)) : SentenceAt ctx := .ex A
def zeroTest {ctx} (a : E ctx) : SentenceAt ctx := .eq (.app (program ctx a) Syn.var) PTm.zero

private def growth {ctx} (amp k c n : E ctx) : E ctx :=
  powE amp (2*(k+1)) - c * powE n (k+2)

/-- RH via the classical Redheffer matrices. -/
def RH : Fm PTm 0 := allN (ctx := []) "k" <| exN "c" <| allN "x" <| zeroTest <|
  growth (call (absDet false) [1,0,0,1,1,0,v "x"+1]) (v "k") (v "c") (v "x"+1)

/-- Dirichlet GRH via the first-column progression masks; one c for every q,a. -/
def progressionGRH : Fm PTm 0 := allN (ctx := []) "k" <| exN "c" <| allN "q" <| allN "a" <|
  allN "x" <| zeroTest <| call reduced [v "q",v "a"] *
    growth (call (absDet false) [1,0,0,1,v "q",v "a",v "x"+1]) (v "k") (v "c") (v "x"+1)

/-- A second Dirichlet form uses X^m-1 and a conductor-dependent c. -/
def cyclotomicGRH : Fm PTm 0 := allN (ctx := []) "s" <| allN "k" <| exN "c" <| allN "x" <| zeroTest <|
  growth (call (absDet true) [v "s"+1,0,0,1,1,0,v "x"+1]) (v "k") (v "c") (v "x"+1)

def ERH : Fm PTm 0 := allN (ctx := []) "s" <| allN "H" <| allN "u" <| allN "v" <|
  allN "k" <| exN "c" <| allN "x" <| zeroTest <|
    growth (call (absDet true) [v "s"+1,v "H",v "u",v "v",1,0,v "x"+1]) (v "k") (v "c") (v "x"+1)

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.DivisorMatrices

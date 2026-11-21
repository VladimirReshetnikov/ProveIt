import IPRADerivations.AnalyticNumberTheory.Riemann.PacketLanguage

/-! Imported from the packet `analytic-number-theory/riemann_hypotheses_ipra_2026-11-20`,
`PolynomialCode.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-!
The primitive-recursive symbols compiled here use the five constructors of
ProveIt's PR syntax. A degree-e monic polynomial over F_p is represented by
a base-p word for the e coefficients below the leading 1.
-/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketPolynomial

open LeanProofs.ConciseIPRA PacketLanguage

/-- Base-p encoding of the reduction of the lower coefficients. The leading
monomial is implicit. H+2 is the base of the two input words. -/
def residueWord : PR 5 := program ["d","H","u","v","p"] <|
  sumTo "i" (v "d") <|
    (modE
      (digitE (v "u") (v "H"+2) (v "i") +
        v "p" - modE (digitE (v "v") (v "H"+2) (v "i")) (v "p"))
      (v "p")) * powE (v "p") (v "i")

/-- Read coefficient j of the monic polynomial (d,w) at base p. -/
def monicAt : PR 4 := program ["p","d","w","j"] <|
  iteE (eqB (v "j") (v "d")) 1
    (iteE (leB (v "j"+1) (v "d")) (digitE (v "w") (v "p") (v "j")) 0)

/-- Compare (e,a)(h,b) with (e+h,w) coefficient by coefficient. -/
def productEquals : PR 6 := program ["p","e","a","h","b","w"] <|
  allTo "j" (v "e"+v "h"+1) <|
    eqB
      (modE
        (sumTo "i" (v "j"+1) <|
          call monicAt [v "p",v "e",v "a",v "i"] *
          call monicAt [v "p",v "h",v "b",v "j"-v "i"])
        (v "p"))
      (call monicAt [v "p",v "e"+v "h",v "w",v "j"])

/-- Test if the monic (e,a) divides the monic (d,w), by enumerating
the p^(d−e) possible monic quotients. -/
def divides : PR 5 := program ["p","e","a","d","w"] <|
  leB (v "e") (v "d") *
    (anyTo "b" (powE (v "p") (v "d"-v "e")) <|
      call productEquals [v "p",v "e",v "a",v "d"-v "e",v "b",v "w"])

/-- A positive-degree monic polynomial is irreducible iff it has no proper
monic divisor of positive degree. -/
def irred : PR 3 := program ["p","e","a"] <|
  leB 1 (v "e") *
    (allTo "t" (v "e"-1) <|
      allTo "b" (powE (v "p") (v "t"+1)) <|
        eqB (call divides [v "p",v "t"+1,v "b",v "e",v "a"]) 0)

/-- Sum the degrees of the distinct factors of F of degree dividing k. -/
def factorSum : PR 4 := program ["p","k","d","w"] <|
  sumTo "t" (v "d") <|
    eqB (modE (v "k") (v "t"+1)) 0 * (v "t"+1) *
      (sumTo "a" (powE (v "p") (v "t"+1)) <|
        call irred [v "p",v "t"+1,v "a"] *
        call divides [v "p",v "t"+1,v "a",v "d",v "w"])

/-- At a prime p and k>0 this is deg gcd(F, X^(p^k)-X). For k=0 it is
deg gcd(F,0)=d. Values at p<2 are totalized to zero. -/
def rootDegree : PR 6 := program ["d","H","u","v","p","k"] <|
  iteE (leB 2 (v "p"))
    (iteE (eqB (v "k") 0) (v "d")
      (call factorSum [v "p",v "k",v "d",
        call residueWord [v "d",v "H",v "u",v "v",v "p"]]))
    0

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketPolynomial

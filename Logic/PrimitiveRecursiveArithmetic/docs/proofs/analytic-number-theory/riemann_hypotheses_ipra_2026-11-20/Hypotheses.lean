import Hierarchy
import PolynomialCode

/-! The three primary statements. The bit tested by each closed equality is a
truncated excess (zero precisely when the requested inequality holds). -/
namespace RiemannIPRA
open LeanProofs.ConciseIPRA
open PacketLanguage

/-- Integer whose logarithm is the polynomial Chebyshev sum. -/
def primeProduct : PR 5 := program ["d","H","u","v","x"] <|
  prodTo "p" (v "x"+1) (iteE (call primeCode [v "p"])
    (prodTo "j" (call logCode [v "x"]) (iteE
      (leB (powE (v "p") (v "j"+1)) (v "x"))
      (powE (v "p") (call PacketPolynomial.rootDegree
        [v "d",v "H",v "u",v "v",v "p",v "j"+1])) 1)) 1)

def logProduct : PR 5 := program ["d","H","u","v","x"] <|
  call logCode [call primeProduct [v "d",v "H",v "u",v "v",v "x"]]

def dyadicGap : PR 5 := program ["d","H","u","v","n"] <|
  let a := call logProduct [v "d",v "H",v "u",v "v",2*v "n"]
  let b := 2*call logProduct [v "d",v "H",v "u",v "v",v "n"]
  (a-b)+(b-a)

def allowance : PR 3 := program ["d","H","n"] <|
  1000 * powE (v "d"+1) 4 * powE (v "H"+2) 2 *
    powE (1 + call logCode [2*v "n"]) 2

/-- Ordered external arguments d−1, H, u, v, n−100. Every variable ranges
over all naturals. The zero-test is the arithmetic matrix of all three sentences. -/
def excess : PR 5 := program ["degreeOffset","H","u","v","start"] <|
  let d := v "degreeOffset" + 1
  let n := v "start" + 100
  powE (call dyadicGap [d,v "H",v "u",v "v",n]) 2 -
    n * powE (call allowance [d,v "H",n]) 2

def RH : Fm PTm 0 := RHHierarchy.RHOf excess
def GRH : Fm PTm 0 := RHHierarchy.GRHOf excess
def ERH : Fm PTm 0 := RHHierarchy.ERHOf excess

theorem erh_implies_grh : Prf PRAAx [] (.imp ERH GRH) :=
  RHHierarchy.erh_implies_grh excess

theorem grh_implies_rh : Prf PRAAx [] (.imp GRH RH) :=
  RHHierarchy.grh_implies_rh excess

theorem erh_implies_rh : Prf PRAAx [] (.imp ERH RH) :=
  RHHierarchy.erh_implies_rh excess

end RiemannIPRA

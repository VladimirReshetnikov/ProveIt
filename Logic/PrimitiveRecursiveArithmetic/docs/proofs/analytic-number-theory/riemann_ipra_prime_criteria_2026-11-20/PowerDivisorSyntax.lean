import MertensSyntax

/-! Closed iPRA presentations obtained by convolution of reciprocal Euler
coefficients with the indicator of the h-th powers (h ≥ 2). -/
namespace PowerDivisorSyntax
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices

/-- The positive and negative coefficient counts of the twisted local-global
product. Summing signed counts retains multiplicities at every prime of F. -/
def coefficientPart (field odd : Bool) : PR 6 := program ["d","H","u","v","h","n"] <|
  sumTo "j" (v "n") <|
    let power := powE (v "j"+1) (v "h")
    let quotient := divE (v "n") power
    eqB (modE (v "n") power) 0 *
      (if field then call (MertensSyntax.fieldPart odd) [v "d",v "H",v "u",v "v",quotient]
       else call (MertensSyntax.mobiusPart odd) [quotient])

/-- Direct signed rational-prime formula, including λ(n) at h=2. -/
def rationalPart (odd : Bool) : PR 2 := program ["h","n"] <|
  let residue := fun {ctx : List String} (p n h : E ctx) => modE (call valuation [p,n]) h
  let allowed := allTo "p" (v "n"+1) <|
    leB (call primeCode [v "p"]) (leB (residue (v "p") (v "n") (v "h")) 1)
  let negativeCount := sumTo "p" (v "n"+1) <| call primeCode [v "p"] *
    eqB (residue (v "p") (v "n") (v "h")) 1
  leB 1 (v "n") * allowed * eqB (modE negativeCount 2) (if odd then 1 else 0)

inductive Source | rationalDivisors | rationalLocal | polynomial

def prefixPart (src : Source) (odd : Bool) : PR 8 := program ["d","H","u","v","h","q","a","N"] <|
  sumTo "i" (v "N") <|
    let n := v "i"+1
    eqB (modE n (v "q")) (v "a") * (match src with
      | .rationalLocal => call (rationalPart odd) [v "h",n]
      | .rationalDivisors => call (coefficientPart false odd) [v "d",v "H",v "u",v "v",v "h",n]
      | .polynomial => call (coefficientPart true odd) [v "d",v "H",v "u",v "v",v "h",n])

inductive Family | riemann | progression | cyclotomic | dedekind

private def matrix {ctx} (src : Source) (d H u v' h q a N k c : E ctx) : E ctx :=
  let args := [d,H,u,v',h,q,a,N]
  let pos := call (prefixPart src false) args
  let neg := call (prefixPart src true) args
  powE ((pos-neg)+(neg-pos)) (2*(k+1)) - c*powE N (k+2)

private def exponent {ctx : List String} (offset : Option Nat) (z : E ctx) : E ctx :=
  match offset with | none => z+2 | some j => E.num (j+2)

/-- For some j the exponent is j+2. For none one witness works
simultaneously for every exponent h ≥ 2. -/
def statement (family : Family) (offset : Option Nat) (direct : Bool := false) : Fm PTm 0 :=
  let rational := if direct then Source.rationalLocal else Source.rationalDivisors
  match family with
  | .riemann => allN (ctx := []) "k" <| exN "c" <| allN "z" <| allN "N" <| zeroTest <|
      matrix rational 1 0 0 1 (exponent offset (v "z")) 1 0 (v "N") (v "k") (v "c")
  | .progression => allN (ctx := []) "k" <| exN "c" <| allN "z" <| allN "q" <| allN "a" <|
      allN "N" <| zeroTest <| call reduced [v "q",v "a"] *
        matrix rational 1 0 0 1 (exponent offset (v "z")) (v "q") (v "a") (v "N") (v "k") (v "c")
  | .cyclotomic => allN (ctx := []) "s" <| allN "k" <| exN "c" <| allN "z" <| allN "N" <|
      zeroTest <| matrix .polynomial (v "s"+1) 0 0 1 (exponent offset (v "z")) 1 0 (v "N") (v "k") (v "c")
  | .dedekind => allN (ctx := []) "s" <| allN "H" <| allN "u" <| allN "v" <|
      allN "k" <| exN "c" <| allN "z" <| allN "N" <| zeroTest <|
        matrix .polynomial (v "s"+1) (v "H") (v "u") (v "v") (exponent offset (v "z")) 1 0 (v "N") (v "k") (v "c")

end PowerDivisorSyntax

import DivisorMatrices
import Lagarias

/-! Rational Gram energy of the polynomial or progression Mertens sequence.
All sums are over naturals and the denominator of the energy is (N!)². -/
namespace FareyEnergy
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices

/-- The number of ordered residue pairs (x,y) mod d with gcd(x,y,d)=1. -/
def jordanTwo : PR 1 := program ["d"] <|
  sumTo "x" (v "d") <| sumTo "y" (v "d") <| allTo "j" (v "d"-1) <|
    let t := v "j"+2
    1 - (eqB (modE (v "d") t) 0 * eqB (modE (v "x") t) 0 * eqB (modE (v "y") t) 0)

/-- Numerator of the sum over multiples of j, separately for both signs of
the determinant. All quotients N!/k here are exact, with 1 ≤ k ≤ N. -/
def multiplePart (fieldWeights odd : Bool) : PR 8 :=
  program ["d","H","u","v","q","a","N","j"] <|
    sumTo "i" (v "N") <|
      let k := v "i"+1
      eqB (modE k (v "j")) 0 * divE (call Lagarias.factorial [v "N"]) k *
        call (leibnizPart fieldWeights odd)
          [v "d",v "H",v "u",v "v",v "q",v "a",divE (v "N") k]

def energyNumerator (fieldWeights : Bool) : PR 7 := program ["d","H","u","v","q","a","N"] <|
  sumTo "t" (v "N") <|
    let j := v "t"+1
    let xs := [v "d",v "H",v "u",v "v",v "q",v "a",v "N",j]
    let plus := call (multiplePart fieldWeights false) xs
    let minus := call (multiplePart fieldWeights true) xs
    call jordanTwo [j] * powE ((plus-minus)+(minus-plus)) 2

private def excess {ctx} (fieldWeights : Bool) (d H u v' q a k c N : E ctx) : E ctx :=
  let r := k+1
  powE (call (energyNumerator fieldWeights) [d,H,u,v',q,a,N]) r -
    c * powE (call Lagarias.factorial [N]) (2*r) * powE N (r+1)

def RH : Fm PTm 0 := allN (ctx := []) "k" <| exN "c" <| allN "t" <| zeroTest <|
  excess false 1 0 0 1 1 0 (v "k") (v "c") (v "t"+1)

def progressionGRH : Fm PTm 0 := allN (ctx := []) "k" <| exN "c" <| allN "q" <|
  allN "a" <| allN "t" <| zeroTest <|
    call reduced [v "q",v "a"] *
      excess false 1 0 0 1 (v "q") (v "a") (v "k") (v "c") (v "t"+1)

def cyclotomicGRH : Fm PTm 0 := allN (ctx := []) "s" <| allN "k" <| exN "c" <|
  allN "t" <| zeroTest <|
    excess true (v "s"+1) 0 0 1 1 0 (v "k") (v "c") (v "t"+1)

def ERH : Fm PTm 0 := allN (ctx := []) "s" <| allN "H" <| allN "u" <| allN "v" <|
  allN "k" <| exN "c" <| allN "t" <| zeroTest <|
    excess true (v "s"+1) (v "H") (v "u") (v "v") 1 0 (v "k") (v "c") (v "t"+1)
end FareyEnergy

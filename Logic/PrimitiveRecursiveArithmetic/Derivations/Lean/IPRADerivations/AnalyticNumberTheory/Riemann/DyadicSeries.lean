import IPRADerivations.AnalyticNumberTheory.Riemann.DivisorMatrices

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`DyadicSeries.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Weighted series of reciprocal Euler coefficients, encoded wholly by
dyadic rationals. The quantified convergence rate depends only on the
displayed numerical witness. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.DyadicSeries
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices

def level : PR 2 := program ["r","N"] <| divE (call logCode [v "N"]) (2*v "r")
def denominator : PR 2 := program ["r","N"] <|
  powE 2 ((v "r"+1) * call level [v "r",v "N"])

def partAt (field odd : Bool) : PR 7 := program ["d","H","u","v","q","a","N"] <|
  iteE (v "N") (call (leibnizPart field odd) [v "d",v "H",v "u",v "v",v "q",v "a",v "N"]) 0

/-- The numerator sums first differences, normalized to the final denominator. -/
def seriesPart (field odd : Bool) : PR 8 := program ["d","H","u","v","q","a","r","N"] <|
  sumTo "i" (v "N") <|
    let args := [v "d",v "H",v "u",v "v",v "q",v "a"]
    let inc := call (partAt field odd) (args ++ [v "i"+1]) +
               call (partAt field (!odd)) (args ++ [v "i"])
    let levels := call level [v "r",v "N"] - call level [v "r",v "i"+1]
    inc * powE 2 ((v "r"+1)*levels)

/-- Common arguments for the two versions. Mode selects a bound for a
prefix or a tail estimate between cutoffs P and Q given by offsets. -/
def matrix (field withRate : Bool) : PR 12 :=
  program ["d","H","u","v","q","a","r","K","N","t","i","j"] <|
    let args := [v "d",v "H",v "u",v "v",v "q",v "a",v "r"]
    let signedDiff := fun (a b : E _) => (a-b)+(b-a)
    let pos := fun (n : E _) => call (seriesPart field false) (args ++ [n])
    let neg := fun (n : E _) => call (seriesPart field true) (args ++ [n])
    let den := fun (n : E _) => call denominator [v "r",n]
    let limit := powE 2 (v "K") * den (v "N")
    let initial := signedDiff (pos (v "N")) (neg (v "N")) - limit
    if withRate then
      let threshold := powE 2 (4*v "r"*(v "t"+v "K"))
      let p := threshold + v "i"
      let q := threshold + v "j"
      let lhs := pos p * den q + neg q * den p
      let rhs := neg p * den q + pos q * den p
      initial + (powE 2 (v "t") * signedDiff lhs rhs - den p * den q)
    else initial

inductive Family | riemann | progression | cyclotomic | dedekind

/-- In a progression family K precedes all modulus and residue quantifiers. -/
def statement (family : Family) (withRate : Bool) : Fm PTm 0 :=
  let finish := fun {ctx : List String} (field : Bool)
    (d H u v' q a r K guard : E ("j"::"i"::"t"::"N"::ctx)) =>
    allN (ctx := ctx) "N" <| allN "t" <| allN "i" <| allN "j" <| zeroTest <|
      guard * call (matrix field withRate) [d,H,u,v',q,a,r,K,.var ⟨3, by simp⟩,.var ⟨2, by simp⟩,.var ⟨1, by simp⟩,.var ⟨0, by simp⟩]
  match family with
  | .riemann => allN (ctx := []) "k" <| exN "K" <| finish (ctx := ["K","k"]) false 1 0 0 1 1 0 (v "k"+1) (v "K") 1
  | .progression => allN (ctx := []) "k" <| exN "K" <| allN "q" <| allN "a" <|
      finish (ctx := ["a","q","K","k"]) false 1 0 0 1 (v "q") (v "a") (v "k"+1) (v "K") (call reduced [v "q",v "a"])
  | .cyclotomic => allN (ctx := []) "s" <| allN "k" <| exN "K" <|
      finish (ctx := ["K","k","s"]) true (v "s"+1) 0 0 1 1 0 (v "k"+1) (v "K") 1
  | .dedekind => allN (ctx := []) "s" <| allN "H" <| allN "u" <| allN "v" <| allN "k" <| exN "K" <|
      finish (ctx := ["K","k","v","u","H","s"]) true (v "s"+1) (v "H") (v "u") (v "v") 1 0 (v "k"+1) (v "K") 1

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.DyadicSeries

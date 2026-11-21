import IPRADerivations.AnalyticNumberTheory.Riemann.Hypotheses
import IPRADerivations.AnalyticNumberTheory.Riemann.RHCounterexamples

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`Lagarias.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Rational lower and upper enclosures for Lagarias's divisor-sum criterion.
The matrices below are compiled to ProveIt PR symbols; all denominators are
positive on the indicated inputs. Analytic correctness is proved in the report. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.Lagarias
open LeanProofs.ConciseIPRA PacketLanguage

def factorial : PR 1 := program ["n"] <| prodTo "j" (v "n") (v "j" + 1)

def harmonicNumerator : PR 1 := program ["n"] <|
  sumTo "j" (v "n") (divE (call factorial [v "n"]) (v "j" + 1))

def divisorSum : PR 1 := program ["n"] <|
  sumTo "j" (v "n") ((v "j" + 1) * eqB (modE (v "n") (v "j" + 1)) 0)

/-- Common denominator for both endpoint sums for log(H_n).
Here b = m*n! and a = n!*(H_n-1). -/
def commonDen : PR 3 := program ["a","b","m"] <|
  prodTo "j" (v "m" + 1) (v "b" + v "j" * v "a")

/-- Lower/upper comparisons are tagged at construction in Lean, yielding two
fixed PR trees. All subtractions in the source language are truncated. -/
def test (upper : Bool) : PR 2 := program ["s","k"] <|
  let n := if upper then v "s" + 1 else v "s" + 2
  let m := 2 * n + v "k" + 1
  let B := call factorial [n]
  let A := call harmonicNumerator [n]
  let a := A - B
  let b := m * B
  let D := call commonDen [a,b,m]
  let logNumer := a * (sumTo "i" m <|
    let nn := if upper then v "s" + 1 else v "s" + 2
    let mm := 2 * nn + v "k" + 1
    let BB := call factorial [nn]
    let aa := call harmonicNumerator [nn] - BB
    let bb := mm * BB
    let j := if upper then v "i" else v "i" + 1
    divE (call commonDen [aa,bb,mm]) (bb + j * aa))
  let en := if upper then powE b m else powE (b + A) m
  let ed := if upper then powE (b - A) m else powE b m
  let lhs := call divisorSum [n] * B * ed * D
  let rhs := A * ed * D + B * en * logNumer
  (if upper then lhs else lhs + 1) - rhs

private def zeroTest (r : PR 2) : Fm PTm 2 :=
  .eq (.app r (Fin.cases (Syn.var 1) (fun _ => Syn.var 0))) PTm.zero

/-- Weak closed-order form with arbitrary external precision. -/
def upperRH : Fm PTm 0 := .all (.all (zeroTest (test true)))

/-- Positive strict form, with a precision witness for every n ≥ 2. -/
def strictRH : Fm PTm 0 := .all (.ex (zeroTest (test false)))

theorem upper_no_counterexample :
    Prf PRAAx [] (Fm.iff upperRH (RHCounterexamples.neg (RHCounterexamples.counter upperRH))) :=
  RHCounterexamples.no_counterexample (.binder (.binder (.matrix _)))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.Lagarias

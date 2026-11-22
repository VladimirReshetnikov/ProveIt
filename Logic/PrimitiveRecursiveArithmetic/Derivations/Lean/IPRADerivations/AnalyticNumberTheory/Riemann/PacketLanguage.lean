import ConciseIPRA.PR

/-! Imported from the packet `analytic-number-theory/riemann_hypotheses_ipra_2026-11-20`,
`PacketLanguage.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! A small front end for constructing the repository's actual PR symbols.
Names below are checked against their finite scope at elaboration. A bounded
aggregate adds a counter to the scope; compilation supplies the accumulator
separately, so nested ranges can read every outer parameter. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketLanguage
open LeanProofs.ConciseIPRA

abbrev R := PR
def zeroR {n : Nat} : R n := .comp .zero Fin.elim0
def sucR {n : Nat} (f : R n) : R n := .comp .succ (fun _ => f)
def numeral {n : Nat} : Nat → R n
  | 0 => zeroR
  | k+1 => sucR (numeral k)
def binary {n : Nat} (f : R 2) (x y : R n) : R n :=
  .comp f (Fin.cases x (fun _ => y))
def addR : R 2 := .prec (.proj 0) (sucR (.proj 1))
def mulR : R 2 := .prec zeroR (binary addR (.proj 1) (.proj 2))
def predR : R 1 := .prec .zero (.proj 0)
def reversedSub : R 2 := .prec (.proj 0) (.comp predR (fun _ => .proj 1))
def subR : R 2 := binary reversedSub (.proj 1) (.proj 0)
def powR : R 2 := binary
  (.prec (numeral 1) (binary mulR (.proj 1) (.proj 2))) (.proj 1) (.proj 0)
def isZeroR : R 1 := .prec (numeral 1) zeroR
def clipR : R 1 := .prec .zero (numeral 1)
def maxR : R 2 := binary addR (.proj 0) (binary subR (.proj 1) (.proj 0))

inductive Aggregate where
  | total | product | maximum | someBit | everyBit

inductive E : List String → Type where
  | var {ctx : List String} (i : Fin ctx.length) : E ctx
  | num {ctx : List String} (k : Nat) : E ctx
  | app {ctx : List String} {k : Nat} (f : PR k) (args : Fin k → E ctx) : E ctx
  | agg {ctx : List String} (kind : Aggregate) (name : String) (bound : E ctx) (body : E (name :: ctx)) : E ctx

def program (ctx : List String) : E ctx → R ctx.length
  | .var i => .proj i
  | .num k => numeral k
  | .app f args => .comp f (fun i => program ctx (args i))
  | .agg kind name bound body =>
    let b := program (name :: ctx) body
    let atStep : R (ctx.length + 2) :=
      .comp b (Fin.cases (.proj 0) (fun i => .proj i.succ.succ))
    let acc : R (ctx.length + 2) := .proj 1
    let init : R ctx.length := match kind with
      | .product | .everyBit => numeral 1
      | _ => zeroR
    let step := match kind with
      | .total => binary addR acc atStep
      | .product => binary mulR acc atStep
      | .maximum => binary maxR acc atStep
      | .someBit => .comp clipR (fun _ => binary addR acc atStep)
      | .everyBit => binary mulR acc (.comp clipR (fun _ => atStep))
    .comp (.prec init step) (Fin.cases (program ctx bound) (fun i => .proj i))

variable {ctx : List String}
def v (name : String) (h : ctx.idxOf name < ctx.length := by decide) : E ctx :=
  .var ⟨ctx.idxOf name, h⟩
def call {k : Nat} (f : R k) (args : List (E ctx)) (h : args.length = k := by rfl) : E ctx :=
  .app f (fun i => args[i.val]'(h ▸ i.isLt))

instance {k : Nat} : OfNat (E ctx) k := ⟨.num k⟩
instance : Add (E ctx) := ⟨fun a b => call addR [a,b]⟩
instance : Sub (E ctx) := ⟨fun a b => call subR [a,b]⟩
instance : Mul (E ctx) := ⟨fun a b => call mulR [a,b]⟩
def powE (a b : E ctx) := call powR [a,b]
instance : HPow (E ctx) (E ctx) (E ctx) := ⟨fun a b => call powR [a,b]⟩
def leB (a b : E ctx) : E ctx := call isZeroR [a-b]
def eqB (a b : E ctx) : E ctx := leB a b * leB b a
def iteE (test yes no : E ctx) : E ctx := call clipR [test] * yes + call isZeroR [test] * no

def sumTo (j : String) (b : E ctx) (s : E (j::ctx)) := E.agg .total j b s
def prodTo (j : String) (b : E ctx) (s : E (j::ctx)) := E.agg .product j b s
def maxTo (j : String) (b : E ctx) (s : E (j::ctx)) := E.agg .maximum j b s
def anyTo (j : String) (b : E ctx) (s : E (j::ctx)) := E.agg .someBit j b s
def allTo (j : String) (b : E ctx) (s : E (j::ctx)) := E.agg .everyBit j b s

/-- Quotient by positive b is the largest candidate i ≤ a with i*b ≤ a.
Division by zero gives zero; the residual a - (a / 0) * 0 equals a. -/
def quotientR := program ["a","b"] <|
  iteE (v "b") (maxTo "i" (v "a"+1) (v "i" * leB (v "i"*v "b") (v "a"))) 0
def divE (a b : E ctx) := call quotientR [a,b]
def modE (a b : E ctx) := a - divE a b * b
def digitE (word base index : E ctx) := modE (divE word (base ^ index)) base

/-- Floor of the binary logarithm on positive integers, totalized at zero. -/
def logCode := program ["x"] <|
  maxTo "i" (v "x" + 1) (v "i" * leB (powE 2 (v "i")) (v "x"))
def primeCode := program ["p"] <|
  leB 2 (v "p") * allTo "i" (v "p" - 2)
    (eqB (eqB (modE (v "p") (v "i"+2)) 0) 0)
end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketLanguage

import DiophantineConsistency.PRALanguage
import Foundation.FirstOrder.Arithmetic.Schemata

/-! Object-theory primitives for primitive-recursive arithmetic. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRATheory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage

/-- A positional member of a finite code list. -/
def getCode : {n m : ℕ} → Codes n m → Fin m → Code n
  | _, _, .nil _, i => Fin.elim0 i
  | _, _, .cons h t, i => Fin.cases h (getCode t) i

abbrev TermN (n : ℕ) := Semiterm language Empty n

def applyCode {n m : ℕ} (c : Code m) (v : Fin m → TermN n) : TermN n := .func c v

def vars (n : ℕ) : Fin n → TermN n := fun i => .bvar i

def equalClosure {n : ℕ} (a b : TermN n) : Sentence language :=
  ∀⁰* (Semiformula.rel Language.ORing.Rel.eq ![a, b])

def zeroEquation (n : ℕ) : Sentence language :=
  equalClosure (applyCode (.zero n) (vars n)) (applyCode (.zero 0) Fin.elim0)

def projectionEquation {n : ℕ} (i : Fin n) : Sentence language :=
  equalClosure (applyCode (.proj i) (vars n)) (.bvar i)

def compositionEquation {m n : ℕ} (f : Code m) (g : Codes n m) : Sentence language :=
  equalClosure (applyCode (.comp f g) (vars n))
    (applyCode f (fun i => applyCode (getCode g i) (vars n)))

def recursionBaseEquation {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentence language :=
  let params : Fin n → TermN n := vars n
  equalClosure (applyCode (.prec f g) (Fin.cases (applyCode (.zero 0) Fin.elim0) params))
    (applyCode f params)

def recursionStepEquation {n : ℕ} (f : Code n) (g : Code (n+2)) : Sentence language :=
  let params : Fin n → TermN (n+1) := fun i => .bvar i.succ
  let counter : TermN (n+1) := .bvar 0
  let previous := applyCode (.prec f g) (Fin.cases counter params)
  equalClosure (applyCode (.prec f g)
    (Fin.cases (applyCode .succ (fun _ => counter)) params))
    (applyCode g (Fin.cases counter (Fin.cases previous params)))

inductive DefiningEquation : Theory language
  | zero (n : ℕ) : DefiningEquation (zeroEquation n)
  | projection {n : ℕ} (i : Fin n) : DefiningEquation (projectionEquation i)
  | composition {m n : ℕ} (f : Code m) (g : Codes n m) :
      DefiningEquation (compositionEquation f g)
  | recursionBase {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquation (recursionBaseEquation f g)
  | recursionStep {n : ℕ} (f : Code n) (g : Code (n+2)) :
      DefiningEquation (recursionStepEquation f g)

/-- The fixed function equations plus all language equality and open induction.
Successor and order axioms remain separate until explicitly supplied. -/
def core : Theory language :=
  (𝗘𝗤 language) ∪ DefiningEquation ∪ InductionScheme language Semiformula.Open

end DiophantineConsistency.PRATheory

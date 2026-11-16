import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Exact object-language FLT targets

Blueprint status: these sources were NOT compiled in the delivery environment.
They use the inspected ProveIt interfaces at commit
bb4427b10219ad61e0d2875fdde04bcd23b47ec6 (Lean/Mathlib v4.32.0).

This file defines actual primitive-recursive function codes and first-order
formulas. It does not assert or assume the four missing `Prf PRAAx` values.
The paper supplies the human proofs and the explicit work needed to construct
them. In particular, there is no implication from an ambient Lean arithmetic
theorem to one of these proof objects.
-/

namespace FLTIPRA.ObjectLanguage

open LeanProofs.ConciseIPRA
open scoped Fm

/-- A constant function code of arbitrary arity. -/
def constCode (k : Nat) : Nat → PR k
  | 0 => .comp .zero (fun i => Fin.elim0 i)
  | n + 1 => .comp .succ ![constCode k n]

/-- addCode(n,x)=n+x; the recursion argument is first. -/
def addCode : PR 2 :=
  .prec (.proj 0) (.comp .succ ![.proj 1])

/-- mulCode(n,x)=n*x. Step arguments are (counter,accumulator,x). -/
def mulCode : PR 2 :=
  .prec (constCode 1 0) (.comp addCode ![.proj 1, .proj 2])

/-- powCode(n,x)=x^n, with exponent first and base second. -/
def powCode : PR 2 :=
  .prec (constCode 1 1) (.comp mulCode ![.proj 1, .proj 2])

def numeral (scope n : Nat) : PTm scope :=
  PTm.app (constCode 0 n) (fun i => Fin.elim0 i)

def addTerm {scope : Nat} (x y : PTm scope) : PTm scope :=
  PTm.app addCode ![x, y]

def mulTerm {scope : Nat} (x y : PTm scope) : PTm scope :=
  PTm.app mulCode ![x, y]

def powTerm {scope : Nat} (x n : PTm scope) : PTm scope :=
  PTm.app powCode ![n, x]

def nonzero {scope : Nat} (x : PTm scope) : Fm PTm scope :=
  Fm.imp (Fm.eq x PTm.zero) Fm.bot

/-- FLT matrix for arbitrary terms. Nonzero and positive coincide in N. -/
def fermatMatrix {scope : Nat} (n x y z : PTm scope) : Fm PTm scope :=
  Fm.imp (nonzero x)
    (Fm.imp (nonzero y)
      (Fm.imp (nonzero z)
        (Fm.imp
          (Fm.eq (addTerm (powTerm x n) (powTerm y n)) (powTerm z n))
          Fm.bot)))

/-- An open formula with free variables 0=x, 1=y, 2=z. -/
def fixedMatrix (n : Nat) : Fm PTm 3 :=
  fermatMatrix (numeral 3 n) (PTm.var 0) (PTm.var 1) (PTm.var 2)

/-- Universal closure of the fixed-exponent FLT matrix. -/
def fixedSentence (n : Nat) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (fixedMatrix n)))

/-- The exact requested theorem type for a fixed exponent. -/
abbrev InternalFLT (n : Nat) : Prop :=
  Prf PRAAx ([] : List (Fm PTm 0)) (fixedSentence n)

/-- d divides n, with witness k and a bound-free existential formula.
The proof uses bounded quotient selection, but the specification need not.
-/
def dividesFormula {scope : Nat} (d : Nat) (n : PTm scope) : Fm PTm scope :=
  Fm.ex (Fm.eq (mulTerm (numeral (scope + 1) d) (PTm.var 0))
    (Syn.shift n))

def coveredFormula {scope : Nat} (n : PTm scope) : Fm PTm scope :=
  Fm.or (dividesFormula 3 n)
    (Fm.or (dividesFormula 4 n)
      (Fm.or (dividesFormula 5 n) (dividesFormula 7 n)))

/-- Free variable0=n. The nonzero guard is sufficient when a base divides n. -/
def coverageBody : Fm PTm 1 :=
  let n : PTm 1 := PTm.var 0
  Fm.imp (nonzero n) (Fm.imp (coveredFormula n)
    (Fm.all (Fm.all (Fm.all
      (fermatMatrix (PTm.var 3 : PTm 4)
        (PTm.var 0) (PTm.var 1) (PTm.var 2))))))

def coverageSentence : Fm PTm 0 := Fm.all coverageBody

abbrev InternalCoverage : Prop :=
  Prf PRAAx ([] : List (Fm PTm 0)) coverageSentence

/-- Fields to be filled by the object-language development, not assumptions
silently added to iPRA. This structure has no supplied inhabitant here. -/
structure RequiredProofObjects : Prop where
  cubic : InternalFLT 3
  quartic : InternalFLT 4
  quintic : InternalFLT 5
  septimal : InternalFLT 7
  allCovered : InternalCoverage

/-- Once an actual derivation is supplied, the existing repository theorem
translates it into the native scalar calculus. -/
theorem toNative {n : Nat} (h : InternalFLT n) :
    NPrf [] (NFm.ofPRA (fixedSentence n)) := by
  exact (pra_iff_native).mp h

/- Remaining theorem, intentionally not declared using an axiom or a hole:

    constructRequiredProofObjects : RequiredProofObjects

The construction order and exact induction invariants are in the paper's
formalization section. Every bounded routine must be coded with PR.prec/comp;
every induction must invoke PRA.qfInd on its characteristic-function formula.
Polynomial normalization must emit Prf derivations using previously proved
arithmetic laws. An ambient `ring` proof is not by itself this derivation.
-/

end FLTIPRA.ObjectLanguage

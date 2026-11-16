import ConciseIPRA.NativeBiInterpretation

/-!
# OCiPRA object-language contract interfaces

This file is an integration-oriented outline against the current
`LeanProofs.ConciseIPRA` API.  It contains no `axiom` and no `sorry`.
Its proof fields are explicit obligations: constructing a record requires an
actual `NPrf` or `Prf PRAAx` derivation.

The file was prepared without a Lean binary in the artifact environment and is
therefore not claimed compiler-checked.  The definitions intentionally follow
interfaces already used by the repository's checked object examples.
-/

namespace LeanProofs.ConciseIPRA.OCiPRA

open Syn
open scoped Fm

/-- The numeral one in the ordinary iPRA term language. -/
def one {n : Nat} : PTm n := PTm.succ PTm.zero

/-- A Boolean primitive-recursive test accepts exactly when it returns one. -/
def accepts {n : Nat} (test : PR n) : Fm PTm n :=
  PTm.app test Syn.var ≐ one

/-- Acceptance is quantifier-free, so it is eligible for `PRA.qfInd`. -/
theorem accepts_qf {n : Nat} (test : PR n) : (accepts test).QF := trivial

/-- A formula together with an object-iPRA proof of its Booleanization. -/
structure Booleanized (n : Nat) where
  formula : Fm PTm n
  test : PR n
  equivalent : [] ⊢[PRAAx] Fm.iff formula (accepts test)

namespace Booleanized

variable {n : Nat}

/-- Use the forward half of a supplied Booleanization proof. -/
theorem toTest (b : Booleanized n) {Γ : List (Fm PTm n)}
    (h : Γ ⊢[PRAAx] b.formula) : Γ ⊢[PRAAx] accepts b.test :=
  Prf.iffMp b.equivalent.ofNil h

/-- Use the backward half of a supplied Booleanization proof. -/
theorem fromTest (b : Booleanized n) {Γ : List (Fm PTm n)}
    (h : Γ ⊢[PRAAx] accepts b.test) : Γ ⊢[PRAAx] b.formula :=
  Prf.iffMpr b.equivalent.ofNil h

end Booleanized

/-- A deterministic proof-carrying program contract.

The postcondition has the output in de Bruijn slot zero and the `n` inputs in
slots one through `n`.  `certified` is the local object-language proof; it is
not inferred from host evaluation.
-/
structure ProgramContract (n : Nat) where
  pre : Fm PTm n
  program : PR n
  post : Fm PTm (n + 1)
  certified : [pre] ⊢[PRAAx]
    post.subst (inst (PTm.app program Syn.var))

namespace ProgramContract

variable {n : Nat}

/-- A deterministic contract yields an existential witness theorem. -/
theorem existsOutput (c : ProgramContract n) :
    [c.pre] ⊢[PRAAx] Fm.ex c.post :=
  Prf.exI (PTm.app c.program Syn.var) c.certified

/-- Discharge the advertised precondition. -/
theorem asImplication (c : ProgramContract n) :
    [] ⊢[PRAAx] (c.pre ⟶ Fm.ex c.post) :=
  Prf.impI c.existsOutput

end ProgramContract

/-- The exact proof data needed to close a quantifier-free induction. -/
structure QFInductionCertificate {n : Nat} (Γ : List (Fm PTm n)) where
  invariant : Fm PTm (n + 1)
  qf : invariant.QF
  base : Γ ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: Γ.map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (Syn.var 0)))

namespace QFInductionCertificate

variable {n : Nat} {Γ : List (Fm PTm n)}

/-- Close a supplied base/step certificate using the repository induction rule. -/
theorem conclude (c : QFInductionCertificate Γ) :
    Γ ⊢[PRAAx] Fm.all c.invariant :=
  PRA.qfInd c.invariant c.qf c.base c.step

end QFInductionCertificate

/-- A proof-producing contract in the native scalar calculus. -/
structure NativeContract (n : Nat) where
  assumptions : List (NFm n)
  conclusion : NFm n
  proof : NPrf assumptions conclusion

namespace NativeContract

variable {n : Nat}

/-- Transfer a native derivation to the ordinary iPRA calculus. -/
theorem toPRA (c : NativeContract n) :
    c.assumptions.map NFm.toPRA ⊢[PRAAx] c.conclusion.toPRA :=
  native_iff_pra.mp c.proof

end NativeContract

/-- A relational contract does not pretend that a canonical witness exists.
Its sole proof field is an actual object-language totality derivation. -/
structure RelationalContract (n : Nat) where
  pre : Fm PTm n
  witnessPost : Fm PTm (n + 1)
  total : [pre] ⊢[PRAAx] Fm.ex witnessPost

namespace RelationalContract

variable {n : Nat}

/-- Discharge the precondition of a relational contract. -/
theorem asImplication (c : RelationalContract n) :
    [] ⊢[PRAAx] (c.pre ⟶ Fm.ex c.witnessPost) :=
  Prf.impI c.total

end RelationalContract

end LeanProofs.ConciseIPRA.OCiPRA

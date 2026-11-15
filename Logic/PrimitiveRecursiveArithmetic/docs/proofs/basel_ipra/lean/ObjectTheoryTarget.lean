import ConciseIPRA.NativeBiInterpretation
import BaselSpec

/-!
# The required object-theory certification boundary

STATUS: uncompiled interface and conditional assembly only.  No completed
Basel derivation, PR compiler, or compiler-correctness proof is provided.
There are no axioms or `sorry` placeholders.  The theorems at the end only
state how an eventual checked iPRA derivation transfers to the existing
native core; they do not assert that such a derivation has been constructed.

Intended environment: ProveIt at
b03925cccc76d55b9dc2a00864a5e0544b64aa7f, Lean 4.32.0.
-/

namespace BaselIPRA.ObjectTheory

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Standard numerical evaluation of a PR syntax tree, used for the external
compiler specification only.  It is not an object-theory soundness theorem. -/
def evalPR : {k : Nat} → PR k → (Fin k → Nat) → Nat
  | _, .zero, _ => 0
  | _, .succ, xs => xs 0 + 1
  | _, .proj i, xs => xs i
  | _, .comp f gs, xs => evalPR f (fun i => evalPR (gs i) xs)
  | _, .prec f g, xs =>
      Nat.rec (evalPR f (fun i => xs i.succ))
        (fun y previous =>
          evalPR g (Fin.cases y (Fin.cases previous (fun i => xs i.succ))))
        (xs 0)

/-- What remains to be constructed by an explicit structural PR compiler.
The correctness field only identifies the compiled program; it does not prove
that its value is always zero. -/
structure CompiledBaselProgram where
  code : PR 2
  correct : ∀ k n,
    evalPR code (Fin.cases k (Fin.cases n Fin.elim0)) = Spec.checkBasel k n

/-- In the body of forall k, forall n, variable 0 denotes n and variable 1
denotes k.  The checker already contains the guard cutoff(k) <= n. -/
def checkerTerm (c : CompiledBaselProgram) : PTm 2 :=
  PTm.app c.code (Fin.cases (PTm.var 1)
    (Fin.cases (PTm.var 0) Fin.elim0))

def baselMatrix (c : CompiledBaselProgram) : Fm PTm 2 :=
  Fm.eq (checkerTerm c) PTm.zero

def baselFormula (c : CompiledBaselProgram) : Fm PTm 0 :=
  Fm.all (Fm.all (baselMatrix c))

/-- This is the deliverable that a COMPLETE formalization must supply. -/
def InternalBaselProof (c : CompiledBaselProgram) : Prop :=
  ([] : List (Fm PTm 0)) ⊢[PRAAx] baselFormula c

/-- CONDITIONAL ASSEMBLY: the existing checked bi-interpretation transports
an eventual iPRA proof to the native core. -/
theorem native_of_internal (c : CompiledBaselProgram)
    (h : InternalBaselProof c) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (baselFormula c)) := by
  simpa using
    (pra_iff_native (Γ := ([] : List (Fm PTm 0)))
      (φ := baselFormula c)).mp h

/-- An implementation may first prove the equivalent scalar-theory formula.
This theorem uses the existing translation, without assuming correctness of
any external numerical calculation. -/
theorem internal_iff_scalar (c : CompiledBaselProgram) :
    InternalBaselProof c ↔
      (([] : List (Fm Tm 0)) ⊢[TeqAx]
        (baselFormula c).map (fun _ => FromPRA.sigma)) := by
  exact pra_iff_teq (Γ := ([] : List (Fm PTm 0))) (φ := baselFormula c)

end BaselIPRA.ObjectTheory

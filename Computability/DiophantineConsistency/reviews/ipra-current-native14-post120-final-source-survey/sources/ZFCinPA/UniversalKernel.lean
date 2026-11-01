import ZFCinPA.SeparationKernel

/-!
# Universal proof kernels for the staged `𝗭𝗙𝗖` certificate compiler

The arithmetic staged compiler
(`BoundedPAConsistency.StagedTruthCertificateProofCompiler`) drives its four
recursive certificate fields through `PAInductionKernel`: a model-coded unary
predicate plus PA proofs, under a closed context, of the zero and successor
premises of PA's induction recognizer.  `𝗭𝗙𝗖` has no induction axiom, so the
set-theoretic mirror cannot store recognizer premises.  What every kernel
consumer actually uses, however, is only the *compiled* shape: a represented
proof of `context 🡒 ∀⁰ predicate`.

`UniversalKernel` records exactly that shape.  It keeps the arithmetic
kernel's combinators that are independent of the induction recognizer —
`compile`, `ofUniversalProof`, `recontextualize` — and drops the
induction-specific constructors and the `shiftFixed` side condition, which
only PA's recognizer consumed.  The one genuinely set-theoretic constructor
is `ofOmegaInduction`: it wraps `SeparationKernel`'s internalized ω-induction
(`zfcOmegaInductionOfShiftFixed`'s underlying fixed source derivation) into a
kernel whose predicate is the ω-relativized implication
`isVonNeumannNatQ 🡒 K`, with the base and successor premises supplied as
constructor arguments already carrying the context antecedent, in the pattern
of the arithmetic `kernelOfStructuralUniversalProof`.

Two transport constructors, `ofEq` and `withPredicate`, rewrite a kernel
along a context or predicate equality without touching the stored proof
term's shape.  Later assembly steps must use these instead of forcing
definitional equality of large represented formulas inside structure
literals; the projection lemmas below make the rewrites cheap.
-/

set_option autoImplicit false

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SeparationKernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A universal proof template under a closed context formula.

`predicate` may carry a nonstandard code chosen by an internal formula
compiler; `compileImplication` is a genuine represented proof, so its `.val`
is a proof code in the ambient model.  This is the recognizer-free core of
the arithmetic `PAInductionKernel` interface. -/
structure UniversalKernel (T : InternalTheory V ℒₛₑₜ)
    (context : Bootstrapping.Formula V ℒₛₑₜ) where
  predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1
  compileImplication : T ⊢! context 🡒 ∀⁰ predicate

namespace UniversalKernel

variable {T : InternalTheory V ℒₛₑₜ}
variable {context : Bootstrapping.Formula V ℒₛₑₜ}

/-- Specialize the stored implication at an actual context proof.  This is
the only elimination a staged certificate compiler needs. -/
noncomputable def compile (kernel : UniversalKernel T context)
    (hcontext : T ⊢! context) : T ⊢! ∀⁰ kernel.predicate :=
  TProof.modusPonens kernel.compileImplication hcontext

/-- Install an already proved universal statement behind the kernel
interface.  Unlike the arithmetic `PAInductionKernel.ofUniversalProof`, no
coded-closedness certificate is required: there is no induction recognizer
left to satisfy. -/
noncomputable def ofUniversalProof
    (predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (proof : T ⊢! context 🡒 ∀⁰ predicate) :
    UniversalKernel T context where
  predicate := predicate
  compileImplication := proof

@[simp] lemma ofUniversalProof_predicate
    (predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (proof : T ⊢! context 🡒 ∀⁰ predicate) :
    (ofUniversalProof predicate proof).predicate = predicate := rfl

/-- Change the closed context of a kernel along a represented implication.
The predicate is unchanged; the stored proof is precomposed, so this
operation performs no syntax decoding. -/
noncomputable def recontextualize
    {outer inner : Bootstrapping.Formula V ℒₛₑₜ}
    (h : T ⊢! outer 🡒 inner)
    (kernel : UniversalKernel T inner) :
    UniversalKernel T outer where
  predicate := kernel.predicate
  compileImplication := Entailment.C_trans h kernel.compileImplication

@[simp] lemma recontextualize_predicate
    {outer inner : Bootstrapping.Formula V ℒₛₑₜ}
    (h : T ⊢! outer 🡒 inner)
    (kernel : UniversalKernel T inner) :
    (recontextualize h kernel).predicate = kernel.predicate := rfl

/-! ## Cheap transports

Represented formulas produced by internal code builders are large.  A
structure literal whose expected type mentions one such formula while the
supplied field mentions a merely propositionally equal one forces the
elaborator into a defeq check that can be catastrophically expensive.  The
two constructors below perform the identification once, through an explicit
`Eq`, and their `rfl` projection lemmas let all later reasoning stay at the
level of rewriting. -/

/-- Transport a kernel along a context equality. -/
noncomputable def ofEq
    {context' : Bootstrapping.Formula V ℒₛₑₜ}
    (kernel : UniversalKernel T context) (h : context = context') :
    UniversalKernel T context' where
  predicate := kernel.predicate
  compileImplication := h ▸ kernel.compileImplication

@[simp] lemma ofEq_predicate
    {context' : Bootstrapping.Formula V ℒₛₑₜ}
    (kernel : UniversalKernel T context) (h : context = context') :
    (kernel.ofEq h).predicate = kernel.predicate := rfl

/-- Transport a kernel along a predicate equality. -/
noncomputable def withPredicate
    (kernel : UniversalKernel T context)
    (predicate' : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (h : kernel.predicate = predicate') :
    UniversalKernel T context where
  predicate := predicate'
  compileImplication := h ▸ kernel.compileImplication

@[simp] lemma withPredicate_predicate
    (kernel : UniversalKernel T context)
    (predicate' : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (h : kernel.predicate = predicate') :
    (kernel.withPredicate predicate' h).predicate = predicate' := rfl

/-! ## The ω-induction constructor

`SeparationKernel` compiles, once, a fixed source derivation showing that
ω-induction at a model-coded predicate `K` follows from the Separation
instance at `K` plus Infinity.  The kernel installed here re-plays that
derivation under an arbitrary closed context: both premises arrive with the
context antecedent already attached, and Hilbert's implication-distribution
law (`⨀₁`) retains that antecedent through the two modus-ponens steps of the
source implication chain.  The compiled predicate is deliberately the
ω-relativized implication `isVonNeumannNatQ 🡒 K`: `ℒₛₑₜ` has no constant for
`ω`, so "for every natural" can only be expressed by relativizing to the von
Neumann class predicate. -/

/-- Install internalized ω-induction at a shift-fixed model-coded predicate
as a universal kernel under an arbitrary closed context.

`hK` is the coded closedness of `K` consumed by the Separation-schema
recognizer inside the fixed source derivation; it does not resurface as a
kernel field because no further recognizer inspects the compiled
predicate. -/
noncomputable def ofOmegaInduction
    (context : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      context 🡒 ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      context 🡒
        ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    UniversalKernel ((𝗭𝗙𝗖 : SetTheory).internalize V) context where
  predicate := isVonNeumannNatQ 🡒 K
  compileImplication := by
    have h := compileOmegaTemplate K hK omegaSourceProof
    rw [translate_srcOmegaInduction] at h
    exact (Entailment.C_of_conseq h) ⨀₁ hzero ⨀₁ hsucc

@[simp] lemma ofOmegaInduction_predicate
    (context : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      context 🡒 ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      context 🡒
        ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    (ofOmegaInduction context K hK hzero hsucc).predicate =
      (isVonNeumannNatQ 🡒 K) := rfl

/-- ω-induction kernel from context-free premises: the context antecedent is
attached by weakening (`C_of_conseq`), so one pair of plain internal proofs
installs the kernel under every context. -/
noncomputable def ofOmegaInductionProofs
    (context : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    UniversalKernel ((𝗭𝗙𝗖 : SetTheory).internalize V) context :=
  ofOmegaInduction context K hK
    (Entailment.C_of_conseq hzero) (Entailment.C_of_conseq hsucc)

@[simp] lemma ofOmegaInductionProofs_predicate
    (context : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    (ofOmegaInductionProofs context K hK hzero hsucc).predicate =
      (isVonNeumannNatQ 🡒 K) := rfl

end UniversalKernel

end ZFCinPA
end LeanProofs

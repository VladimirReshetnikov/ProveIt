import ZFCinPA.UniversalKernel

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.UniversalKernelCheckedAudit
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SeparationKernel

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V ℒₛₑₜ}
variable {context : Bootstrapping.Formula V ℒₛₑₜ}

#print axioms LeanProofs.ZFCinPA.UniversalKernel.compile
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofUniversalProof
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofUniversalProof_predicate
#print axioms LeanProofs.ZFCinPA.UniversalKernel.recontextualize
#print axioms LeanProofs.ZFCinPA.UniversalKernel.recontextualize_predicate
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofEq
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofEq_predicate
#print axioms LeanProofs.ZFCinPA.UniversalKernel.withPredicate
#print axioms LeanProofs.ZFCinPA.UniversalKernel.withPredicate_predicate
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofOmegaInduction
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofOmegaInduction_predicate
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofOmegaInductionProofs
#print axioms LeanProofs.ZFCinPA.UniversalKernel.ofOmegaInductionProofs_predicate

example (kernel : UniversalKernel T context) (hcontext : T ⊢! context) :
    T ⊢! ∀⁰ kernel.predicate := UniversalKernel.compile kernel hcontext

example (predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (proof : T ⊢! context 🡒 ∀⁰ predicate) : UniversalKernel T context :=
  UniversalKernel.ofUniversalProof predicate proof

example (predicate : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (proof : T ⊢! context 🡒 ∀⁰ predicate) :
    (UniversalKernel.ofUniversalProof predicate proof).predicate = predicate :=
  UniversalKernel.ofUniversalProof_predicate predicate proof

example {outer inner : Bootstrapping.Formula V ℒₛₑₜ}
    (h : T ⊢! outer 🡒 inner) (kernel : UniversalKernel T inner) :
    UniversalKernel T outer := UniversalKernel.recontextualize h kernel

example {outer inner : Bootstrapping.Formula V ℒₛₑₜ}
    (h : T ⊢! outer 🡒 inner) (kernel : UniversalKernel T inner) :
    (UniversalKernel.recontextualize h kernel).predicate = kernel.predicate :=
  UniversalKernel.recontextualize_predicate h kernel

example {context' : Bootstrapping.Formula V ℒₛₑₜ}
    (kernel : UniversalKernel T context) (h : context = context') :
    UniversalKernel T context' := UniversalKernel.ofEq kernel h

example {context' : Bootstrapping.Formula V ℒₛₑₜ}
    (kernel : UniversalKernel T context) (h : context = context') :
    (kernel.ofEq h).predicate = kernel.predicate :=
  UniversalKernel.ofEq_predicate kernel h

example (kernel : UniversalKernel T context)
    (predicate' : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (h : kernel.predicate = predicate') : UniversalKernel T context :=
  UniversalKernel.withPredicate kernel predicate' h

example (kernel : UniversalKernel T context)
    (predicate' : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (h : kernel.predicate = predicate') :
    (kernel.withPredicate predicate' h).predicate = predicate' :=
  UniversalKernel.withPredicate_predicate kernel predicate' h

example (C : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! C 🡒 ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      C 🡒 ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    UniversalKernel ((𝗭𝗙𝗖 : SetTheory).internalize V) C :=
  UniversalKernel.ofOmegaInduction C K hK hzero hsucc

example (C : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! C 🡒 ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      C 🡒 ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    (UniversalKernel.ofOmegaInduction C K hK hzero hsucc).predicate =
      (isVonNeumannNatQ 🡒 K) :=
  UniversalKernel.ofOmegaInduction_predicate C K hK hzero hsucc

example (C : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    UniversalKernel ((𝗭𝗙𝗖 : SetTheory).internalize V) C :=
  UniversalKernel.ofOmegaInductionProofs C K hK hzero hsucc

example (C : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0]))) :
    (UniversalKernel.ofOmegaInductionProofs C K hK hzero hsucc).predicate =
      (isVonNeumannNatQ 🡒 K) :=
  UniversalKernel.ofOmegaInductionProofs_predicate C K hK hzero hsucc

-- The result remains omega-relativized; closedness and both induction
-- premises remain explicit inputs even when the context is already proved.
example (C : Bootstrapping.Formula V ℒₛₑₜ)
    (K : Bootstrapping.Semiformula V ℒₛₑₜ 1)
    (hK : Bootstrapping.shift ℒₛₑₜ K.val = K.val)
    (hzero : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! C 🡒 ∀⁰ (isEmptyQ 🡒 K))
    (hsucc : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢!
      C 🡒 ∀⁰ ∀⁰ (K.subst ![.bvar 1] 🡒 (isSuccQ 🡒 K.subst ![.bvar 0])))
    (hC : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! C) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! ∀⁰ (isVonNeumannNatQ 🡒 K) :=
  (UniversalKernel.ofOmegaInduction C K hK hzero hsucc).compile hC

example {outer inner : Bootstrapping.Formula V ℒₛₑₜ}
    (h : T ⊢! outer 🡒 inner) (kernel : UniversalKernel T inner)
    (houter : T ⊢! outer) : T ⊢! ∀⁰ kernel.predicate :=
  (UniversalKernel.recontextualize h kernel).compile houter

end LeanProofs.ZFCinPA.UniversalKernelCheckedAudit

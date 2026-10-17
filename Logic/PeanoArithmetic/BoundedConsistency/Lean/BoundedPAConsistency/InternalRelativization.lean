import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

/-!
Represented relativization of internal formulas to a definable class.

Fix an internal formula code `d` with one bound variable `#0` (the domain
formula `δ(x)`). The relativization `relativize L d p` of an internal formula
code `p` (in negation normal form, as Foundation codes formulas) leaves atoms
and the propositional connectives unchanged and guards every quantifier:

    ∀ q  ↦  ∀ (¬δ(#0) ∨ q^δ),        ∃ q  ↦  ∃ (δ(#0) ∧ q^δ).

It is one `UformulaRec1` construction with `d` as the recursion parameter,
hence a total Σ₁-definable function in every model of IΣ₁, defined at every
internal code (nonstandard ones included). This module proves its constructor
equations. Preservation of well-formed (semi)formulas, commutation with
negation, shift and substitution, and transport of internal derivations
are further obligations.

This is the represented counterpart of a relative interpretation's formula
translation (`LO.FirstOrder.DirectTranslation` is the external one). It is the
syntactic core of the PA-internal proof transports needed for the
ZF/ZFC comparison through `L` and for the well-founded-part comparison.
-/
namespace LeanProofs.BoundedPAConsistency.InternalRelativization

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace Relativization

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !qqRelDef y k R v”
  nrel := .mkSigma “y param k R v. !qqNRelDef y k R v”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. ∃ nd, !(negGraph L) nd param ∧ ∃ z, !qqOrDef z nd y₁ ∧ !qqAllDef y z”
  exs := .mkSigma “y param p₁ y₁. ∃ z, !qqAndDef z param y₁ ∧ !qqExsDef y z”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel := fun _ k R v ↦ ^rel k R v
  nrel := fun _ k R v ↦ ^nrel k R v
  verum := fun _ ↦ ^⊤
  falsum := fun _ ↦ ^⊥
  and := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all := fun d _ y₁ ↦ ^∀ (neg L d ^⋎ y₁)
  exs := fun d _ y₁ ↦ ^∃ (d ^⋏ y₁)
  allChanges := fun d ↦ d
  exsChanges := fun d ↦ d
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end Relativization

open Relativization

variable (L)

/-- Relativization of the internal formula `p` to the class defined by `d`. -/
noncomputable def relativize (d p : V) : V := (construction L).result L d p

noncomputable def relativizeGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L

variable {L}

instance relativize.defined : 𝚺₁-Function₂[V] relativize L via relativizeGraph L :=
  (construction L).result_defined

instance relativize.definable : 𝚺₁-Function₂[V] relativize L := relativize.defined.to_definable

instance relativize.definable' : Γ-[m + 1]-Function₂[V] relativize L :=
  relativize.definable.of_sigmaOne

section Equations

variable {d : V}

@[simp] lemma relativize_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    relativize L d (^rel k R v) = ^rel k R v := by
  simp [relativize, hR, hv, construction]

@[simp] lemma relativize_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    relativize L d (^nrel k R v) = ^nrel k R v := by
  simp [relativize, hR, hv, construction]

@[simp] lemma relativize_verum : relativize L d (^⊤ : V) = ^⊤ := by
  simp [relativize, construction]

@[simp] lemma relativize_falsum : relativize L d (^⊥ : V) = ^⊥ := by
  simp [relativize, construction]

@[simp] lemma relativize_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    relativize L d (p ^⋏ q) = relativize L d p ^⋏ relativize L d q := by
  simp [relativize, hp, hq, construction]

@[simp] lemma relativize_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    relativize L d (p ^⋎ q) = relativize L d p ^⋎ relativize L d q := by
  simp [relativize, hp, hq, construction]

@[simp] lemma relativize_all {p : V} (hp : IsUFormula L p) :
    relativize L d (^∀ p) = ^∀ (neg L d ^⋎ relativize L d p) := by
  simp [relativize, hp, construction]

@[simp] lemma relativize_exs {p : V} (hp : IsUFormula L p) :
    relativize L d (^∃ p) = ^∃ (d ^⋏ relativize L d p) := by
  simp [relativize, hp, construction]

lemma relativize_not_uformula {x : V} (h : ¬IsUFormula L x) : relativize L d x = 0 :=
  (construction L).result_prop_not _ h

end Equations

end LeanProofs.BoundedPAConsistency.InternalRelativization

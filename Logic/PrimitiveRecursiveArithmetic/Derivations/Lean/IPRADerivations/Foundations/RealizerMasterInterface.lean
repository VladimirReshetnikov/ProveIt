import IPRADerivations.Foundations.RealizerGraph
import IPRADerivations.Foundations.BoundedSyntax

/-!
# A derived interface for an actual finite list of input certificates

For fixed X and inner:PR2 the numerical query selects the actual list
inner(q,p). Valid certificates are exactly the canonical bounded X masters
for that list. The observation is the actual code; its relatedness checker
is a compiled bounded forall of the original observations. The realizer
from X to this interface has demand inner and the identity transformer.
No global soundness or stability contract is an input to the constructor.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealizerMasterInterface

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def boundTerm (X : Interface) (inner : PR 2) (q p : PTm n) : PTm n := masterBound X (ap2 inner q p) p
def verifyTerm (X : Interface) (inner : PR 2) (C q p : PTm n) : PTm n := masterBit X (ap2 inner q p) C p
def relationFormula (X : Interface) (inner : PR 2) : BFm 4 :=
  .all (length (ap2 inner (var 2) (var 3))) (.eq
    (ap4 X.related
      (ap3 X.observe (entry (var 1) (var 0)) (entry (ap2 inner (var 3) (var 4)) (var 0)) (var 4))
      (ap3 X.observe (entry (var 2) (var 0)) (entry (ap2 inner (var 3) (var 4)) (var 0)) (var 4))
      (entry (ap2 inner (var 3) (var 4)) (var 0)) (var 4)) one)

def bundle (X : Interface) (inner : PR 2) : Interface where
  query := PTm.toPR (one : PTm 2)
  bound := PTm.toPR (boundTerm X inner (var 0) (var 1))
  verify := PTm.toPR (verifyTerm X inner (var 0) (var 1) (var 2))
  observe := PTm.toPR (var 0 : PTm 3)
  related := BoundedSyntax.bitF (relationFormula X inner)

@[simp] theorem subst_boundTerm {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (inner : PR 2) (q p : PTm n) :
    Syn.subst σ (boundTerm X inner q p) = boundTerm X inner (Syn.subst σ q) (Syn.subst σ p) := by simp [boundTerm]
@[simp] theorem subst_verifyTerm {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (inner : PR 2) (C q p : PTm n) :
    Syn.subst σ (verifyTerm X inner C q p) = verifyTerm X inner (Syn.subst σ C) (Syn.subst σ q) (Syn.subst σ p) := by simp [verifyTerm]

theorem query_at (X : Interface) (inner : PR 2) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (bundle X inner).query q p ≐ one := by
  simpa [bundle,ap2] using toPR_eq (Γ := Γ) (one : PTm 2) ![q,p]
theorem bound_at (X : Interface) (inner : PR 2) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (bundle X inner).bound q p ≐ masterBound X (ap2 inner q p) p := by
  change Γ ⊢[PRAAx] PTm.app (PTm.toPR (boundTerm X inner (var 0) (var 1))) ![q,p] ≐ boundTerm X inner q p
  simpa only [subst_boundTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    toPR_eq (Γ := Γ) (boundTerm X inner (var 0) (var 1)) ![q,p]
theorem verifier_at (X : Interface) (inner : PR 2) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (bundle X inner).verify C q p ≐ masterBit X (ap2 inner q p) C p := by
  simpa [bundle,ap3,verifyTerm] using toPR_eq (Γ := Γ) (verifyTerm X inner (var 0) (var 1) (var 2)) ![C,q,p]
theorem observation_at (X : Interface) (inner : PR 2) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (bundle X inner).observe C q p ≐ C := by
  simpa [bundle,ap3] using toPR_eq (Γ := Γ) (var 0 : PTm 3) ![C,q,p]

theorem validity (X : Interface) (inner : PR 2) (C q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (valid (bundle X inner) C q p) (masterValid X (ap2 inner q p) C p) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact masterBit_sound X _ _ _ ((verifier_at X inner C q p).eqSymm.eqTrans (.andE₂ Prf.hyp0))
  · have h := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := masterValid X (ap2 inner q p) C p)
    exact .andI (lt_congr (.eqRefl _) (bound_at X inner q p).eqSymm (.andE₁ h))
      ((verifier_at X inner C q p).eqTrans (masterBit_complete X _ _ _ h))

theorem relation_formula (X : Interface) (inner : PR 2) (C C' q p : PTm n) :
    (BoundedSyntax.formula (relationFormula X inner)).subst ![C,C',q,p] =
      masterRelated X (ap2 inner q p) C C' p := by
  simp [relationFormula,BoundedSyntax.formula,masterRelated,related,Syn.up,Syn.shift]

theorem eq_one_iff {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] Fm.iff (a ≐ one) (b ≐ one) :=
  .andI (.impI (e.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (e.wk.eqTrans Prf.hyp0))

theorem relation_reflection (X : Interface) (inner : PR 2) (C C' q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (ap4 (bundle X inner).related C C' q p ≐ one) (masterRelated X (ap2 inner q p) C C' p) := by
  have e : Γ ⊢[PRAAx] ap4 (bundle X inner).related C C' q p ≐
      BoundedSyntax.bit (relationFormula X inner) ![C,C',q,p] :=
    BoundedSyntax.program_correct (relationFormula X inner) ![C,C',q,p]
  have eqbits := eq_one_iff e
  exact eqbits.iffTrans (by
    simpa only [relation_formula] using BoundedSyntax.bounded_reflection (Γ := Γ)
      (relationFormula X inner) ![C,C',q,p])

theorem relatedness (X : Interface) (inner : PR 2) (C C' q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (related (bundle X inner) C C' q p) (masterRelated X (ap2 inner q p) C C' p) := by
  have e := congrApp (Γ := Γ) (bundle X inner).related (ts := ![ap3 (bundle X inner).observe C q p,
      ap3 (bundle X inner).observe C' q p,q,p]) (us := ![C,C',q,p]) (fun i => by
        fin_cases i; exact observation_at X inner C q p; exact observation_at X inner C' q p
        exact .eqRefl _; exact .eqRefl _)
  have eqbits := eq_one_iff e
  exact eqbits.iffTrans (relation_reflection X inner C C' q p)

def transformF : PR 3 := PTm.toPR (var 0 : PTm 3)
theorem transform_at (C q p : PTm n) : Γ ⊢[PRAAx] ap3 transformF C q p ≐ C := by
  simpa [transformF,ap3] using toPR_eq (Γ := Γ) (var 0 : PTm 3) ![C,q,p]

/-- The master-interface operation is built from the actual checker laws. -/
def realizer (X : Interface) (inner : PR 2) : Realizer X (bundle X inner) where
  demand := inner
  transform := transformF
  guard := zero ≐ zero
  residuals := []
  sound := by
    apply valid_congr (bundle X inner) (transform_at (var 0) (var 1) (var 2)).eqSymm (.eqRefl _) (.eqRefl _)
    apply (validity X inner (var 0) (var 1) (var 2)).iffMpr
    exact .hyp (by simp)
  stable := by
    apply related_congr (bundle X inner) (transform_at (var 0) (var 2) (var 3)).eqSymm
      (transform_at (var 1) (var 2) (var 3)).eqSymm (.eqRefl _) (.eqRefl _)
    apply (relatedness X inner (var 0) (var 1) (var 2) (var 3)).iffMpr
    exact .hyp (by simp)

def code (inner : PR 2) : RealizerGraph.Code := ⟨inner,transformF,zero ≐ zero,[]⟩
theorem realizer_code (X : Interface) (inner : PR 2) :
    RealizerGraph.Code.ofRealizer (realizer X inner) = code inner := rfl

def primitive (X : Interface) (inner : PR 2) : RealizerGraph.Primitive X (bundle X inner) where
  code := code inner
  sound := (realizer X inner).sound
  stable := (realizer X inner).stable
def program (X : Interface) (inner : PR 2) : RealizerGraph.Program X (bundle X inner) :=
  .primitive (primitive X inner)
theorem program_code (X : Interface) (inner : PR 2) : (program X inner).code = code inner := rfl

theorem master_interface_validity_closed (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (Fm.iff (valid (bundle X inner) (var 0) (var 1) (var 2))
        (masterValid X (ap2 inner (var 1) (var 2)) (var 0) (var 2))) :=
  closeUniv 3 (validity X inner _ _ _)
theorem master_interface_relatedness_closed (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (Fm.iff (related (bundle X inner) (var 0) (var 1) (var 2) (var 3))
        (masterRelated X (ap2 inner (var 2) (var 3)) (var 0) (var 1) (var 3))) :=
  closeUniv 4 (relatedness X inner _ _ _ _)
theorem master_interface_programs_closed (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 (bundle X inner).bound (var 1) (var 2) ≐ masterBound X (ap2 inner (var 1) (var 2)) (var 2) ⋏
        (ap3 (bundle X inner).verify (var 0) (var 1) (var 2) ≐ masterBit X (ap2 inner (var 1) (var 2)) (var 0) (var 2) ⋏
          ap3 (bundle X inner).observe (var 0) (var 1) (var 2) ≐ var 0)) :=
  closeUniv 3 (.andI (bound_at X inner _ _) (.andI (verifier_at X inner _ _ _) (observation_at X inner _ _ _)))
theorem master_interface_soundness (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (realizer X inner)) :=
  bounded_realizer_soundness (realizer X inner)
theorem master_interface_stability (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (realizer X inner)) :=
  bounded_realizer_stability (realizer X inner)
theorem master_interface_sealed (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (realizer X inner)) :=
  bounded_realizer_sealed (realizer X inner)

end LeanProofs.IPRA.Foundations.RealizerMasterInterface

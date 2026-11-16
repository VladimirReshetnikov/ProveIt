module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherence
@[expose] public section

/-! Source bound substitution replaces index zero and lowers every old successor
index. This is distinct from rewriting the relational target language. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

/-- The full vector has length `n+1`; the tail keeps all `n` old variables. -/
def singleBoundSubst {n : Nat} (u : SourceTerm n) (t : SourceTerm (n+1)) : SourceTerm n :=
  Rew.subst (Fin.cases u Semiterm.bvar) t

@[simp] theorem singleBoundSubst_zero {n : Nat} (u : SourceTerm n) :
    singleBoundSubst u (.bvar 0) = u := by simp [singleBoundSubst]

@[simp] theorem singleBoundSubst_succ {n : Nat} (u : SourceTerm n) (i : Fin n) :
    singleBoundSubst u (.bvar i.succ) = .bvar i := by simp [singleBoundSubst]

@[simp] theorem singleBoundSubst_fvar {n : Nat} (u : SourceTerm n) (i : Nat) :
    singleBoundSubst u (.fvar i) = .fvar i := by simp [singleBoundSubst]

@[simp] theorem singleBoundSubst_func {n k : Nat} (u : SourceTerm n)
    (fn : Presentation.language.Func k) (ts : Fin k → SourceTerm (n+1)) :
    singleBoundSubst u (.func fn ts) = .func fn (fun i => singleBoundSubst u (ts i)) := rfl

/-- Recursive compatibility consumes finite isomorphism coverage, rather than
an infinitely encoded environment or a choice of canonical outputs. -/
def SubstitutionCompatible {n : Nat} (t : SourceTerm (n+1)) :=
  ∀ (u : SourceTerm n) {Γ : List Form}, CoherencePremises Γ →
    ∀ (b : Fin n → Term 0) (f : Nat → Term 0) (a : Term 0),
      IsoCoverage Γ b b f f u →
      IsoCoverage Γ (Fin.cases a b) (Fin.cases a b) f f t →
      ND.Proof Γ (value u b f a) → ∀ (r s : Term 0),
      ND.Proof Γ (value (singleBoundSubst u t) b f r) →
      ND.Proof Γ (value t (Fin.cases a b) f s) → ND.Proof Γ (orderIso r s)

def substitutionBoundZero {n : Nat} : SubstitutionCompatible (.bvar (0 : Fin (n+1))) := by
  intro u Γ A b f a Hu _ ha r s hr hs
  have hru : ND.Proof Γ (value u b f r) := by simpa only [singleBoundSubst_zero] using hr
  have hra := termValuesCoherent u A b b f f Hu r a hru ha
  exact isoEqualityTransport A.equality r a r s (A.equality.reflexive r) (andRight hs) hra

def substitutionBoundTail {n : Nat} (i : Fin n) :
    SubstitutionCompatible (.bvar i.succ) := by
  intro u Γ A b f a _ H _ r s hr hs
  have hr' : ND.Proof Γ (value (.bvar i) b f r) := by
    simpa only [singleBoundSubst_succ] using hr
  exact isoEqualityTransport A.equality (b i) (b i) r s (andRight hr') (andRight hs) H

def substitutionFree {n : Nat} (i : Nat) :
    SubstitutionCompatible (.fvar i : SourceTerm (n+1)) := by
  intro u Γ A b f a _ H _ r s hr hs
  have hr' : ND.Proof Γ (value (.fvar i) b f r) := by
    simpa only [singleBoundSubst_fvar] using hr
  exact isoEqualityTransport A.equality (f i) (f i) r s (andRight hr') (andRight hs) H

def substitutionZero {n : Nat} : SubstitutionCompatible (Presentation.zero : SourceTerm (n+1)) := by
  intro u Γ A b f a _ _ _ r s hr hs
  exact zeroValuesCoherent A.equality b b f f r s hr hs

@[simp] theorem freeShiftEnv_cons {n : Nat} (a : Term 0) (b : Fin n → Term 0) :
    freeShiftEnv (Fin.cases a b) = Fin.cases (Rew.shift a) (freeShiftEnv b) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

#print axioms singleBoundSubst_zero
#print axioms singleBoundSubst_succ
#print axioms substitutionBoundZero
#print axioms substitutionBoundTail
#print axioms substitutionFree
#print axioms substitutionZero
end M6.PA.ForwardRelational

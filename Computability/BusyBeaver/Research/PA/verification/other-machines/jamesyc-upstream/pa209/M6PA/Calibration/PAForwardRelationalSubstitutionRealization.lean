module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionPremises
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

/-- Finite source-occurrence tree of actual substitution-image realizations. -/
def TermRealization {n k : Nat} (Γ : List Form)
    (σ : Rew Presentation.language Nat n Nat k)
    (b : Fin k → Term 0) (f : Nat → Term 0)
    (c : Fin n → Term 0) (g : Nat → Term 0) : SourceTerm n → Type
  | .bvar i => SubstitutionLeaf Γ (σ (.bvar i)) b f (c i)
  | .fvar i => SubstitutionLeaf Γ (σ (.fvar i)) b f (g i)
  | .func _ ts => ∀ i, TermRealization Γ σ b f c g (ts i)

def TermRealization.up {Γ : List Form} {n k : Nat} (t : SourceTerm n)
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0}
    {f : Nat → Term 0} {c : Fin n → Term 0} {g : Nat → Term 0}
    (h : TermRealization Γ σ b f c g t) (p : Form) : TermRealization (p :: Γ) σ b f c g t := by
  cases t with
  | bvar i => exact SubstitutionLeaf.up h p
  | fvar i => exact SubstitutionLeaf.up h p
  | func fn ts => exact fun i => TermRealization.up (ts i) (h i) p

def TermRealization.shift {Γ : List Form} {n k : Nat} (t : SourceTerm n)
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0}
    {f : Nat → Term 0} {c : Fin n → Term 0} {g : Nat → Term 0}
    (h : TermRealization Γ σ b f c g t) :
    TermRealization (shifted Γ) σ (freeShiftEnv b) (freeShiftEnv f)
      (freeShiftEnv c) (freeShiftEnv g) t := by
  cases t with
  | bvar i => exact SubstitutionLeaf.shift h
  | fvar i => exact SubstitutionLeaf.shift h
  | func fn ts => exact fun i => TermRealization.shift (ts i) (h i)

def TermRealization.sourceCoverage {Γ : List Form} {n k : Nat} (t : SourceTerm n)
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0}
    {f : Nat → Term 0} {c : Fin n → Term 0} {g : Nat → Term 0}
    (h : TermRealization Γ σ b f c g t) : EnvironmentCoverage Γ c g t := by
  cases t with
  | bvar i => exact valueDomain _ _ _ _ h.witness
  | fvar i => exact valueDomain _ _ _ _ h.witness
  | func fn ts => exact fun i => TermRealization.sourceCoverage (ts i) (h i)

def TermRealization.imageCoverage {Γ : List Form} {n k : Nat} (t : SourceTerm n)
    {σ : Rew Presentation.language Nat n Nat k} {b : Fin k → Term 0}
    {f : Nat → Term 0} {c : Fin n → Term 0} {g : Nat → Term 0}
    (h : TermRealization Γ σ b f c g t) : EnvironmentCoverage Γ b f (σ t) := by
  cases t with
  | bvar i => exact h.coverage
  | fvar i => exact h.coverage
  | func fn ts =>
    rw [Rew.func]
    exact fun i => TermRealization.imageCoverage (ts i) (h i)

/-- Comparison of arbitrary actual values under a finite realized source Rew. -/
def RealizedTermCompatible {n : Nat} (t : SourceTerm n) :=
  ∀ {k : Nat} (σ : Rew Presentation.language Nat n Nat k) {Γ : List Form},
    SubstitutionPremises Γ → ∀ (b : Fin k → Term 0) (f : Nat → Term 0)
      (c : Fin n → Term 0) (g : Nat → Term 0), TermRealization Γ σ b f c g t →
      ∀ r s, ND.Proof Γ (value (σ t) b f r) → ND.Proof Γ (value t c g s) →
        ND.Proof Γ (orderIso r s)

def realizedBound {n : Nat} (i : Fin n) : RealizedTermCompatible (.bvar i) := by
  intro k σ Γ A b f c g H r s hr hs
  have hi := termValueUniqueUpToIso A.coherence A.identity (σ (.bvar i)) b f H.coverage
    r (c i) hr H.witness
  exact isoEqualityTransport A.coherence.equality r (c i) r s
    (A.coherence.equality.reflexive r) (andRight hs) hi

def realizedFree {n : Nat} (i : Nat) : RealizedTermCompatible (.fvar i : SourceTerm n) := by
  intro k σ Γ A b f c g H r s hr hs
  have hi := termValueUniqueUpToIso A.coherence A.identity (σ (.fvar i)) b f H.coverage
    r (g i) hr H.witness
  exact isoEqualityTransport A.coherence.equality r (g i) r s
    (A.coherence.equality.reflexive r) (andRight hs) hi

def realizedZero {n : Nat} : RealizedTermCompatible (Presentation.zero : SourceTerm n) := by
  intro k σ Γ A b f c g _ r s hr hs
  have hr' : ND.Proof Γ (value Presentation.zero b f r) := by
    simpa only [Presentation.zero, Rew.func, value] using hr
  exact zeroValuesCoherent A.coherence.equality b b f f r s hr' hs

#print axioms TermRealization.up
#print axioms TermRealization.shift
#print axioms TermRealization.sourceCoverage
#print axioms TermRealization.imageCoverage
#print axioms realizedBound
#print axioms realizedFree
#print axioms realizedZero
end M6.PA.ForwardRelational

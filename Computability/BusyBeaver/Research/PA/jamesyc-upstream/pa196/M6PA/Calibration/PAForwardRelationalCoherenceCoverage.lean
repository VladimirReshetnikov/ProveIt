module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherencePremises
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

/-- A finite occurrence tree of actual isomorphism proofs, with bound and free
source environments kept separate. No host environment is numerically encoded. -/
def IsoCoverage {n : Nat} (Γ : List Form)
    (b b' : Fin n → Term 0) (f f' : Nat → Term 0) : SourceTerm n → Type
  | .bvar i => ND.Proof Γ (orderIso (b i) (b' i))
  | .fvar i => ND.Proof Γ (orderIso (f i) (f' i))
  | .func _ ts => ∀ i, IsoCoverage Γ b b' f f' (ts i)

def IsoCoverage.up {Γ : List Form} {n : Nat} (t : SourceTerm n)
    {b b' : Fin n → Term 0} {f f' : Nat → Term 0}
    (h : IsoCoverage Γ b b' f f' t) (p : Form) :
    IsoCoverage (p :: Γ) b b' f f' t := by
  cases t with
  | bvar i => exact ND.up h p
  | fvar i => exact ND.up h p
  | func fn ts => exact fun i => IsoCoverage.up (ts i) (h i) p

def IsoCoverage.shift {Γ : List Form} {n : Nat} (t : SourceTerm n)
    {b b' : Fin n → Term 0} {f f' : Nat → Term 0}
    (h : IsoCoverage Γ b b' f f' t) :
    IsoCoverage (shifted Γ) (freeShiftEnv b) (freeShiftEnv b')
      (freeShiftEnv f) (freeShiftEnv f') t := by
  cases t with
  | bvar i => exact isoShift h
  | fvar i => exact isoShift h
  | func fn ts => exact fun i => IsoCoverage.shift (ts i) (h i)

/-- Generic coherent-value proof type used by structural recursion. -/
def ValuesCoherent {n : Nat} (t : SourceTerm n) :=
  ∀ {Γ : List Form}, CoherencePremises Γ →
    ∀ (b b' : Fin n → Term 0) (f f' : Nat → Term 0),
      IsoCoverage Γ b b' f f' t → ∀ (r s : Term 0),
        ND.Proof Γ (value t b f r) → ND.Proof Γ (value t b' f' s) →
          ND.Proof Γ (orderIso r s)

#print axioms IsoCoverage.up
#print axioms IsoCoverage.shift
end M6.PA.ForwardRelational

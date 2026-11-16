module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherenceBinary
@[expose] public section

/-! Constructive typed term-value coherence. Every existential witness in both
value derivations is eliminated; arithmetic steps invoke full two-input
isomorphism coherence. This is not raw equality or numerical syntax coding. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def termValuesCoherent {n : Nat} (t : SourceTerm n) : ValuesCoherent t :=
  match t with
  | .bvar i => fun A b b' f f' H r s hr hs =>
      isoEqualityTransport A.equality (b i) (b' i) r s (andRight hr) (andRight hs) H
  | .fvar i => fun A b b' f f' H r s hr hs =>
      isoEqualityTransport A.equality (f i) (f' i) r s (andRight hr) (andRight hs) H
  | .func .zero _ => fun A b b' f f' _ r s hr hs => zeroValuesCoherent A.equality b b' f f' r s hr hs
  | .func .succ ts => fun A b b' f f' H r s hr hs =>
      successorValuesCoherent (ts 0) (termValuesCoherent (ts 0)) A b b' f f'
        (Fin.cases (H 0) (fun i => Fin.elim0 i)) r s hr hs
  | .func .add ts => fun A b b' f f' H r s hr hs =>
      binaryValuesCoherent .addition (ts 0) (ts 1)
        (termValuesCoherent (ts 0)) (termValuesCoherent (ts 1)) A b b' f f'
        (Fin.cases (H 0) (Fin.cases (H 1) (fun i => Fin.elim0 i))) r s hr hs
  | .func .mul ts => fun A b b' f f' H r s hr hs =>
      binaryValuesCoherent .multiplication (ts 0) (ts 1)
        (termValuesCoherent (ts 0)) (termValuesCoherent (ts 1)) A b b' f f'
        (Fin.cases (H 0) (Fin.cases (H 1) (fun i => Fin.elim0 i))) r s hr hs

def reflexiveIsoAt {Γ : List Form} (E : FormulaEquality Γ)
    (hidentity : ND.Proof Γ identityStatement) (x : Term 0)
    (hx : ND.Proof Γ (Ordinal.domain x)) : ND.Proof Γ (orderIso x x) := by
  obtain ⟨x,rfl⟩ := groundName x
  exact orderIsoFromExists E x (identityAt x hidentity hx)

def reflexiveIsoCoverage {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (hidentity : ND.Proof Γ identityStatement) (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (H : EnvironmentCoverage Γ b f t) :
    IsoCoverage Γ b b f f t := by
  cases t with
  | bvar i => exact reflexiveIsoAt E hidentity (b i) H
  | fvar i => exact reflexiveIsoAt E hidentity (f i) H
  | func fn ts => exact fun i => reflexiveIsoCoverage E hidentity (ts i) b f (H i)

/-- Same-environment uniqueness only modulo genuine witnessed order isomorphism.
The domain coverage is finite and occurrence-indexed. -/
def termValueUniqueUpToIso {Γ : List Form} {n : Nat} (A : CoherencePremises Γ)
    (hidentity : ND.Proof Γ identityStatement) (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (H : EnvironmentCoverage Γ b f t)
    (r s : Term 0) (hr : ND.Proof Γ (value t b f r)) (hs : ND.Proof Γ (value t b f s)) :
    ND.Proof Γ (orderIso r s) :=
  termValuesCoherent t A b b f f (reflexiveIsoCoverage A.equality hidentity t b f H) r s hr hs

#print axioms termValuesCoherent
#print axioms reflexiveIsoCoverage
#print axioms termValueUniqueUpToIso
end M6.PA.ForwardRelational

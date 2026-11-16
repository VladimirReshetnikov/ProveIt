module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotalityConstructors
@[expose] public section

/-! Structural ND totality for typed PA terms. Coverage requests domain proofs
only at the finitely many variable occurrences of this term. Neither infinite
environment coding nor semantic representatives are used. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult

/-- A finite proof tree indexed by the term, not a proof family over all Nat.
The function branch has the finite arity of the actual source symbol. -/
def EnvironmentCoverage {n : Nat} (Γ : List Form)
    (b : Fin n → Term 0) (f : Nat → Term 0) : SourceTerm n → Type
  | .bvar i => ND.Proof Γ (Ordinal.domain (b i))
  | .fvar i => ND.Proof Γ (Ordinal.domain (f i))
  | .func _ ts => ∀ i, EnvironmentCoverage Γ b f (ts i)

/-- Actual LK/ND proof, conditional only on explicit closed arithmetic
hypotheses and finite-occurrence domain coverage. -/
def termTotality {Γ : List Form} {n : Nat} (A : TotalityPremises Γ)
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) :
    EnvironmentCoverage Γ b f t → ND.Proof Γ (hasValue t b f) :=
  match t with
  | .bvar i => fun h => valueIntro _ b f (b i) (andIntro h (A.eqRefl (b i)))
  | .fvar i => fun h => valueIntro _ b f (f i) (andIntro h (A.eqRefl (f i)))
  | .func .zero _ => fun _ => A.zero
  | .func .succ ts => fun h => successorTotal A (ts 0) b f (termTotality A (ts 0) b f (h 0))
  | .func .add ts => fun h => additionTotal A (ts 0) (ts 1) b f
      (termTotality A (ts 0) b f (h 0)) (termTotality A (ts 1) b f (h 1))
  | .func .mul ts => fun h => multiplicationTotal A (ts 0) (ts 1) b f
      (termTotality A (ts 0) b f (h 0)) (termTotality A (ts 1) b f (h 1))

/-- Optional stronger environment-proof families instantiate the finite tree.
These host functions are NOT claimed to have internal numerical codes. -/
def coverageFromFamilies {Γ : List Form} {n : Nat}
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hb : ∀ i, ND.Proof Γ (Ordinal.domain (b i)))
    (hf : ∀ i, ND.Proof Γ (Ordinal.domain (f i))) : EnvironmentCoverage Γ b f t := by
  cases t with
  | bvar i => exact hb i
  | fvar i => exact hf i
  | func fn ts => exact fun i => coverageFromFamilies (ts i) b f hb hf

/-- In particular a default environment needs only a single domain proof,
not infinitely many independent assumptions. -/
def constantEnvironmentCoverage {Γ : List Form} {n : Nat}
    (t : SourceTerm n) (z : Term 0) (hz : ND.Proof Γ (Ordinal.domain z)) :
    EnvironmentCoverage Γ (fun _ => z) (fun _ => z) t :=
  coverageFromFamilies t _ _ (fun _ => hz) (fun _ => hz)

#print axioms termTotality
#print axioms coverageFromFamilies
#print axioms constantEnvironmentCoverage
end M6.PA.ForwardRelational

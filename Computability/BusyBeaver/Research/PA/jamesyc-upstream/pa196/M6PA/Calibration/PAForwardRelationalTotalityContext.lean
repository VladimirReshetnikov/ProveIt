module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotality
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- Finite list of environment terms actually read by the source term. -/
def environmentInputs {n : Nat} (b : Fin n → Term 0) (f : Nat → Term 0) :
    SourceTerm n → List (Term 0)
  | .bvar i => [b i]
  | .fvar i => [f i]
  | .func _ ts => (List.ofFn (fun i => environmentInputs b f (ts i))).flatten

def coverageFromInputs {Γ : List Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ∀ x, x ∈ environmentInputs b f t → ND.Proof Γ (Ordinal.domain x)) :
    EnvironmentCoverage Γ b f t := by
  cases t with
  | bvar i => exact h _ (by simp [environmentInputs])
  | fvar i => exact h _ (by simp [environmentInputs])
  | func fn ts =>
    intro i
    apply coverageFromInputs (ts i) b f
    intro x hx
    apply h x
    simp only [environmentInputs,List.mem_flatten,List.mem_ofFn]
    exact ⟨environmentInputs b f (ts i), ⟨i,rfl⟩, hx⟩

def totalityAxioms : List Form :=
  [reflexivityFormula,zeroInhabited,successorClosed,PairGraph.addClosedResult,
    PairGraph.mulClosedResult]

def totalityContext {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) : List Form :=
  totalityAxioms ++ (environmentInputs b f t).map Ordinal.domain

def termTotalityDerivation {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    ND.Proof (totalityContext t b f) (hasValue t b f) := by
  apply termTotality
    (TotalityPremises.mk
      (assumption (by simp [totalityContext,totalityAxioms]))
      (assumption (by simp [totalityContext,totalityAxioms]))
      (assumption (by simp [totalityContext,totalityAxioms]))
      (assumption (by simp [totalityContext,totalityAxioms]))
      (assumption (by simp [totalityContext,totalityAxioms])))
  apply coverageFromInputs
  intro x hx
  exact assumption (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x,hx,rfl⟩)))

#print axioms coverageFromInputs
#print axioms termTotalityDerivation
end M6.PA.ForwardRelational

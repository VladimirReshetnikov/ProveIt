module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherence
public import M6PA.Calibration.PAForwardRelationalTotalityGuarded
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

/-- Finite genuine isomorphism guards at exactly the variable occurrences. -/
def environmentRelations {n : Nat} (b b' : Fin n → Term 0) (f f' : Nat → Term 0) :
    SourceTerm n → List Form
  | .bvar i => [orderIso (b i) (b' i)]
  | .fvar i => [orderIso (f i) (f' i)]
  | .func _ ts => (List.ofFn (fun i => environmentRelations b b' f f' (ts i))).flatten

def isoCoverageFromRelations {Γ : List Form} {n : Nat} (t : SourceTerm n)
    (b b' : Fin n → Term 0) (f f' : Nat → Term 0)
    (h : ∀ p, p ∈ environmentRelations b b' f f' t → ND.Proof Γ p) :
    IsoCoverage Γ b b' f f' t := by
  cases t with
  | bvar i => exact h _ (by simp [environmentRelations])
  | fvar i => exact h _ (by simp [environmentRelations])
  | func fn ts =>
    intro i
    apply isoCoverageFromRelations (ts i) b b' f f'
    intro p hp
    apply h p
    simp only [environmentRelations,List.mem_flatten,List.mem_ofFn]
    exact ⟨environmentRelations b b' f f' (ts i), ⟨i,rfl⟩, hp⟩

def coherenceAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    emptyFormula,adjunctionFormula,addCoherenceStatement,mulCoherenceStatement]

def coherencePremisesFromContext {Γ : List Form}
    (h : ∀ p, p ∈ coherenceAxioms → p ∈ Γ) : CoherencePremises Γ :=
  ⟨⟨⟨assumption (h _ (by simp [coherenceAxioms])),assumption (h _ (by simp [coherenceAxioms])),
       assumption (h _ (by simp [coherenceAxioms]))⟩,assumption (h _ (by simp [coherenceAxioms]))⟩,
    assumption (h _ (by simp [coherenceAxioms])),assumption (h _ (by simp [coherenceAxioms])),
    assumption (h _ (by simp [coherenceAxioms])),assumption (h _ (by simp [coherenceAxioms]))⟩

def guardedCoherenceStatement {n : Nat} (t : SourceTerm n)
    (b b' : Fin n → Term 0) (f f' : Nat → Term 0) (r s : Term 0) : Form :=
  guardContext (environmentRelations b b' f f' t)
    (value t b f r 🡒 value t b' f' s 🡒 orderIso r s)

def guardedCoherenceDerivation {n : Nat} (t : SourceTerm n)
    (b b' : Fin n → Term 0) (f f' : Nat → Term 0) (r s : Term 0) :
    ND.Proof coherenceAxioms (guardedCoherenceStatement t b b' f f' r s) := by
  apply dischargeContext
  apply impIntro
  apply impIntro
  apply termValuesCoherent t (coherencePremisesFromContext (by
    intro p hp; simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (Or.inr hp)))) b b' f f'
  · apply isoCoverageFromRelations
    intro p hp
    exact assumption (by simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (Or.inl hp)))
  · exact assumption (by simp)
  · exact assumption (by simp)

#print axioms isoCoverageFromRelations
#print axioms guardedCoherenceDerivation
end M6.PA.ForwardRelational

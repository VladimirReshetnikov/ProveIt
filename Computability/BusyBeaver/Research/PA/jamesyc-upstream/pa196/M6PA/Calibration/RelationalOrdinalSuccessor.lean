module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalSuccessorClosure
@[expose] public section

/-! Finite actual-basis supplier for ordinal successor existence. All source
premises are ordinary equality base, adjunction and fixed intersection. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def domainSuccessorExists (a : Term n) : Formula n :=
  ∃¹ (domain (.bvar 0) ⋏ successor (Rew.bShift a) (.bvar 0))

def domainSuccessorStatement (a : Term n) : Formula n := domain a 🡒 domainSuccessorExists a

def domainSuccessorFromAxioms {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (hi : ND.Proof Γ intersectionFormula)
    (hadj : ND.Proof Γ adjunctionFormula) (a : Term 0) (ha : ND.Proof Γ (domain a)) :
    ND.Proof Γ (domainSuccessorExists a) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    apply exsElim (rawSuccessor (.fvar i) hadj)
    let σ : Formula 1 := successor (Rew.bShift (.fvar i)) (.bvar 0)
    let C := σ.free :: shifted Γ
    have hs : ND.Proof C (successor (.fvar (i+1)) (.fvar 0)) := by
      have h : ND.Proof C σ.free := assumption (by simp [C])
      convert h using 1 ; dsimp [σ] ; successorSyntax
    have da : ND.Proof C (domain (.fvar (i+1))) := by
      convert up (shiftProof ha) σ.free using 1 ; ordinalSyntax
    have db := successorDomain (e.shift.up σ.free)
      (up (equalityTransShift et) σ.free) (up (intersectionAxiomShift hi) σ.free)
      (.fvar (i+1)) (.fvar 0) da hs
    apply exsIntro _ (.fvar 0)
    have h := andIntro db hs
    convert h using 1
    successorSyntax

def successorAxioms : List Form :=
  [reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula,
    adjunctionFormula,intersectionFormula]

def domainSuccessorDerivation (a : Term 0) : ND.Proof successorAxioms (domainSuccessorStatement a) := by
  apply impIntro
  exact domainSuccessorFromAxioms
    ⟨assumption (by simp [successorAxioms]), assumption (by simp [successorAxioms]),
      assumption (by simp [successorAxioms])⟩
    (assumption (by simp [successorAxioms])) (assumption (by simp [successorAxioms]))
    (assumption (by simp [successorAxioms])) a (assumption (by simp))

/-- Numeric proof with allocator and full finite LK budget exposed. The
source equality, intersection and adjunction suppliers are all paid here. -/
def domainSuccessorSupplier (a : Term 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (domainSuccessorDerivation a) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (domainSuccessorStatement a) f lo z) := by
  apply compileContext successorAxioms (domainSuccessorStatement a)
    (domainSuccessorDerivation a) f lo z hlo hf hbudget
  intro p hp
  by_cases hr : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases hs : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases ht : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  by_cases hc : p = congruenceFormula
  · subst p; exact congruenceSupplier f lo z (by omega)
  by_cases ha : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z hlo hz hadj
  have he : p = intersectionFormula := by
    simpa [successorAxioms,hr,hs,ht,hc,ha] using hp
  subst p
  exact intersectionAxiomSupplier f lo z hlo (by omega)

#print axioms domainSuccessorFromAxioms
#print axioms domainSuccessorDerivation
#print axioms domainSuccessorSupplier
end M6.PA.RelationalSource.Ordinal


module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphEntry
@[expose] public section

/-! Adjunction adds a real Kuratowski edge and preserves all old edges. This
one-way extension is not yet an exact classification or functionality theorem. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def extensionExists (g a b : Term n) : Formula n :=
  ∃¹ (edge (.bvar 0) (Rew.bShift a) (Rew.bShift b) ⋏ inclusion (Rew.bShift g) (.bvar 0))

def insertedEdge {Γ : List Form} (g p h a b : Nat)
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (eq (.fvar p) (.fvar p))) :
    ND.Proof Γ (edge (.fvar h) (.fvar a) (.fvar b)) := by
  have hi := adjunctionAt g p h p ha
  have hm := mp (ND.orRight hr) (andRight hi)
  exact edgeFromEntry h a b p hm hp

def extensionFromEntry {Γ : List Form} (g p a b : Nat)
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (eq (.fvar p) (.fvar p)))
    (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (extensionExists (.fvar g) (.fvar a) (.fvar b)) := by
  apply exsElim (adjunctionWitness g p hadj)
  let σ : Formula 1 := adjunction (.fvar g) (.fvar p) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (g+1)) (.fvar (p+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; graphSyntax
  have hp' : ND.Proof C (kuratowski (.fvar (p+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    convert up (shiftProof hp) σ.free using 1 ; graphSyntax
  have hr' : ND.Proof C (eq (.fvar (p+1)) (.fvar (p+1))) := by
    convert up (shiftProof hr) σ.free using 1 ; graphSyntax
  have he := insertedEdge (g+1) (p+1) 0 (a+1) (b+1) ha hp' hr'
  have hi := adjunctionInclusion (g+1) (p+1) 0 ha
  apply exsIntro _ (.fvar 0)
  convert andIntro he hi using 1 <;>
    (dsimp [C,σ,extensionExists] <;> graphSyntax)

def extensionWitness {Γ : List Form} (g a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hrefl : ND.Proof Γ reflexivityFormula) :
    ND.Proof Γ (extensionExists (.fvar g) (.fvar a) (.fvar b)) := by
  apply exsElim (kuratowskiWitness a b hempty hadj)
  let σ : Formula 1 := kuratowski (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (kuratowski (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; graphSyntax
  have hr : ND.Proof C (eq (.fvar 0) (.fvar 0)) := by
    have h := allElim _ (.fvar 0) (up (shiftProof hrefl) σ.free)
    convert h using 1 ; simp only [reflexivityFormula,eqAtom] ; graphSyntax
  have he := extensionFromEntry (g+1) 0 (a+1) (b+1) hp hr
    (up (adjunctionClosedShift hadj) σ.free)
  convert he using 1 <;> (dsimp [C,σ,extensionExists] <;> graphSyntax)

def extensionDerivation (g a b : Nat) :
    ND.Proof [emptyFormula,adjunctionFormula,reflexivityFormula]
      (extensionExists (.fvar g) (.fvar a) (.fvar b)) :=
  extensionWitness g a b (assumption (by simp)) (assumption (by simp)) (assumption (by simp))

def extensionSupplier (g a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (extensionDerivation g a b) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (extensionExists (.fvar g) (.fvar a) (.fvar b)) f lo z) := by
  apply compileContext [emptyFormula,adjunctionFormula,reflexivityFormula]
    (extensionExists (.fvar g) (.fvar a) (.fvar b)) (extensionDerivation g a b)
    f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases he : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  · by_cases ha : p = adjunctionFormula
    · subst p; exact adjunctionSupplier f lo z hlo hz hadj
    · have hr : p = reflexivityFormula := by simpa [he,ha] using hp
      subst p; exact reflexivitySupplier f lo z

#print axioms insertedEdge
#print axioms extensionFromEntry
#print axioms extensionWitness
#print axioms extensionSupplier
end M6.PA.RelationalSource.PairGraph

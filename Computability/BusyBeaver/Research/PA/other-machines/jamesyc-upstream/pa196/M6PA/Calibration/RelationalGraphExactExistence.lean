module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphClassification
@[expose] public section

/-! Finite existence of an exact graph extension, discharging all ordinary
nonlogical suppliers. This does not assert canonical choice of the new graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula EqualityProofs equalityTransShift)

def exactExtensionExists (g a b : Term n) : Formula n :=
  ∃¹ exactExtension (Rew.bShift g) (.bvar 0) (Rew.bShift a) (Rew.bShift b)

macro "exactGraphSyntax" : tactic => `(tactic|
  (simp only [exactExtensionExists,exactExtension,classified]; graphSyntax))

def exactFromEntry {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (g p a b : Nat)
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (exactExtensionExists (.fvar g) (.fvar a) (.fvar b)) := by
  apply exsElim (adjunctionWitness g p hadj)
  let σ : Formula 1 := adjunction (.fvar g) (.fvar p) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (g+1)) (.fvar (p+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; graphSyntax
  have he := adjunctionExact (e.shift.up σ.free) (up (equalityTransShift et) σ.free)
    (g+1) (p+1) 0 (a+1) (b+1) ha (up (kuratowskiShift p a b hp) σ.free)
  apply exsIntro _ (.fvar 0)
  convert he using 1 <;> (dsimp [C,σ] <;> exactGraphSyntax)

def exactWitness {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (g a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (exactExtensionExists (.fvar g) (.fvar a) (.fvar b)) := by
  apply exsElim (kuratowskiWitness a b hempty hadj)
  let σ : Formula 1 := kuratowski (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (kuratowski (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; graphSyntax
  have he := exactFromEntry (e.shift.up σ.free) (up (equalityTransShift et) σ.free)
    (g+1) 0 (a+1) (b+1) hp (up (adjunctionClosedShift hadj) σ.free)
  convert he using 1 <;> (dsimp [C,σ] <;> exactGraphSyntax)

def exactContext : List Form :=
  [emptyFormula,adjunctionFormula,reflexivityFormula,symmetryFormula,transitivityFormula,congruenceFormula]

def exactDerivation (g a b : Nat) :
    ND.Proof exactContext (exactExtensionExists (.fvar g) (.fvar a) (.fvar b)) :=
  exactWitness ⟨assumption (by simp [exactContext]),assumption (by simp [exactContext]),
    assumption (by simp [exactContext])⟩ (assumption (by simp [exactContext]))
    g a b (assumption (by simp [exactContext])) (assumption (by simp [exactContext]))

def exactSupplier (g a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (exactDerivation g a b) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (exactExtensionExists (.fvar g) (.fvar a) (.fvar b)) f lo z) := by
  apply compileContext exactContext (exactExtensionExists (.fvar g) (.fvar a) (.fvar b))
    (exactDerivation g a b) f lo z hlo hf hbudget
  intro p hp
  classical
  by_cases h0 : p = emptyFormula
  · subst p; exact emptySupplier f lo z (by omega)
  by_cases h1 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier f lo z hlo hz hadj
  by_cases h2 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier f lo z
  by_cases h3 : p = symmetryFormula
  · subst p; exact symmetrySupplier f lo z
  by_cases h4 : p = transitivityFormula
  · subst p; exact transitivitySupplier f lo z
  have h5 : p = congruenceFormula := by simpa [exactContext,h0,h1,h2,h3,h4] using hp
  subst p; exact congruenceSupplier f lo z (by omega)

#print axioms exactFromEntry
#print axioms exactWitness
#print axioms exactSupplier
end M6.PA.RelationalSource.PairGraph


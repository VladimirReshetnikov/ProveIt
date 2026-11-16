module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionZeroExistence
@[expose] public section

/-! The actual-basis zero-input addition-prefix instance. Every finite ordinary
set/equality premise is discharged at the same allocator. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def zeroPrefixStatement (a b : Term n) : Formula n :=
  sourceImply (Ordinal.zero a ⋏ Ordinal.domain b) (addPrefixExists a b)

def zeroPrefixDerivation (a b : Nat) : ND.Proof exactContext (zeroPrefixStatement (.fvar a) (.fvar b)) := by
  apply impIntro
  let q : Form := Ordinal.zero (.fvar a) ⋏ Ordinal.domain (.fvar b)
  have hq : ND.Proof (q :: exactContext) q := assumption (by simp)
  let E : FormulaEquality exactContext :=
    ⟨⟨assumption (by simp [exactContext]),assumption (by simp [exactContext]),
      assumption (by simp [exactContext])⟩,assumption (by simp [exactContext])⟩
  exact zeroPrefixWitness (E.weaken (fun r hr => List.mem_cons_of_mem q hr)) a b
    (andLeft hq) (andRight hq) (assumption (by simp [exactContext]))
    (assumption (by simp [exactContext]))

def graphContextSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hz : lo+6 < z) (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (p : Form) (hp : p ∈ exactContext) : NativeCalculus.ActualBasis.Proof (code p f lo z) := by
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

def zeroPrefixSupplier (a b : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+6 < z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+lkBudget (zeroPrefixDerivation a b) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (zeroPrefixStatement (.fvar a) (.fvar b)) f lo z) :=
  compileContext exactContext _ (zeroPrefixDerivation a b) f lo z hlo hf hbudget
    (graphContextSupplier f lo z hlo hz hadj)

#print axioms zeroPrefixDerivation
#print axioms zeroPrefixSupplier
end M6.PA.RelationalSource.PairGraph

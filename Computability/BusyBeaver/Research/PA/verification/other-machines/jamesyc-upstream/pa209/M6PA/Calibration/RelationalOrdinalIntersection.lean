module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalEmpty
@[expose] public section

/-! Represented intersections supplied by one ordinary Separation instance.
No extensional identification of the witness is made. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def intersection (a s c : Term n) : Formula n :=
  ∀¹ sourceIff (mem (Rew.bShift c) (.bvar 0))
    (mem (Rew.bShift s) (.bvar 0) ⋏ mem (Rew.bShift a) (.bvar 0))

def intersectionExists (a s : Term n) : Formula n :=
  ∃¹ intersection (Rew.bShift a) (Rew.bShift s) (.bvar 0)

def intersectionProperty (a : Term 0) : Formula 1 :=
  mem (Rew.bShift a) (.bvar 0)

macro "intersectionSyntax" : tactic => `(tactic|
  (simp only [intersection,intersectionExists,intersectionProperty,
    separationFormula,liftMember,memAtom,sourceIff,sourceImply,
    mem,eq,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   finishSourceSyntax))

def intersectionFromSeparation {Γ : List Form} (a s : Term 0)
    (d : ND.Proof Γ (separationFormula (intersectionProperty a))) :
    ND.Proof Γ (intersectionExists a s) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases s with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j =>
      convert allElim _ (.fvar j) d using 1 ; intersectionSyntax

def intersectionDerivation (a s : Term 0) :
    ND.Proof [separationFormula (intersectionProperty a)] (intersectionExists a s) :=
  intersectionFromSeparation a s (assumption (by simp))

def intersectionSupplier (a s : Term 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hz : lo+3+depth (intersectionProperty a) ≤ z)
    (hbudget : lo+lkBudget (intersectionDerivation a s) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (intersectionExists a s) f lo z) := by
  apply compileContext [separationFormula (intersectionProperty a)]
    (intersectionExists a s) (intersectionDerivation a s) f lo z hlo hf hbudget
  intro p hp
  have he : p = separationFormula (intersectionProperty a) := by simpa using hp
  subst p
  exact separationSupplier (intersectionProperty a) f lo z hlo hf hz

#print axioms intersectionFromSeparation
#print axioms intersectionSupplier
end M6.PA.RelationalSource.Ordinal

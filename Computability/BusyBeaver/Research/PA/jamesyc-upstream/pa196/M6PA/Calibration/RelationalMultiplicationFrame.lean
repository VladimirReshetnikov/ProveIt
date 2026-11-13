module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationPrefixExtension
public import M6PA.Calibration.RelationalMultiplicationCompactSyntax
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult addPrefix mulPrefix

def mulGraphExists (top base zero : Term n) : Formula n :=
  ∃¹ mulPrefix (Rew.bShift top) (Rew.bShift base) (Rew.bShift zero) (.bvar 0)

macro "mulWitnessSyntax" : tactic => `(tactic|
  (first | (simp only [mulGraphExists,exactExtension,classified]; mulCompactSyntax) | mulCompactSyntax))

def mulPrefixShift {Γ : List Form} (top base z g : Nat)
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g))) :
    ND.Proof (shifted Γ) (mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar (g+1))) := by
  convert shiftProof hp using 1 <;> mulCompactSyntax

def mulAddShift {Γ : List Form} (x y z : Nat)
    (h : ND.Proof Γ (addResult (.fvar x) (.fvar y) (.fvar z))) :
    ND.Proof (shifted Γ) (addResult (.fvar (x+1)) (.fvar (y+1)) (.fvar (z+1))) := by
  convert shiftProof h using 1 <;> mulCompactSyntax

#print axioms mulPrefixShift
#print axioms mulAddShift
end M6.PA.RelationalSource.PairGraph

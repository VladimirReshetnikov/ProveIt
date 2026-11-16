module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionResultSupplier
@[expose] public section

/-! Capture-safe applications of the paid ordinal-valued addition totality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def addOutputAt {Γ : List Form} (base x : Nat)
    (h : ND.Proof Γ (addOutputConclusion base))
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) :
    ND.Proof Γ (addOutput (.fvar x) (.fvar base)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addOutput (.fvar x) (.fvar base)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      ((try simp only [addOutputConclusion,addOutput]) <;> prefixSyntax)
  exact mp hx hh

def addTotalAt {Γ : List Form} (base x : Nat)
    (h : ND.Proof Γ (addTotalStatement base))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar base)))
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) :
    ND.Proof Γ (addOutput (.fvar x) (.fvar base)) :=
  addOutputAt base x (mp hb h) hx

#print axioms addOutputAt
#print axioms addTotalAt
end M6.PA.RelationalSource.PairGraph

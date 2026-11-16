module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoZero
public import M6PA.Calibration.RelationalAdditionTrace
@[expose] public section

/-! Successor and zero representatives are disjoint modulo the actual
existential order-isomorphism relation, not just raw object equality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorIsoZeroFalse {Γ : List Form} (E : FormulaEquality Γ) (a c z : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hi : ND.Proof Γ (orderIso (.fvar c) (.fvar z))) : ND.Proof Γ ⊥ := by
  have hc := orderIsoZeroBackward c z hz hi
  exact noSuccessorZero E a c hc hs

def successorNotIsoZero {Γ : List Form} (E : FormulaEquality Γ) (a c z : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z))) :
    ND.Proof Γ (orderIso (.fvar c) (.fvar z)).neg := by
  apply byContradiction
  let p : Form := (orderIso (.fvar c) (.fvar z)).neg.neg
  have hi : ND.Proof (p::Γ) (orderIso (.fvar c) (.fvar z)) :=
    assumption (by simp [p,Semiformula.neg_neg])
  exact successorIsoZeroFalse (E.weaken (fun q hq => List.mem_cons_of_mem p hq))
    a c z (up hs p) (up hz p) hi

#print axioms successorIsoZeroFalse
#print axioms successorNotIsoZero
end M6.PA.RelationalSource.PairGraph

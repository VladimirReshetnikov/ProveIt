import PA194FoundationIdentityEmpty
import PA194FoundationLK
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
def emptyIdentityStatement (a : Nat) : Form :=
  sourceImply (Ordinal.zero (.fvar a)) (identityExists (.fvar a))
def emptyIdentityDerivation (a : Nat) : ND.Proof [] (emptyIdentityStatement a) := by
  apply impIntro
  exact emptyIdentityExists a (assumption (by simp))
end M6.PA.RelationalSource.PairGraph
namespace PA194Logic.Relational.Source.PairGraph
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic PA194Logic.Relational

def emptyIdentityFoundationDerivation (a : Nat) : LO.FirstOrder.Derivation [emptyIdentityStatement a] :=
  emptyIdentityDerivation a
noncomputable def emptyIdentitySupplier (a : Nat) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo)
    (hbudget : lo+foundationBudget (emptyIdentityFoundationDerivation a) ≤ z) :
    Proof (code (emptyIdentityStatement a) f lo z) := by
  apply compileFoundationContext [] (emptyIdentityStatement a)
    (emptyIdentityFoundationDerivation a) f lo z hlo hf hbudget
  intro p hp
  exact False.elim (List.not_mem_nil hp)
#print axioms emptyIdentityFoundationDerivation
#print axioms emptyIdentitySupplier
end PA194Logic.Relational.Source.PairGraph

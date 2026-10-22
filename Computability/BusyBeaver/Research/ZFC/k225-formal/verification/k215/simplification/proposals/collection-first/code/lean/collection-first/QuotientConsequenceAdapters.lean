import GICConsequences
import QuotientCollectionFirst

/-!
The exact current public Separation and Replacement signatures, proved from
one quotient collection theorem. Only the namespace is new; this is an
independently checked proposal, not a production source replacement.
-/

namespace SetTheory.BusyBeaver.ZFC.QuotientConsequenceAdapters

open KQHyp

universe u
variable {V : Type u}

theorem quotient_separation (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h)
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ x, KQ1Model.quotientMember mem witness h x b ↔
      KQ1Model.quotientMember mem witness h x a ∧
        SetTheory.Sat (KQ1Model.quotientMember mem witness h) (scons x env) phi :=
  GICConsequences.separation _
    (QuotientCollectionFirst.quotient_fullGIC mem witness h) phi env a

theorem quotient_replacement (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (phi : Form) (env : Nat → KQ1Model.Domain mem witness h)
    (hFunctional : Functional (relOf (KQ1Model.quotientMember mem witness h) phi env))
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ y, KQ1Model.quotientMember mem witness h y b ↔
      ∃ x, KQ1Model.quotientMember mem witness h x a ∧
        relOf (KQ1Model.quotientMember mem witness h) phi env y x :=
  GICConsequences.replacement _
    (QuotientCollectionFirst.quotient_fullGIC mem witness h) phi env hFunctional a

#print axioms quotient_separation
#print axioms quotient_replacement

end SetTheory.BusyBeaver.ZFC.QuotientConsequenceAdapters

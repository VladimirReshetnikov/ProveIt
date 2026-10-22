import GICConsequences
import BusyBeaver.ZFC.WFModelCore

/-!
Second use of the generic partial-Replacement-to-Separation theorem.

This reproduces WFModel.domain_separation's exact public type from the
already proved domain_replacement. Production integration should move
domain_separation below domain_replacement. The latter's proof does not
use the former, so the proposed reordering is acyclic.
-/

namespace SetTheory.BusyBeaver.ZFC.WFSeparationAdapter

open WellFoundedPart WFRelativization WFModel

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem domain_separation (H : ZFAxioms mem) (hc : ClosedWF mem)
    (phi : Form) (env : Nat → Domain mem) (a : Domain mem) :
    ∃ s : Domain mem, ∀ x, domainMem mem x s ↔
      domainMem mem x a ∧ Sat (domainMem mem) (scons x env) phi :=
  GICConsequences.separation_of_replacement (domainMem mem)
    (WFModel.domain_replacement H hc) phi env a

#print axioms domain_separation

end SetTheory.BusyBeaver.ZFC.WFSeparationAdapter

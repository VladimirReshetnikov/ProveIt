import FirstOrder.Completeness
import BusyBeaver.ZFC.InductiveAttemptsCore
import BusyBeaver.ZFC.KQ1Basic
import BusyBeaver.ZFC.KQ1ReplacementNative
import BusyBeaver.ZFC.KQ1Collect
import BusyBeaver.ZFC.WFModelCore

/-!
ZF from the quotient interface `KQHyp.QHyp`.

The bisimulation quotient of a `QHyp` structure satisfies the six `ZFAxioms` fields (infinity
through `InductiveAttempts.ordinary_infinity_of_container` from an empty set in a singleton-closed
set), exact power sets, and closure of the internally well-founded part (`wf_closure`, from the
quotient's collection). Its well-founded part is then a model of ZF with Foundation
(`WFModel.domain_models_ZF`), so ZF has no refutation (`zf_consistent`).
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1ZF

open KQHyp WellFoundedPart WFModel SingletonInfinity

universe u
variable {V : Type u}

theorem base (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    FiniteSets.Base (KQ1Model.quotientMember mem witness h) where
  ext := KQ1Model.quotient_extensional mem witness h
  pair := KQ1Basic.quotient_pair mem witness h
  sep := KQ1Separation.quotient_separation mem witness h
  union := KQ1Basic.quotient_union mem witness h

theorem zfAxioms (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ZFAxioms (KQ1Model.quotientMember mem witness h) where
  ext := KQ1Model.quotient_extensional mem witness h
  sep := KQ1Separation.quotient_separation mem witness h
  pair := KQ1Basic.quotient_pair mem witness h
  union := KQ1Basic.quotient_union mem witness h
  inf := by
    obtain ⟨Y, ⟨e, heY, he⟩, hY⟩ := KQ1Basic.quotient_empty_singleton_container mem witness h
    exact InductiveAttempts.ordinary_infinity_of_container (base mem witness h)
      (KQ1ReplacementNative.quotient_replacement mem witness h) e he Y heY
      (closed_of_exact_singletons (base mem witness h).toBase Y hY)
  repl := KQ1ReplacementNative.quotient_replacement mem witness h

theorem closedWF (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ClosedWF (KQ1Model.quotientMember mem witness h) := fun a ha =>
  wf_closure (base mem witness h) a (KQ1Collect.quotient_fullGIC mem witness h witnessForm (fun _ => a)) ha

theorem nonempty (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    Nonempty (Domain (KQ1Model.quotientMember mem witness h)) := by
  obtain ⟨e, he⟩ := KQ1Basic.quotient_empty mem witness h
  exact ⟨⟨e, wf_empty (base mem witness h) e he⟩⟩

/-- **A `QHyp` structure refutes no ZF proof of falsity.** -/
theorem zf_consistent (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ¬ BProv ZFax_s [] Form.fBot := by
  obtain ⟨x⟩ := nonempty mem witness h
  intro hf
  exact soundness_BProv hf (fun _ => x)
    (domain_models_ZF (zfAxioms mem witness h) (closedWF mem witness h)
      (KQ1Power.quotient_power mem witness h) (fun _ => x))
    (fun _ hNil => by cases hNil)

#print axioms zf_consistent

end SetTheory.BusyBeaver.ZFC.KQ1ZF

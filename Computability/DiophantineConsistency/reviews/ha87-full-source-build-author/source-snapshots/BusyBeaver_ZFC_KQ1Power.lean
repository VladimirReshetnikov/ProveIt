import BusyBeaver.ZFC.KQ1Separation
import BusyBeaver.ZFC.PowerSyntax

/-!
The actual quotient Power Set axiom of a `QHyp` structure.

The trace instances are the literal SeparationChoice matrices for the
formula Mem(0,1). The power filter is PowerSyntax.powerChoiceForm.
No collection assumption for arbitrary semantic predicates is added.
Quotient induction turns interpreted subset into the actual quotient
subset relation, and bridge_Pow gives the repository's Pow_form.

This follows the trace/filter construction in upstream S_ax.v:S_power,
297ab8df7e5de329605c3875b4934643b371a5e3, using the existing
equality-free profile resources. No other ZF axiom or machine endpoint
is inferred from this one axiom.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Power

open KQHyp

open Form ProfileCollection ProfileComposition ProfileAxioms
open ProfileModel CompositionModel

universe u
variable {V : Type u}

/-- These traces use the actual source formula z in x, with x a parameter. -/
theorem trace_instance (mem : V → V → Prop) (h : ModelsGIC mem) (a x : V) :
    CollectionInstance mem (SeparationChoice mem a (fun z => Member mem z x)) :=
  KQ1Separation.separation_instance mem h a (.fMem 0 1) (fun _ => x)


/-- Quantification over all quotient elements is exactly interpreted subset. -/
theorem quotient_sub (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (x a : V) :
    SetTheory.Sub (KQ1Model.quotientMember mem witness h)
      (KQ1Model.mk mem witness h x) (KQ1Model.mk mem witness h a) ↔
      InterpretedSub mem x a := by
  constructor
  · intro hs z hz
    exact hs (KQ1Model.mk mem witness h z) hz
  · intro hs z
    induction z using Quotient.ind with
    | _ z => exact hs z

/-- Power Set in the actual quotient, with every quotient subset included. -/
theorem quotient_power (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (a : KQ1Model.Domain mem witness h) :
    ∃ p, ∀ x, KQ1Model.quotientMember mem witness h x p ↔
      SetTheory.Sub (KQ1Model.quotientMember mem witness h) x a := by
  induction a using Quotient.ind with
  | _ a =>
    obtain ⟨p, hp⟩ := h.power a
    refine ⟨KQ1Model.mk mem witness h p, ?_⟩
    intro x
    induction x using Quotient.ind with
    | _ x => exact (hp x).trans (quotient_sub mem witness h x a).symm

/-- The repository's actual Power Set formula holds under every valuation. -/
theorem quotient_pow_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ env, SetTheory.Sat (KQ1Model.quotientMember mem witness h) env Pow_form :=
  bridge_Pow.mpr (quotient_power mem witness h)

end SetTheory.BusyBeaver.ZFC.KQ1Power

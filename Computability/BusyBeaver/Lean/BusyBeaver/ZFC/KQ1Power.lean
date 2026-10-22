import BusyBeaver.ZFC.KQ1Separation

/-!
The Power Set axiom in the quotient of a `QHyp` structure.

The hypothesis already supplies interpreted power. Quotient induction identifies
interpreted subsets with subsets of the quotient, and `bridge_Pow` gives `Pow_form`.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Power

open KQHyp

open Form ProfileCollection ProfileComposition ProfileAxioms
open ProfileModel CompositionModel

universe u
variable {V : Type u}

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

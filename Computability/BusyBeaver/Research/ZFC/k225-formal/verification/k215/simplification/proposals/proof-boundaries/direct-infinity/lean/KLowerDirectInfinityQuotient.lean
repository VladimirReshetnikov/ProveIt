import KLowerDirectInfinity
import BusyBeaver.ZFC.KQ1Model

/-!
The direct seed proof supplies the exact ordinary Infinity shape required by
ZFAxioms.inf, in the repository's actual bisimulation quotient.

The current QHyp is accepted as the already-established quotient interface;
its singleton field is never used in this proof. Splitting the final ZF module
to accept this proof, then rebuilding K215, remains an integration step.
-/

namespace SetTheory.BusyBeaver.ZFC.KLowerDirectInfinity

open KLower

universe u

theorem quotient_presentation {A : Type u} (raw : A → A → Prop)
    (witness : A) (h : KQHyp.QHyp raw) :
    DirectInfinity.QuotientPresentation raw
      (KQ1Model.quotientMember raw witness h) (KQ1Model.mk raw witness h) := by
  refine ⟨fun q => Quotient.exists_rep q, ?_⟩
  intro a b
  change (∃ z, raw z b ∧ ProfileCollection.Eqv raw a z) ↔
    ∃ z, raw z b ∧ KQ1Model.mk raw witness h a = KQ1Model.mk raw witness h z
  exact exists_congr fun z =>
    and_congr Iff.rfl (KQ1Model.mk_eq_iff raw witness h a z).symm

/-- Exact target of the `inf` field in the current ZFAxioms structure. -/
theorem ordinary_quotient_infinity {V : Type u} {mem : V → V → Prop}
    (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x)
    {t : V} (ht : ∀ z, ¬ mem z t) (witness : Tag mem t)
    (h : KQHyp.QHyp (tmem mem t)) :
    ∃ I,
      (∃ e, KQ1Model.quotientMember (tmem mem t) witness h e I ∧
        ∀ z, ¬ KQ1Model.quotientMember (tmem mem t) witness h z e) ∧
      ∀ x, KQ1Model.quotientMember (tmem mem t) witness h x I →
        ∃ sx, KQ1Model.quotientMember (tmem mem t) witness h sx I ∧
          ∀ z, KQ1Model.quotientMember (tmem mem t) witness h z sx ↔
            KQ1Model.quotientMember (tmem mem t) witness h z x ∨ z = x := by
  obtain ⟨e, I, he, hI⟩ := tagged_infinity hs hirr ht
  obtain ⟨hqe, hqI⟩ := DirectInfinity.quotient_infinity (tmem mem t)
    (KQ1Model.quotientMember (tmem mem t) witness h)
    (KQ1Model.mk (tmem mem t) witness h)
    (quotient_presentation (tmem mem t) witness h) he hI
  exact ⟨KQ1Model.mk (tmem mem t) witness h I,
    ⟨KQ1Model.mk (tmem mem t) witness h e, hqI.1, hqe⟩, hqI.2⟩

#print axioms quotient_presentation
#print axioms ordinary_quotient_infinity

end SetTheory.BusyBeaver.ZFC.KLowerDirectInfinity

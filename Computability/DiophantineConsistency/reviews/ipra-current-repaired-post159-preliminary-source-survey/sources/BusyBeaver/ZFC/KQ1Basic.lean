import BusyBeaver.ZFC.KQ1Separation

/-!
Empty Set, Pairing, Union and singleton-closed containers in the actual
quotient of a `QHyp` structure. Every resource comes from the existing formula-indexed
collection instances. Equality in the quotient is actual Lean equality.

SingletonClosed and singletonClosedForm express the upstream INF_lib
interface: every root belongs to a set closed under singleton formation.
They are deliberately distinct from ZF.Zf.Inf_form, which asserts a set
containing the empty set and closed under von Neumann successors.

The underlying resource proofs follow S_ax.v:S_eset/S_pair/S_union/S_inf,
upstream 297ab8df7e5de329605c3875b4934643b371a5e3, through the attributed
profile and quotient modules. No whole ZF or machine endpoint is claimed.
-/

namespace SetTheory.BusyBeaver.ZFC.KQ1Basic

open KQHyp

open Form ProfileCollection ProfileComposition ProfileAxioms
open ProfileModel CompositionModel

universe u
variable {V : Type u}

def emptyForm : Form := fEx (fAll (fImp (fMem 0 1) fBot))

theorem sat_emptyForm (mem : V → V → Prop) (env : Nat → V) :
    Sat mem env emptyForm ↔ ∃ e, ∀ z, ¬ mem z e := by
  simp only [emptyForm, Sat, scons]

theorem interpreted_empty (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) : ∃ e, ∀ z, ¬ Member mem z e := by
  obtain ⟨e, he⟩ := empty_of_collection mem witness (false_instance mem witness h.gic)
  exact ⟨e, empty_of_raw_empty mem e he⟩

theorem quotient_empty (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∃ e, ∀ z, ¬ KQ1Model.quotientMember mem witness h z e := by
  obtain ⟨e, he⟩ := interpreted_empty mem witness h
  refine ⟨KQ1Model.mk mem witness h e, ?_⟩
  intro z
  induction z using Quotient.ind with
  | _ z => exact he z

theorem quotient_empty_form (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (env : Nat → KQ1Model.Domain mem witness h) :
    Sat (KQ1Model.quotientMember mem witness h) env emptyForm :=
  (sat_emptyForm _ env).mpr (quotient_empty mem witness h)

theorem interpreted_pair (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (a b : V) :
    ∃ p, ∀ z, Member mem z p ↔ Eqv mem z a ∨ Eqv mem z b := by
  obtain ⟨p, hp⟩ := h.pairs a b
  exact ⟨p, pair_of_profile mem h.refl (fun _ _ _ => h.trans) a b p hp⟩

theorem quotient_pair (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (a b : KQ1Model.Domain mem witness h) :
    ∃ p, ∀ z, KQ1Model.quotientMember mem witness h z p ↔ z = a ∨ z = b := by
  induction a, b using Quotient.ind₂ with
  | _ a b =>
    obtain ⟨p, hp⟩ := interpreted_pair mem witness h a b
    refine ⟨KQ1Model.mk mem witness h p, ?_⟩
    intro z
    induction z using Quotient.ind with
    | _ z =>
      exact (hp z).trans (or_congr (KQ1Model.mk_eq_iff mem witness h z a).symm
        (KQ1Model.mk_eq_iff mem witness h z b).symm)

theorem quotient_pair_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ env, Sat (KQ1Model.quotientMember mem witness h) env Pair_form :=
  bridge_Pair.mpr (quotient_pair mem witness h)


theorem quotient_union (mem : V → V → Prop) (witness : V) (h : QHyp mem)
    (a : KQ1Model.Domain mem witness h) :
    ∃ b, ∀ z, KQ1Model.quotientMember mem witness h z b ↔
      ∃ x, KQ1Model.quotientMember mem witness h z x ∧
        KQ1Model.quotientMember mem witness h x a := by
  induction a using Quotient.ind with
  | _ a =>
    obtain ⟨b, hb⟩ := h.union a
    refine ⟨KQ1Model.mk mem witness h b, ?_⟩
    intro z
    induction z using Quotient.ind with
    | _ z =>
      apply (hb z).trans
      constructor
      · rintro ⟨x, hxa, hzx⟩
        exact ⟨KQ1Model.mk mem witness h x, hzx, hxa⟩
      · rintro ⟨x, hzx, hxa⟩
        obtain ⟨x, rfl⟩ := Quotient.exists_rep x
        exact ⟨x, hxa, hzx⟩

theorem quotient_union_form (mem : V → V → Prop) (witness : V) (h : QHyp mem) :
    ∀ env, Sat (KQ1Model.quotientMember mem witness h) env Union_form :=
  bridge_Union.mpr (quotient_union mem witness h)

/-- Every root belongs to a set closed under exact singleton formation. -/
def SingletonClosed (mem : V → V → Prop) : Prop :=
  ∀ root, ∃ v, mem root v ∧ ∀ x, mem x v →
    ∃ s, mem s v ∧ ∀ z, mem z s ↔ z = x

/-- The actual INF_lib-shaped sentence, separate from ordinary Inf_form. -/
def singletonClosedForm : Form :=
  fAll (fEx (fAnd (fMem 1 0) (fAll (fImp (fMem 0 1)
    (fEx (fAnd (fMem 0 2) (fAll (fIff (fMem 0 1) (fEq 0 2)))))))))

theorem sat_singletonClosedForm (mem : V → V → Prop) (env : Nat → V) :
    Sat mem env singletonClosedForm ↔ SingletonClosed mem := by
  simp only [singletonClosedForm, SingletonClosed, Sat, Sat_fIff, scons]


theorem quotient_singleton_closed (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) : SingletonClosed (KQ1Model.quotientMember mem witness h) := by
  intro root
  induction root using Quotient.ind with
  | _ root =>
    obtain ⟨v, hrv, hv⟩ := h.singleton root
    refine ⟨KQ1Model.mk mem witness h v, hrv, ?_⟩
    intro x
    induction x using Quotient.ind with
    | _ x =>
      intro hx
      obtain ⟨s, hsv, hs⟩ := hv x hx
      refine ⟨KQ1Model.mk mem witness h s, hsv, ?_⟩
      intro z
      induction z using Quotient.ind with
      | _ z => exact (hs z).trans (KQ1Model.mk_eq_iff mem witness h z x).symm

theorem quotient_singletonClosed_form (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) (env : Nat → KQ1Model.Domain mem witness h) :
    Sat (KQ1Model.quotientMember mem witness h) env singletonClosedForm :=
  (sat_singletonClosedForm _ env).mpr (quotient_singleton_closed mem witness h)

/-- The empty-root instance, still with singleton rather than von Neumann successors. -/
theorem quotient_empty_singleton_container (mem : V → V → Prop) (witness : V)
    (h : QHyp mem) :
    ∃ v, (∃ e, KQ1Model.quotientMember mem witness h e v ∧
        ∀ z, ¬ KQ1Model.quotientMember mem witness h z e) ∧
      ∀ x, KQ1Model.quotientMember mem witness h x v →
        ∃ s, KQ1Model.quotientMember mem witness h s v ∧
          ∀ z, KQ1Model.quotientMember mem witness h z s ↔ z = x := by
  obtain ⟨e, he⟩ := quotient_empty mem witness h
  obtain ⟨v, hev, hv⟩ := quotient_singleton_closed mem witness h e
  exact ⟨v, ⟨e, hev, he⟩, hv⟩

end SetTheory.BusyBeaver.ZFC.KQ1Basic

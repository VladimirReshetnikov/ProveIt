import BusyBeaver.ZFC.SingletonInfinityCore
import BusyBeaver.ZFC.QuotientBasic

namespace SetTheory.BusyBeaver.ZFC.SingletonInfinity

open Form

universe u
variable {V : Type u} {mem : V → V → Prop}

theorem quotientBase (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    Base (QuotientModel.quotientMember rawMem witness h) where
  ext := QuotientModel.quotient_extensional rawMem witness h
  pair := QuotientBasic.quotient_pair rawMem witness h
  sep := QuotientSeparation.quotient_separation rawMem witness h

/-- The actual quotient supplies an empty-root singleton index, not yet a
set closed under von Neumann successor. -/
theorem quotient_index (rawMem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC rawMem) :
    ∃ e N, (∀ z, ¬ QuotientModel.quotientMember rawMem witness h z e) ∧
      Index (quotientBase rawMem witness h) e N := by
  obtain ⟨Y, ⟨e, heY, he⟩, hY⟩ :=
    QuotientBasic.quotient_empty_singleton_container rawMem witness h
  exact ⟨e, (index_of_container (quotientBase rawMem witness h) e Y heY
    (closed_of_exact_singletons (quotientBase rawMem witness h) Y hY)).imp fun _ hN => ⟨he, hN⟩⟩

end SetTheory.BusyBeaver.ZFC.SingletonInfinity

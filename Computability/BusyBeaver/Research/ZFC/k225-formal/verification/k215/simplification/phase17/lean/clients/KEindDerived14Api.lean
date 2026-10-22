import BusyBeaver.ZFC.KEind222

namespace KEindDerived14Api
open SetTheory.BusyBeaver.ZFC
open Tarski (NF Thm)

theorem interpretation {Ax : NF → Prop} {f : NF} (h : Thm Ax f) :
    KThmK.ThmK (fun g => ∃ a, Ax a ∧ KEind222.th a = g) (KEind222.th f) :=
  KEind222.thm_th h

theorem completeness (T : NF → Prop)
    (hT : ∀ f, T f → KCode222.C222 (Code254.enc (KEind222.th f)))
    (hnone : ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, T f → ∀ e : Nat → D, Tarski.Sat mem e f) → (Nat → D) → False) :
    KCode222.C222 Code254.F := KEind222.c222_complete T hT hnone

#print axioms interpretation
#print axioms completeness
end KEindDerived14Api

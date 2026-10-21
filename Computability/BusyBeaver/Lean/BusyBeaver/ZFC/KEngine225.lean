import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KTable225

/-!
The 225's table (in K230 labels) keeps K230's register routines: it agrees with K230 on the 44
engine rows they read, so the register lemmas, and with them the symbolic executor's soundness,
hold for it.
-/

namespace SetTheory.BusyBeaver.ZFC.KEngine225

open KZip KRuntimeCore KTableCore KTape

theorem tm225_agree : AgreeRows tm225 tm230 boxRows := by decide

theorem tm225_box : BoxLemmas tm225 := boxLemmas tm225_agree (.inl ⟨rfl, rfl, rfl⟩)

/-- Every run the symbolic executor certifies on the 225's table is a run of the machine. -/
theorem tm225_exec_sound {br : Branch} {tgt : SConf → Bool} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (f : Nat) (s : SConf) (s' : SConf) (h : exec tm225 br tgt f s false = some s') :
    tgt s' = true ∧ Reach1 tm225 (conc n vs s) (conc n vs s') :=
  let ⟨hg, _, h1⟩ := exec_sound tm225_box n hv f s false s' h
  ⟨hg, h1 rfl⟩

end SetTheory.BusyBeaver.ZFC.KEngine225

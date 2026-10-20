import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KTable221

/-!
The 221's table (in K230 labels) keeps K230's register routines: it agrees with K230 on the 23
engine states they read, so the register lemmas, and with them the symbolic executor's soundness,
hold for it.
-/

namespace SetTheory.BusyBeaver.ZFC.KEngine221

open KZip KRuntimeCore KTableCore KTape

theorem tm221_agree : Agree tm221 tm230 boxStates := agree_of_agreeB (by decide)

theorem tm221_box : BoxLemmas tm221 := boxLemmas tm221_agree

/-- Every run the symbolic executor certifies on the 221's table is a run of the machine. -/
theorem tm221_exec_sound {br : Branch} {tgt : SConf → Bool} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (f : Nat) (s : SConf) (s' : SConf) (h : exec tm221 br tgt f s false = some s') :
    tgt s' = true ∧ Reach1 tm221 (conc n vs s) (conc n vs s') :=
  let ⟨hg, _, h1⟩ := exec_sound tm221_box n hv f s false s' h
  ⟨hg, h1 rfl⟩

end SetTheory.BusyBeaver.ZFC.KEngine221

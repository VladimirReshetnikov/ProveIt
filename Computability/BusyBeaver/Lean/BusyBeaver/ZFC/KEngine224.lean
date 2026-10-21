import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KTable224

/-!
The 224's table (Source 125, in K labels) keeps K230's register routines: it agrees with K230 on
the 44 engine rows they read, so the register lemmas, and with them the symbolic executor's
soundness, hold for it. Layer B of the Lean endpoint therefore carries over from the 225; what is
new for the 224 is its source and the calibration of its calculus K′.
-/

namespace SetTheory.BusyBeaver.ZFC.KEngine224

open KZip KRuntimeCore KTableCore KTape

theorem tm224_agree : AgreeRows tm224 tm230 boxRows := by decide

theorem tm224_box : BoxLemmas tm224 := boxLemmas tm224_agree (.inl ⟨rfl, rfl, rfl⟩)

/-- Every run the symbolic executor certifies on the 224's table is a run of the machine. -/
theorem tm224_exec_sound {br : Branch} {tgt : SConf → Bool} (n : Nat) {vs : List Nat}
    (hv : Valid br vs) (f : Nat) (s : SConf) (s' : SConf) (h : exec tm224 br tgt f s false = some s') :
    tgt s' = true ∧ Reach1 tm224 (conc n vs s) (conc n vs s') :=
  let ⟨hg, _, h1⟩ := exec_sound tm224_box n hv f s false s' h
  ⟨hg, h1 rfl⟩

end SetTheory.BusyBeaver.ZFC.KEngine224

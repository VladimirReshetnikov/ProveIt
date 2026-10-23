import PathFrame
import LeftFrameGeometry215
import BusyBeaver.ZFC.KHomeReady

/-!
The same literal template records supply the hardware and source certificates.
There is no second template roster or external identifier join in these proofs.
All 35 source actions are checked by kernel reduction, and the generic framing
theorem lifts each check to every preserved prefix.
-/
namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215
open RegisterPath PathFrame KZip KRuntimeCore KTableCore

def checkSourceAction (t : LocalTemplate) : Bool :=
  controlCheck t.isContinue t.controlArg t.suffix t.result

theorem all_source_actions : templates.all checkSourceAction = true := by
  decide +kernel

theorem every_template_source {t : LocalTemplate} (ht : t ∈ templates)
    (P : List Bool) :
    (if t.isContinue then continuePath t.controlArg (P ++ t.suffix)
      else breakPath t.controlArg (P ++ t.suffix)) = P ++ t.result := by
  have h := List.all_eq_true.mp all_source_actions t ht
  exact controlCheck_sound h P

theorem action_counts :
    (templates.filter LocalTemplate.isContinue).length = 29 ∧
    (templates.filter (fun t => !t.isContinue)).length = 6 := by
  decide +kernel

/-- The actual K215 table supplies the existing Home rows and boundary. -/
theorem home_ready : KHomeReady.ready tm215 = true := by
  decide +kernel

/-- A shared literal record binds a positive whole-tape machine contract and
the exact source operation, uniformly in every accepted prefix and every gap.
The existing register-block contracts remain explicit; no site occurrence or
whole-machine endpoint has been assumed or established by this theorem. -/
theorem every_template_control (B : BoxLemmas tm215)
    {t : LocalTemplate} (ht : t ∈ templates)
    (P : List Bool) {j : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215
      (zc t.start.1 ((P ++ t.suffix.dropLast).reverse ++ [true])
        (t.suffix.getLastD false :: List.replicate (n + 16) false ++ true :: sepsR vs))
      (zc 84 [true]
        (P ++ t.result ++ List.replicate (n + (16 + t.suffix.length - t.result.length)) false ++
          true :: sepsR vs)) ∧
    (if t.isContinue then continuePath t.controlArg (P ++ t.suffix)
      else breakPath t.controlArg (P ++ t.suffix)) = P ++ t.result := by
  obtain ⟨rows, hb⟩ := KHomeReady.ready_sound home_ready
  exact ⟨every_template_full B rows hb ht P hs n hv, every_template_source ht P⟩

#print axioms all_source_actions
#print axioms every_template_source
#print axioms action_counts
#print axioms home_ready
#print axioms every_template_control
end SetTheory.BusyBeaver.ZFC.KLeftFrame215

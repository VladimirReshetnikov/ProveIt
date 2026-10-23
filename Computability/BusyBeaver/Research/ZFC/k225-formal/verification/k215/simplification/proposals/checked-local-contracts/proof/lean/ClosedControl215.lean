import PathFrameTemplates215
import BusyBeaver.ZFC.KTape

/-!
Close the final machine-specific premise of the 35 whole-tape control contracts.
The exact maintained K215 table agrees with the already proved K230 register
engine and uses the existing increment-tail bypass. No whole-machine endpoint
or semantic site-coverage theorem is imported or assumed.
-/

namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215

open RegisterPath PathFrame KZip KRuntimeCore KTableCore

/-- The same finite row check and existing engine proof used by KEndpoint215. -/
theorem tm215_box : BoxLemmas tm215 :=
  KTape.boxLemmas (by decide +kernel) (.inr rfl)

/-- Every inherited control template has a checked source action and a positive
exact machine execution, with every machine-specific premise discharged.
The remaining premises specify a template, a safe Home prefix and a register
file with the existing minimum length; all gaps and register values are free. -/
theorem every_template_control_closed
    {t : LocalTemplate} (ht : t ∈ templates)
    (P : List Bool) {j : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j)
    (n : Nat) (vs : List Nat) (hvs : 10 ≤ vs.length) :
    Reach1 tm215
      (zc t.start.1 ((P ++ t.suffix.dropLast).reverse ++ [true])
        (t.suffix.getLastD false :: List.replicate (n + 16) false ++ true :: sepsR vs))
      (zc 84 [true]
        (P ++ t.result ++ List.replicate (n + (16 + t.suffix.length - t.result.length)) false ++
          true :: sepsR vs)) ∧
    (if t.isContinue then continuePath t.controlArg (P ++ t.suffix)
      else breakPath t.controlArg (P ++ t.suffix)) = P ++ t.result :=
  every_template_control tm215_box ht P hs n ⟨hvs, trivial⟩

#print axioms tm215_box
#print axioms every_template_control_closed

end SetTheory.BusyBeaver.ZFC.KLeftFrame215

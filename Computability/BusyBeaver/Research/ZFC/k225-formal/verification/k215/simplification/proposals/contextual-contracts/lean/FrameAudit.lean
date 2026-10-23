import BusyBeaver.ZFC.KFramedControl215

namespace K215FrameAudit
open SetTheory.BusyBeaver.ZFC
open KZip KRuntimeCore KTableCore KFramedControl215

/-- Closed client: explicit whole-tape source/target and every gap/register file. -/
theorem actual_control_runtime (B : BoxLemmas tm215) (rows : KHome.Rows tm215)
    (hb : KHome.Boundary tm215) {d : Descriptor} (hd : d ∈ descriptors)
    (p : List Bool) {k : Nat}
    (hp : KHome.scanBound 0 (p.reverse.map Seg.bit) = some k)
    (n : Nat) (vs : List Nat) (hv : 10 ≤ vs.length) :
    Reach1 tm215
      (zc d.state (d.suffix.reverse.tail ++ p.reverse ++ [true])
        (d.suffix.reverse.headD false ::
          (List.replicate (n + 16) false ++ true :: sepsR vs)))
      (zc 84 [true]
        (p ++ d.result ++
          List.replicate (n + 16 + d.suffix.length - d.result.length) false ++ true :: sepsR vs)) :=
  (control_contract B rows hb hd p hp n ⟨hv, trivial⟩).1

/-- The same descriptor uses the actual source `execute`, without prefix escape. -/
theorem actual_control_source {d : Descriptor} (hd : d ∈ descriptors)
    (p : List Bool) (r : RegisterPath.Registers) :
    RegisterPath.execute d.action (p ++ d.suffix) r = some ⟨p ++ d.result, r⟩ := by
  have hh := of_decide_eq_true (List.all_eq_true.mp all_aligned d hd)
  exact KControlFrame.controlSuffix_frame hh.2.2.1 p r

/-- The guard is essential independently of the transition table. -/
theorem boundary_guard_is_essential :
    sstep tm215 none (KLeftFrame.addLeft [.bit true] (0, true, [], [])) ≠
      KLeftFrame.mapStep [.bit true] (sstep tm215 none (0, true, [], [])) := by decide

theorem all_runtime_templates_accounted_for :
    descriptors.map (fun d => d.index.val) = List.range 35 := descriptor_indices

#print axioms actual_control_runtime
#print axioms actual_control_source
#print axioms boundary_guard_is_essential
#print axioms all_runtime_templates_accounted_for
end K215FrameAudit

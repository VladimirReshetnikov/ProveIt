import BusyBeaver.ZFC.KDecoderPrefix215
import FrameContracts

/-! Future source-only sketch. Not elaborated, compiled or adopted.
FrameContracts is the pinned batch219 proposal, not a current library module.
The new theorem is an exact dispatch-prefix adapter, with no site certificates.
It deliberately concludes Reach; the residual caller theorem supplies Reach1. -/
namespace SetTheory.BusyBeaver.ZFC.NextControlLead
open KZip KRuntimeCore KSim SiteCoverage KFrameContracts KTableCore

/-- The actual decoder prefix reaches the exact port certified by CallerOK. -/
theorem dispatch_to_framed_port {word : List Bool} {e : RegisterPath.Edge} {q : Nat}
    (leaf : LeafAt KSource215.t215 word e)
    (port : portState K215Decoder.roles 0 word.dropLast = some q)
    (n : Nat) (vs : List Nat) :
    Reach tm215 (conc n vs (start word))
      (KFrameContracts.leafPort q word (n + (64 - word.length)) vs) := by
  obtain ⟨pre, bit, q', _, _, hsplit, _, routed, hprefix⟩ :=
    KDecoderPrefix215.leaf_prefix leaf
  have checked : portState K215Decoder.roles 0 word.dropLast = some q' := by
    obtain ⟨pre', _, _, _, _, split', path, atRole, state, _, _, _⟩ := routed
    have drop : word.dropLast = pre' := by simp [split']
    rw [drop, portState_of_path path atRole, state]
  have same : q' = q := Option.some.inj (checked.symm.trans port)
  subst q
  obtain ⟨steps, _, _, run⟩ := hprefix n vs
  have exactPort : conc n vs (KDecoderPrefix215.leafPort pre bit q') =
      KFrameContracts.leafPort q' word (n + (64 - word.length)) vs := by
    rw [KDecoderPrefix215.conc_leafPort]
    simp [KFrameContracts.leafPort, hsplit, KSim.D0]
  exact ⟨steps, by simpa only [exactPort] using run⟩

end SetTheory.BusyBeaver.ZFC.NextControlLead

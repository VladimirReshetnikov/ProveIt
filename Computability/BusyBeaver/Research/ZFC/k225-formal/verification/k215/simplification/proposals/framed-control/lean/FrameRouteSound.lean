import FrameCallers

/-! The executable role-port certificate produces the maintained semantic
RolePath relation. This is the reverse direction of the existing path-to-check
lemma; it makes the finite caller-routing certificates directly reusable. -/
namespace SetTheory.BusyBeaver.ZFC.KFrameContracts

theorem followRoles_sound {rs : Array DecoderCertificate.Role}
    {first last : Nat} {pre : List Bool}
    (h : followRoles rs first pre = some last) :
    DecoderPaths.RolePath rs first pre last := by
  induction pre generalizing first with
  | nil =>
    simp only [followRoles, Option.some.injEq] at h
    subst last
    exact .nil _
  | cons b pre ih =>
    cases hat : rs[first]? with
    | none => simp [followRoles, hat] at h
    | some r =>
      cases hedge : (if b then r.one else r.zero) with
      | primitive node action => simp [followRoles, hat, hedge] at h
      | internal next block =>
        exact .cons hat hedge (ih (by simpa [followRoles, hat, hedge] using h))

theorem portState_sound {rs : Array DecoderCertificate.Role}
    {first q : Nat} {pre : List Bool}
    (h : portState rs first pre = some q) :
    ∃ last r, DecoderPaths.RolePath rs first pre last ∧
      rs[last]? = some r ∧ r.state = q := by
  cases hp : followRoles rs first pre with
  | none => simp [portState, hp] at h
  | some last =>
    cases hat : rs[last]? with
    | none => simp [portState, hp, hat] at h
    | some r =>
      exact ⟨last, r, followRoles_sound hp, hat, by simpa [portState, hp, hat] using h⟩

end SetTheory.BusyBeaver.ZFC.KFrameContracts

namespace SetTheory.BusyBeaver.ZFC.KFrameCallers
open KFrameContracts

/-- Every accepted caller has an actual route in the maintained decoder roles,
    ending at a role whose state is the checked primitive-entry state. -/
theorem all_caller_routes {c : Caller} (hc : c ∈ callers) :
    ∃ last r, DecoderPaths.RolePath K215Decoder.roles 0 c.word.dropLast last ∧
      K215Decoder.roles[last]? = some r ∧ r.state = (metaAt c.templateIndex).q :=
  portState_sound (caller_bindings hc).2

#print axioms KFrameContracts.followRoles_sound
#print axioms KFrameContracts.portState_sound
#print axioms all_caller_routes

end SetTheory.BusyBeaver.ZFC.KFrameCallers

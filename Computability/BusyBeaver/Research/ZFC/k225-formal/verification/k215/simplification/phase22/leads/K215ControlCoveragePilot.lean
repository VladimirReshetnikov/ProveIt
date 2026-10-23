import KControlRowsPilot
import FrameRouteSound
import BusyBeaver.ZFC.KSource215Program

/-! Source-only pilot. Not compiled or adopted.
Requires the exact batch219 framed-control source closure, not merely its data.
The finite theorem below compares complete word/action rows in their existing
order. It neither counts callers to infer exhaustiveness nor repeats CallerOK.
-/
namespace SetTheory.BusyBeaver.ZFC.K215ControlCoveragePilot
open RegisterPath RMBisim SiteCoverage KControlRowsPilot
open KFrameContracts KFrameCallers

/-- Only these exact word/action pairs may remain literal controls. -/
def literalControl (Q : List Bool) (e : Edge) : Bool :=
  decide ((Q = [false, false, true] ∧ e = .brk 1) ∨
    (Q = [true, true, false, true, true] ∧ e = .brk 1))

theorem literalControl_spec {Q : List Bool} {e : Edge}
    (h : literalControl Q e = true) :
    (Q = [false, false, true] ∧ e = .brk 1) ∨
      (Q = [true, true, false, true, true] ∧ e = .brk 1) :=
  of_decide_eq_true h

def callerRows : List Row :=
  callers.map (fun c => (c.word, action (metaAt c.templateIndex)))

def sharedControlRows : List Row :=
  (controlRows [] KSource215.t215).filter
    (fun row => !(literalControl row.1 row.2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- CLOSED FINITE CERTIFICATE, PROPOSED ONLY: this proof has not been run.
Own inert source parsing found this ordered equality exactly, with 1,423 rows.
Only pure finite source/caller data are reduced; no symbolic TM run is called.
If resource limits require sharding, use contiguous DFS subtree chunks rather
than 1,425 linear membership searches or a count-only substitute. -/
theorem shared_control_rows_exact : sharedControlRows = callerRows := by
  decide +kernel

/-- Every actual control leaf is either one of the two exact literal rows
or a member of the already validated caller family, with the SAME full word
and source action. This is the missing validity-to-exhaustiveness bridge. -/
theorem control_leaf_cases {Q : List Bool} {e : Edge}
    (hl : LeafAt KSource215.t215 Q e) (he : isControl e = true) :
    literalControl Q e = true ∨
      ∃ c, c ∈ callers ∧ c.word = Q ∧ action (metaAt c.templateIndex) = e := by
  by_cases hLit : literalControl Q e = true
  · exact Or.inl hLit
  · have hmem : (Q, e) ∈ controlRows [] KSource215.t215 := by
      simpa only [List.reverse_nil, List.nil_append] using
        controlRows_complete hl he []
    have hfilter : (Q, e) ∈ sharedControlRows := by
      apply List.mem_filter.mpr
      refine ⟨hmem, ?_⟩
      cases hcase : literalControl Q e <;> simp_all
    rw [shared_control_rows_exact] at hfilter
    obtain ⟨c, hc, hrow⟩ := List.mem_map.mp hfilter
    exact Or.inr ⟨c, hc,
      congrArg (fun row : Row => row.1) hrow,
      congrArg (fun row : Row => row.2) hrow⟩

/-- A successful arbitrary-input walk uses its complete consumed word,
including zero extension, when the control classifier is applied. -/
theorem walk_leaf {P : List Bool} {e : Edge} {d : Nat}
    (hw : walk KSource215.p215 (KSource215.p215.nnodes + 1)
      KSource215.p215.root P 0 = some (e, d)) :
    LeafAt KSource215.t215 (consume P d) e := by
  have ht : twalk KSource215.t215 P 0 = some (e, d) := by
    simpa only [← KSource215.t215_eq, ← walk_root] using hw
  have hl := (twalk_leafAt KSource215.t215 P 0 e d ht).2
  simpa only [Nat.sub_zero, RMEquiv.consume_eq] using hl

/-- Concrete residual contract supplied by the packet after classification.
The decoder prefix from dispatch is deliberately not suppressed. -/
theorem shared_control_residual {Q : List Bool} {e : Edge}
    (hl : LeafAt KSource215.t215 Q e) (he : isControl e = true)
    (hLit : literalControl Q e ≠ true) :
    ∃ c, c ∈ callers ∧ c.word = Q ∧ action (metaAt c.templateIndex) = e ∧
      ∀ (n : Nat) (vs : List Nat), KRuntimeCore.Valid none vs →
        KZip.Reach1 KTableCore.tm215
          (leafPort (metaAt c.templateIndex).q Q (n + (64 - Q.length)) vs)
          (KZip.zc 84 [true]
            (sourceResult (metaAt c.templateIndex) Q ++
              List.replicate (n + (64 - (sourceResult (metaAt c.templateIndex) Q).length)) false ++
                true :: KRuntimeCore.sepsR vs)) := by
  rcases control_leaf_cases hl he with h | ⟨c, hc, hword, haction⟩
  · exact (hLit h).elim
  · refine ⟨c, hc, hword, haction, ?_⟩
    intro n vs hv
    simpa only [hword] using (all_caller_standard hc n hv).2

#print axioms shared_control_rows_exact
#print axioms control_leaf_cases
#print axioms walk_leaf
#print axioms shared_control_residual
end SetTheory.BusyBeaver.ZFC.K215ControlCoveragePilot

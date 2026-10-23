import BusyBeaver.ZFC.SiteCoverage

/-! Source-only pilot. Not compiled or adopted.
A reverse-prefix fold lists only control leaves in false-first DFS order.
The completeness theorem connects exact consumed words in LeafAt to these rows.
No machine executor, caller lookup, or count argument occurs here. -/
namespace SetTheory.BusyBeaver.ZFC.KControlRowsPilot
open RegisterPath RMBisim SiteCoverage

abbrev Row := List Bool × Edge

def isControl : Edge → Bool
  | .brk _ | .cont _ => true
  | _ => false

def controlRows : List Bool → Tree → List Row
  | _, .none => []
  | revPrefix, .leaf e =>
      if isControl e then [(revPrefix.reverse, e)] else []
  | revPrefix, .node a b =>
      controlRows (false :: revPrefix) a ++ controlRows (true :: revPrefix) b

theorem controlRows_complete {t : Tree} {Q : List Bool} {e : Edge}
    (hl : LeafAt t Q e) (he : isControl e = true) :
    ∀ revPrefix, (revPrefix.reverse ++ Q, e) ∈ controlRows revPrefix t := by
  induction hl with
  | here e =>
      intro revPrefix
      simp only [controlRows, he, if_true, List.append_nil, List.mem_singleton]
  | left hl ih =>
      intro revPrefix
      apply List.mem_append.mpr
      apply Or.inl
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (false :: revPrefix)
  | right hl ih =>
      intro revPrefix
      apply List.mem_append.mpr
      apply Or.inr
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (true :: revPrefix)

/-- Pointwise weakening preserves the complete coverage check, including
its rejection of failed decoder branches. No test is executed by this proof. -/
theorem allSites_mono (test test' : List Bool → Edge → Bool)
    (hsound : ∀ Q e, test Q e = true → test' Q e = true) (t : Tree) :
    ∀ revPrefix, allSites test revPrefix t = true →
      allSites test' revPrefix t = true := by
  induction t with
  | none => intro revPrefix h; cases h
  | leaf e => intro revPrefix h; exact hsound revPrefix.reverse e h
  | node a b iha ihb =>
      intro revPrefix h
      exact Bool.and_eq_true_iff.mpr
        ⟨iha (false :: revPrefix) (Bool.and_eq_true_iff.mp h).1,
         ihb (true :: revPrefix) (Bool.and_eq_true_iff.mp h).2⟩

end SetTheory.BusyBeaver.ZFC.KControlRowsPilot

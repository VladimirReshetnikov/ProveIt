import BusyBeaver.ZFC.KCB1Suffix

/-! A concrete first producer for the semantic port interface.
The all-prefix LeftWord guard remains explicit; this does not yet discharge
routing and guard coverage for all 86 CB1 source occurrences. -/
namespace SetTheory.BusyBeaver.ZFC.KCB1Contract
open KZip KRuntimeCore KSim RegisterPath KDecoderPrefix215 KCB1Suffix
open SiteCoverage DecoderPaths DecoderSourceBinding K215Decoder

theorem cb1_strip (A : List Bool) :
    stripPath false 1 (A ++ [false, false, true]) = A ++ [false] := by
  simp [stripPath, stripRev, List.reverse_append, List.reverse_cons]

theorem cb1_path (A : List Bool) :
    breakPath 1 (A ++ [false, false, true]) = A ++ [true] := by
  rw [breakPath, cb1_strip]
  simp [incPath, incRev, List.reverse_append, List.reverse_cons]

theorem cb1_overflow (A : List Bool) :
    allOnes (stripPath false 1 (A ++ [false, false, true])) = false := by
  rw [cb1_strip]
  simp [allOnes]

theorem ready_checked : KHomeReady.ready KTableCore.tm215 = true := by decide +kernel

/-- Full CB1 suffix contract for the maintained table, all gaps and registers.
Only a finite read-only traversal guard depends on the complete prefix A. -/
theorem port_contract (A : List Bool)
    (hw : leftCheck KTableCore.tm215 1 (A.reverse ++ [true]) 2 = true)
    (hlen : A.length + 3 ≤ 48) :
    PortContract KTableCore.tm215 (leafPort (A ++ [false, false]) true 108)
      (A ++ [false, false, true]) (.brk 1) := by
  refine ⟨by simpa using hlen, ?_⟩
  intro n vs _
  have h := cb1_leafPort (M := KTableCore.tm215) rfl rfl rfl
    (KHomeReady.ready_sound ready_checked).2 A (leftCheck_sound hw)
    (by unfold D0; omega) n vs
  simpa only [cb1_path, cb1_overflow] using h

/-- For a source leaf routed through q108/true, the existing decoder theorem
and one guarded CB1 contract supply semantic dispatch coverage. -/
theorem edge_contract (A : List Bool)
    (leaf : LeafAt KSource215.t215 (A ++ [false, false, true]) (.brk 1))
    (route : RoutedEntry formal sourceNodes roles 0 (A ++ [false, false, true]) 108 true 2 1)
    (hw : leftCheck KTableCore.tm215 1 (A.reverse ++ [true]) 2 = true)
    (hlen : A.length + 3 ≤ 48) :
    EdgeContract KTableCore.tm215 (A ++ [false, false, true]) (.brk 1) := by
  obtain ⟨pre, b, q, op, arg, hsplit, _, hr, hprefix⟩ := leaf_prefix leaf
  obtain ⟨hq, hb⟩ := routed_control_unique route hr
  cases hq
  cases hb
  have he : (A ++ [false, false]) ++ [true] = pre ++ [true] := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsplit
  have hr : true :: (A ++ [false, false]).reverse = true :: pre.reverse := by
    simpa using congrArg List.reverse he
  have hp : A ++ [false, false] = pre := by
    simpa only [List.reverse_reverse] using congrArg List.reverse (List.cons.inj hr).2
  cases hp
  apply PortContract.precompose (port := leafPort (A ++ [false, false]) true 108)
  · intro n vs
    obtain ⟨steps, _, _, hrun⟩ := hprefix n vs
    exact ⟨steps, hrun⟩
  · exact port_contract A hw hlen

#print axioms cb1_strip
#print axioms port_contract
#print axioms edge_contract
end SetTheory.BusyBeaver.ZFC.KCB1Contract

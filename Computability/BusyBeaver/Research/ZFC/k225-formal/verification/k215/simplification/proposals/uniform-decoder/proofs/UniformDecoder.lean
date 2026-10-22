import BusyBeaver.ZFC.DecoderPaths

/-!
Uniform decoder clocks, against ProveIt 2ca3a5c16f0876d2cab842056353c03a1ed2f5f0.
The route, exit control, last bit and clock are selected before the arbitrary tape.
This file adds a theorem; it does not change the machine or its checked endpoint.
The induction is adapted from DecoderPaths.source_path_chain_routed.
-/
namespace SetTheory.BusyBeaver.ZFC.DecoderPaths
open FramedWindow DecoderCertificate
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Finite top-of-source inspection, with a generic semantic justification. -/
def atLeastDepth (nodes : Array Node) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, node =>
      match nodes[node]? with
      | some (.fork l r) => atLeastDepth nodes k l && atLeastDepth nodes k r
      | _ => false

theorem atLeastDepth_sound {nodes : Array Node} {k node : Nat}
    {word : List Bool} {op arg : Nat}
    (h : atLeastDepth nodes k node = true)
    (path : SourcePath nodes node word op arg) : k ≤ word.length := by
  induction k generalizing node word with
  | zero => omega
  | succ k ih =>
    cases path with
    | leaf hn => simp [atLeastDepth, hn] at h
    | @fork n l u bit w op arg hn tail =>
      simp only [atLeastDepth, hn, Bool.and_eq_true] at h
      have hc : atLeastDepth nodes k (if bit then u else l) = true := by
        cases bit
        · exact h.1
        · exact h.2
      exact Nat.succ_le_succ (ih hc tail)

/-- A finite source route has one clock and one exit on every matching tape.
The lower bound is zero only for a one-bit source word. -/
theorem source_path_chain_uniform
    (M : Table) (nodes : Array Node) (roles : Array Role) (blocks : Array Block)
    (good : ∀ (rid : Nat) (r : Role), roles[rid]? = some r →
      EdgeSpec M nodes roles blocks r false ∧ EdgeSpec M nodes roles blocks r true)
    (checked : blocks.toList.all (blockCheck M) = true)
    (durations : ∀ b ∈ blocks.toList, 1 ≤ b.steps ∧ b.steps ≤ 7)
    {node : Nat} {w : List Bool} {op arg : Nat} (path : SourcePath nodes node w op arg) :
    ∀ (rid : Nat) (r : Role), roles[rid]? = some r → r.node = node →
      ∃ steps q bit,
        w.length - 1 ≤ steps ∧ steps ≤ 7 * (w.length - 1) ∧
        RoutedEntry M nodes roles rid w q bit op arg ∧
        ∀ a t, Before t a r.suffix → Reads t a w →
          Chain blocks.toList t r.state a q (a + (w.length : Int) - 1) steps ∧
          t (a + (w.length : Int) - 1) = bit := by
  induction path with
  | leaf hn =>
    intro rid r hr he
    have hg := (good rid r hr).1
    simp [EdgeSpec, he, hn] at hg
  | @fork node l u bit w op arg hn tail ih =>
    intro rid r hr he
    have hg : EdgeSpec M nodes roles blocks r bit := by
      cases bit
      · exact (good rid r hr).1
      · exact (good rid r hr).2
    simp only [EdgeSpec, he, hn] at hg
    cases hedge : (if bit then r.one else r.zero) with
    | primitive n action =>
      simp only [hedge] at hg
      cases hc : nodes[if bit then u else l]? with
      | none => simp [hc] at hg
      | some cn =>
        cases cn with
        | fork l' u' => simp [hc] at hg
        | leaf op' arg' =>
          simp only [hc] at hg
          cases tail with
          | leaf ht =>
            rw [hc] at ht
            cases ht
            have heq : (if bit then u else l) = n := hg.2.1
            refine ⟨0, r.state, bit, by simp, by simp, ?_, ?_⟩
            · exact ⟨[], rid, r, n, action, rfl, RolePath.nil rid,
                hr, rfl, hedge, heq ▸ hc, hg.2.2⟩
            · intro a t hs hw
              exact ⟨by simpa using (Chain.done (bs := blocks.toList) (t := t) r.state a),
                by simpa using hw.1⟩
          | fork ht _ => rw [hc] at ht; cases ht
    | internal k j =>
      simp only [hedge] at hg
      cases hc : nodes[if bit then u else l]? with
      | none => simp [hc] at hg
      | some cn =>
        cases cn with
        | leaf op' arg' => simp [hc] at hg
        | fork l' u' =>
          cases hrole : roles[k]? with
          | none => simp [hc, hrole] at hg
          | some s =>
            cases hblock : blocks[j]? with
            | none => simp [hc, hrole, hblock] at hg
            | some b =>
              simp only [hc, hrole, hblock] at hg
              obtain ⟨_, hsnode, hssuffix, hentry, hexit, hlen, hword⟩ := hg
              have hmem : b ∈ blocks.toList := by
                simpa using (Array.mem_of_getElem? hblock)
              have hbcheck := (List.all_eq_true.mp checked) b hmem
              have hbpos : 0 < b.word.length := by
                have hh : (0 < b.steps ∧ 0 < b.word.length) ∧
                    check M b.steps b.entry 0 (cells b.word) b.exit 1 = true := by
                  simpa [blockCheck, Bool.and_eq_true] using hbcheck
                exact hh.1.2
              obtain ⟨steps, q, last, lo, hi, hend, hsem⟩ := ih k s hrole hsnode
              have wpos : 0 < w.length := by
                obtain ⟨pre, _, _, _, _, hsplit, _⟩ := hend
                rw [hsplit]; simp
              obtain ⟨blo, bhi⟩ := durations b hmem
              refine ⟨b.steps + steps, q, last, ?_, ?_, ?_, ?_⟩
              · simp only [List.length_cons]; omega
              · simp only [List.length_cons]; omega
              · obtain ⟨pre, final, s', leaf, action, hsplit, hroute,
                    hat, hstate, he', hleaf, hrow⟩ := hend
                refine ⟨bit :: pre, final, s', leaf, action, ?_,
                  RolePath.cons hr hedge hroute, hat, hstate, he', hleaf, hrow⟩
                simp only [hsplit, List.cons_append]
              · intro a t hs hw
                have hall : Before t (a + 1) (r.suffix ++ [bit]) := before_snoc hs hw.1
                have hbword : Before t (a + 1) b.word := by
                  rw [hword]
                  exact before_drop hall _ (by omega)
                have hsc : Before t (a + 1) s.suffix := by
                  rw [hssuffix]; exact before_tail2 hall
                obtain ⟨hchain, ht⟩ := hsem (a + 1) t hsc hw.2
                have hwindow := before_window hbpos hbword
                have hmore := Chain.more b a q (a + 1 + (w.length : Int) - 1)
                  steps hmem hwindow (by simpa [hexit] using hchain)
                have hpos : a + 1 + (w.length : Int) - 1 =
                    a + ((bit :: w).length : Int) - 1 := by
                  simp only [List.length_cons]; omega
                exact ⟨by simpa only [hentry, hpos] using hmore,
                  by simpa only [hpos] using ht⟩

end SetTheory.BusyBeaver.ZFC.DecoderPaths

namespace SetTheory.BusyBeaver.ZFC.K215SourcePaths
open FramedWindow DecoderCertificate DecoderPaths K215Decoder

theorem source_depth_three : atLeastDepth sourceNodes 3 sourceRoot = true := by
  decide +kernel

theorem source_path_length {w : List Bool} {op arg : Nat}
    (path : SourcePath sourceNodes sourceRoot w op arg) : 3 ≤ w.length :=
  atLeastDepth_sound source_depth_three path

/-- Exact K215 instance: one source-determined clock and port for every
integer head position and every matching full tape. -/
theorem reaches_primitive_uniform {w : List Bool} {op arg : Nat}
    (path : SourcePath sourceNodes sourceRoot w op arg) :
    ∃ steps q bit,
      w.length - 1 ≤ steps ∧ steps ≤ 7 * (w.length - 1) ∧
      RoutedEntry formal sourceNodes roles 0 w q bit op arg ∧
      ∀ (a : Int) (t : Tape), t (a - 1) = true → Reads t a w →
        run (fullStep formal) steps ⟨84, a, t⟩ =
          some ⟨q, a + (w.length : Int) - 1, t⟩ ∧
        t (a + (w.length : Int) - 1) = bit := by
  obtain ⟨steps, q, bit, lo, hi, route, sem⟩ :=
    source_path_chain_uniform formal sourceNodes roles blocks semantic_edges
      all_blocks_checked durations path 0 rootRole root_role rfl
  refine ⟨steps, q, bit, lo, hi, route, ?_⟩
  intro a t marker word
  have hc : Before t a rootRole.suffix := by
    simpa [Before, Reads, rootRole] using marker
  obtain ⟨chain, last⟩ := sem a t hc word
  exact ⟨chain_sound formal blocks.toList all_blocks_checked t chain, last⟩

/-- Every K215 prefix makes at least two physical steps, uniformly in the tape. -/
theorem reaches_primitive_uniform_positive {w : List Bool} {op arg : Nat}
    (path : SourcePath sourceNodes sourceRoot w op arg) :
    ∃ steps q bit, 2 ≤ steps ∧
      RoutedEntry formal sourceNodes roles 0 w q bit op arg ∧
      ∀ (a : Int) (t : Tape), t (a - 1) = true → Reads t a w →
        run (fullStep formal) steps ⟨84, a, t⟩ =
          some ⟨q, a + (w.length : Int) - 1, t⟩ := by
  obtain ⟨steps, q, bit, lo, _, route, sem⟩ := reaches_primitive_uniform path
  have depth := source_path_length path
  exact ⟨steps, q, bit, by omega, route, fun a t hm hw => (sem a t hm hw).1⟩

#print axioms reaches_primitive_uniform
#print axioms reaches_primitive_uniform_positive
#print axioms source_path_length
end SetTheory.BusyBeaver.ZFC.K215SourcePaths

#print axioms SetTheory.BusyBeaver.ZFC.DecoderPaths.source_path_chain_uniform

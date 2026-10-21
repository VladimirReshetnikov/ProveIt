import BusyBeaver.ZFC.DecoderPaths
import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.SiteCoverage

/-! Kernel binding of the shared decoder certificate to the exact source
program in ProveIt. This removes the earlier Python-only expansion boundary. -/
namespace SetTheory.BusyBeaver.ZFC.DecoderSourceBinding
open FramedWindow DecoderCertificate DecoderPaths K215Decoder
open SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def primitive (op arg : Nat) : RegisterPath.Edge :=
  match op with
  | 0 => .inc arg
  | 1 => .decnz arg
  | 2 => .brk arg
  | 3 => .cont arg
  | _ => .halt

def sourceTree (nodes : Array Node) : Nat → Nat → Tree
  | 0, _ => .none
  | f+1, n => match nodes[n]? with
    | none => .none
    | some (.leaf op arg) => .leaf (primitive op arg)
    | some (.fork l u) => .node (sourceTree nodes f l) (sourceTree nodes f u)

/-- Literal equality, checked by kernel reduction against the upstream source. -/
theorem source_tree_eq : sourceTree sourceNodes 203 sourceRoot = KSource215.t215 := by rfl

/-- Every exact leaf of the expanded source has the corresponding source-DAG path. -/
theorem source_path_of_leaf (nodes : Array Node) : ∀ f n w e,
    LeafAt (sourceTree nodes f n) w e →
      ∃ op arg, e = primitive op arg ∧ SourcePath nodes n w op arg := by
  intro f
  induction f with
  | zero => intro n w e h; cases h
  | succ f ih =>
    intro n w e h
    cases hn : nodes[n]? with
    | none => simp only [sourceTree,hn] at h; cases h
    | some node =>
      cases node with
      | leaf op arg =>
        simp only [sourceTree,hn] at h
        cases h
        exact ⟨op,arg,rfl,SourcePath.leaf hn⟩
      | fork l u =>
        simp only [sourceTree,hn] at h
        cases h with
        | left hl =>
          obtain ⟨op,arg,he,hp⟩ := ih l _ _ hl
          exact ⟨op,arg,he,SourcePath.fork (b := false) hn hp⟩
        | right hl =>
          obtain ⟨op,arg,he,hp⟩ := ih u _ _ hl
          exact ⟨op,arg,he,SourcePath.fork (b := true) hn hp⟩

/-- Every upstream source leaf now has a whole-tape shared-decoder theorem.
The theorem ends at primitive entry; it does not assert primitive execution. -/
theorem upstream_leaf_reaches_routed {w : List Bool} {e : RegisterPath.Edge}
    (leaf : LeafAt KSource215.t215 w e)
    (a : Int) (t : Tape) (marker : t (a-1) = true) (word : Reads t a w) :
    ∃ op arg steps q bit,
      e = primitive op arg ∧ w.length-1 ≤ steps ∧ steps ≤ 7*(w.length-1) ∧
      FramedWindow.run (fullStep formal) steps ⟨84,a,t⟩ = some ⟨q,a+(w.length : Int)-1,t⟩ ∧
      t (a+(w.length : Int)-1) = bit ∧ DecoderPaths.RoutedEntry formal sourceNodes roles 0 w q bit op arg := by
  rw [← source_tree_eq] at leaf
  obtain ⟨op,arg,he,hp⟩ := source_path_of_leaf sourceNodes 203 sourceRoot w e leaf
  obtain ⟨steps,q,bit,lo,hi,hr,hbit,hentry⟩ :=
    K215SourcePaths.reaches_primitive_routed hp a t marker word
  exact ⟨op,arg,steps,q,bit,he,lo,hi,hr,hbit,hentry⟩

/-- The repository walk semantics, including implicit zero padding and consumed
path truncation, feeds the certified decoder without any per-block hypotheses. -/
theorem upstream_walk_reaches_routed (P : List Bool) (e : RegisterPath.Edge) (d : Nat)
    (walks : RegisterPath.walk KSource215.p215 (KSource215.p215.nnodes+1)
      KSource215.p215.root P 0 = some (e,d))
    (a : Int) (t : Tape) (marker : t (a-1) = true)
    (word : Reads t a (consume P d)) :
    ∃ op arg steps q bit,
      e = primitive op arg ∧ d-1 ≤ steps ∧ steps ≤ 7*(d-1) ∧
      FramedWindow.run (fullStep formal) steps ⟨84,a,t⟩ = some ⟨q,a+(d : Int)-1,t⟩ ∧
      t (a+(d : Int)-1) = bit ∧ DecoderPaths.RoutedEntry formal sourceNodes roles 0 (consume P d) q bit op arg := by
  have hw : twalk KSource215.t215 P 0 = some (e,d) := by
    simpa only [walk_root,KSource215.t215_eq] using walks
  have hl := (twalk_leafAt KSource215.t215 P 0 e d hw).2
  have hleaf : LeafAt KSource215.t215 (consume P d) e := by
    simpa only [Nat.sub_zero,RMEquiv.consume_eq] using hl
  have hresult := upstream_leaf_reaches_routed hleaf a t marker word
  have hc : (consume P d).length = d := by
    unfold consume
    simp
  simpa only [hc] using hresult


#print axioms source_tree_eq
#print axioms upstream_leaf_reaches_routed
#print axioms upstream_walk_reaches_routed
end SetTheory.BusyBeaver.ZFC.DecoderSourceBinding

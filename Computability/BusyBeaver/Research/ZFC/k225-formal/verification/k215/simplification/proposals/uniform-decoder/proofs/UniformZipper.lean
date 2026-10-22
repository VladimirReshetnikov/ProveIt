import BusyBeaver.ZFC.KDecoderPrefix215
import UniformDecoder

/-! Stronger exact entry contract for the maintained K215 source and table.
The same clock works for every natural gap and every register list.
This adapts KDecoderPrefix215.entry_run, without choosing a trial tape or
proving uniqueness of separately obtained routes. -/
namespace SetTheory.BusyBeaver.ZFC.KDecoderPrefix215
open KZip KRuntimeCore KSim FramedWindow DecoderCertificate DecoderPaths
open DecoderSourceBinding K215Decoder RegisterPath SiteCoverage
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem leaf_prefix_uniform {word : List Bool} {e : RegisterPath.Edge}
    (leaf : LeafAt KSource215.t215 word e) :
    ∃ pre bit q op arg steps,
      word = pre ++ [bit] ∧ e = primitive op arg ∧
      RoutedEntry formal sourceNodes roles 0 word q bit op arg ∧
      2 ≤ steps ∧ pre.length ≤ steps ∧ steps ≤ 7 * pre.length ∧
      ∀ n vs, KZip.run KTableCore.tm215 steps (conc n vs (start word)) =
        some (conc n vs (leafPort pre bit q)) := by
  rw [← source_tree_eq] at leaf
  obtain ⟨op, arg, he, path⟩ := source_path_of_leaf sourceNodes 203 sourceRoot word e leaf
  obtain ⟨steps, q, bit, lo, hi, route, sem⟩ :=
    K215SourcePaths.reaches_primitive_uniform path
  have depth := K215SourcePaths.source_path_length path
  obtain ⟨pre, hsplit⟩ : ∃ pre, word = pre ++ [bit] := by
    obtain ⟨pre, _, _, _, _, hsplit, _⟩ := route
    exact ⟨pre, hsplit⟩
  have hlen : word.length - 1 = pre.length := by simp [hsplit]
  have hhead : (word.length : Int) - 1 = (pre.length : Int) := by simp [hsplit]
  refine ⟨pre, bit, q, op, arg, steps, hsplit, he, route, by omega,
    hlen ▸ lo, hlen ▸ hi, ?_⟩
  intro n vs
  let rest := List.replicate (n + (D0 - word.length)) false ++ true :: sepsR vs
  let z := zc 84 [true] (word ++ rest)
  let t := KZipTape.tape z
  have hrel : KZipTape.Rel ⟨84, 0, t⟩ z := KZipTape.rel_full z
  have hm : t (-1) = true := by
    have h := (hrel.2 0).2
    change t (-1) = (trim [true]).getD 0 false at h
    rw [← List.headD_eq_getD, headD_trim] at h
    exact h
  have hw : Reads t 0 word := reads_of_rel word hrel
  obtain ⟨hs, _⟩ := sem 0 t (by simpa using hm) hw
  have hrel' : KZipTape.Rel ⟨84, 0, t⟩ (zc 84 [true] (pre ++ (bit :: rest))) := by
    simpa only [z, hsplit, List.append_assoc, List.singleton_append] using hrel
  have hend : KZipTape.Rel ⟨q, (pre.length : Int), t⟩
      (zc q (pre.reverse ++ [true]) (bit :: rest)) := by
    simpa only [Int.zero_add] using rel_word pre hrel' q
  have hs' : FramedWindow.run (fullStep (KZipTape.table KTableCore.tm215)) steps
      ⟨84, 0, t⟩ = some ⟨q, (pre.length : Int), t⟩ := by
    simpa only [formal, Int.zero_add, hhead] using hs
  have hz := KZipTape.run_reflect hrel hend
    ⟨trim_trim _, trim_trim _⟩ ⟨trim_trim _, trim_trim _⟩ hs'
  have hstart : conc n vs (start word) = z := by
    simpa only [z, rest, List.append_assoc] using conc_start n vs word
  have hport : conc n vs (leafPort pre bit q) =
      zc q (pre.reverse ++ [true]) (bit :: rest) := by
    simp only [conc_leafPort, rest, hsplit, List.length_append,
      List.length_singleton, List.cons_append]
  simpa only [hstart, hport] using hz

/-- This retains the upstream walk's implicit zero padding. -/
theorem walk_prefix_uniform (P : List Bool) (e : RegisterPath.Edge) (d : Nat)
    (walks : RegisterPath.walk KSource215.p215 (KSource215.p215.nnodes + 1)
      KSource215.p215.root P 0 = some (e, d)) :
    ∃ pre bit q op arg steps,
      consume P d = pre ++ [bit] ∧ e = primitive op arg ∧
      RoutedEntry formal sourceNodes roles 0 (consume P d) q bit op arg ∧
      2 ≤ steps ∧ pre.length ≤ steps ∧ steps ≤ 7 * pre.length ∧
      ∀ n vs, KZip.run KTableCore.tm215 steps (conc n vs (start (consume P d))) =
        some (conc n vs (leafPort pre bit q)) := by
  have hw : RMBisim.twalk KSource215.t215 P 0 = some (e, d) := by
    simpa only [RMBisim.walk_root, KSource215.t215_eq] using walks
  have hl := (twalk_leafAt KSource215.t215 P 0 e d hw).2
  have hleaf : LeafAt KSource215.t215 (consume P d) e := by
    simpa only [Nat.sub_zero, RMEquiv.consume_eq] using hl
  exact leaf_prefix_uniform hleaf

/-- A tail may be reflexive: the certified decoder already made progress.
The predicate `valid` can retain either decrement polarity or any other
precise register precondition. Targets may depend on the natural parameters. -/
theorem prefix_tail_sound {pre : List Bool} {bit : Bool} {q steps : Nat}
    {word : List Bool} (positive : 0 < steps)
    (hpref : ∀ n vs, KZip.run KTableCore.tm215 steps (conc n vs (start word)) =
      some (conc n vs (leafPort pre bit q)))
    (valid : Nat → List Nat → Prop) (target : Nat → List Nat → KZip.Conf)
    (tail : ∀ n vs, valid n vs →
      Reach KTableCore.tm215 (conc n vs (leafPort pre bit q)) (target n vs)) :
    ∀ n vs, valid n vs →
      Reach1 KTableCore.tm215 (conc n vs (start word)) (target n vs) := by
  intro n vs hv
  have hp : Reach1 KTableCore.tm215 (conc n vs (start word))
      (conc n vs (leafPort pre bit q)) := by
    refine ⟨steps - 1, ?_⟩
    simpa only [Nat.sub_add_cancel positive] using hpref n vs
  exact hp.trans_reach (tail n vs hv)

#print axioms leaf_prefix_uniform
#print axioms walk_prefix_uniform
#print axioms prefix_tail_sound
end SetTheory.BusyBeaver.ZFC.KDecoderPrefix215

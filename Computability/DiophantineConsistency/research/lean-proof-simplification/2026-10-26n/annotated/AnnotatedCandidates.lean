/-!
UNCOMPILED REVIEW CANDIDATES. No Lean toolchain was available for this review.
Target source commit: b310142330df89e48413c8fce62e7de223e1c7d5.
This scratch file does not modify the source snapshot. Candidate theorem names
are suffixed to coexist with the currently checked declarations.
-/
import DiophantineConsistency.AnnotatedParents

namespace DiophantineConsistency.AnnotatedParents

/-- Same statement as check_raw_iff; reuse the already available total raw
six-field table decoder, then the existing typed-list checker theorem.
The decoder is used only in a Prop proof, not added to the executable checker. -/
theorem check_raw_iff_short (fuel : Nat) (history expected : List Nat) (parents : Nat)
    (hf : expected.length ≤ fuel) :
    check fuel (AnnotatedCodeArithmetic.listCode history)
      (AnnotatedCodeArithmetic.listCode expected) parents = 1 ↔
      ∃ indices : List Nat, parents = AnnotatedCodeArithmetic.listCode indices ∧
        indices.map (fun i => history[i]?) = expected.map some := by
  constructor
  · intro h
    obtain ⟨rows, hr⟩ :=
      AnnotatedRenameScan.decodeTable_total parents parents (Nat.le_refl _)
    have he : AnnotatedCodeArithmetic.listCode (rows.map AnnotatedRename.rowCode) = parents :=
      AnnotatedRenameScan.tableCode_of_decode hr
    refine ⟨rows.map AnnotatedRename.rowCode, he.symm, ?_⟩
    exact (check_lists fuel history expected _ hf).mp (by simpa only [he] using h)
  · rintro ⟨indices, rfl, h⟩
    exact (check_lists fuel history expected indices hf).mpr h

end DiophantineConsistency.AnnotatedParents

namespace DiophantineConsistency.AnnotatedProofCode.Tree

/-- Fuse the two existing decoder soundness inductions, retaining both facts. -/
theorem decode_spec_short {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) : t.quote = code ∧ t.depth ≤ fuel := by
  induction fuel generalizing code t with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases code with
    | zero => simp [decode] at h
    | succ code =>
      have hp := Nat.pair_unpair code
      simp only [decode] at h
      cases he : (Nat.unpair code).1 with
      | zero =>
        simp only [he] at h hp
        cases h
        exact ⟨by simp only [quote, hp], by simp [depth]⟩
      | succ left =>
        simp only [he] at h hp
        cases ha : decode fuel left with
        | none => simp [ha] at h
        | some a =>
          cases hb : decode fuel (Nat.unpair code).2 with
          | none => simp [ha, hb] at h
          | some b =>
            simp only [ha, hb, Option.pure_def] at h
            cases h
            obtain ⟨hqa, hda⟩ := ih ha
            obtain ⟨hqb, hdb⟩ := ih hb
            exact ⟨by simp only [quote, hqa, hqb, hp], by simp only [depth]; omega⟩

theorem decoded_depth_le_short {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) : t.depth ≤ fuel :=
  (decode_spec_short h).2

theorem quote_of_decode_short {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) : t.quote = code :=
  (decode_spec_short h).1

/-- Optional public API: the two soundness facts and the existing completeness
lemma characterize successful decoding even for arbitrary raw natural codes. -/
theorem decode_eq_some_iff_short {fuel code : Nat} {t : Tree} :
    decode fuel code = some t ↔ t.quote = code ∧ t.depth ≤ fuel := by
  constructor
  · exact decode_spec_short
  · rintro ⟨rfl, hf⟩
    exact decode_quote t fuel hf

end DiophantineConsistency.AnnotatedProofCode.Tree

#print axioms DiophantineConsistency.AnnotatedParents.check_raw_iff_short
#print axioms DiophantineConsistency.AnnotatedProofCode.Tree.decode_spec_short
#print axioms DiophantineConsistency.AnnotatedProofCode.Tree.decoded_depth_le_short
#print axioms DiophantineConsistency.AnnotatedProofCode.Tree.quote_of_decode_short
#print axioms DiophantineConsistency.AnnotatedProofCode.Tree.decode_eq_some_iff_short

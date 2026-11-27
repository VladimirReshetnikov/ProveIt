import DiophantineConsistency.ObjectNumericWire

/-! # Internal descent bounds for the actual numeric tree projections -/
noncomputable section
namespace DiophantineConsistency.ObjectWireBounds
open SetTheory ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem self_le_square (x : N H) : x≤x*x := by
  rcases ObjectNaturalDiscrete.zero_or_add_one H x with hz | ⟨s,rfl⟩
  · simp only [hz,zero_mul,le_refl]
  · exact (ObjectNaturalOrder.Natural.le_iff_exists_add H _ _).mpr ⟨(s+1)*s,by ring⟩

private theorem max_le_pair (a b : N H) : max a b ≤ ObjectNatPairing.pair H a b :=
  (self_le_square H (max a b)).trans (MaxSquarePairing.max_square_le_pair a b)

theorem right_le_pair (a b : N H) : b ≤ ObjectNatPairing.pair H a b :=
  (le_max_right a b).trans (max_le_pair H a b)

theorem pred_le (n : N H) : ObjectPredecessor.pred H n≤n := by
  by_cases hz : n=0
  · simp only [hz,ObjectPredecessor.pred_zero,le_refl]
  · calc
      ObjectPredecessor.pred H n ≤ ObjectPredecessor.pred H n + 1 := le_self_add
      _ = n := (ObjectPredecessor.pred_spec H n hz).symm

theorem pred_lt {n : N H} (hn : n≠0) : ObjectPredecessor.pred H n<n :=
  (ObjectNaturalDiscrete.lt_iff_exists_add_one H _ _).mpr
    ⟨0,by simpa only [add_zero] using ObjectPredecessor.pred_spec H n hn⟩

theorem left_le_pred (code : N H) :
    ObjectNumericWire.treeLeft H code≤ObjectPredecessor.pred H code := by
  let ab := ObjectUnpair.unpair H (ObjectPredecessor.pred H code)
  have h := (le_max_left ab.1 ab.2).trans (max_le_pair H ab.1 ab.2)
  simpa only [ab, ObjectUnpair.pair_unpair, ObjectNumericWire.treeLeft] using h

theorem right_le_pred (code : N H) :
    ObjectNumericWire.treeRight H code≤ObjectPredecessor.pred H code := by
  have h := right_le_pair H
    (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).1
    (ObjectUnpair.unpair H (ObjectPredecessor.pred H code)).2
  simpa only [ObjectUnpair.pair_unpair,ObjectNumericWire.treeRight] using h

theorem left_lt {code : N H} (hc : code≠0) : ObjectNumericWire.treeLeft H code<code :=
  (left_le_pred H code).trans_lt (pred_lt H hc)
theorem right_lt {code : N H} (hc : code≠0) : ObjectNumericWire.treeRight H code<code :=
  (right_le_pred H code).trans_lt (pred_lt H hc)
theorem leftChild_lt {code : N H} (hc : code≠0) :
    ObjectPredecessor.pred H (ObjectNumericWire.treeLeft H code)<code :=
  (pred_le H _).trans_lt (left_lt H hc)

/-- This classifies the outer wire constructor. It does not assert that
the two child codes satisfy any recursive tree/formula grammar. -/
theorem zero_or_atom_or_fork (code : N H) :
    code=0 ∨ (∃ n,code=ObjectNumericWire.atom H n) ∨
      ∃ a b,code=ObjectNumericWire.fork H a b := by
  rcases ObjectNumericWire.zero_or_cons H code with hz | hc
  · exact Or.inl hz
  · right
    by_cases hl : ObjectNumericWire.treeLeft H code=0
    · exact Or.inl ⟨ObjectNumericWire.treeRight H code,by
        simpa only [hl,ObjectNumericWire.cons,ObjectNumericWire.atom] using hc⟩
    · right
      refine ⟨ObjectPredecessor.pred H (ObjectNumericWire.treeLeft H code),
        ObjectNumericWire.treeRight H code,?_⟩
      simpa only [ObjectNumericWire.cons,ObjectNumericWire.fork,
        ← ObjectPredecessor.pred_spec H (ObjectNumericWire.treeLeft H code) hl] using hc

end DiophantineConsistency.ObjectWireBounds

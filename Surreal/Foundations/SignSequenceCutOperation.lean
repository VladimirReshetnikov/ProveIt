import Surreal.Foundations.SignSequenceCut
import Surreal.Foundations.SignSequenceSimplicity
import Surreal.Foundations.SmallCutData

/-!
# The simplest small-cut operation

The existence and simplicity proofs together define a canonical cut
operation on the actual sign carrier. Its output separates the options,
is a prefix of every separator, and satisfies the ordinal birthday bound
required by `found:sub:package`. Reindexing and equal separator predicates
preserve its value. Sign reversal obeys the negated-cut rule
`found:eq:negcut`, and all bounds in `found:lem:bounds` follow.

These results do not supply addition, multiplication, or a field instance.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The canonical simplest separator of a small separated cut. -/
def cut (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) : SignSequence.{u} :=
  (existsUnique_simplest_separator c (small_cut_fillers c)).choose

/-- The cut operation separates its two option families. -/
theorem cut_realizes (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    c.IsRealizedBy (cut c) :=
  (existsUnique_simplest_separator c (small_cut_fillers c)).choose_spec.1.1

/-- The cut value is a sign prefix of every other separator. -/
theorem cut_isPrefix (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (y : SignSequence.{u}) (hy : c.IsRealizedBy y) : IsPrefix (cut c) y :=
  (existsUnique_simplest_separator c (small_cut_fillers c)).choose_spec.1.2 y hy

/-- The cut value is the unique separator of minimum birthday. -/
theorem cut_eq_iff (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (x : SignSequence.{u}) :
    cut c = x ↔ c.IsRealizedBy x ∧
      ∀ y, c.IsRealizedBy y → x.birthday ≤ y.birthday := by
  constructor
  · rintro rfl
    exact ⟨cut_realizes c, fun y hy => (cut_isPrefix c y hy).1⟩
  · rintro ⟨hx, hmin⟩
    exact IsPrefix.antisymm (cut_isPrefix c x hx)
      (isPrefix_of_minimum_birthday (ordConnected_separators c) hx hmin (cut_realizes c))

/-- Reconstructing from the canonical truncation options returns the
original sign sequence. -/
@[simp] theorem cut_canonicalCut (x : SignSequence.{u}) : cut (canonicalCut x) = x :=
  IsPrefix.antisymm (cut_isPrefix _ x (canonicalCut_realized x))
    (canonicalCut_isPrefix x _ (cut_realizes _))

/-- Any common strict bound on the option birthdays bounds the birthday
of the simplest separator. -/
theorem birthday_cut_le (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (b : Ordinal.{u}) (hl : ∀ i, (c.left i).birthday < b)
    (hr : ∀ i, (c.right i).birthday < b) : (cut c).birthday ≤ b := by
  obtain ⟨y, hb, hy⟩ := exists_cut_separator_of_birthday_lt c b hl hr
  simpa only [hb] using (cut_isPrefix c y hy).1

/-- The explicit small supremum of successor option birthdays is a rank
bound for the cut constructor, including empty option families. -/
theorem birthday_cut_le_iSup (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    (cut c).birthday ≤ ⨆ i : c.Left ⊕ c.Right, (Sum.elim c.left c.right i).birthday + 1 := by
  apply birthday_cut_le
  · intro i
    exact Ordinal.lt_iSup_add_one (fun j => (Sum.elim c.left c.right j).birthday) (Sum.inl i)
  · intro i
    exact Ordinal.lt_iSup_add_one (fun j => (Sum.elim c.left c.right j).birthday) (Sum.inr i)

/-- Cut values depend only on the separators, hence not on duplicate
options or their particular indexing types. -/
theorem cut_congr (c d : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    (h : ∀ x, c.IsRealizedBy x ↔ d.IsRealizedBy x) : cut c = cut d :=
  IsPrefix.antisymm (cut_isPrefix c _ ((h _).mpr (cut_realizes d)))
    (cut_isPrefix d _ ((h _).mp (cut_realizes c)))

@[simp] theorem cut_reindex (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·))
    {L R : Type u} (eL : L ≃ c.Left) (eR : R ≃ c.Right) :
    cut (c.reindex eL eR) = cut c :=
  cut_congr _ _ (fun x => SmallCutData.reindex_isRealizedBy_iff c eL eR x)

/-- Sign reversal preserves the prefix relation. -/
theorem IsPrefix.neg {x y : SignSequence.{u}} (h : IsPrefix x y) : IsPrefix (-x) (-y) :=
  ⟨h.1, fun i hi => congrArg Neg.neg (h.2 i hi)⟩

/-- Swap and negate the option families, as in `found:eq:negcut`. -/
def negateCut (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := c.Right
  Right := c.Left
  left i := -c.right i
  right i := -c.left i
  separated i j := (neg_lt_neg_iff _ _).mpr (c.separated j i)

@[simp] theorem negateCut_realizes_iff
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) (x : SignSequence.{u}) :
    (negateCut c).IsRealizedBy x ↔ c.IsRealizedBy (-x) := by
  change (∀ i, -c.right i < x) ∧ (∀ i, x < -c.left i) ↔
    (∀ i, c.left i < -x) ∧ (∀ i, -x < c.right i)
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun i => by simpa only [neg_neg] using (neg_lt_neg_iff _ _).mpr (hr i),
      fun i => by simpa only [neg_neg] using (neg_lt_neg_iff _ _).mpr (hl i)⟩
  · rintro ⟨hl, hr⟩
    exact ⟨fun i => by simpa only [neg_neg] using (neg_lt_neg_iff _ _).mpr (hr i),
      fun i => by simpa only [neg_neg] using (neg_lt_neg_iff _ _).mpr (hl i)⟩

/-- The actual simplest cut operation satisfies Conway's negation rule. -/
@[simp] theorem cut_negateCut
    (c : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·)) :
    cut (negateCut c) = -cut c := by
  apply (cut_eq_iff _ _).mpr
  constructor
  · rw [negateCut_realizes_iff, neg_neg]
    exact cut_realizes c
  · intro y hy
    exact (cut_isPrefix c (-y) ((negateCut_realizes_iff c y).mp hy)).1

/-- Every small family has a strict lower bound in the constructed sign
carrier, completing the two-sided bound assertion of `found:lem:bounds`. -/
theorem exists_strict_lower_bound (I : Type u) (f : I → SignSequence.{u}) :
    ∃ b : SignSequence.{u}, ∀ i, b < f i :=
  small_cut_fillers.exists_strict_lower_bound I f

/-- A small family of positive sign numbers has a positive strict lower
bound, including the empty family (`found:lem:bounds`). -/
theorem exists_positive_lower_bound (I : Type u) (f : I → SignSequence.{u})
    (hf : ∀ i, 0 < f i) : ∃ b : SignSequence.{u}, 0 < b ∧ ∀ i, b < f i :=
  small_cut_fillers.exists_strict_lower_bound_above 0 I f hf

/-- The predicate-based version of cut filling uses explicit smallness
witnesses for both option sets. -/
theorem exists_separator_of_small_sets (L R : Set SignSequence.{u})
    [Small.{u} L] [Small.{u} R] (h : ∀ l ∈ L, ∀ r ∈ R, l < r) :
    ∃ x, (∀ l ∈ L, l < x) ∧ (∀ r ∈ R, x < r) :=
  small_cut_fillers.exists_separator_of_small_sets L R h

instance : DenselyOrdered SignSequence.{u} where
  dense x y h := by
    obtain ⟨z, hx, hy⟩ := small_cut_fillers.exists_strict_lower_bound_above x PUnit
      (fun _ => y) (fun _ => h)
    exact ⟨z, hx, hy PUnit.unit⟩

instance : NoMinOrder SignSequence.{u} where
  exists_lt x := by
    obtain ⟨y, hy⟩ := exists_strict_lower_bound PUnit (fun _ => x)
    exact ⟨y, hy PUnit.unit⟩

instance : NoMaxOrder SignSequence.{u} where
  exists_gt x := by
    obtain ⟨y, hy⟩ := small_strict_upper_bounds PUnit (fun _ => x)
    exact ⟨y, hy PUnit.unit⟩

end

end Surreal.Foundations.SignSequence

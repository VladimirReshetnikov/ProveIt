import KlarnerConstant.GeometricLinear
import KlarnerConstant.GeometricDeletion
import KlarnerConstant.PublishedSystem

/-!
# The geometric coefficient profile and recurrence interface

The seventeen coefficient sequences in this file are no longer abstract:
each is the aggregate count of occurrences of the corresponding
`BuiNeighborhood` over normalized fixed polyominoes.

The elementary parts of the published recurrence system are discharged here:

* nonnegativity and the degree-zero convention follow from finite counting;
* the degree-one values are computed on the unique normalized singleton;
* `C`, `D`, and `E` use the proved north-leaf deletion maps;
* `F`, `G`, `H`, `R`, and `T` use the proved finite pattern partitions.

`GeometricBuiGaps` consequently exposes exactly the nine non-elementary
recurrence fields as a reusable interface.  The dedicated geometric modules
prove those fields, and `GeometricComplete.lean` supplies them to construct the
literal `PublishedBuiRecurrences` instance, with no other combinatorial
assumptions hidden in the adapter.
-/

namespace LeanProofs.KlarnerConstant

/-- The actual seventeen Bui coefficient sequences obtained by summing local
pattern occurrences over normalized polyominoes. -/
noncomputable def geometricCoefficientProfile : CoefficientProfile where
  c := BuiNeighborhood.c.coefficient
  d := BuiNeighborhood.d.coefficient
  e := BuiNeighborhood.e.coefficient
  f := BuiNeighborhood.f.coefficient
  g := BuiNeighborhood.g.coefficient
  h := BuiNeighborhood.h.coefficient
  p := BuiNeighborhood.p.coefficient
  q := BuiNeighborhood.q.coefficient
  r := BuiNeighborhood.r.coefficient
  s := BuiNeighborhood.s.coefficient
  t := BuiNeighborhood.t.coefficient
  u := BuiNeighborhood.u.coefficient
  v := BuiNeighborhood.v.coefficient
  w := BuiNeighborhood.w.coefficient
  x := BuiNeighborhood.x.coefficient
  y := BuiNeighborhood.y.coefficient
  z := BuiNeighborhood.z.coefficient

private theorem geometricCoefficient_nonnegative
    (kind : BuiNeighborhood) (n : ℕ) :
    0 ≤ kind.coefficient n := by
  unfold BuiNeighborhood.coefficient
  exact_mod_cast Nat.zero_le (kind.aggregateOccurrenceCount n)

/-- Every coordinate of the geometric profile is nonnegative. -/
theorem geometricCoefficientProfile_nonnegative :
    geometricCoefficientProfile.Nonnegative := by
  exact
    ⟨fun n ↦ geometricCoefficient_nonnegative .c n,
      fun n ↦ geometricCoefficient_nonnegative .d n,
      fun n ↦ geometricCoefficient_nonnegative .e n,
      fun n ↦ geometricCoefficient_nonnegative .f n,
      fun n ↦ geometricCoefficient_nonnegative .g n,
      fun n ↦ geometricCoefficient_nonnegative .h n,
      fun n ↦ geometricCoefficient_nonnegative .p n,
      fun n ↦ geometricCoefficient_nonnegative .q n,
      fun n ↦ geometricCoefficient_nonnegative .r n,
      fun n ↦ geometricCoefficient_nonnegative .s n,
      fun n ↦ geometricCoefficient_nonnegative .t n,
      fun n ↦ geometricCoefficient_nonnegative .u n,
      fun n ↦ geometricCoefficient_nonnegative .v n,
      fun n ↦ geometricCoefficient_nonnegative .w n,
      fun n ↦ geometricCoefficient_nonnegative .x n,
      fun n ↦ geometricCoefficient_nonnegative .y n,
      fun n ↦ geometricCoefficient_nonnegative .z n⟩

private theorem normalizedPolyomino_zero_elim
    (P : NormalizedPolyomino 0) : False := by
  have hpositive : 0 < P.toPolyomino.cells.card :=
    Finset.card_pos.mpr P.toPolyomino.nonempty
  rw [P.card_cells] at hpositive
  omega

private theorem geometricAggregate_zero (kind : BuiNeighborhood) :
    kind.aggregateOccurrenceCount 0 = 0 := by
  classical
  unfold BuiNeighborhood.aggregateOccurrenceCount
  apply Finset.sum_eq_zero
  intro P _
  exact (normalizedPolyomino_zero_elim P).elim

private theorem geometricCoefficient_zero (kind : BuiNeighborhood) :
    kind.coefficient 0 = 0 := by
  unfold BuiNeighborhood.coefficient
  exact_mod_cast geometricAggregate_zero kind

/-- All geometric coefficient sequences use the positive-index convention. -/
theorem geometricCoefficientProfile_zeroAtZero :
    geometricCoefficientProfile.ZeroAtZero := by
  exact
    ⟨geometricCoefficient_zero .c, geometricCoefficient_zero .d,
      geometricCoefficient_zero .e, geometricCoefficient_zero .f,
      geometricCoefficient_zero .g, geometricCoefficient_zero .h,
      geometricCoefficient_zero .p, geometricCoefficient_zero .q,
      geometricCoefficient_zero .r, geometricCoefficient_zero .s,
      geometricCoefficient_zero .t, geometricCoefficient_zero .u,
      geometricCoefficient_zero .v, geometricCoefficient_zero .w,
      geometricCoefficient_zero .x, geometricCoefficient_zero .y,
      geometricCoefficient_zero .z⟩

/-! ## Exact degree-one coefficients -/

/-- The unique one-cell polyomino before recording its normalization proof. -/
private def singletonPolyomino : Polyomino where
  cells := {(0, 0)}
  nonempty := by simp
  edgeConnected := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact Relation.ReflTransGen.refl

private theorem singletonPolyomino_southwestAnchor :
    singletonPolyomino.southwestAnchor = (0, 0) := by
  apply singletonPolyomino.isSouthwestAnchor_unique
  · exact singletonPolyomino.southwestAnchor_isSouthwest
  · refine ⟨by simp [singletonPolyomino], ?_, ?_⟩
    · intro c hc
      simp only [singletonPolyomino, Finset.mem_singleton] at hc
      subst c
      simp
    · intro c hc _
      simp only [singletonPolyomino, Finset.mem_singleton] at hc
      subst c
      simp

/-- The canonical normalized one-cell polyomino. -/
private noncomputable def singletonNormalizedPolyomino :
    NormalizedPolyomino 1 where
  toPolyomino := singletonPolyomino
  southwestAnchor_eq := singletonPolyomino_southwestAnchor
  card_cells := by simp [singletonPolyomino]

private theorem normalizedPolyomino_one_eq_singleton
    (P : NormalizedPolyomino 1) : P = singletonNormalizedPolyomino := by
  apply NormalizedPolyomino.ext
  apply Polyomino.ext
  obtain ⟨cell, hcells⟩ := Finset.card_eq_one.mp P.card_cells
  have horigin : (0, 0) ∈ ({cell} : Finset Cell) := by
    rw [← hcells]
    exact P.origin_mem
  have hcell : cell = (0, 0) := by
    have : (0, 0) = cell := by
      simpa only [Finset.mem_singleton] using horigin
    exact this.symm
  subst cell
  simpa [singletonNormalizedPolyomino, singletonPolyomino] using hcells

private theorem univ_normalizedPolyomino_one :
    (Finset.univ : Finset (NormalizedPolyomino 1)) =
      {singletonNormalizedPolyomino} := by
  ext P
  simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
  exact normalizedPolyomino_one_eq_singleton P

private theorem occursAt_singleton_origin_of_required_subset
    (pattern : OffsetPattern)
    (hrequired : pattern.required ⊆ {(0, 0)})
    (hforbidden : (0, 0) ∉ pattern.forbidden) :
    pattern.OccursAt ({(0, 0)} : Finset Cell) (0, 0) := by
  constructor
  · intro offset hoffset
    have hzero : offset = (0, 0) :=
      Finset.mem_singleton.mp (hrequired hoffset)
    subst offset
    simp
  · intro offset hoffset hmem
    have hzero : offset = (0 : Cell) := by
      have hadd : (0 : Cell) + offset = (0 : Cell) :=
        Finset.mem_singleton.mp hmem
      simpa only [zero_add] using hadd
    subst offset
    exact hforbidden hoffset

private theorem not_occursAt_singleton_origin_of_required_nonzero
    (pattern : OffsetPattern) (offset : Cell)
    (hrequired : offset ∈ pattern.required) (hoffset : offset ≠ (0 : Cell)) :
    ¬pattern.OccursAt ({(0, 0)} : Finset Cell) (0, 0) := by
  intro hoccurs
  have hmem := hoccurs.1 offset hrequired
  have hzero : offset = (0 : Cell) := by
    have hadd : (0 : Cell) + offset = (0 : Cell) :=
      Finset.mem_singleton.mp hmem
    simpa only [zero_add] using hadd
  exact hoffset hzero

private theorem occurrenceCount_singleton_eq_one
    (pattern : OffsetPattern)
    (hoccurs : pattern.OccursAt ({(0, 0)} : Finset Cell) (0, 0)) :
    pattern.occurrenceCount ({(0, 0)} : Finset Cell) = 1 := by
  classical
  unfold OffsetPattern.occurrenceCount OffsetPattern.occurrenceAnchors
  rw [Finset.filter_eq_self.mpr]
  · simp
  · intro anchor hanchor
    have hzero : anchor = (0, 0) := Finset.mem_singleton.mp hanchor
    subst anchor
    exact hoccurs

private theorem occurrenceCount_singleton_eq_zero
    (pattern : OffsetPattern)
    (hoccurs : ¬pattern.OccursAt ({(0, 0)} : Finset Cell) (0, 0)) :
    pattern.occurrenceCount ({(0, 0)} : Finset Cell) = 0 := by
  classical
  unfold OffsetPattern.occurrenceCount OffsetPattern.occurrenceAnchors
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro anchor hanchor
  have hzero : anchor = (0, 0) := Finset.mem_singleton.mp hanchor
  subst anchor
  exact hoccurs

private theorem singleton_positive_pattern_occurs :
    ∀ kind : BuiNeighborhood,
      kind = .c ∨ kind = .d ∨ kind = .e ∨ kind = .f ∨
        kind = .g ∨ kind = .h →
      kind.pattern.OccursAt ({(0, 0)} : Finset Cell) (0, 0) := by
  intro kind hkind
  rcases hkind with rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply occursAt_singleton_origin_of_required_subset <;>
    simp [BuiNeighborhood.pattern, buiCPattern, buiDPattern, buiEPattern,
      buiFPattern, buiGPattern, buiHPattern]

private theorem singleton_multicell_pattern_not_occurs :
    ∀ kind : BuiNeighborhood,
      kind = .p ∨ kind = .q ∨ kind = .r ∨ kind = .s ∨
        kind = .t ∨ kind = .u ∨ kind = .v ∨ kind = .w ∨
        kind = .x ∨ kind = .y ∨ kind = .z →
      ¬kind.pattern.OccursAt ({(0, 0)} : Finset Cell) (0, 0) := by
  intro kind hkind
  apply not_occursAt_singleton_origin_of_required_nonzero
    kind.pattern (1, 0)
  · rcases hkind with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      simp [BuiNeighborhood.pattern, buiPPattern, buiQPattern, buiRPattern,
        buiSPattern, buiTPattern, buiUPattern, buiVPattern, buiWPattern,
        buiXPattern, buiYPattern, buiZPattern]
  · norm_num

private theorem geometricCoefficient_one_eq_singleton_count
    (kind : BuiNeighborhood) :
    kind.coefficient 1 =
      (kind.pattern.occurrenceCount ({(0, 0)} : Finset Cell) : ℚ) := by
  classical
  unfold BuiNeighborhood.coefficient BuiNeighborhood.aggregateOccurrenceCount
  rw [univ_normalizedPolyomino_one]
  simp [BuiNeighborhood.occurrenceCount, singletonNormalizedPolyomino,
    singletonPolyomino]

/-- Uniform computation of all seventeen degree-one coefficients. -/
private theorem geometricCoefficient_one (kind : BuiNeighborhood) :
    kind.coefficient 1 =
      match kind with
      | .c => 1
      | .d => 1
      | .e => 1
      | .f => 1
      | .g => 1
      | .h => 1
      | .p => 0
      | .q => 0
      | .r => 0
      | .s => 0
      | .t => 0
      | .u => 0
      | .v => 0
      | .w => 0
      | .x => 0
      | .y => 0
      | .z => 0 := by
  rw [geometricCoefficient_one_eq_singleton_count]
  cases kind with
  | c =>
      rw [occurrenceCount_singleton_eq_one _
        (singleton_positive_pattern_occurs .c (by simp))]
      norm_num
  | d =>
      rw [occurrenceCount_singleton_eq_one _
        (singleton_positive_pattern_occurs .d (by simp))]
      norm_num
  | e =>
      rw [occurrenceCount_singleton_eq_one _
        (singleton_positive_pattern_occurs .e (by simp))]
      norm_num
  | f =>
      rw [occurrenceCount_singleton_eq_one _
        (singleton_positive_pattern_occurs .f (by simp))]
      norm_num
  | g =>
      rw [occurrenceCount_singleton_eq_one _
        (singleton_positive_pattern_occurs .g (by simp))]
      norm_num
  | h =>
      rw [occurrenceCount_singleton_eq_one _
        (singleton_positive_pattern_occurs .h (by simp))]
      norm_num
  | p =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .p (by simp))]
      norm_num
  | q =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .q (by simp))]
      norm_num
  | r =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .r (by simp))]
      norm_num
  | s =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .s (by simp))]
      norm_num
  | t =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .t (by simp))]
      norm_num
  | u =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .u (by simp))]
      norm_num
  | v =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .v (by simp))]
      norm_num
  | w =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .w (by simp))]
      norm_num
  | x =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .x (by simp))]
      norm_num
  | y =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .y (by simp))]
      norm_num
  | z =>
      rw [occurrenceCount_singleton_eq_zero _
        (singleton_multicell_pattern_not_occurs .z (by simp))]
      norm_num

/-- The exact degree-one values from Bui's published system: the six
single-cell neighborhoods contribute one, and the eleven multi-cell
neighborhoods contribute zero. -/
theorem geometricCoefficientProfile_initial :
    geometricCoefficientProfile.PublishedInitialValues := by
  exact
    ⟨geometricCoefficient_one .c, geometricCoefficient_one .d,
      geometricCoefficient_one .e, geometricCoefficient_one .f,
      geometricCoefficient_one .g, geometricCoefficient_one .h,
      geometricCoefficient_one .p, geometricCoefficient_one .q,
      geometricCoefficient_one .r, geometricCoefficient_one .s,
      geometricCoefficient_one .t, geometricCoefficient_one .u,
      geometricCoefficient_one .v, geometricCoefficient_one .w,
      geometricCoefficient_one .x, geometricCoefficient_one .y,
      geometricCoefficient_one .z⟩

/-- The `G` coordinate of the actual geometric profile dominates the number
of normalized fixed polyominoes. -/
theorem fixedPolyominoCount_le_geometricCoefficientProfile_g (n : ℕ) :
    (fixedPolyominoCount n : ℚ) ≤ geometricCoefficientProfile.g n := by
  have hnat : fixedPolyominoCount n ≤
      BuiNeighborhood.g.aggregateOccurrenceCount n := by
    simpa [gCount, BuiNeighborhood.aggregateOccurrenceCount,
      BuiNeighborhood.occurrenceCount] using fixedPolyominoCount_le_gCount n
  change (fixedPolyominoCount n : ℚ) ≤
    (BuiNeighborhood.g.aggregateOccurrenceCount n : ℚ)
  exact_mod_cast hnat

/-! ## The nine-field geometric interface -/

/-- The nine non-elementary published recurrence fields.  All fields refer to
the actual occurrence-count profile; the dedicated geometric modules prove
them and `GeometricComplete.lean` assembles the resulting structure. -/
structure GeometricBuiGaps : Prop where
  p : ∀ n, 2 ≤ n → geometricCoefficientProfile.p n ≤
    cauchyTwo geometricCoefficientProfile.e geometricCoefficientProfile.h n +
    cauchyTwo geometricCoefficientProfile.q geometricCoefficientProfile.d n +
    cauchyTwo geometricCoefficientProfile.x geometricCoefficientProfile.r n +
    cauchyTwo geometricCoefficientProfile.v geometricCoefficientProfile.y n +
    cauchyThree geometricCoefficientProfile.u geometricCoefficientProfile.y
      geometricCoefficientProfile.z n
  q : ∀ n, 2 ≤ n → geometricCoefficientProfile.q n ≤
    geometricCoefficientProfile.g (n - 1) +
    cauchyTwo geometricCoefficientProfile.g geometricCoefficientProfile.e (n - 1) +
    geometricCoefficientProfile.u (n - 2) +
    cauchyTwo geometricCoefficientProfile.t geometricCoefficientProfile.g (n - 2) +
    cauchyTwo geometricCoefficientProfile.r geometricCoefficientProfile.u (n - 2)
  s : ∀ n, 2 ≤ n → geometricCoefficientProfile.s n ≤
    geometricCoefficientProfile.g (n - 1) +
    cauchyTwo geometricCoefficientProfile.e geometricCoefficientProfile.e (n - 1) +
    geometricCoefficientProfile.t (n - 2) +
    cauchyTwo geometricCoefficientProfile.x geometricCoefficientProfile.g (n - 2) +
    cauchyTwo geometricCoefficientProfile.y geometricCoefficientProfile.u (n - 2)
  u : ∀ n, 2 ≤ n → geometricCoefficientProfile.u n ≤
    cauchyTwo geometricCoefficientProfile.d geometricCoefficientProfile.h n +
    cauchyTwo geometricCoefficientProfile.s geometricCoefficientProfile.d n +
    cauchyTwo geometricCoefficientProfile.y geometricCoefficientProfile.r n +
    cauchyTwo geometricCoefficientProfile.w geometricCoefficientProfile.y n +
    cauchyThree geometricCoefficientProfile.u geometricCoefficientProfile.z
      geometricCoefficientProfile.z n
  v : ∀ n, 2 ≤ n → geometricCoefficientProfile.v n ≤
    geometricCoefficientProfile.s (n - 1) +
    cauchyTwo geometricCoefficientProfile.g geometricCoefficientProfile.g (n - 2) +
    cauchyTwo geometricCoefficientProfile.t geometricCoefficientProfile.e (n - 2) +
    cauchyTwo geometricCoefficientProfile.r geometricCoefficientProfile.t (n - 2)
  w : ∀ n, 2 ≤ n → geometricCoefficientProfile.w n ≤
    geometricCoefficientProfile.s (n - 1) +
    cauchyTwo geometricCoefficientProfile.e geometricCoefficientProfile.g (n - 2) +
    cauchyTwo geometricCoefficientProfile.x geometricCoefficientProfile.e (n - 2) +
    cauchyTwo geometricCoefficientProfile.y geometricCoefficientProfile.t (n - 2)
  x : ∀ n, 2 ≤ n → geometricCoefficientProfile.x n ≤
    geometricCoefficientProfile.d (n - 1) +
    geometricCoefficientProfile.g (n - 2) +
    geometricCoefficientProfile.u (n - 2)
  y : ∀ n, 2 ≤ n → geometricCoefficientProfile.y n ≤
    geometricCoefficientProfile.c (n - 1) +
    geometricCoefficientProfile.g (n - 2) +
    geometricCoefficientProfile.t (n - 2)
  z : ∀ n, 2 ≤ n → geometricCoefficientProfile.z n ≤
    geometricCoefficientProfile.c (n - 1) +
    geometricCoefficientProfile.e (n - 2) +
    geometricCoefficientProfile.x (n - 2)

/-- The already-proved finite geometry plus exactly the nine fields in
`GeometricBuiGaps` produce Bui's literal published recurrence system for the
actual occurrence-count sequences. -/
theorem publishedBuiRecurrences_of_geometricGaps
    (gaps : GeometricBuiGaps) :
    PublishedBuiRecurrences geometricCoefficientProfile where
  nonnegative := geometricCoefficientProfile_nonnegative
  zeroAtZero := geometricCoefficientProfile_zeroAtZero
  initial := geometricCoefficientProfile_initial
  c := by
    intro n hn
    simpa [geometricCoefficientProfile] using
      buiC_coefficient_le_e_pred hn
  d := by
    intro n hn
    simpa [geometricCoefficientProfile] using
      buiD_coefficient_le_g_pred hn
  e := by
    intro n hn
    simpa [geometricCoefficientProfile] using
      buiE_coefficient_le_f_pred hn
  f := by
    intro n _
    simpa [geometricCoefficientProfile] using
      (buiF_coefficient_eq_g_add_p n).le
  g := by
    intro n _
    simpa [geometricCoefficientProfile] using
      (buiG_coefficient_eq_e_add_q n).le
  h := by
    intro n _
    simpa [geometricCoefficientProfile] using
      (buiH_coefficient_eq_d_add_s n).le
  p := gaps.p
  q := gaps.q
  r := by
    intro n _
    simpa [geometricCoefficientProfile] using
      (buiR_coefficient_eq_y_add_w n).le
  s := gaps.s
  t := by
    intro n _
    simpa [geometricCoefficientProfile] using
      (buiT_coefficient_eq_x_add_v n).le
  u := gaps.u
  v := gaps.v
  w := gaps.w
  x := gaps.x
  y := gaps.y
  z := gaps.z

end LeanProofs.KlarnerConstant

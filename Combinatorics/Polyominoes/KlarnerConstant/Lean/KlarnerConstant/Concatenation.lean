import KlarnerConstant.Counting

/-!
# Concatenation and supermultiplicativity of fixed polyominoes

This module gives an explicit injective concatenation of normalized fixed
polyominoes.  Given normalized polyominoes `P` and `Q`, place the origin of
`Q` immediately above a canonically selected topmost cell of `P`.  The two
cell sets are separated by a horizontal cut, so their union has the sum of
their cardinalities and the cut can be recovered from the output.

The construction does not normalize its output after joining the pieces:
`P` retains its southwest anchor at the origin, while every translated cell
of `Q` lies strictly above `P`.  Recoverability of the cut makes the map on
pairs injective and proves supermultiplicativity of `fixedPolyominoCount`.
-/

namespace LeanProofs.KlarnerConstant

private theorem edgePath_mono {s t : Finset Cell} {a b : Cell}
    (hst : s ⊆ t)
    (h : Relation.ReflTransGen (EdgeAdjacentIn s) a b) :
    Relation.ReflTransGen (EdgeAdjacentIn t) a b := by
  exact Relation.ReflTransGen.mono
    (r := EdgeAdjacentIn s) (p := EdgeAdjacentIn t)
    (fun _ _ hxy ↦ ⟨hst hxy.1, hst hxy.2.1, hxy.2.2⟩) a b h

/-- Two edge-connected cell sets joined by one grid edge have an
edge-connected union. -/
theorem edgeConnected_union_of_adjacent {s t : Finset Cell}
    (hs : EdgeConnected s) (ht : EdgeConnected t)
    {a b : Cell} (ha : a ∈ s) (hb : b ∈ t)
    (hab : EdgeAdjacent a b) : EdgeConnected (s ∪ t) := by
  intro x hx y hy
  have hsu : s ⊆ s ∪ t := by
    intro c hc
    exact Finset.mem_union.mpr (Or.inl hc)
  have htu : t ⊆ s ∪ t := by
    intro c hc
    exact Finset.mem_union.mpr (Or.inr hc)
  have habu : EdgeAdjacentIn (s ∪ t) a b :=
    ⟨hsu ha, htu hb, hab⟩
  have hbau : EdgeAdjacentIn (s ∪ t) b a :=
    ⟨htu hb, hsu ha, edgeAdjacent_symm hab⟩
  rcases Finset.mem_union.mp hx with hxs | hxt
  · rcases Finset.mem_union.mp hy with hys | hyt
    · exact edgePath_mono hsu (hs x hxs y hys)
    · exact
        ((edgePath_mono hsu (hs x hxs a ha)).trans
          (Relation.ReflTransGen.single habu)).trans
          (edgePath_mono htu (ht b hb y hyt))
  · rcases Finset.mem_union.mp hy with hys | hyt
    · exact
        ((edgePath_mono htu (ht x hxt b hb)).trans
          (Relation.ReflTransGen.single hbau)).trans
          (edgePath_mono hsu (hs a ha y hys))
    · exact edgePath_mono htu (ht x hxt y hyt)

namespace Polyomino

/-- Lexicographic key `(-y,x)`, whose least value is topmost, then leftmost. -/
private def northKey (c : Cell) : ℤ ×ₗ ℤ :=
  toLex (-c.2, c.1)

/-- Convert a `(-y,x)` key back to the cell `(x,y)`. -/
private def cellOfNorthKey (k : ℤ ×ₗ ℤ) : Cell :=
  ((ofLex k).2, -(ofLex k).1)

private theorem cellOfNorthKey_key (c : Cell) :
    cellOfNorthKey (northKey c) = c := by
  simp [cellOfNorthKey, northKey]

/-- A canonical topmost cell, with the leftmost one chosen in case of a tie. -/
noncomputable def northAnchor (P : Polyomino) : Cell :=
  cellOfNorthKey
    ((P.cells.image northKey).min' (P.nonempty.image northKey))

theorem northAnchor_mem (P : Polyomino) : P.northAnchor ∈ P.cells := by
  let keys := P.cells.image northKey
  have hkeys : keys.Nonempty := P.nonempty.image northKey
  have hmin : keys.min' hkeys ∈ keys := Finset.min'_mem keys hkeys
  rcases Finset.mem_image.mp hmin with ⟨c, hc, hckey⟩
  have hanchor : P.northAnchor = c := by
    unfold northAnchor
    change cellOfNorthKey (keys.min' hkeys) = c
    rw [← hckey]
    exact cellOfNorthKey_key c
  rwa [hanchor]

/-- Every cell lies weakly below the canonical north anchor. -/
theorem cell_y_le_northAnchor (P : Polyomino) {c : Cell}
    (hc : c ∈ P.cells) : c.2 ≤ P.northAnchor.2 := by
  let keys := P.cells.image northKey
  have hkeys : keys.Nonempty := P.nonempty.image northKey
  have hmem : northKey c ∈ keys :=
    Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hle : keys.min' hkeys ≤ northKey c :=
    Finset.min'_le keys _ hmem
  have hy := Prod.Lex.monotone_fst _ _ hle
  change (ofLex (keys.min' hkeys)).1 ≤ -c.2 at hy
  have hneg : c.2 ≤ -(ofLex (keys.min' hkeys)).1 := by
    omega
  simpa only [northAnchor, keys, hkeys, cellOfNorthKey] using hneg

/-- Translation preserves the number of cells. -/
theorem card_cells_translate (P : Polyomino) (v : Cell) :
    (P.translate v).cells.card = P.cells.card := by
  classical
  change (P.cells.image fun c ↦ v + c).card = P.cells.card
  exact Finset.card_image_of_injective P.cells (add_right_injective v)

/-- Translation by a fixed lattice vector is injective on polyominoes. -/
theorem translate_injective (v : Cell) :
    Function.Injective (fun P : Polyomino ↦ P.translate v) := by
  intro P Q h
  apply Polyomino.ext
  have hc :
      P.cells.image (fun c ↦ v + c) =
        Q.cells.image (fun c ↦ v + c) :=
    congrArg Polyomino.cells h
  exact (Finset.image_injective (add_right_injective v)) hc

end Polyomino

namespace NormalizedPolyomino

/-- All cells of a normalized polyomino lie on or above row zero. -/
theorem cell_y_nonneg {n : ℕ} (P : NormalizedPolyomino n)
    {c : Cell} (hc : c ∈ P.toPolyomino.cells) : 0 ≤ c.2 := by
  have h := P.toPolyomino.southwestAnchor_min_y hc
  rw [P.southwestAnchor_eq] at h
  exact h

/-- A cell of a normalized polyomino on row zero has nonnegative
horizontal coordinate. -/
theorem cell_x_nonneg_of_y_eq_zero {n : ℕ}
    (P : NormalizedPolyomino n) {c : Cell}
    (hc : c ∈ P.toPolyomino.cells) (hy : c.2 = 0) : 0 ≤ c.1 := by
  have hrow : P.toPolyomino.southwestAnchor.2 = c.2 := by
    rw [P.southwestAnchor_eq]
    exact hy.symm
  have hx := P.toPolyomino.southwestAnchor_min_x hc hrow
  rw [P.southwestAnchor_eq] at hx
  exact hx

/-- The vector that moves an origin immediately above the canonical north
anchor of `P`. -/
noncomputable def stackShift {n : ℕ} (P : NormalizedPolyomino n) : Cell :=
  (P.toPolyomino.northAnchor.1, P.toPolyomino.northAnchor.2 + 1)

/-- The translated upper component in the vertical stack. -/
noncomputable def translatedUpper {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) : Polyomino :=
  Q.toPolyomino.translate P.stackShift

/-- The cell set obtained by putting `Q` immediately above `P`. -/
noncomputable def stackCells {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) : Finset Cell :=
  P.toPolyomino.cells ∪ (translatedUpper P Q).cells

theorem stackShift_mem_translatedUpper {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    P.stackShift ∈ (translatedUpper P Q).cells := by
  unfold translatedUpper
  change P.stackShift ∈
    Q.toPolyomino.cells.image (fun c ↦ P.stackShift + c)
  apply Finset.mem_image.mpr
  refine ⟨(0, 0), Q.origin_mem, ?_⟩
  apply Prod.ext <;> simp

theorem northAnchor_edgeAdjacent_stackShift {l : ℕ}
    (P : NormalizedPolyomino l) :
    EdgeAdjacent P.toPolyomino.northAnchor P.stackShift := by
  simp [EdgeAdjacent, stackShift]

theorem northAnchor_y_nonneg {l : ℕ}
    (P : NormalizedPolyomino l) :
    0 ≤ P.toPolyomino.northAnchor.2 :=
  P.cell_y_nonneg P.toPolyomino.northAnchor_mem

/-- Every cell in the translated upper component lies strictly above the
north anchor of the lower component. -/
theorem northAnchor_y_lt_of_mem_translatedUpper {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m)
    {c : Cell} (hc : c ∈ (translatedUpper P Q).cells) :
    P.toPolyomino.northAnchor.2 < c.2 := by
  unfold translatedUpper at hc
  change c ∈ Q.toPolyomino.cells.image
    (fun d ↦ P.stackShift + d) at hc
  rcases Finset.mem_image.mp hc with ⟨d, hd, rfl⟩
  have hd0 : 0 ≤ d.2 := Q.cell_y_nonneg hd
  change P.toPolyomino.northAnchor.2 <
    P.toPolyomino.northAnchor.2 + 1 + d.2
  omega

theorem lower_upper_disjoint {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    Disjoint P.toPolyomino.cells (translatedUpper P Q).cells := by
  refine Finset.disjoint_left.mpr ?_
  intro c hcP hcQ
  exact (not_lt_of_ge (P.toPolyomino.cell_y_le_northAnchor hcP))
    (P.northAnchor_y_lt_of_mem_translatedUpper Q hcQ)

theorem card_stackCells {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    (stackCells P Q).card = l + m := by
  rw [stackCells,
    Finset.card_union_of_disjoint (P.lower_upper_disjoint Q),
    P.card_cells]
  change l + (Q.toPolyomino.translate P.stackShift).cells.card = l + m
  rw [Q.toPolyomino.card_cells_translate, Q.card_cells]

/-- The unnormalized-looking union is a polyomino; normalization is proved
separately below. -/
noncomputable def stackPolyomino {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) : Polyomino where
  cells := stackCells P Q
  nonempty := P.toPolyomino.nonempty.mono fun c hc ↦
    Finset.mem_union.mpr (Or.inl hc)
  edgeConnected := edgeConnected_union_of_adjacent
    P.toPolyomino.edgeConnected (translatedUpper P Q).edgeConnected
    P.toPolyomino.northAnchor_mem (P.stackShift_mem_translatedUpper Q)
    P.northAnchor_edgeAdjacent_stackShift

/-- The stack already has southwest anchor `(0,0)`. -/
theorem stackPolyomino_isSouthwestAnchor {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    (stackPolyomino P Q).IsSouthwestAnchor (0, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · change (0, 0) ∈ stackCells P Q
    exact Finset.mem_union.mpr (Or.inl P.origin_mem)
  · intro c hc
    change c ∈ stackCells P Q at hc
    change 0 ≤ c.2
    rcases Finset.mem_union.mp hc with hcP | hcQ
    · exact P.cell_y_nonneg hcP
    · have htop := P.northAnchor_y_nonneg
      have hupper := P.northAnchor_y_lt_of_mem_translatedUpper Q hcQ
      omega
  · intro c hc hrow
    change c ∈ stackCells P Q at hc
    change 0 ≤ c.1
    have hy : c.2 = 0 := by
      simpa using hrow.symm
    rcases Finset.mem_union.mp hc with hcP | hcQ
    · exact P.cell_x_nonneg_of_y_eq_zero hcP hy
    · have htop := P.northAnchor_y_nonneg
      have hupper := P.northAnchor_y_lt_of_mem_translatedUpper Q hcQ
      omega

/-- Vertically stack two normalized polyominoes. -/
noncomputable def stack {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    NormalizedPolyomino (l + m) where
  toPolyomino := stackPolyomino P Q
  southwestAnchor_eq := by
    apply (stackPolyomino P Q).isSouthwestAnchor_unique
    · exact (stackPolyomino P Q).southwestAnchor_isSouthwest
    · exact P.stackPolyomino_isSouthwestAnchor Q
  card_cells := P.card_stackCells Q

end NormalizedPolyomino

/-- Cells weakly below the horizontal cut at height `h`. -/
def lowerCells (s : Finset Cell) (h : ℤ) : Finset Cell :=
  s.filter fun c ↦ c.2 ≤ h

/-- Cells strictly above the horizontal cut at height `h`. -/
def upperCells (s : Finset Cell) (h : ℤ) : Finset Cell :=
  s.filter fun c ↦ h < c.2

namespace NormalizedPolyomino

theorem lowerCells_stack {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    lowerCells (stack P Q).toPolyomino.cells
        P.toPolyomino.northAnchor.2 = P.toPolyomino.cells := by
  change lowerCells (stackCells P Q) P.toPolyomino.northAnchor.2 =
    P.toPolyomino.cells
  ext c
  constructor
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hc, hcy⟩
    rcases Finset.mem_union.mp hc with hcP | hcQ
    · exact hcP
    · have hupper := P.northAnchor_y_lt_of_mem_translatedUpper Q hcQ
      omega
  · intro hcP
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_union.mpr (Or.inl hcP),
      P.toPolyomino.cell_y_le_northAnchor hcP⟩

theorem upperCells_stack {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    upperCells (stack P Q).toPolyomino.cells
        P.toPolyomino.northAnchor.2 = (translatedUpper P Q).cells := by
  change upperCells (stackCells P Q) P.toPolyomino.northAnchor.2 =
    (translatedUpper P Q).cells
  ext c
  constructor
  · intro hc
    rcases Finset.mem_filter.mp hc with ⟨hc, hcy⟩
    rcases Finset.mem_union.mp hc with hcP | hcQ
    · have hlower := P.toPolyomino.cell_y_le_northAnchor hcP
      omega
    · exact hcQ
  · intro hcQ
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_union.mpr (Or.inr hcQ),
      P.northAnchor_y_lt_of_mem_translatedUpper Q hcQ⟩

theorem lowerCells_stack_card {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    (lowerCells (stack P Q).toPolyomino.cells
      P.toPolyomino.northAnchor.2).card = l := by
  rw [P.lowerCells_stack Q, P.card_cells]

theorem stack_has_cell_at_next_row {l m : ℕ}
    (P : NormalizedPolyomino l) (Q : NormalizedPolyomino m) :
    ∃ c ∈ (stack P Q).toPolyomino.cells,
      c.2 = P.toPolyomino.northAnchor.2 + 1 := by
  refine ⟨P.stackShift, ?_, ?_⟩
  · change P.stackShift ∈ stackCells P Q
    exact Finset.mem_union.mpr
      (Or.inr (P.stackShift_mem_translatedUpper Q))
  · simp [stackShift]

end NormalizedPolyomino

private theorem lowerCells_card_lt_of_lt_of_next_row
    {s : Finset Cell} {h k : ℤ} (hhk : h < k)
    (hnext : ∃ c ∈ s, c.2 = h + 1) :
    (lowerCells s h).card < (lowerCells s k).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro c hc
    rcases Finset.mem_filter.mp hc with ⟨hcs, hch⟩
    exact Finset.mem_filter.mpr ⟨hcs, by omega⟩
  · intro heq
    rcases hnext with ⟨c, hcs, hcy⟩
    have hmemk : c ∈ lowerCells s k := by
      exact Finset.mem_filter.mpr ⟨hcs, by omega⟩
    have hnmemh : c ∉ lowerCells s h := by
      intro hmemh
      have hle := (Finset.mem_filter.mp hmemh).2
      omega
    rw [← heq] at hmemk
    exact hnmemh hmemk

/-- A horizontal cut with a prescribed lower cardinality and a cell on the
next row has a unique height. -/
theorem cutHeight_unique {s : Finset Cell} {l : ℕ} {h k : ℤ}
    (hhcard : (lowerCells s h).card = l)
    (hkcard : (lowerCells s k).card = l)
    (hhnext : ∃ c ∈ s, c.2 = h + 1)
    (hknext : ∃ c ∈ s, c.2 = k + 1) : h = k := by
  rcases lt_trichotomy h k with hlt | heq | hgt
  · have hcard := lowerCells_card_lt_of_lt_of_next_row hlt hhnext
    rw [hhcard, hkcard] at hcard
    omega
  · exact heq
  · have hcard := lowerCells_card_lt_of_lt_of_next_row hgt hknext
    rw [hkcard, hhcard] at hcard
    omega

/-- The vertical stack as a map on pairs. -/
noncomputable def stackMap (l m : ℕ) :
    NormalizedPolyomino l × NormalizedPolyomino m →
      NormalizedPolyomino (l + m) :=
  fun pq ↦ pq.1.stack pq.2

/-- The horizontal separator makes the vertical-stack construction
injective. -/
theorem stackMap_injective (l m : ℕ) :
    Function.Injective (stackMap l m) := by
  rintro ⟨P₁, Q₁⟩ ⟨P₂, Q₂⟩ hstack
  have hcells :
      (P₁.stack Q₁).toPolyomino.cells =
        (P₂.stack Q₂).toPolyomino.cells :=
    congrArg (fun R ↦ R.toPolyomino.cells) hstack
  have hcard₁ := P₁.lowerCells_stack_card Q₁
  have hcard₂ :
      (lowerCells (P₁.stack Q₁).toPolyomino.cells
        P₂.toPolyomino.northAnchor.2).card = l := by
    rw [hcells]
    exact P₂.lowerCells_stack_card Q₂
  have hnext₁ := P₁.stack_has_cell_at_next_row Q₁
  have hnext₂ :
      ∃ c ∈ (P₁.stack Q₁).toPolyomino.cells,
        c.2 = P₂.toPolyomino.northAnchor.2 + 1 := by
    rcases P₂.stack_has_cell_at_next_row Q₂ with ⟨c, hc, hcy⟩
    refine ⟨c, ?_, hcy⟩
    rw [hcells]
    exact hc
  have hheight :
      P₁.toPolyomino.northAnchor.2 =
        P₂.toPolyomino.northAnchor.2 :=
    cutHeight_unique hcard₁ hcard₂ hnext₁ hnext₂
  have hPcells : P₁.toPolyomino.cells = P₂.toPolyomino.cells := by
    calc
      P₁.toPolyomino.cells =
          lowerCells (P₁.stack Q₁).toPolyomino.cells
            P₁.toPolyomino.northAnchor.2 :=
        (P₁.lowerCells_stack Q₁).symm
      _ = lowerCells (P₁.stack Q₁).toPolyomino.cells
            P₂.toPolyomino.northAnchor.2 := by rw [hheight]
      _ = lowerCells (P₂.stack Q₂).toPolyomino.cells
            P₂.toPolyomino.northAnchor.2 :=
        congrArg
          (fun s ↦ lowerCells s P₂.toPolyomino.northAnchor.2) hcells
      _ = P₂.toPolyomino.cells := P₂.lowerCells_stack Q₂
  have hP : P₁ = P₂ :=
    NormalizedPolyomino.ext (Polyomino.ext hPcells)
  subst P₂
  have hUpperCells :
      (NormalizedPolyomino.translatedUpper P₁ Q₁).cells =
        (NormalizedPolyomino.translatedUpper P₁ Q₂).cells := by
    calc
      (NormalizedPolyomino.translatedUpper P₁ Q₁).cells =
          upperCells (P₁.stack Q₁).toPolyomino.cells
            P₁.toPolyomino.northAnchor.2 :=
        (P₁.upperCells_stack Q₁).symm
      _ = upperCells (P₁.stack Q₂).toPolyomino.cells
            P₁.toPolyomino.northAnchor.2 :=
        congrArg
          (fun s ↦ upperCells s P₁.toPolyomino.northAnchor.2) hcells
      _ = (NormalizedPolyomino.translatedUpper P₁ Q₂).cells :=
        P₁.upperCells_stack Q₂
  have htranslated :
      Q₁.toPolyomino.translate P₁.stackShift =
        Q₂.toPolyomino.translate P₁.stackShift :=
    Polyomino.ext hUpperCells
  have hQpoly : Q₁.toPolyomino = Q₂.toPolyomino :=
    Polyomino.translate_injective P₁.stackShift htranslated
  have hQ : Q₁ = Q₂ := NormalizedPolyomino.ext hQpoly
  exact Prod.ext rfl hQ

/-- Fixed polyomino counts are supermultiplicative. -/
theorem fixedPolyominoCount_supermultiplicative (l m : ℕ) :
    fixedPolyominoCount l * fixedPolyominoCount m ≤
      fixedPolyominoCount (l + m) := by
  unfold fixedPolyominoCount
  simpa only [Fintype.card_prod] using
    Fintype.card_le_of_injective (stackMap l m) (stackMap_injective l m)

/-- The one-cell polyomino at the origin. -/
private def singletonPolyomino : Polyomino where
  cells := {(0, 0)}
  nonempty := ⟨(0, 0), by simp⟩
  edgeConnected := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact Relation.ReflTransGen.refl

private theorem southwestAnchor_singletonPolyomino :
    singletonPolyomino.southwestAnchor = (0, 0) := by
  have h := singletonPolyomino.southwestAnchor_mem
  simpa [singletonPolyomino] using h

/-- A normalized one-cell polyomino, used to start the positivity induction. -/
noncomputable def normalizedSingleton : NormalizedPolyomino 1 where
  toPolyomino := singletonPolyomino
  southwestAnchor_eq := southwestAnchor_singletonPolyomino
  card_cells := by simp [singletonPolyomino]

theorem fixedPolyominoCount_one_pos : 0 < fixedPolyominoCount 1 := by
  unfold fixedPolyominoCount
  exact Fintype.card_pos_iff.mpr ⟨normalizedSingleton⟩

/-- There is at least one normalized fixed polyomino of every positive size. -/
theorem fixedPolyominoCount_pos {n : ℕ} (hn : n ≠ 0) :
    0 < fixedPolyominoCount n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction k with
  | zero => simpa using fixedPolyominoCount_one_pos
  | succ k ih =>
      have hprod :
          0 < fixedPolyominoCount (k + 1) * fixedPolyominoCount 1 :=
        Nat.mul_pos (ih (Nat.succ_ne_zero k)) fixedPolyominoCount_one_pos
      have hle := fixedPolyominoCount_supermultiplicative (k + 1) 1
      exact lt_of_lt_of_le hprod (by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hle)

end LeanProofs.KlarnerConstant

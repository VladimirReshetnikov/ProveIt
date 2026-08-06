import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.FinCases

/-!
# The two solvable block-system families in degree six

There are fifteen partitions of six letters into three pairs and ten
partitions into two triples.  Their stabilizers have orders 48 and 72,
respectively, and are solvable.  We enumerate the partitions explicitly and
kernel-check solvability of each finite stabilizer via the derived series.

The later sextic resolvents have one root for each entry of these tables.
-/

namespace LeanProofs.PolynomialFormulas.Fin6BlockSystems

abbrev S6 := Equiv.Perm (Fin 6)
abbrev PairPartition := Fin 15
abbrev TriplePartition := Fin 10

/-- Labels for the fifteen partitions into three pairs.  Equality of labels,
not the arbitrary order of the labels, is the represented equivalence
relation. -/
def pairLabel : PairPartition → Fin 6 → Fin 3 := ![
  ![0, 0, 1, 1, 2, 2], -- 01 | 23 | 45
  ![0, 0, 1, 2, 1, 2], -- 01 | 24 | 35
  ![0, 0, 1, 2, 2, 1], -- 01 | 25 | 34
  ![0, 1, 0, 1, 2, 2], -- 02 | 13 | 45
  ![0, 1, 0, 2, 1, 2], -- 02 | 14 | 35
  ![0, 1, 0, 2, 2, 1], -- 02 | 15 | 34
  ![0, 1, 1, 0, 2, 2], -- 03 | 12 | 45
  ![0, 1, 2, 0, 1, 2], -- 03 | 14 | 25
  ![0, 1, 2, 0, 2, 1], -- 03 | 15 | 24
  ![0, 1, 1, 2, 0, 2], -- 04 | 12 | 35
  ![0, 1, 2, 1, 0, 2], -- 04 | 13 | 25
  ![0, 1, 2, 2, 0, 1], -- 04 | 15 | 23
  ![0, 1, 1, 2, 2, 0], -- 05 | 12 | 34
  ![0, 1, 2, 1, 2, 0], -- 05 | 13 | 24
  ![0, 1, 2, 2, 1, 0]  -- 05 | 14 | 23
]

/-- Labels for the ten partitions into two triples.  The block containing zero
is assigned label zero, making the enumeration canonical. -/
def tripleLabel : TriplePartition → Fin 6 → Fin 2 := ![
  ![0, 0, 0, 1, 1, 1], -- 012 | 345
  ![0, 0, 1, 0, 1, 1], -- 013 | 245
  ![0, 0, 1, 1, 0, 1], -- 014 | 235
  ![0, 0, 1, 1, 1, 0], -- 015 | 234
  ![0, 1, 0, 0, 1, 1], -- 023 | 145
  ![0, 1, 0, 1, 0, 1], -- 024 | 135
  ![0, 1, 0, 1, 1, 0], -- 025 | 134
  ![0, 1, 1, 0, 0, 1], -- 034 | 125
  ![0, 1, 1, 0, 1, 0], -- 035 | 124
  ![0, 1, 1, 1, 0, 0]  -- 045 | 123
]

/-- A permutation preserves the equivalence relation defined by a block-label
function. -/
def Preserves {m : ℕ} (label : Fin 6 → Fin m) (g : S6) : Prop :=
  ∀ i j, label (g i) = label (g j) ↔ label i = label j

instance preservesDecidable {m : ℕ} (label : Fin 6 → Fin m) (g : S6) :
    Decidable (Preserves label g) := by
  unfold Preserves
  exact Fintype.decidableForallFintype

/-- The full setwise stabilizer of the partition represented by `label`. -/
def partitionStabilizer {m : ℕ} (label : Fin 6 → Fin m) : Subgroup S6 where
  carrier := {g | Preserves label g}
  one_mem' := by simp [Preserves]
  mul_mem' := by
    intro g h hg hh i j
    change label (g (h i)) = label (g (h j)) ↔ label i = label j
    exact (hg (h i) (h j)).trans (hh i j)
  inv_mem' := by
    intro g hg i j
    have h := hg (g⁻¹ i) (g⁻¹ j)
    simpa using h.symm

def pairStabilizer (p : PairPartition) : Subgroup S6 :=
  partitionStabilizer (pairLabel p)

def tripleStabilizer (p : TriplePartition) : Subgroup S6 :=
  partitionStabilizer (tripleLabel p)

/-- Two label functions present the same unlabelled partition. -/
def SamePartition {m n : ℕ} (l : Fin 6 → Fin m) (r : Fin 6 → Fin n) : Prop :=
  ∀ i j, l i = l j ↔ r i = r j

instance samePartitionDecidable {m n : ℕ}
    (l : Fin 6 → Fin m) (r : Fin 6 → Fin n) :
    Decidable (SamePartition l r) := by
  unfold SamePartition
  exact Fintype.decidableForallFintype

theorem SamePartition.symm {m n : ℕ} {l : Fin 6 → Fin m} {r : Fin 6 → Fin n}
    (h : SamePartition l r) : SamePartition r l :=
  fun i j ↦ (h i j).symm

theorem partitionStabilizer_congr {m n : ℕ}
    {l : Fin 6 → Fin m} {r : Fin 6 → Fin n} (h : SamePartition l r) :
    partitionStabilizer l = partitionStabilizer r := by
  ext g
  constructor <;> intro hg i j
  · rw [← h (g i) (g j), ← h i j]
    exact hg i j
  · rw [h (g i) (g j), h i j]
    exact hg i j

/-- Computable cardinality of a label fiber. -/
def fiberCard {m : ℕ} (l : Fin 6 → Fin m) (b : Fin m) : ℕ :=
  (Finset.univ.filter fun i ↦ l i = b).card

theorem fiberCard_eq_ncard {m : ℕ} (l : Fin 6 → Fin m) (b : Fin m) :
    fiberCard l b = Set.ncard {i | l i = b} := by
  classical
  rw [fiberCard, Set.ncard_eq_toFinset_card]
  congr 1
  ext i
  simp

/-! A finite setoid can be labelled by its quotient.  These lemmas isolate the
choice of names for blocks from the relation represented by those names. -/

noncomputable def setoidLabel {m : ℕ} (r : Setoid (Fin 6))
    (e : Quotient r ≃ Fin m) : Fin 6 → Fin m :=
  fun i ↦ e (Quotient.mk'' i)

theorem setoidLabel_samePartition {m : ℕ} (r : Setoid (Fin 6))
    (e : Quotient r ≃ Fin m) :
    ∀ i j, setoidLabel r e i = setoidLabel r e j ↔ r i j := by
  intro i j
  change e (Quotient.mk'' i) = e (Quotient.mk'' j) ↔ r i j
  rw [e.injective.eq_iff, Quotient.eq'']

theorem setoidLabel_fiberCard {m k : ℕ} (r : Setoid (Fin 6))
    (e : Quotient r ≃ Fin m)
    (hr : ∀ i, Set.ncard {j | r j i} = k) :
    ∀ b, fiberCard (setoidLabel r e) b = k := by
  intro b
  rw [fiberCard_eq_ncard]
  obtain ⟨i, hi⟩ := Quotient.mk''_surjective (e.symm b)
  rw [show ({x | setoidLabel r e x = b} : Set (Fin 6)) = {x | r x i} by
    ext x
    change e (Quotient.mk'' x) = b ↔ r x i
    rw [← e.apply_symm_apply b, e.injective.eq_iff, ← hi, Quotient.eq'']]
  exact hr i

theorem preserves_setoidLabel_iff {m : ℕ} (r : Setoid (Fin 6))
    (e : Quotient r ≃ Fin m) (g : S6) :
    Preserves (setoidLabel r e) g ↔
      ∀ i j, r (g i) (g j) ↔ r i j := by
  unfold Preserves
  simp_rw [setoidLabel_samePartition]

set_option maxRecDepth 100000 in
/-- The explicit table contains every unlabelled partition into three pairs. -/
theorem pairLabel_complete (l : Fin 6 → Fin 3)
    (hl : ∀ b, fiberCard l b = 2) :
    ∃ p : PairPartition, SamePartition l (pairLabel p) := by
  revert l
  letI (l : Fin 6 → Fin 3) : Decidable (∀ b, fiberCard l b = 2) :=
    Fintype.decidableForallFintype
  letI (l : Fin 6 → Fin 3) :
      Decidable (∃ p : PairPartition, SamePartition l (pairLabel p)) :=
    Fintype.decidableExistsFintype
  letI : Decidable
      (∀ l : Fin 6 → Fin 3, (∀ b, fiberCard l b = 2) →
        ∃ p : PairPartition, SamePartition l (pairLabel p)) :=
    Fintype.decidableForallFintype
  decide

theorem le_pairStabilizer_of_invariant_setoid
    (G : Subgroup S6) (r : Setoid (Fin 6)) (e : Quotient r ≃ Fin 3)
    (hr : ∀ i, Set.ncard {j | r j i} = 2)
    (hG : ∀ g ∈ G, ∀ i j, r (g i) (g j) ↔ r i j) :
    ∃ p : PairPartition, G ≤ pairStabilizer p := by
  let l := setoidLabel r e
  obtain ⟨p, hp⟩ := pairLabel_complete l (setoidLabel_fiberCard r e hr)
  refine ⟨p, fun g hg ↦ ?_⟩
  change g ∈ partitionStabilizer (pairLabel p)
  rw [← partitionStabilizer_congr hp]
  exact (preserves_setoidLabel_iff r e g).2 (hG g hg)

set_option maxRecDepth 100000 in
/-- The explicit table contains every unlabelled partition into two triples. -/
theorem tripleLabel_complete (l : Fin 6 → Fin 2)
    (hl : ∀ b, fiberCard l b = 3) :
    ∃ p : TriplePartition, SamePartition l (tripleLabel p) := by
  revert l
  letI (l : Fin 6 → Fin 2) : Decidable (∀ b, fiberCard l b = 3) :=
    Fintype.decidableForallFintype
  letI (l : Fin 6 → Fin 2) :
      Decidable (∃ p : TriplePartition, SamePartition l (tripleLabel p)) :=
    Fintype.decidableExistsFintype
  letI : Decidable
      (∀ l : Fin 6 → Fin 2, (∀ b, fiberCard l b = 3) →
        ∃ p : TriplePartition, SamePartition l (tripleLabel p)) :=
    Fintype.decidableForallFintype
  decide

theorem le_tripleStabilizer_of_invariant_setoid
    (G : Subgroup S6) (r : Setoid (Fin 6)) (e : Quotient r ≃ Fin 2)
    (hr : ∀ i, Set.ncard {j | r j i} = 3)
    (hG : ∀ g ∈ G, ∀ i j, r (g i) (g j) ↔ r i j) :
    ∃ p : TriplePartition, G ≤ tripleStabilizer p := by
  let l := setoidLabel r e
  obtain ⟨p, hp⟩ := tripleLabel_complete l (setoidLabel_fiberCard r e hr)
  refine ⟨p, fun g hg ↦ ?_⟩
  change g ∈ partitionStabilizer (tripleLabel p)
  rw [← partitionStabilizer_congr hp]
  exact (preserves_setoidLabel_iff r e g).2 (hG g hg)

@[simp] theorem mem_pairStabilizer (p : PairPartition) (g : S6) :
    g ∈ pairStabilizer p ↔ Preserves (pairLabel p) g := Iff.rfl

@[simp] theorem mem_tripleStabilizer (p : TriplePartition) (g : S6) :
    g ∈ tripleStabilizer p ↔ Preserves (tripleLabel p) g := Iff.rfl

/-! ## Structural solvability of the stabilizers

The proofs below intentionally do not try to evaluate membership in a
classically represented derived subgroup.  A partition stabilizer acts on its
blocks.  The kernel fixes every block and embeds in the product of the
permutation groups of the individual blocks.  All groups occurring in that
extension are permutation groups on at most three letters.
-/

/-- A block labelling together with a chosen representative of every block. -/
structure BlockPresentation (m : ℕ) where
  label : Fin 6 → Fin m
  rep : Fin m → Fin 6
  label_rep : ∀ b, label (rep b) = b

namespace BlockPresentation

variable {m : ℕ} (B : BlockPresentation m)

private def blockMap (g : partitionStabilizer B.label) (b : Fin m) : Fin m :=
  B.label ((g : S6) (B.rep b))

private theorem blockMap_injective (g : partitionStabilizer B.label) :
    Function.Injective (B.blockMap g) := by
  intro b c h
  have h' := (g.property (B.rep b) (B.rep c)).mp h
  simpa [B.label_rep] using h'

/-- The permutation of blocks induced by a partition-preserving permutation. -/
noncomputable def blockPerm (g : partitionStabilizer B.label) :
    Equiv.Perm (Fin m) :=
  Equiv.ofBijective (B.blockMap g)
    ⟨B.blockMap_injective g,
      Finite.injective_iff_surjective.mp (B.blockMap_injective g)⟩

@[simp] theorem blockPerm_apply (g : partitionStabilizer B.label) (b : Fin m) :
    B.blockPerm g b = B.label ((g : S6) (B.rep b)) := rfl

/-- The action of the partition stabilizer on the set of blocks. -/
noncomputable def blockAction :
    partitionStabilizer B.label →* Equiv.Perm (Fin m) where
  toFun := B.blockPerm
  map_one' := by
    apply Equiv.Perm.ext
    intro b
    exact B.label_rep b
  map_mul' := by
    intro g h
    apply Equiv.Perm.ext
    intro b
    change B.label ((g : S6) ((h : S6) (B.rep b))) =
      B.label ((g : S6) (B.rep (B.label ((h : S6) (B.rep b)))))
    exact (g.property ((h : S6) (B.rep b))
      (B.rep (B.label ((h : S6) (B.rep b))))).2 (B.label_rep _).symm

/-- Permutations fixing every block, rather than merely permuting the blocks. -/
def fixesLabels : Subgroup S6 where
  carrier := {g | ∀ i, B.label (g i) = B.label i}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh i
    change B.label (g (h i)) = B.label i
    rw [hg, hh]
  inv_mem' := by
    intro g hg i
    have h := hg (g⁻¹ i)
    simpa using h.symm

theorem fixesLabels_le_stabilizer :
    B.fixesLabels ≤ partitionStabilizer B.label := by
  intro g hg i j
  rw [hg i, hg j]

def fixesToStabilizer :
    B.fixesLabels →* partitionStabilizer B.label :=
  Subgroup.inclusion B.fixesLabels_le_stabilizer

/-- Restriction to one labelled fiber. -/
def fiberRestriction (b : Fin m) :
    B.fixesLabels →* Equiv.Perm {i : Fin 6 // B.label i = b} where
  toFun g := (g : S6).subtypePerm fun i ↦ by
    rw [g.property i]
  map_one' := by
    apply Equiv.Perm.ext
    intro i
    rfl
  map_mul' := by
    intro g h
    apply Equiv.Perm.ext
    intro i
    rfl

/-- Simultaneous restriction to every fiber. -/
def fiberRestrictionPi :
    B.fixesLabels →* ((b : Fin m) → Equiv.Perm {i : Fin 6 // B.label i = b}) :=
  MonoidHom.pi fun b ↦ B.fiberRestriction b

theorem fiberRestrictionPi_injective :
    Function.Injective B.fiberRestrictionPi := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro i
  have hi := congrArg
    (fun q ↦ ((q (B.label i)) ⟨i, rfl⟩ :
      {j : Fin 6 // B.label j = B.label i}).1) hgh
  exact hi

theorem ker_blockAction_le_range_fixesToStabilizer :
    B.blockAction.ker ≤ B.fixesToStabilizer.range := by
  intro g hg
  have hfix : ∀ i, B.label ((g : S6) i) = B.label i := by
    intro i
    have hblock := congrArg
      (fun q : Equiv.Perm (Fin m) ↦ q (B.label i)) hg
    change B.label ((g : S6) (B.rep (B.label i))) = B.label i at hblock
    have hsame :
        B.label ((g : S6) (B.rep (B.label i))) = B.label ((g : S6) i) :=
      (g.property (B.rep (B.label i)) i).2 (B.label_rep _)
    exact hsame.symm.trans hblock
  refine ⟨⟨g, hfix⟩, ?_⟩
  rfl

end BlockPresentation

/-- Symmetric groups on at most three letters are solvable: the sign map has
commutative kernel (the alternating group) and commutative codomain. -/
theorem perm_solvable_of_card_le_three {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X ≤ 3) : IsSolvable (Equiv.Perm X) := by
  have hX' : Nat.card X ≤ 3 := by
    simpa [Nat.card_eq_fintype_card] using hX
  have hcomm : IsMulCommutative (alternatingGroup X) :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mpr hX'
  letI : IsSolvable (alternatingGroup X) :=
    isSolvable_of_comm fun a b ↦ hcomm.is_comm.comm a b
  exact solvable_of_ker_le_range (alternatingGroup X).subtype
    Equiv.Perm.sign fun g hg ↦
      ⟨⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩, rfl⟩

theorem pairLabel_surjective (p : PairPartition) :
    Function.Surjective (pairLabel p) := by
  fin_cases p <;> decide

theorem tripleLabel_surjective (p : TriplePartition) :
    Function.Surjective (tripleLabel p) := by
  fin_cases p <;> decide

noncomputable def pairPresentation (p : PairPartition) : BlockPresentation 3 where
  label := pairLabel p
  rep b := Classical.choose (pairLabel_surjective p b)
  label_rep b := Classical.choose_spec (pairLabel_surjective p b)

noncomputable def triplePresentation (p : TriplePartition) : BlockPresentation 2 where
  label := tripleLabel p
  rep b := Classical.choose (tripleLabel_surjective p b)
  label_rep b := Classical.choose_spec (tripleLabel_surjective p b)

theorem pairFiber_card_le_three (p : PairPartition) (b : Fin 3) :
    Fintype.card {i : Fin 6 // pairLabel p i = b} ≤ 3 := by
  fin_cases p <;> fin_cases b <;> decide

theorem tripleFiber_card_le_three (p : TriplePartition) (b : Fin 2) :
    Fintype.card {i : Fin 6 // tripleLabel p i = b} ≤ 3 := by
  fin_cases p <;> fin_cases b <;> decide

private noncomputable def pairFiberEmbedding (p : PairPartition) :
    (pairPresentation p).fixesLabels →*
      (Equiv.Perm {i : Fin 6 // pairLabel p i = 0}) ×
      ((Equiv.Perm {i : Fin 6 // pairLabel p i = 1}) ×
       Equiv.Perm {i : Fin 6 // pairLabel p i = 2}) :=
  ((pairPresentation p).fiberRestriction 0).prod
    (((pairPresentation p).fiberRestriction 1).prod
      ((pairPresentation p).fiberRestriction 2))

private theorem pairFiberEmbedding_injective (p : PairPartition) :
    Function.Injective (pairFiberEmbedding p) := by
  intro g h hgh
  apply (pairPresentation p).fiberRestrictionPi_injective
  funext b
  fin_cases b
  · exact congrArg Prod.fst hgh
  · exact congrArg (fun q ↦ q.2.1) hgh
  · exact congrArg (fun q ↦ q.2.2) hgh

private noncomputable def tripleFiberEmbedding (p : TriplePartition) :
    (triplePresentation p).fixesLabels →*
      (Equiv.Perm {i : Fin 6 // tripleLabel p i = 0}) ×
       Equiv.Perm {i : Fin 6 // tripleLabel p i = 1} :=
  ((triplePresentation p).fiberRestriction 0).prod
    ((triplePresentation p).fiberRestriction 1)

private theorem tripleFiberEmbedding_injective (p : TriplePartition) :
    Function.Injective (tripleFiberEmbedding p) := by
  intro g h hgh
  apply (triplePresentation p).fiberRestrictionPi_injective
  funext b
  fin_cases b
  · exact congrArg Prod.fst hgh
  · exact congrArg Prod.snd hgh

theorem pairFixesLabels_solvable (p : PairPartition) :
    IsSolvable (pairPresentation p).fixesLabels := by
  letI : IsSolvable (Equiv.Perm {i : Fin 6 // pairLabel p i = 0}) :=
    perm_solvable_of_card_le_three (pairFiber_card_le_three p 0)
  letI : IsSolvable (Equiv.Perm {i : Fin 6 // pairLabel p i = 1}) :=
    perm_solvable_of_card_le_three (pairFiber_card_le_three p 1)
  letI : IsSolvable (Equiv.Perm {i : Fin 6 // pairLabel p i = 2}) :=
    perm_solvable_of_card_le_three (pairFiber_card_le_three p 2)
  exact solvable_of_solvable_injective (pairFiberEmbedding_injective p)

theorem tripleFixesLabels_solvable (p : TriplePartition) :
    IsSolvable (triplePresentation p).fixesLabels := by
  letI : IsSolvable (Equiv.Perm {i : Fin 6 // tripleLabel p i = 0}) :=
    perm_solvable_of_card_le_three (tripleFiber_card_le_three p 0)
  letI : IsSolvable (Equiv.Perm {i : Fin 6 // tripleLabel p i = 1}) :=
    perm_solvable_of_card_le_three (tripleFiber_card_le_three p 1)
  exact solvable_of_solvable_injective (tripleFiberEmbedding_injective p)

theorem pairStabilizer_solvable (p : PairPartition) :
    IsSolvable (pairStabilizer p) := by
  letI : IsSolvable (pairPresentation p).fixesLabels :=
    pairFixesLabels_solvable p
  letI : IsSolvable (Equiv.Perm (Fin 3)) :=
    perm_solvable_of_card_le_three (by decide)
  exact solvable_of_ker_le_range
    (pairPresentation p).fixesToStabilizer
    (pairPresentation p).blockAction
    (pairPresentation p).ker_blockAction_le_range_fixesToStabilizer

theorem tripleStabilizer_solvable (p : TriplePartition) :
    IsSolvable (tripleStabilizer p) := by
  letI : IsSolvable (triplePresentation p).fixesLabels :=
    tripleFixesLabels_solvable p
  letI : IsSolvable (Equiv.Perm (Fin 2)) :=
    perm_solvable_of_card_le_three (by decide)
  exact solvable_of_ker_le_range
    (triplePresentation p).fixesToStabilizer
    (triplePresentation p).blockAction
    (triplePresentation p).ker_blockAction_le_range_fixesToStabilizer

/-- Any subgroup preserving one of the pair partitions is solvable. -/
theorem solvable_of_le_pairStabilizer (G : Subgroup S6) (p : PairPartition)
    (hG : G ≤ pairStabilizer p) : IsSolvable G := by
  letI : IsSolvable (pairStabilizer p) := pairStabilizer_solvable p
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion hG) (Subgroup.inclusion_injective hG)

/-- Any subgroup preserving one of the triple partitions is solvable. -/
theorem solvable_of_le_tripleStabilizer (G : Subgroup S6) (p : TriplePartition)
    (hG : G ≤ tripleStabilizer p) : IsSolvable G := by
  letI : IsSolvable (tripleStabilizer p) := tripleStabilizer_solvable p
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion hG) (Subgroup.inclusion_injective hG)

end LeanProofs.PolynomialFormulas.Fin6BlockSystems

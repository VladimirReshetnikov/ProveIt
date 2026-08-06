import PolynomialFormulas.SexticPartitionResolvents
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Separable

/-!
# Collision-free block descriptors for sextics

The simple scalar pair/triple invariants can collide after specialization.
Here a block is instead represented by its monic root polynomial, and a
partition by the monic polynomial whose roots are those block polynomials.
For an injective ordered root tuple this descriptor determines the partition
exactly.  This is the separation input for the executable resolvent search.
-/

open scoped BigOperators
open Polynomial

namespace LeanProofs.PolynomialFormulas.SexticSeparatingInvariants

open Fin6BlockSystems
open SexticPartitionResolvents

def pairBlock (p : PairPartition) (b : Fin 3) : Finset (Fin 6) :=
  {pairMember p b 0, pairMember p b 1}

def tripleBlock (p : TriplePartition) (b : Fin 2) : Finset (Fin 6) :=
  {tripleMember p b 0, tripleMember p b 1, tripleMember p b 2}

def pairBlocks (p : PairPartition) : Finset (Finset (Fin 6)) :=
  Finset.univ.image (pairBlock p)

def tripleBlocks (p : TriplePartition) : Finset (Finset (Fin 6)) :=
  Finset.univ.image (tripleBlock p)

set_option maxRecDepth 100000 in
theorem pairBlock_injective (p : PairPartition) :
    Function.Injective (pairBlock p) := by
  revert p
  decide

set_option maxRecDepth 100000 in
theorem tripleBlock_injective (p : TriplePartition) :
    Function.Injective (tripleBlock p) := by
  revert p
  decide

theorem card_pairBlocks (p : PairPartition) : (pairBlocks p).card = 3 := by
  rw [pairBlocks, Finset.card_image_of_injective _ (pairBlock_injective p)]
  simp

theorem card_tripleBlocks (p : TriplePartition) : (tripleBlocks p).card = 2 := by
  rw [tripleBlocks, Finset.card_image_of_injective _ (tripleBlock_injective p)]
  simp

set_option maxRecDepth 100000 in
theorem pairBlocks_injective : Function.Injective pairBlocks := by
  intro p q
  revert p q
  decide

set_option maxRecDepth 100000 in
theorem tripleBlocks_injective : Function.Injective tripleBlocks := by
  intro p q
  revert p q
  decide

set_option maxRecDepth 100000 in
theorem pair_mem_pairBlocks_iff (p : PairPartition) (i j : Fin 6) :
    ({i, j} : Finset (Fin 6)) ∈ pairBlocks p ↔
      i ≠ j ∧ pairLabel p i = pairLabel p j := by
  revert p i j
  decide

set_option maxRecDepth 100000 in
theorem triple_mem_tripleBlocks_iff
    (p : TriplePartition) (i j k : Fin 6) :
    ({i, j, k} : Finset (Fin 6)) ∈ tripleBlocks p ↔
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        tripleLabel p i = tripleLabel p j ∧
        tripleLabel p j = tripleLabel p k := by
  revert p i j k
  decide

section RootPolynomials

variable {K : Type*} [CommRing K]

/-- The monic polynomial having precisely the indexed entries as roots. -/
noncomputable def rootPolynomial (r : Fin 6 → K) (s : Finset (Fin 6)) : K[X] :=
  ∏ i ∈ s, (X - C (r i))

theorem rootPolynomial_monic (r : Fin 6 → K) (s : Finset (Fin 6)) :
    (rootPolynomial r s).Monic := by
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem rootPolynomial_natDegree [Nontrivial K]
    (r : Fin 6 → K) (s : Finset (Fin 6)) :
    (rootPolynomial r s).natDegree = s.card := by
  rw [rootPolynomial, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]

theorem rootPolynomial_isRoot_iff [IsDomain K]
    (r : Fin 6 → K) (s : Finset (Fin 6)) (x : K) :
    (rootPolynomial r s).IsRoot x ↔ ∃ i ∈ s, r i = x := by
  classical
  simp only [rootPolynomial, Polynomial.IsRoot, Polynomial.eval_prod,
    Finset.prod_eq_zero_iff, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero]
  constructor
  · rintro ⟨i, hi, hix⟩
    exact ⟨i, hi, hix.symm⟩
  · rintro ⟨i, hi, hix⟩
    exact ⟨i, hi, hix.symm⟩

theorem rootPolynomial_injective [IsDomain K] (r : Fin 6 → K)
    (hr : Function.Injective r) : Function.Injective (rootPolynomial r) := by
  intro s t hst
  apply Finset.Subset.antisymm
  · intro i hi
    have hroot : (rootPolynomial r t).IsRoot (r i) := by
      rw [← hst]
      exact (rootPolynomial_isRoot_iff r s (r i)).2 ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := (rootPolynomial_isRoot_iff r t (r i)).1 hroot
    exact hr hji |>.symm ▸ hj
  · intro i hi
    have hroot : (rootPolynomial r s).IsRoot (r i) := by
      rw [hst]
      exact (rootPolynomial_isRoot_iff r t (r i)).2 ⟨i, hi, rfl⟩
    obtain ⟨j, hj, hji⟩ := (rootPolynomial_isRoot_iff r s (r i)).1 hroot
    exact hr hji |>.symm ▸ hj

theorem rootPolynomial_permute (r : Fin 6 → K) (g : S6)
    (s : Finset (Fin 6)) :
    rootPolynomial (fun i ↦ r (g i)) s =
      rootPolynomial r (s.image g) := by
  classical
  rw [rootPolynomial, rootPolynomial,
    Finset.prod_image g.injective.injOn]

theorem rootPolynomial_map {L : Type*} [CommRing L] (f : K →+* L)
    (r : Fin 6 → K) (s : Finset (Fin 6)) :
    (rootPolynomial r s).map f = rootPolynomial (fun i ↦ f (r i)) s := by
  classical
  simp [rootPolynomial, Polynomial.map_prod]

/-- A finite set is recovered from the monic polynomial having its elements
as roots. -/
theorem prod_X_sub_C_injective [IsDomain K] :
    Function.Injective
      (fun s : Finset K ↦ ∏ x ∈ s, (X - C x : K[X])) := by
  classical
  intro s t hst
  change (∏ x ∈ s, (X - C x : K[X])) =
    ∏ x ∈ t, (X - C x : K[X]) at hst
  apply Finset.Subset.antisymm
  · intro x hx
    have hzS : Polynomial.eval x (∏ y ∈ s, (X - C y : K[X])) = 0 := by
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [Finset.prod_eq_zero_iff]
      exact ⟨x, hx, sub_self x⟩
    have hzT : Polynomial.eval x (∏ y ∈ t, (X - C y : K[X])) = 0 := by
      rw [← hst]
      exact hzS
    simp only [Polynomial.eval_prod, Finset.prod_eq_zero_iff,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hzT
    obtain ⟨y, hy, hxy⟩ := hzT
    exact hxy.symm ▸ hy
  · intro x hx
    have hzT : Polynomial.eval x (∏ y ∈ t, (X - C y : K[X])) = 0 := by
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [Finset.prod_eq_zero_iff]
      exact ⟨x, hx, sub_self x⟩
    have hzS : Polynomial.eval x (∏ y ∈ s, (X - C y : K[X])) = 0 := by
      rw [hst]
      exact hzT
    simp only [Polynomial.eval_prod, Finset.prod_eq_zero_iff,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hzS
    obtain ⟨y, hy, hxy⟩ := hzS
    exact hxy.symm ▸ hy

/-- The block-polynomial descriptor of an unlabelled partition. -/
noncomputable def descriptor (r : Fin 6 → K) (blocks : Finset (Finset (Fin 6))) :
    Polynomial K[X] :=
  ∏ b ∈ blocks, (X - C (rootPolynomial r b))

noncomputable def pairDescriptor (r : Fin 6 → K) (p : PairPartition) :
    Polynomial K[X] := descriptor r (pairBlocks p)

noncomputable def tripleDescriptor (r : Fin 6 → K) (p : TriplePartition) :
    Polynomial K[X] := descriptor r (tripleBlocks p)

theorem descriptor_permute (r : Fin 6 → K) (g : S6)
    (blocks : Finset (Finset (Fin 6))) :
    descriptor (fun i ↦ r (g i)) blocks =
      descriptor r (blocks.image (Finset.image g)) := by
  classical
  rw [descriptor, descriptor,
    Finset.prod_image (Finset.image_injective g.injective).injOn]
  apply Finset.prod_congr rfl
  intro b hb
  rw [rootPolynomial_permute]

theorem descriptor_map {L : Type*} [CommRing L] (f : K →+* L)
    (r : Fin 6 → K) (blocks : Finset (Finset (Fin 6))) :
    (descriptor r blocks).map (Polynomial.mapRingHom f) =
      descriptor (fun i ↦ f (r i)) blocks := by
  classical
  simp [descriptor, Polynomial.map_prod, rootPolynomial_map]

def actBlock (g : S6) (b : Finset (Fin 6)) : Finset (Fin 6) :=
  b.image g

def permuteBlocks (g : S6) (blocks : Finset (Finset (Fin 6))) :
    Finset (Finset (Fin 6)) := blocks.image (actBlock g)

theorem actBlock_injective (g : S6) : Function.Injective (actBlock g) := by
  exact Finset.image_injective g.injective

theorem permuteBlocks_mul (g h : S6) (blocks : Finset (Finset (Fin 6))) :
    permuteBlocks (g * h) blocks = permuteBlocks g (permuteBlocks h blocks) := by
  classical
  rw [permuteBlocks, permuteBlocks, permuteBlocks, Finset.image_image]
  congr 1
  funext b
  ext i
  simp [actBlock]

@[simp] theorem permuteBlocks_one (blocks : Finset (Finset (Fin 6))) :
    permuteBlocks 1 blocks = blocks := by
  classical
  apply Finset.ext
  intro b
  simp only [permuteBlocks, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hab⟩
    rw [← hab]
    simpa [actBlock] using ha
  · intro hb
    exact ⟨b, hb, by ext i; simp [actBlock]⟩

theorem actBlock_pair (g : S6) (i j : Fin 6) :
    actBlock g {i, j} = {g i, g j} := by
  classical
  ext x
  simp [actBlock]

theorem actBlock_triple (g : S6) (i j k : Fin 6) :
    actBlock g {i, j, k} = {g i, g j, g k} := by
  classical
  ext x
  simp [actBlock]

theorem pairBlocks_stabilized_iff (p : PairPartition) (g : S6) :
    permuteBlocks g (pairBlocks p) = pairBlocks p ↔
      Preserves (pairLabel p) g := by
  classical
  constructor
  · intro hs i j
    have hsInv : permuteBlocks g⁻¹ (pairBlocks p) = pairBlocks p := by
      calc
        permuteBlocks g⁻¹ (pairBlocks p) =
            permuteBlocks g⁻¹ (permuteBlocks g (pairBlocks p)) := by rw [hs]
        _ = permuteBlocks (g⁻¹ * g) (pairBlocks p) :=
          (permuteBlocks_mul _ _ _).symm
        _ = pairBlocks p := by simp
    constructor
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · have hblock : ({g i, g j} : Finset (Fin 6)) ∈ pairBlocks p :=
          (pair_mem_pairBlocks_iff p (g i) (g j)).2
            ⟨g.injective.ne hij', hij⟩
        have himage : actBlock g⁻¹ {g i, g j} ∈
            permuteBlocks g⁻¹ (pairBlocks p) :=
          Finset.mem_image.mpr ⟨{g i, g j}, hblock, rfl⟩
        rw [hsInv, actBlock_pair] at himage
        have hpre : ({i, j} : Finset (Fin 6)) ∈ pairBlocks p := by
          simpa using himage
        exact (pair_mem_pairBlocks_iff p i j).1 hpre |>.2
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · have hblock : ({i, j} : Finset (Fin 6)) ∈ pairBlocks p :=
          (pair_mem_pairBlocks_iff p i j).2 ⟨hij', hij⟩
        have himage : actBlock g {i, j} ∈ permuteBlocks g (pairBlocks p) :=
          Finset.mem_image.mpr ⟨{i, j}, hblock, rfl⟩
        rw [hs, actBlock_pair] at himage
        exact (pair_mem_pairBlocks_iff p (g i) (g j)).1 himage |>.2
  · intro hg
    apply Finset.ext
    intro b
    constructor
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp ha with ⟨c, _, rfl⟩
      let i := pairMember p c 0
      let j := pairMember p c 1
      have hij := (pair_mem_pairBlocks_iff p i j).1
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      rw [show pairBlock p c = {i, j} by rfl, actBlock_pair]
      exact (pair_mem_pairBlocks_iff p (g i) (g j)).2
        ⟨g.injective.ne hij.1, (hg i j).2 hij.2⟩
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
      let i := pairMember p c 0
      let j := pairMember p c 1
      have hij := (pair_mem_pairBlocks_iff p i j).1
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      let a := g⁻¹ i
      let e := g⁻¹ j
      have hae : ({a, e} : Finset (Fin 6)) ∈ pairBlocks p :=
        (pair_mem_pairBlocks_iff p a e).2 ⟨by
          intro h; exact hij.1 (g.symm.injective h),
          (hg a e).1 (by simpa [a, e] using hij.2)⟩
      apply Finset.mem_image.mpr
      refine ⟨{a, e}, hae, ?_⟩
      rw [actBlock_pair]
      simp [a, e, i, j, pairBlock]

theorem tripleBlocks_stabilized_iff (p : TriplePartition) (g : S6) :
    permuteBlocks g (tripleBlocks p) = tripleBlocks p ↔
      Preserves (tripleLabel p) g := by
  classical
  constructor
  · intro hs i j
    have hsInv : permuteBlocks g⁻¹ (tripleBlocks p) = tripleBlocks p := by
      calc
        permuteBlocks g⁻¹ (tripleBlocks p) =
            permuteBlocks g⁻¹ (permuteBlocks g (tripleBlocks p)) := by rw [hs]
        _ = permuteBlocks (g⁻¹ * g) (tripleBlocks p) :=
          (permuteBlocks_mul _ _ _).symm
        _ = tripleBlocks p := by simp
    constructor
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · obtain ⟨l, hil, hjl, hlabel⟩ :=
          exists_third_in_tripleBlock p (g i) (g j)
            (g.injective.ne hij') hij
        have hblock : ({g i, g j, l} : Finset (Fin 6)) ∈ tripleBlocks p :=
          (triple_mem_tripleBlocks_iff p (g i) (g j) l).2
            ⟨g.injective.ne hij', hil, hjl, hij, hlabel⟩
        have himage : actBlock g⁻¹ {g i, g j, l} ∈
            permuteBlocks g⁻¹ (tripleBlocks p) :=
          Finset.mem_image.mpr ⟨{g i, g j, l}, hblock, rfl⟩
        rw [hsInv, actBlock_triple] at himage
        have hpre : ({i, j, g⁻¹ l} : Finset (Fin 6)) ∈ tripleBlocks p := by
          simpa using himage
        exact (triple_mem_tripleBlocks_iff p i j (g⁻¹ l)).1
          hpre |>.2.2.2.1
    · intro hij
      by_cases hij' : i = j
      · simpa [hij']
      · obtain ⟨k, hik, hjk, hlabel⟩ :=
          exists_third_in_tripleBlock p i j hij' hij
        have hblock : ({i, j, k} : Finset (Fin 6)) ∈ tripleBlocks p :=
          (triple_mem_tripleBlocks_iff p i j k).2
            ⟨hij', hik, hjk, hij, hlabel⟩
        have himage : actBlock g {i, j, k} ∈
            permuteBlocks g (tripleBlocks p) :=
          Finset.mem_image.mpr ⟨{i, j, k}, hblock, rfl⟩
        rw [hs, actBlock_triple] at himage
        exact (triple_mem_tripleBlocks_iff p (g i) (g j) (g k)).1
          himage |>.2.2.2.1
  · intro hg
    apply Finset.ext
    intro b
    constructor
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp ha with ⟨c, _, rfl⟩
      let i := tripleMember p c 0
      let j := tripleMember p c 1
      let k := tripleMember p c 2
      have hijk := (triple_mem_tripleBlocks_iff p i j k).1
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      rw [show tripleBlock p c = {i, j, k} by rfl, actBlock_triple]
      exact (triple_mem_tripleBlocks_iff p (g i) (g j) (g k)).2
        ⟨g.injective.ne hijk.1, g.injective.ne hijk.2.1,
          g.injective.ne hijk.2.2.1,
          (hg i j).2 hijk.2.2.2.1,
          (hg j k).2 hijk.2.2.2.2⟩
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
      let i := tripleMember p c 0
      let j := tripleMember p c 1
      let k := tripleMember p c 2
      have hijk := (triple_mem_tripleBlocks_iff p i j k).1
        (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
      let a := g⁻¹ i
      let e := g⁻¹ j
      let f := g⁻¹ k
      have haef : ({a, e, f} : Finset (Fin 6)) ∈ tripleBlocks p :=
        (triple_mem_tripleBlocks_iff p a e f).2 ⟨by
          intro h; exact hijk.1 (g.symm.injective h), by
          intro h; exact hijk.2.1 (g.symm.injective h), by
          intro h; exact hijk.2.2.1 (g.symm.injective h),
          (hg a e).1 (by simpa [a, e] using hijk.2.2.2.1),
          (hg e f).1 (by simpa [e, f] using hijk.2.2.2.2)⟩
      apply Finset.mem_image.mpr
      refine ⟨{a, e, f}, haef, ?_⟩
      rw [actBlock_triple]
      simp [a, e, f, i, j, k, tripleBlock]

theorem descriptor_injective [IsDomain K] (r : Fin 6 → K)
    (hr : Function.Injective r) : Function.Injective (descriptor r) := by
  classical
  intro s t hst
  have hroots : s.image (rootPolynomial r) = t.image (rootPolynomial r) := by
    apply prod_X_sub_C_injective
    change (∏ q ∈ s.image (rootPolynomial r), (X - C q)) =
      ∏ q ∈ t.image (rootPolynomial r), (X - C q)
    rw [Finset.prod_image (rootPolynomial_injective r hr).injOn,
      Finset.prod_image (rootPolynomial_injective r hr).injOn]
    simpa only [descriptor] using hst
  exact Finset.image_injective (rootPolynomial_injective r hr) hroots

theorem pairDescriptor_injective [IsDomain K] (r : Fin 6 → K)
    (hr : Function.Injective r) : Function.Injective (pairDescriptor r) := by
  intro p q hpq
  apply pairBlocks_injective
  exact descriptor_injective r hr hpq

theorem tripleDescriptor_injective [IsDomain K] (r : Fin 6 → K)
    (hr : Function.Injective r) : Function.Injective (tripleDescriptor r) := by
  intro p q hpq
  apply tripleBlocks_injective
  exact descriptor_injective r hr hpq

/-- For distinct specialized roots, the descriptor stabilizer is exactly the
pair-block stabilizer.  In particular, no specialization collision can enlarge
the stabilizer. -/
theorem pairDescriptor_permute_eq_self_iff [IsDomain K]
    (r : Fin 6 → K) (hr : Function.Injective r)
    (p : PairPartition) (g : S6) :
    pairDescriptor (fun i ↦ r (g i)) p = pairDescriptor r p ↔
      Preserves (pairLabel p) g := by
  rw [pairDescriptor, descriptor_permute]
  change descriptor r (permuteBlocks g (pairBlocks p)) =
    descriptor r (pairBlocks p) ↔ _
  rw [(descriptor_injective r hr).eq_iff, pairBlocks_stabilized_iff]

/-- For distinct specialized roots, the descriptor stabilizer is exactly the
triple-block stabilizer. -/
theorem tripleDescriptor_permute_eq_self_iff [IsDomain K]
    (r : Fin 6 → K) (hr : Function.Injective r)
    (p : TriplePartition) (g : S6) :
    tripleDescriptor (fun i ↦ r (g i)) p = tripleDescriptor r p ↔
      Preserves (tripleLabel p) g := by
  rw [tripleDescriptor, descriptor_permute]
  change descriptor r (permuteBlocks g (tripleBlocks p)) =
    descriptor r (tripleBlocks p) ↔ _
  rw [(descriptor_injective r hr).eq_iff, tripleBlocks_stabilized_iff]

end RootPolynomials

theorem exists_pairBlocks_permute (g : S6) (p : PairPartition) :
    ∃ q : PairPartition,
      permuteBlocks g (pairBlocks p) = pairBlocks q := by
  classical
  let label := transportedLabel (pairLabel p) g
  have hcard : ∀ b, fiberCard label b = 2 := by
    intro b
    rw [fiberCard_transportedLabel]
    exact pairLabel_fiberCard p b
  obtain ⟨q, hq⟩ := pairLabel_complete label hcard
  refine ⟨q, Finset.ext fun b ↦ ?_⟩
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨c, _, rfl⟩
    let i := pairMember p c 0
    let j := pairMember p c 1
    have hij := (pair_mem_pairBlocks_iff p i j).1
      (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
    rw [show pairBlock p c = {i, j} by rfl, actBlock_pair]
    exact (pair_mem_pairBlocks_iff q (g i) (g j)).2
      ⟨g.injective.ne hij.1,
        (hq _ _).1 (by simpa [label, transportedLabel] using hij.2)⟩
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    let i := pairMember q c 0
    let j := pairMember q c 1
    have hij := (pair_mem_pairBlocks_iff q i j).1
      (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
    let a := g⁻¹ i
    let e := g⁻¹ j
    have hae : ({a, e} : Finset (Fin 6)) ∈ pairBlocks p :=
      (pair_mem_pairBlocks_iff p a e).2 ⟨by
        intro h; exact hij.1 (g.symm.injective h), by
        have hl : label i = label j := (hq i j).2 hij.2
        simpa [label, transportedLabel, a, e] using hl⟩
    apply Finset.mem_image.mpr
    refine ⟨{a, e}, hae, ?_⟩
    rw [actBlock_pair]
    simp [a, e, i, j, pairBlock]

theorem exists_tripleBlocks_permute (g : S6) (p : TriplePartition) :
    ∃ q : TriplePartition,
      permuteBlocks g (tripleBlocks p) = tripleBlocks q := by
  classical
  let label := transportedLabel (tripleLabel p) g
  have hcard : ∀ b, fiberCard label b = 3 := by
    intro b
    rw [fiberCard_transportedLabel]
    exact tripleLabel_fiberCard p b
  obtain ⟨q, hq⟩ := tripleLabel_complete label hcard
  refine ⟨q, Finset.ext fun b ↦ ?_⟩
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨c, _, rfl⟩
    let i := tripleMember p c 0
    let j := tripleMember p c 1
    let k := tripleMember p c 2
    have hijk := (triple_mem_tripleBlocks_iff p i j k).1
      (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
    rw [show tripleBlock p c = {i, j, k} by rfl, actBlock_triple]
    exact (triple_mem_tripleBlocks_iff q (g i) (g j) (g k)).2
      ⟨g.injective.ne hijk.1, g.injective.ne hijk.2.1,
        g.injective.ne hijk.2.2.1,
        (hq _ _).1 (by simpa [label, transportedLabel] using hijk.2.2.2.1),
        (hq _ _).1 (by simpa [label, transportedLabel] using hijk.2.2.2.2)⟩
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨c, _, rfl⟩
    let i := tripleMember q c 0
    let j := tripleMember q c 1
    let k := tripleMember q c 2
    have hijk := (triple_mem_tripleBlocks_iff q i j k).1
      (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
    let a := g⁻¹ i
    let e := g⁻¹ j
    let f := g⁻¹ k
    have haef : ({a, e, f} : Finset (Fin 6)) ∈ tripleBlocks p :=
      (triple_mem_tripleBlocks_iff p a e f).2 ⟨by
        intro h; exact hijk.1 (g.symm.injective h), by
        intro h; exact hijk.2.1 (g.symm.injective h), by
        intro h; exact hijk.2.2.1 (g.symm.injective h), by
        have hl : label i = label j := (hq i j).2 hijk.2.2.2.1
        simpa [label, transportedLabel, a, e] using hl, by
        have hl : label j = label k := (hq j k).2 hijk.2.2.2.2
        simpa [label, transportedLabel, e, f] using hl⟩
    apply Finset.mem_image.mpr
    refine ⟨{a, e, f}, haef, ?_⟩
    rw [actBlock_triple]
    simp [a, e, f, i, j, k, tripleBlock]

noncomputable def pairPartitionMap (g : S6) (p : PairPartition) :
    PairPartition := Classical.choose (exists_pairBlocks_permute g p)

theorem pairPartitionMap_blocks (g : S6) (p : PairPartition) :
    permuteBlocks g (pairBlocks p) = pairBlocks (pairPartitionMap g p) :=
  Classical.choose_spec (exists_pairBlocks_permute g p)

theorem pairPartitionMap_injective (g : S6) :
    Function.Injective (pairPartitionMap g) := by
  intro p q hpq
  apply pairBlocks_injective
  apply (Finset.image_injective (actBlock_injective g))
  change permuteBlocks g (pairBlocks p) = permuteBlocks g (pairBlocks q)
  rw [pairPartitionMap_blocks, pairPartitionMap_blocks, hpq]

noncomputable def pairPartitionPerm (g : S6) :
    PairPartition ≃ PairPartition :=
  Equiv.ofBijective (pairPartitionMap g)
    ⟨pairPartitionMap_injective g,
      Finite.injective_iff_surjective.mp (pairPartitionMap_injective g)⟩

@[simp] theorem pairPartitionPerm_apply (g : S6) (p : PairPartition) :
    pairPartitionPerm g p = pairPartitionMap g p := rfl

noncomputable def triplePartitionMap (g : S6) (p : TriplePartition) :
    TriplePartition := Classical.choose (exists_tripleBlocks_permute g p)

theorem triplePartitionMap_blocks (g : S6) (p : TriplePartition) :
    permuteBlocks g (tripleBlocks p) = tripleBlocks (triplePartitionMap g p) :=
  Classical.choose_spec (exists_tripleBlocks_permute g p)

theorem triplePartitionMap_injective (g : S6) :
    Function.Injective (triplePartitionMap g) := by
  intro p q hpq
  apply tripleBlocks_injective
  apply (Finset.image_injective (actBlock_injective g))
  change permuteBlocks g (tripleBlocks p) = permuteBlocks g (tripleBlocks q)
  rw [triplePartitionMap_blocks, triplePartitionMap_blocks, hpq]

noncomputable def triplePartitionPerm (g : S6) :
    TriplePartition ≃ TriplePartition :=
  Equiv.ofBijective (triplePartitionMap g)
    ⟨triplePartitionMap_injective g,
      Finite.injective_iff_surjective.mp (triplePartitionMap_injective g)⟩

@[simp] theorem triplePartitionPerm_apply (g : S6) (p : TriplePartition) :
    triplePartitionPerm g p = triplePartitionMap g p := rfl

/-! ## Finite scalar separation -/

/-- The standard equivalence between bivariate polynomials and polynomials in
one variable whose coefficients are univariate polynomials. -/
noncomputable def bivariateEquiv (K : Type*) [CommRing K] :
    MvPolynomial (Fin 2) K ≃+* Polynomial (Polynomial K) :=
  (MvPolynomial.finSuccEquiv K 1).toRingEquiv.trans
    (Polynomial.mapEquiv
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv)

section Bivariate

variable {K : Type*} [CommRing K]

noncomputable def bivariateRootPolynomial (r : Fin 6 → K)
    (s : Finset (Fin 6)) : MvPolynomial (Fin 2) K :=
  ∏ i ∈ s, (MvPolynomial.X 1 - MvPolynomial.C (r i))

noncomputable def bivariateDescriptor (r : Fin 6 → K)
    (blocks : Finset (Finset (Fin 6))) : MvPolynomial (Fin 2) K :=
  ∏ b ∈ blocks, (MvPolynomial.X 0 - bivariateRootPolynomial r b)

noncomputable def pairBivariateDescriptor (r : Fin 6 → K)
    (p : PairPartition) : MvPolynomial (Fin 2) K :=
  bivariateDescriptor r (pairBlocks p)

noncomputable def tripleBivariateDescriptor (r : Fin 6 → K)
    (p : TriplePartition) : MvPolynomial (Fin 2) K :=
  bivariateDescriptor r (tripleBlocks p)

@[simp] theorem bivariateEquiv_X_zero :
    bivariateEquiv K (MvPolynomial.X 0) =
      (Polynomial.X : Polynomial (Polynomial K)) := by
  simp [bivariateEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem bivariateEquiv_X_one :
    bivariateEquiv K (MvPolynomial.X 1) =
      Polynomial.C (Polynomial.X : Polynomial K) := by
  change Polynomial.map
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1)) = _
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide]
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem bivariateEquiv_C (a : K) :
    bivariateEquiv K (MvPolynomial.C a) =
      Polynomial.C (Polynomial.C a) := by
  change Polynomial.map
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv.toRingHom
      (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C a)) = _
  rw [MvPolynomial.finSuccEquiv_apply]
  simp

theorem bivariateEquiv_bivariateRootPolynomial (r : Fin 6 → K)
    (s : Finset (Fin 6)) :
    bivariateEquiv K (bivariateRootPolynomial r s) =
      Polynomial.C (rootPolynomial r s) := by
  classical
  simp [bivariateRootPolynomial, rootPolynomial]

theorem bivariateEquiv_bivariateDescriptor (r : Fin 6 → K)
    (blocks : Finset (Finset (Fin 6))) :
    bivariateEquiv K (bivariateDescriptor r blocks) = descriptor r blocks := by
  classical
  simp [bivariateDescriptor, descriptor,
    bivariateEquiv_bivariateRootPolynomial]

theorem pairBivariateDescriptor_injective [IsDomain K]
    (r : Fin 6 → K) (hr : Function.Injective r) :
    Function.Injective (pairBivariateDescriptor r) := by
  intro p q hpq
  apply pairDescriptor_injective r hr
  have h := congrArg (bivariateEquiv K) hpq
  simpa only [pairBivariateDescriptor,
    bivariateEquiv_bivariateDescriptor, pairDescriptor] using h

theorem tripleBivariateDescriptor_injective [IsDomain K]
    (r : Fin 6 → K) (hr : Function.Injective r) :
    Function.Injective (tripleBivariateDescriptor r) := by
  intro p q hpq
  apply tripleDescriptor_injective r hr
  have h := congrArg (bivariateEquiv K) hpq
  simpa only [tripleBivariateDescriptor,
    bivariateEquiv_bivariateDescriptor, tripleDescriptor] using h

theorem bivariateRootPolynomial_map {L : Type*} [CommRing L]
    (f : K →+* L) (r : Fin 6 → K) (s : Finset (Fin 6)) :
    MvPolynomial.map f (bivariateRootPolynomial r s) =
      bivariateRootPolynomial (fun i ↦ f (r i)) s := by
  classical
  simp [bivariateRootPolynomial]

theorem bivariateDescriptor_map {L : Type*} [CommRing L]
    (f : K →+* L) (r : Fin 6 → K)
    (blocks : Finset (Finset (Fin 6))) :
    MvPolynomial.map f (bivariateDescriptor r blocks) =
      bivariateDescriptor (fun i ↦ f (r i)) blocks := by
  classical
  simp [bivariateDescriptor, bivariateRootPolynomial_map]

theorem bivariateRootPolynomial_permute (r : Fin 6 → K) (g : S6)
    (s : Finset (Fin 6)) :
    bivariateRootPolynomial (fun i ↦ r (g i)) s =
      bivariateRootPolynomial r (s.image g) := by
  classical
  rw [bivariateRootPolynomial, bivariateRootPolynomial,
    Finset.prod_image g.injective.injOn]

theorem bivariateDescriptor_permute (r : Fin 6 → K) (g : S6)
    (blocks : Finset (Finset (Fin 6))) :
    bivariateDescriptor (fun i ↦ r (g i)) blocks =
      bivariateDescriptor r (permuteBlocks g blocks) := by
  classical
  rw [bivariateDescriptor, bivariateDescriptor, permuteBlocks,
    Finset.prod_image (actBlock_injective g).injOn]
  apply Finset.prod_congr rfl
  intro b hb
  rw [actBlock, bivariateRootPolynomial_permute]

theorem exists_pairBivariateDescriptor_permute
    (r : Fin 6 → K) (g : S6) (p : PairPartition) :
    ∃ q : PairPartition,
      pairBivariateDescriptor (fun i ↦ r (g i)) p =
        pairBivariateDescriptor r q := by
  obtain ⟨q, hq⟩ := exists_pairBlocks_permute g p
  refine ⟨q, ?_⟩
  rw [pairBivariateDescriptor, bivariateDescriptor_permute, hq]
  rfl

theorem exists_tripleBivariateDescriptor_permute
    (r : Fin 6 → K) (g : S6) (p : TriplePartition) :
    ∃ q : TriplePartition,
      tripleBivariateDescriptor (fun i ↦ r (g i)) p =
        tripleBivariateDescriptor r q := by
  obtain ⟨q, hq⟩ := exists_tripleBlocks_permute g p
  refine ⟨q, ?_⟩
  rw [tripleBivariateDescriptor, bivariateDescriptor_permute, hq]
  rfl

theorem pairBivariateDescriptor_permute (r : Fin 6 → K)
    (g : S6) (p : PairPartition) :
    pairBivariateDescriptor (fun i ↦ r (g i)) p =
      pairBivariateDescriptor r (pairPartitionPerm g p) := by
  rw [pairBivariateDescriptor, bivariateDescriptor_permute,
    pairPartitionPerm_apply, pairPartitionMap_blocks]
  rfl

theorem tripleBivariateDescriptor_permute (r : Fin 6 → K)
    (g : S6) (p : TriplePartition) :
    tripleBivariateDescriptor (fun i ↦ r (g i)) p =
      tripleBivariateDescriptor r (triplePartitionPerm g p) := by
  rw [tripleBivariateDescriptor, bivariateDescriptor_permute,
    triplePartitionPerm_apply, triplePartitionMap_blocks]
  rfl

theorem pairBivariateDescriptor_permute_eq_self_iff [IsDomain K]
    (r : Fin 6 → K) (hr : Function.Injective r)
    (p : PairPartition) (g : S6) :
    pairBivariateDescriptor (fun i ↦ r (g i)) p =
        pairBivariateDescriptor r p ↔ Preserves (pairLabel p) g := by
  constructor
  · intro h
    apply (pairDescriptor_permute_eq_self_iff r hr p g).1
    have h' := congrArg (bivariateEquiv K) h
    simpa only [pairBivariateDescriptor,
      bivariateEquiv_bivariateDescriptor, pairDescriptor] using h'
  · intro h
    apply (bivariateEquiv K).injective
    simpa only [pairBivariateDescriptor,
      bivariateEquiv_bivariateDescriptor, pairDescriptor] using
      (pairDescriptor_permute_eq_self_iff r hr p g).2 h

theorem tripleBivariateDescriptor_permute_eq_self_iff [IsDomain K]
    (r : Fin 6 → K) (hr : Function.Injective r)
    (p : TriplePartition) (g : S6) :
    tripleBivariateDescriptor (fun i ↦ r (g i)) p =
        tripleBivariateDescriptor r p ↔ Preserves (tripleLabel p) g := by
  constructor
  · intro h
    apply (tripleDescriptor_permute_eq_self_iff r hr p g).1
    have h' := congrArg (bivariateEquiv K) h
    simpa only [tripleBivariateDescriptor,
      bivariateEquiv_bivariateDescriptor, tripleDescriptor] using h'
  · intro h
    apply (bivariateEquiv K).injective
    simpa only [tripleBivariateDescriptor,
      bivariateEquiv_bivariateDescriptor, tripleDescriptor] using
      (tripleDescriptor_permute_eq_self_iff r hr p g).2 h

noncomputable def pairDescriptorValue (x : Fin 2 → ℕ)
    (r : Fin 6 → K) (p : PairPartition) : K :=
  MvPolynomial.eval (fun i ↦ (x i : K)) (pairBivariateDescriptor r p)

noncomputable def tripleDescriptorValue (x : Fin 2 → ℕ)
    (r : Fin 6 → K) (p : TriplePartition) : K :=
  MvPolynomial.eval (fun i ↦ (x i : K)) (tripleBivariateDescriptor r p)

theorem pairDescriptorValue_permute (x : Fin 2 → ℕ)
    (r : Fin 6 → K) (g : S6) (p : PairPartition) :
    pairDescriptorValue x (fun i ↦ r (g i)) p =
      pairDescriptorValue x r (pairPartitionPerm g p) := by
  rw [pairDescriptorValue, pairBivariateDescriptor_permute]
  rfl

theorem tripleDescriptorValue_permute (x : Fin 2 → ℕ)
    (r : Fin 6 → K) (g : S6) (p : TriplePartition) :
    tripleDescriptorValue x (fun i ↦ r (g i)) p =
      tripleDescriptorValue x r (triplePartitionPerm g p) := by
  rw [tripleDescriptorValue, tripleBivariateDescriptor_permute]
  rfl

theorem map_pairDescriptorValue {L : Type*} [CommRing L]
    (f : K →+* L) (x : Fin 2 → ℕ) (r : Fin 6 → K)
    (p : PairPartition) :
    f (pairDescriptorValue x r p) =
      pairDescriptorValue x (fun i ↦ f (r i)) p := by
  rw [pairDescriptorValue, pairDescriptorValue]
  calc
    f (MvPolynomial.eval (fun i ↦ (x i : K))
        (pairBivariateDescriptor r p)) =
        MvPolynomial.eval₂ f (fun i ↦ f (x i : K))
          (pairBivariateDescriptor r p) :=
      MvPolynomial.eval₂_comp f _ _
    _ = MvPolynomial.eval₂ f (fun i ↦ (x i : L))
          (pairBivariateDescriptor r p) := by
      congr 1
      funext i
      simp
    _ = MvPolynomial.eval (fun i ↦ (x i : L))
          (MvPolynomial.map f (pairBivariateDescriptor r p)) := by
      rw [MvPolynomial.eval_map]
    _ = MvPolynomial.eval (fun i ↦ (x i : L))
          (pairBivariateDescriptor (fun i ↦ f (r i)) p) := by
      rw [pairBivariateDescriptor, bivariateDescriptor_map]
      rfl

theorem map_tripleDescriptorValue {L : Type*} [CommRing L]
    (f : K →+* L) (x : Fin 2 → ℕ) (r : Fin 6 → K)
    (p : TriplePartition) :
    f (tripleDescriptorValue x r p) =
      tripleDescriptorValue x (fun i ↦ f (r i)) p := by
  rw [tripleDescriptorValue, tripleDescriptorValue]
  calc
    f (MvPolynomial.eval (fun i ↦ (x i : K))
        (tripleBivariateDescriptor r p)) =
        MvPolynomial.eval₂ f (fun i ↦ f (x i : K))
          (tripleBivariateDescriptor r p) :=
      MvPolynomial.eval₂_comp f _ _
    _ = MvPolynomial.eval₂ f (fun i ↦ (x i : L))
          (tripleBivariateDescriptor r p) := by
      congr 1
      funext i
      simp
    _ = MvPolynomial.eval (fun i ↦ (x i : L))
          (MvPolynomial.map f (tripleBivariateDescriptor r p)) := by
      rw [MvPolynomial.eval_map]
    _ = MvPolynomial.eval (fun i ↦ (x i : L))
          (tripleBivariateDescriptor (fun i ↦ f (r i)) p) := by
      rw [tripleBivariateDescriptor, bivariateDescriptor_map]
      rfl

theorem pairDescriptorValue_permute_fixed_iff [IsDomain K]
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (hr : Function.Injective r)
    (hx : Function.Injective (pairDescriptorValue x r))
    (p : PairPartition) (g : S6) :
    pairDescriptorValue x (fun i ↦ r (g i)) p = pairDescriptorValue x r p ↔
      Preserves (pairLabel p) g := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := exists_pairBivariateDescriptor_permute r g p
    have hv : pairDescriptorValue x r q = pairDescriptorValue x r p := by
      rw [pairDescriptorValue, ← hq]
      exact h
    have hpq := hx hv
    subst q
    exact (pairBivariateDescriptor_permute_eq_self_iff r hr p g).1 hq
  · intro h
    apply congrArg (MvPolynomial.eval (fun i ↦ (x i : K)))
    exact (pairBivariateDescriptor_permute_eq_self_iff r hr p g).2 h

theorem tripleDescriptorValue_permute_fixed_iff [IsDomain K]
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (hr : Function.Injective r)
    (hx : Function.Injective (tripleDescriptorValue x r))
    (p : TriplePartition) (g : S6) :
    tripleDescriptorValue x (fun i ↦ r (g i)) p = tripleDescriptorValue x r p ↔
      Preserves (tripleLabel p) g := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := exists_tripleBivariateDescriptor_permute r g p
    have hv : tripleDescriptorValue x r q = tripleDescriptorValue x r p := by
      rw [tripleDescriptorValue, ← hq]
      exact h
    have hpq := hx hv
    subst q
    exact (tripleBivariateDescriptor_permute_eq_self_iff r hr p g).1 hq
  · intro h
    apply congrArg (MvPolynomial.eval (fun i ↦ (x i : K)))
    exact (tripleBivariateDescriptor_permute_eq_self_iff r hr p g).2 h

noncomputable def pairEvaluatedResolvent (x : Fin 2 → ℕ)
    (r : Fin 6 → K) : Polynomial K :=
  ∏ p : PairPartition, (Polynomial.X - Polynomial.C (pairDescriptorValue x r p))

noncomputable def tripleEvaluatedResolvent (x : Fin 2 → ℕ)
    (r : Fin 6 → K) : Polynomial K :=
  ∏ p : TriplePartition,
    (Polynomial.X - Polynomial.C (tripleDescriptorValue x r p))

theorem pairEvaluatedResolvent_permute (x : Fin 2 → ℕ)
    (r : Fin 6 → K) (g : S6) :
    pairEvaluatedResolvent x (fun i ↦ r (g i)) =
      pairEvaluatedResolvent x r := by
  rw [pairEvaluatedResolvent]
  simp_rw [pairDescriptorValue_permute]
  exact (pairPartitionPerm g).prod_comp
    (fun p ↦ Polynomial.X - Polynomial.C (pairDescriptorValue x r p))

theorem tripleEvaluatedResolvent_permute (x : Fin 2 → ℕ)
    (r : Fin 6 → K) (g : S6) :
    tripleEvaluatedResolvent x (fun i ↦ r (g i)) =
      tripleEvaluatedResolvent x r := by
  rw [tripleEvaluatedResolvent]
  simp_rw [tripleDescriptorValue_permute]
  exact (triplePartitionPerm g).prod_comp
    (fun p ↦ Polynomial.X - Polynomial.C (tripleDescriptorValue x r p))

theorem pairEvaluatedResolvent_map {L : Type*} [CommRing L]
    (f : K →+* L) (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (pairEvaluatedResolvent x r).map f =
      pairEvaluatedResolvent x (fun i ↦ f (r i)) := by
  classical
  rw [pairEvaluatedResolvent, pairEvaluatedResolvent, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [map_pairDescriptorValue]

theorem tripleEvaluatedResolvent_map {L : Type*} [CommRing L]
    (f : K →+* L) (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (tripleEvaluatedResolvent x r).map f =
      tripleEvaluatedResolvent x (fun i ↦ f (r i)) := by
  classical
  rw [tripleEvaluatedResolvent, tripleEvaluatedResolvent, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [map_tripleDescriptorValue]

theorem pairEvaluatedResolvent_monic (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (pairEvaluatedResolvent x r).Monic := by
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem tripleEvaluatedResolvent_monic (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (tripleEvaluatedResolvent x r).Monic := by
  exact Polynomial.monic_prod_of_monic _ _
    (fun _ _ ↦ Polynomial.monic_X_sub_C _)

theorem pairEvaluatedResolvent_natDegree [Nontrivial K]
    (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (pairEvaluatedResolvent x r).natDegree = 15 := by
  rw [pairEvaluatedResolvent,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

theorem tripleEvaluatedResolvent_natDegree [Nontrivial K]
    (x : Fin 2 → ℕ) (r : Fin 6 → K) :
    (tripleEvaluatedResolvent x r).natDegree = 10 := by
  rw [tripleEvaluatedResolvent,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp

theorem pairEvaluatedResolvent_isRoot_iff [IsDomain K]
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (z : K) :
    (pairEvaluatedResolvent x r).IsRoot z ↔
      ∃ p : PairPartition, pairDescriptorValue x r p = z := by
  classical
  simp only [Polynomial.IsRoot, pairEvaluatedResolvent,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero]
  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, hp.symm⟩

theorem tripleEvaluatedResolvent_isRoot_iff [IsDomain K]
    (x : Fin 2 → ℕ) (r : Fin 6 → K) (z : K) :
    (tripleEvaluatedResolvent x r).IsRoot z ↔
      ∃ p : TriplePartition, tripleDescriptorValue x r p = z := by
  classical
  simp only [Polynomial.IsRoot, tripleEvaluatedResolvent,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero]
  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, hp.symm⟩

end Bivariate

section FieldSpecialization

variable {F : Type*} [Field F]

theorem pairEvaluatedResolvent_separable_iff
    (x : Fin 2 → ℕ) (r : Fin 6 → F) :
    (pairEvaluatedResolvent x r).Separable ↔
      Function.Injective (pairDescriptorValue x r) := by
  rw [pairEvaluatedResolvent, Polynomial.separable_prod_X_sub_C_iff]

theorem tripleEvaluatedResolvent_separable_iff
    (x : Fin 2 → ℕ) (r : Fin 6 → F) :
    (tripleEvaluatedResolvent x r).Separable ↔
      Function.Injective (tripleDescriptorValue x r) := by
  rw [tripleEvaluatedResolvent, Polynomial.separable_prod_X_sub_C_iff]

end FieldSpecialization

/-- A nonzero multivariate polynomial over a characteristic-zero domain is
nonzero at some tuple of natural numbers.  The proof uses the explicit finite
grid supplied by the combinatorial Nullstellensatz, so it also justifies a
terminating enumeration search. -/
theorem exists_nat_eval_ne_zero
    {R σ : Type*} [CommRing R] [IsDomain R] [CharZero R] [Finite σ]
    (P : MvPolynomial σ R) (hP : P ≠ 0) :
    ∃ x : σ → ℕ, MvPolynomial.eval (fun i ↦ (x i : R)) P ≠ 0 := by
  classical
  by_contra hex
  push_neg at hex
  apply hP
  let S : σ → Finset R := fun i ↦
    (Finset.range (P.degreeOf i + 1)).image fun n : ℕ ↦ (n : R)
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P S
  · intro i
    have hcard : (S i).card = P.degreeOf i + 1 := by
      change ((Finset.range (P.degreeOf i + 1)).image
        (fun n : ℕ ↦ (n : R))).card = P.degreeOf i + 1
      rw [Finset.card_image_of_injective _ Nat.cast_injective]
      simp
    rw [hcard]
    omega
  · intro x hx
    choose n hnRange hnx using fun i ↦ Finset.mem_image.mp (hx i)
    have heq : (fun i ↦ (n i : R)) = x := by
      funext i
      exact hnx i
    rw [← heq]
    exact hex n

/-- A finite injective family of multivariate polynomials can be separated by
a single natural-number evaluation point. -/
theorem exists_nat_eval_injective
    {R σ α : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Finite σ] [Fintype α] [DecidableEq α]
    (f : α → MvPolynomial σ R) (hf : Function.Injective f) :
    ∃ x : σ → ℕ,
      Function.Injective fun a ↦
        MvPolynomial.eval (fun i ↦ (x i : R)) (f a) := by
  classical
  let pairs : Finset (α × α) :=
    Finset.univ.filter fun ab ↦ ab.1 ≠ ab.2
  let P : MvPolynomial σ R := ∏ ab ∈ pairs, (f ab.1 - f ab.2)
  have hP : P ≠ 0 := by
    change (∏ ab ∈ pairs, (f ab.1 - f ab.2)) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro ab hab
    exact sub_ne_zero.mpr (hf.ne (Finset.mem_filter.mp hab).2)
  obtain ⟨x, hx⟩ := exists_nat_eval_ne_zero P hP
  refine ⟨x, ?_⟩
  intro a b hab
  by_contra hab'
  apply hx
  simp only [P, map_prod]
  apply Finset.prod_eq_zero (i := (a, b))
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab'⟩
  · simp [hab]

theorem exists_pairDescriptor_separating_evaluation
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (r : Fin 6 → K) (hr : Function.Injective r) :
    ∃ x : Fin 2 → ℕ,
      Function.Injective fun p ↦
        MvPolynomial.eval (fun i ↦ (x i : K))
          (pairBivariateDescriptor r p) :=
  exists_nat_eval_injective _ (pairBivariateDescriptor_injective r hr)

theorem exists_tripleDescriptor_separating_evaluation
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (r : Fin 6 → K) (hr : Function.Injective r) :
    ∃ x : Fin 2 → ℕ,
      Function.Injective fun p ↦
        MvPolynomial.eval (fun i ↦ (x i : K))
          (tripleBivariateDescriptor r p) :=
  exists_nat_eval_injective _ (tripleBivariateDescriptor_injective r hr)

theorem exists_pairDescriptorValue_injective
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (r : Fin 6 → K) (hr : Function.Injective r) :
    ∃ x : Fin 2 → ℕ, Function.Injective (pairDescriptorValue x r) := by
  obtain ⟨x, hx⟩ := exists_pairDescriptor_separating_evaluation r hr
  refine ⟨x, ?_⟩
  change Function.Injective fun p ↦
    MvPolynomial.eval (fun i ↦ (x i : K)) (pairBivariateDescriptor r p)
  exact hx

theorem exists_tripleDescriptorValue_injective
    {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (r : Fin 6 → K) (hr : Function.Injective r) :
    ∃ x : Fin 2 → ℕ, Function.Injective (tripleDescriptorValue x r) := by
  obtain ⟨x, hx⟩ := exists_tripleDescriptor_separating_evaluation r hr
  refine ⟨x, ?_⟩
  change Function.Injective fun p ↦
    MvPolynomial.eval (fun i ↦ (x i : K)) (tripleBivariateDescriptor r p)
  exact hx

end LeanProofs.PolynomialFormulas.SexticSeparatingInvariants

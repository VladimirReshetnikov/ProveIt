import New.Spanning.RemainingTerms.Gain
import New.Spanning.RemainingTerms.LatticesOfCorank

/-!
# The sum over pairs of near terms

For a fixed class `c`, a pair of near terms over a block `(c, s, c')` is sorted by its label, a
component of `s` in the reduced image of the Bessel subgroup, and by its common lattice. Over a
given lattice and label there are few terms, and the sum over the lattices is bounded.

The main notions used in the statements:
* a class `c : S.Classes` is a double coset of the unitary group of the definite space `X₀` at the
  finite adeles, with representative `h_c`;
* a block is a triple `(c, s, c')`, with `s` in the finite group `S.ResidueGL`. A rational isometry
  `γ` is a term over it if `h_c⁻¹ γ h_c'` is integral with reduction `s`;
* `S.IsNearPairOverAgreeingBlock c c' q`: the two terms in `q` are near, are the chosen
  representatives of their double cosets, have a cell rank, and lie over one block `(c, s, c')`
  whose `s` agrees (`S.Agrees s`);
* `commonLink γ γ'`: the subspace of `X₀` that two terms have in common; its dimension is the rank
  of their common lattice `L₁₂ = S.pairLattice c c' γ γ'`, which has corank `l` if this dimension is
  `k - l`;
* `S.termLattice c c' γ`: the lattice `L_γ ⊆ Λ ∩ X₀` of a term, where `Λ` is the adelic lattice of
  the class `c` and `Λ ∩ X₀` is `S.classLatticeX₀ c`.

The main result is `New.Filling.sum_pairDiscriminant_inv_le`.
-/

namespace New.Filling

open NumberField Matrix Module Fintype ENNReal Pointwise

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- If every index `i` is related by `R` to some `y` of the same weight, and at most `x` indices are
related to each `y`, then the sum over the indices is at most `x` times the sum over the `y`. -/
lemma tsum_le_tsum_mul_of_encard_le {I Y : Type} {v : I → ℝ≥0∞} {w : Y → ℝ≥0∞} {x : ℝ≥0∞}
    (R : I → Y → Prop) (h_cover : ∀ i : I, ∃ y : Y, R i y ∧ v i = w y)
    (h_fibre : ∀ y : Y, {i : I | R i y}.encard ≤ x) : ∑' i : I, v i ≤ (∑' y : Y, w y) * x := by
  choose chosenY h_over h_weight using h_cover
  calc ∑' i, v i = ∑' y, ∑' i : chosenY ⁻¹' {y}, v i := (ENNReal.tsum_fiberwise v chosenY).symm
    _ ≤ ∑' y, w y * x := ENNReal.tsum_le_tsum fun y ↦ by
      have h_const (i : chosenY ⁻¹' {y}) : v i = w y := by
        rw [h_weight i, show chosenY i = y from i.2]
      have h_subset : chosenY ⁻¹' {y} ⊆ {i : I | R i y} :=
        fun i (hi : chosenY i = y) ↦ by simpa [hi] using h_over i
      rw [tsum_congr h_const, tsum_set_const, mul_comm]
      grw [h_subset, h_fibre]
    _ = (∑' y, w y) * x := ENNReal.tsum_mul_right

/-- For positive `n` and `l ≤ n ^ 3`, twice the exponent `2000 n ^ 6 (l + 1) f` in the
count of the terms over a lattice is at most `10 ^ 5 n ^ 9 f`. -/
lemma two_mul_count_exponent_le {n f l : ℕ} (hn : 0 < n) (hl : l ≤ n ^ 3) :
    2 * (2000 * n ^ 6 * (l + 1) * f) ≤ 10 ^ 5 * n ^ 9 * f := by
  have h_cube : 1 ≤ n ^ 3 := Nat.pow_pos hn
  have h_corank : n ^ 6 * (l + 1) * f ≤ n ^ 6 * (n ^ 3 + n ^ 3) * f := by gcongr
  nlinarith [Nat.zero_le (n ^ 9 * f)]

variable (S) in
/-- The terms `γ` and `γ'` from the class `c'` to the class `c` both have the label `t`
(`S.IsNearTermAt`), and their common lattice `S.pairLattice c c' γ γ'` is a lattice in `Λ ∩ X₀` that
lies in the lattices `S.termLattice` of both terms and whose rank is the dimension of
`commonLink γ γ'`, the subspace of `X₀` that the terms share. -/
structure IsLabelledPair (c c' : S.Classes) (t : S.reducedImage besselS) (γ γ' : S.G E) : Prop where
  /-- The first term is near and has the label `t`. -/
  isNearTermAt_left : S.IsNearTermAt c t (c', γ)
  /-- The second term is near and has the label `t`. -/
  isNearTermAt_right : S.IsNearTermAt c t (c', γ')
  /-- The common lattice lies in the lattice of the first term. -/
  le_termLattice_left : S.pairLattice c c' γ γ' ≤ S.termLattice c c' γ
  /-- The common lattice lies in the lattice of the second term. -/
  le_termLattice_right : S.pairLattice c c' γ γ' ≤ S.termLattice c c' γ'
  /-- The common lattice lies in `Λ ∩ X₀`. -/
  le_classLatticeX₀ : S.pairLattice c c' γ γ' ≤ S.classLatticeX₀ c
  /-- The rank of the common lattice is the dimension of the subspace that the terms share. -/
  isLatticeOfRank : IsLatticeOfRank (finrank E (commonLink γ γ')) (S.pairLattice c c' γ γ')

/-- Let `E` be a CM field with a primitive 5040th root of unity, `S` admissible filling data of
shape `𝔰` over `E`, and `c`, `c'` classes. A near pair consists of two rational isometries `γ`, `γ'`
that are near, chosen in their double cosets and of some cell rank, and lie over one block
`(c, s, c')`: both `h_c⁻¹ γ h_c'` and `h_c⁻¹ γ' h_c'` are integral with the same reduction `s`,
which agrees (`S.Agrees s`). Such a pair has a common label `t`, and the lattices `S.termLattice` of
both terms contain their common lattice `S.pairLattice c c' γ γ'`. This is a lattice in
`Λ ∩ X₀ = S.classLatticeX₀ c`. -/
lemma exists_isLabelledPair_of_isNearPairOverAgreeingBlock [S.IsAdmissible] {c c' : S.Classes}
    {γ γ' : S.G E} (h_pair : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    ∃ t : S.reducedImage besselS, S.IsLabelledPair c c' t γ γ' := by
  obtain ⟨⟨h_near, h_level⟩, ⟨h_near', h_level'⟩, s, hs, h_over, h_over'⟩ := h_pair
  -- The label is that of the block `(c, s, c')` over which both terms lie. The common lattice is
  -- cut out of the intersection of the lattices of the two terms, each of which lies in `Λ ∩ X₀`.
  have h_le_inf : S.pairLattice c c' γ γ' ≤ S.termLattice c c' γ ⊓ S.termLattice c c' γ' :=
    inf_le_right
  exact ⟨(Subgroup.groupEquivQuotientProdSubgroup s).2,
    { isNearTermAt_left := ⟨⟨h_near, _, h_level⟩, s, h_over, rfl⟩
      isNearTermAt_right := ⟨⟨h_near', _, h_level'⟩, s, h_over', rfl⟩
      le_termLattice_left := h_le_inf.trans inf_le_left
      le_termLattice_right := h_le_inf.trans inf_le_right
      le_classLatticeX₀ := (h_le_inf.trans inf_le_left).trans inf_le_left
      isLatticeOfRank := isLatticeOfRank_pairLattice hs h_over h_over' h_level h_level' }⟩

variable (S) in
/-- The lattices `L ⊆ Λ ∩ X₀` of rank `r` with discriminant at most `S.discriminantBound`. -/
abbrev ClassBoundedDiscLattice (c : S.Classes) (r : ℕ) : Type :=
  {L : Submodule (Ô E) (𝔰.κ → 𝔸f E) // IsLatticeOfRank r L ∧
    L ≤ S.classLatticeX₀ c ∧ discriminant r L ≤ S.discriminantBound}

variable (S) in
/-- The near pairs over a block `(c, s, c')` with agreeing `s`
(`S.IsNearPairOverAgreeingBlock c c'`) whose common lattice has corank `l` and discriminant at most
`S.discriminantBound`. -/
def boundedDiscNearPairs (l : ℕ) (c c' : S.Classes) : Set (S.G E × S.G E) :=
  {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧
    finrank E (commonLink q.1 q.2) + l = 𝔰.k ∧
    S.pairDiscriminant c c' q.1 q.2 ≤ S.discriminantBound}

/-- Let `E` be a CM field with a primitive 5040th root of unity and `f` infinite places, `S`
admissible filling data of shape `𝔰` over `E` with size parameter `b = S.b`, and `c` a class, with
adelic lattice `Λ`. Let `n = 𝔰.n`, let `k = 𝔰.k` be the dimension of the definite space `X₀`, and
let `l ≤ n³`, `r + l = k`. A near pair over `(c, c')` is two near, chosen terms over one block
`(c, s, c')` with `s` agreeing; its common lattice `L₁₂ ⊆ Λ ∩ X₀` has rank the dimension of the
subspace of `X₀` that the terms share, and corank `l` if this rank is `r`. The sum of
`(disc L₁₂) ^ (-k)` over all classes `c'` and all such pairs with corank `l` and discriminant at
most `S.discriminantBound = b ^ (n³ f)` is at most the number of labels, times the sum of
`(disc L) ^ (-k)` over the lattices `L ⊆ Λ ∩ X₀` of rank `r` with the same bound on the
discriminant, times `S.tailScale = b ^ (k f / 4)`. -/
lemma sum_pairDiscriminant_inv_le_tsum [S.IsAdmissible] {c : S.Classes} {r l : ℕ}
    (hl_le : l ≤ 𝔰.n ^ 3) (h_rank : r + l = 𝔰.k) :
    ∑ c' : S.Classes, ∑' q : S.boundedDiscNearPairs l c c',
        ENNReal.ofReal (S.pairDiscriminant c c' q.val.fst q.val.snd ^ 𝔰.k)⁻¹ ≤
      Nat.card (S.reducedImage besselS) *
        (∑' L : S.ClassBoundedDiscLattice c r,
          ENNReal.ofReal (discriminant r (L : Submodule (Ô E) (𝔰.κ → 𝔸f E)) ^ 𝔰.k)⁻¹) *
        ENNReal.ofReal S.tailScale := by
  -- Send a pair to its label and common lattice. Both of its terms then lie in the set `terms` of
  -- this label and lattice, so each fibre has at most as many elements as the square of that set.
  let terms : S.reducedImage besselS × S.ClassBoundedDiscLattice c r → Set (S.Classes × S.G E) :=
    fun (t, L) ↦ {p | S.IsNearTermAt c t p ∧ L.val ≤ S.termLattice c p.1 p.2}
  let termPair : (Σ c' : S.Classes, S.boundedDiscNearPairs l c c') →
      (S.Classes × S.G E) × S.Classes × S.G E
    | ⟨c', (γ, γ'), _⟩ => ((c', γ), (c', γ'))
  have h_inj : Function.Injective termPair := by
    rintro ⟨c', ⟨γ, γ'⟩, h_mem⟩ ⟨c'', ⟨δ, δ'⟩, h_mem'⟩ h_eq
    obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ : (c' = c'' ∧ γ = δ) ∧ c' = c'' ∧ γ' = δ' := by
      simpa only [termPair, Prod.mk.injEq] using h_eq
    rfl
  rw [← tsum_fintype (L := .unconditional _), ← ENNReal.tsum_sigma]
  refine (tsum_le_tsum_mul_of_encard_le (x := .ofReal S.tailScale)
    (w := fun (_, L) ↦ .ofReal (discriminant r L.val ^ 𝔰.k)⁻¹)
    (fun i y ↦ termPair i ∈ terms y ×ˢ terms y) ?_ ?_).trans_eq ?_
  · -- Both terms of a pair have the label of its block, and their lattices contain the common one.
    rintro ⟨c', ⟨γ, γ'⟩, h_pair, h_link, h_disc⟩
    obtain rfl : r = finrank E (commonLink γ γ') := Nat.add_right_cancel (h_rank.trans h_link.symm)
    obtain ⟨t, ht⟩ : ∃ t : S.reducedImage besselS, S.IsLabelledPair c c' t γ γ' :=
      exists_isLabelledPair_of_isNearPairOverAgreeingBlock h_pair
    let L : S.ClassBoundedDiscLattice c (finrank E (commonLink γ γ')) :=
      ⟨S.pairLattice c c' γ γ', ht.isLatticeOfRank, ht.le_classLatticeX₀, h_disc⟩
    have h_left : (c', γ) ∈ terms (t, L) := ⟨ht.isNearTermAt_left, ht.le_termLattice_left⟩
    have h_right : (c', γ') ∈ terms (t, L) := ⟨ht.isNearTermAt_right, ht.le_termLattice_right⟩
    exact ⟨(t, L), Set.mk_mem_prod h_left h_right, rfl⟩
  · -- The number of choices for both terms is at most the square of the count over a lattice.
    rintro ⟨t, L, hL, h_le, h_disc⟩
    let termsOverL : Set (S.Classes × S.G E) := terms (t, ⟨L, hL, h_le, h_disc⟩)
    let exponent : ℕ := 2000 * 𝔰.n ^ 6 * (l + 1) * numInfPlaces E
    have h_exponent : 2 * exponent ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E :=
      two_mul_count_exponent_le 𝔰.ϱ.succ_pos hl_le
    have h_terms : termsOverL.encard ≤ ENNReal.ofReal (S.b ^ exponent) :=
      encard_setOf_isNearTermAt_and_le_termLattice_le t h_rank hL h_le h_disc
    calc ((termPair ⁻¹' (termsOverL ×ˢ termsOverL)).encard : ℝ≥0∞)
        ≤ (termsOverL ×ˢ termsOverL).encard := mod_cast Set.encard_le_encard_of_injOn
          (Set.mapsTo_preimage termPair (termsOverL ×ˢ termsOverL)) h_inj.injOn
      _ ≤ .ofReal (S.b ^ exponent) * .ofReal (S.b ^ exponent) := by
          grw [Set.encard_prod, ENat.toENNReal_mul, h_terms]
      _ = .ofReal (S.b ^ (2 * exponent)) := by
          rw [← ofReal_mul (pow_nonneg (zero_le_one.trans S.one_le_b) exponent), ← pow_add, two_mul]
      _ ≤ .ofReal S.tailScale := ofReal_le_ofReal (pow_le_tailScale h_exponent)
  · simp [ENNReal.tsum_prod', ENat.card_eq_coe_natCard]

/-- **Count.** Let `E` be a CM field with a primitive 5040th root of unity and `f` infinite places,
and let `S` be admissible filling data of shape `𝔰` over `E`, with size parameter `b = S.b` and
prime `N = S.N`. Let `n = 𝔰.n`, let `k = 𝔰.k` be the dimension of the definite space `X₀`, and let
`l ≤ n³`. For classes `c`, `c'` a near pair is two near, chosen terms over one block `(c, s, c')`
with `s` agreeing; its common lattice `L₁₂` is a lattice in `X₀` of rank the dimension of the
subspace that the terms share, and has corank `l` if this rank is `k - l`. The sum of
`(disc L₁₂) ^ (-k)` over all `c`, `c'` and all such pairs with corank `l` and discriminant at most
`S.discriminantBound = b ^ (n³ f)` is at most `tailScale ^ (l + 2) * pairCountScale`. Here
`tailScale = b ^ (k f / 4)`, and `pairCountScale` is the number of labels times the number of
classes, divided by `N ^ (k f)`. -/
theorem sum_pairDiscriminant_inv_le [S.IsAdmissible] {l : ℕ} (hl_le : l ≤ 𝔰.n ^ 3) :
    ∑ c : S.Classes, ∑ c' : S.Classes, ∑' q : S.boundedDiscNearPairs l c c',
        ENNReal.ofReal (S.pairDiscriminant c c' q.val.fst q.val.snd ^ 𝔰.k)⁻¹ ≤
      ENNReal.ofReal (S.tailScale ^ (l + 2) * S.pairCountScale) := by
  obtain h_corank_gt | h_corank_le := lt_or_ge 𝔰.k l
  · -- No lattice has corank above `k`, so the sum is empty.
    have h_empty (c c' : S.Classes) : IsEmpty (S.boundedDiscNearPairs l c c') := by
      refine ⟨fun ⟨q, h_pair, h_link, h_disc⟩ ↦ ?_⟩
      have h_le : l ≤ 𝔰.k := Nat.le_of_add_left_le h_link.le
      exact h_corank_gt.not_ge h_le
    simp only [tsum_empty, Finset.sum_const_zero, zero_le]
  obtain ⟨r, h_rank⟩ : ∃ r : ℕ, r + l = 𝔰.k := ⟨𝔰.k - l, Nat.sub_add_cancel h_corank_le⟩
  have h_tailScale_nonneg : 0 ≤ S.tailScale := Real.rpow_nonneg (zero_le_one.trans S.one_le_b) _
  let ratio : ℝ := card S.Classes / S.N ^ (𝔰.k * numInfPlaces E)
  calc _ ≤ ∑ c : S.Classes, Nat.card (S.reducedImage besselS) *
         (∑' L : S.ClassBoundedDiscLattice c r,
          ENNReal.ofReal (discriminant r L.val ^ 𝔰.k)⁻¹) * .ofReal S.tailScale :=
        Finset.sum_le_sum fun c _ ↦ sum_pairDiscriminant_inv_le_tsum hl_le h_rank
    _ ≤ Nat.card (S.reducedImage besselS) * .ofReal (ratio * S.tailScale ^ (l + 1)) *
          .ofReal S.tailScale := by
        grw [← Finset.sum_mul, ← Finset.mul_sum, sum_discriminant_inv_le h_rank]
    _ = .ofReal (S.tailScale ^ (l + 2) * S.pairCountScale) := by
        rw [← ofReal_natCast, ← ofReal_mul (by positivity), ← ofReal_mul (by positivity),
          pairCountScale]
        congr 1
        ring

end New.Filling

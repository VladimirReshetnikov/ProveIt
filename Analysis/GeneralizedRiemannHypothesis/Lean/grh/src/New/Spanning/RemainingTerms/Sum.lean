import New.Spanning.RemainingTerms.Count
import New.Spanning.RemainingTerms.Denominators
import New.Spanning.RemainingTerms.Size

/-!
# The remaining terms: a bound for their sum

Size, gain and count are combined: pairs of terms that do not lie in the same link class contribute
at most `b ^ (-k f) 𝒟_id`, and pairs in the same link class gain the norm of the places at which the
block meets.

* `New.Filling.sum_termSize_mul_le`: sets of near pairs, one for each two classes, with
  `τ ^ (l + 6) D η ^ (-k) ≤ B` contribute at most `τ B` in all. Here `l` is the corank of the common
  lattice, the gain `η` is such that `(d η)²` is at most the product of the two gauges for the
  discriminant `d` of that lattice, and `D` bounds the second moments of both cell ranks.
* `New.Filling.sum_termSize_mul_not_inSameLinkClass_le`: pairs with different links, or with equal
  links and `𝗀 = 0`, contribute at most `b ^ (-k f) 𝒟_id`.
* `New.Filling.sum_termSize_mul_inSameLinkClass_le`: pairs with equal links and `𝗀 ≠ 0` over blocks
  that meet at places of total norm at least `z` contribute at most `(b ^ (2 f) / z) ^ k 𝒟_main`.
* `New.Filling.secondMoment_remainingTerms_le`, `New.Filling.linkSecondMoment_le_of_le_meetNorm`:
  the resulting bounds for the second moment of the remaining terms.

Here `b = S.b` is the scale, `M = S.M` the congruence level, `k = 𝔰.k` and `n = 𝔰.n` are sizes of
the shape, `f` is the number of infinite places, `τ = S.tailScale = b ^ (k f / 4)` is the number
whose powers may be lost, `𝗀 = S.termDisc`, `𝒟_id = S.identitySecondMoment` and
`𝒟_main = S.mainSecondMoment`.

Notions from other files:
* `S.cellRank γ`: the cell rank of a rational element `γ`, the index of its cell.
* `S.termsOver c s c'`: the rational elements that are integral in the position given by the classes
  `c`, `c'` and have reduction `s`; the triple `(c, s, c')` is called a block.
* `S.IsNearPairOverAgreeingBlock c c' q`: both terms of `q` are near, are the chosen elements of
  their orbits, have a cell rank, and lie over one block `(c, s, c')` whose `s` agrees
  (`S.Agrees s`).
* `S.pairDiscriminant c c' γ γ'`: the discriminant of the common lattice `L₁₂` of two terms, a
  lattice in `commonLink γ γ'`; its corank is `k - finrank E (commonLink γ γ')`.
* `S.termSize c c' γ`: the bound `τ² (D_j / (n_p G ^ k)) ^ (1 / 2)` for the orbit of `γ`, with the
  second moment `D_j = S.cellRankSecondMoment j`, the gauge `G = S.levelGauge j c c' γ` and
  `n_p = S.pairCountScale`.

## Relation to the literature

The second moment of the Poincaré series expands over pairs of rational elements congruent mod `M`.
Discriminant gains, lattice counts and a weighted Schur test show that degenerate terms and pairs
with different links are negligible, and that the remaining terms shrink where frames meet mod `M`,
which isolates the main term. Discarding small cells and off-diagonal terms of Petersson-type and
relative trace formulas by congruences and counts is known in the literature. Related work:
Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023; Kowalski–Saha–Tsimerman, Local
spectral equidistribution for Siegel modular forms, 2012; Blomer, Density theorems for GL(n), 2023.
-/

open ENNReal Fin Finset Module

namespace New.Filling

/-- A term `γ` over the classes `c`, `c'` determines the reduction `s` of its block `(c, s, c')`. -/
lemma eq_of_mem_termsOver {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {c c' : S.Classes} {γ : S.G E} {s s' : S.ResidueGL}
    (h : γ ∈ S.termsOver c s c') (h' : γ ∈ S.termsOver c s' c') : s = s' := by
  obtain ⟨k : S.latticeStabilizer, rfl, hk : k.val = S.translateByClassReps c c' γ⟩ := h
  obtain ⟨k' : S.latticeStabilizer, rfl, hk' : k'.val = S.translateByClassReps c c' γ⟩ := h'
  rw [Subtype.ext (hk.trans hk'.symm)]

/-- The common lattice of a near pair (two near representative terms over one block whose `s`
agrees) has discriminant at least `1`. -/
lemma IsNearPairOverAgreeingBlock.one_le_pairDiscriminant {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] {c c' : S.Classes} {q : S.G E × S.G E}
    (hq : S.IsNearPairOverAgreeingBlock c c' q) : 1 ≤ S.pairDiscriminant c c' q.1 q.2 := by
  obtain ⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, h_agrees, h_over, h_over'⟩ := hq
  exact Filling.one_le_pairDiscriminant h_agrees h_over h_over' h_cell h_cell'

/-- For a near pair `(γ, γ')`, the square of the discriminant of the common lattice is at most
`(2 / M) ^ (2 i f)` times the product of the two gauges, where `i` is the codimension in each link
(`New.link`) of the intersection of the links, `M = S.M` is the congruence level and `f` is the
number of infinite places. -/
lemma IsNearPairOverAgreeingBlock.pairDiscriminant_sq_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E]
    {c c' : S.Classes} {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    S.pairDiscriminant c c' γ γ' ^ 2 ≤
      (2 / S.M) ^ (2 * S.linkCorank γ γ' * numInfPlaces E) *
        (S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ') := by
  obtain ⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, h_agrees, h_over, h_over'⟩ := hq
  simpa only [ite_self, Nat.cast_one, mul_one] using
    Filling.pairDiscriminant_sq_le h_agrees (one_le_meetNorm s) h_over h_over' h_cell h_cell'

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
Let `(γ, γ')` be a near pair over the classes `c`, `c'`. Its common lattice has corank at most `n³`
and discriminant at most `S.discriminantBound = b ^ (n³ f)`. -/
lemma IsNearPairOverAgreeingBlock.corank_le_and_pairDiscriminant_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {c c' : S.Classes} {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    𝔰.k - finrank E (commonLink γ γ') ≤ 𝔰.n ^ 3 ∧
    S.pairDiscriminant c c' γ γ' ≤ S.discriminantBound := by
  -- With `i` the corank of the links and `d` the discriminant, the gain and the bound for the
  -- gauges give `(M / 2) ^ (i f) * d ≤ b ^ (n³ f)`, where `d ≥ 1` and `M / 2 ≥ b ^ 18`.
  set j : Fin (𝔰.ϱ + 2) := S.cellRank γ
  set j' : Fin (𝔰.ϱ + 2) := S.cellRank γ'
  set i : ℕ := S.linkCorank γ γ'
  set d : ℝ := S.pairDiscriminant c c' γ γ'
  have h_one_le_d : 1 ≤ d := hq.one_le_pairDiscriminant
  have h_gain : d ^ 2 ≤ (2 / S.M) ^ (2 * i * numInfPlaces E) *
      (S.levelGauge j c c' γ * S.levelGauge j' c c' γ') := hq.pairDiscriminant_sq_le
  obtain ⟨⟨⟨h_near, -⟩, h_cell⟩, ⟨⟨h_near', -⟩, h_cell'⟩, s, -, h_over, h_over'⟩ := hq
  have h_corank : 𝔰.k ≤ finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) :=
    le_finrank_commonLink_add h_cell γ'
  have h_gauge_pos' : 0 < S.levelGauge j' c c' γ' := levelGauge_pos h_over' h_cell'
  have h_bound : 0 ≤ S.discriminantBound :=
    h_gauge_pos'.le.trans (h_near'.levelGauge_le h_over' h_cell')
  have hM : 2 ≤ S.M := two_le_M
  have hb₂ : 2 ≤ S.b := two_le_b
  have h_ratio : (2 / S.M : ℝ) ≤ (S.b ^ 18)⁻¹ := by
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    calc
      2 * S.b ^ 18 ≤ S.b ^ 19 := by grw [hb₂, ← pow_succ']
      _ ≤ (S.M : ℝ) := S.le_M
  have h_pow_mul_disc_le : S.b ^ (18 * i * numInfPlaces E) * d ≤ S.discriminantBound := by
    refine le_of_sq_le_sq ?_ h_bound
    calc
      _ = d ^ 2 * (S.b ^ 18) ^ (2 * i * numInfPlaces E) := by ring
      _ ≤ (S.b ^ 18)⁻¹ ^ (2 * i * numInfPlaces E) * (S.discriminantBound * S.discriminantBound) *
          (S.b ^ 18) ^ (2 * i * numInfPlaces E) := by
        grw [h_gain, h_near.levelGauge_le h_over h_cell,
          h_near'.levelGauge_le h_over' h_cell', h_ratio]
      _ = S.discriminantBound ^ 2 := by
        rw [inv_pow]
        field_simp
  refine ⟨?_,
    (le_mul_of_one_le_left (by positivity) (one_le_pow₀ S.one_le_b)).trans h_pow_mul_disc_le⟩
  have h_exp : 18 * i * numInfPlaces E ≤ 𝔰.n ^ 3 * numInfPlaces E :=
    (pow_le_pow_iff_right₀ (by linarith : 1 < S.b)).1
      ((le_mul_of_one_le_right (by positivity) h_one_le_d).trans h_pow_mul_disc_le)
  have h_codim : 18 * i ≤ 𝔰.n ^ 3 := Nat.le_of_mul_le_mul_right h_exp NeZero.one_le
  have h_rank_excess_le : j.val - 𝔰.ϱ ≤ 1 := by lia
  have h_cube : 𝔰.n ≤ 𝔰.n ^ 3 := Nat.le_self_pow three_ne_zero _
  have h_ϱ_large : 10 ^ 5 ≤ 𝔰.ϱ := S.ten_pow_five_le_varrho
  lia

/-- A near pair (two near representative terms over one block whose `s` agrees) lies in
`S.boundedDiscNearPairs l c c'`, the set of near pairs of corank `l` and bounded discriminant, for
`l` the corank of its common lattice. -/
lemma IsNearPairOverAgreeingBlock.mem_boundedDiscNearPairs {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes}
    {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) :
    (γ, γ') ∈ S.boundedDiscNearPairs (𝔰.k - finrank E (commonLink γ γ')) c c' :=
  have h_rank : finrank E (commonLink γ γ') ≤ 𝔰.k :=
    (Submodule.finrank_le _).trans (by simp)
  ⟨hq, Nat.add_sub_cancel' h_rank, hq.corank_le_and_pairDiscriminant_le.right⟩

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
Let `c`, `c'` be classes and `γ` a rational point of cell rank `j = S.cellRank γ` whose gauge
`G = S.levelGauge j c c' γ` is positive. If the constant `S.cellRankSecondMoment j` is at most `D`,
then the square of the size `S.termSize c c' γ` is at most `τ⁴ D / (n_p G ^ k)`. -/
lemma termSize_sq_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [S.IsAdmissible] {c c' : S.Classes} {γ : S.G E} {D : ℝ}
    (h_gauge_pos : 0 < S.levelGauge (S.cellRank γ) c c' γ)
    (hD : S.cellRankSecondMoment (S.cellRank γ) ≤ D) :
    S.termSize c c' γ ^ 2 ≤
      S.tailScale ^ 4 * D / (S.pairCountScale * S.levelGauge (S.cellRank γ) c c' γ ^ 𝔰.k) := by
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  have h_moment_nonneg : 0 ≤ S.cellRankSecondMoment (S.cellRank γ) :=
    cellRankSecondMoment_nonneg _
  rw [termSize, orbitBound, ← levelGauge, mul_pow, Real.sq_sqrt (by positivity)]
  grw [hD]
  exact le_of_eq (by ring)

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
Let `(γ, γ')` be a near pair over the classes `c`, `c'` and `d` the discriminant of its common
lattice `S.pairLattice`. Let `η > 0`. If `(d η)²` is at most the product of the two gauges and the
constants `S.cellRankSecondMoment` of both cell ranks are at most `D`, then the product of the sizes
`S.termSize` is at most `τ⁴ D η ^ (-k) d ^ (-k) / n_p`. -/
lemma IsNearPairOverAgreeingBlock.termSize_mul_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes}
    {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) {η D : ℝ} (hη : 0 < η)
    (h_gain : (S.pairDiscriminant c c' γ γ' * η) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ')
    (hD : S.cellRankSecondMoment (S.cellRank γ) ≤ D)
    (hD' : S.cellRankSecondMoment (S.cellRank γ') ≤ D) :
    S.termSize c c' γ * S.termSize c c' γ' ≤
      S.tailScale ^ 4 * D / η ^ 𝔰.k / S.pairCountScale *
        (S.pairDiscriminant c c' γ γ' ^ 𝔰.k)⁻¹ := by
  set d : ℝ := S.pairDiscriminant c c' γ γ'
  set G : ℝ := S.levelGauge (S.cellRank γ) c c' γ
  set G' : ℝ := S.levelGauge (S.cellRank γ') c c' γ'
  have h_one_le_d : 1 ≤ d := hq.one_le_pairDiscriminant
  obtain ⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, -, h_over, h_over'⟩ := hq
  have hD₀ : 0 ≤ D := (cellRankSecondMoment_nonneg _).trans hD
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  have hG : 0 < G := levelGauge_pos h_over h_cell
  have hG' : 0 < G' := levelGauge_pos h_over' h_cell'
  refine le_of_sq_le_sq ?_ (by positivity)
  calc
    _ = S.termSize c c' γ ^ 2 * S.termSize c c' γ' ^ 2 := mul_pow ..
    _ ≤ S.tailScale ^ 4 * D / (S.pairCountScale * G ^ 𝔰.k) *
        (S.tailScale ^ 4 * D / (S.pairCountScale * G' ^ 𝔰.k)) := by
      grw [termSize_sq_le hG hD, termSize_sq_le hG' hD']
    _ = (S.tailScale ^ 4 * D / S.pairCountScale) ^ 2 / (G * G') ^ 𝔰.k := by ring
    _ ≤ (S.tailScale ^ 4 * D / S.pairCountScale) ^ 2 / ((d * η) ^ 2) ^ 𝔰.k := by gcongr
    _ = _ := by ring

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
Let `(γ, γ')` be a near pair over the classes `c`, `c'`, whose common lattice `S.pairLattice` has
corank `l = k - finrank E (commonLink γ γ')` and discriminant `d = S.pairDiscriminant c c' γ γ'`.
Let `η > 0`. Suppose that `(d η)²` is at most the product of the two gauges, `D` bounds the
constants `S.cellRankSecondMoment` of both cell ranks, and `τ ^ (l + 6) D η ^ (-k) ≤ B`. Then the
product of the sizes `S.termSize` is at most `B d ^ (-k) / (τ ^ (l + 2) n_p)`. -/
lemma IsNearPairOverAgreeingBlock.ofReal_termSize_mul_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes}
    {γ γ' : S.G E} (hq : S.IsNearPairOverAgreeingBlock c c' (γ, γ')) {η D B : ℝ} (hη : 0 < η)
    (h_gain : (S.pairDiscriminant c c' γ γ' * η) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ')
    (hD : S.cellRankSecondMoment (S.cellRank γ) ≤ D)
    (hD' : S.cellRankSecondMoment (S.cellRank γ') ≤ D)
    (h_budget : S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 6) * D / η ^ 𝔰.k ≤ B) :
    ENNReal.ofReal (S.termSize c c' γ * S.termSize c c' γ') ≤
      .ofReal (B / (S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 2) * S.pairCountScale)) *
        .ofReal (S.pairDiscriminant c c' γ γ' ^ 𝔰.k)⁻¹ := by
  set l : ℕ := 𝔰.k - finrank E (commonLink γ γ')
  have hτ : 0 < S.tailScale := zero_lt_one.trans_le one_le_tailScale
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  have h_one_le_disc : 1 ≤ S.pairDiscriminant c c' γ γ' := hq.one_le_pairDiscriminant
  have h_const : S.tailScale ^ 4 * D / η ^ 𝔰.k / S.pairCountScale ≤
      B / (S.tailScale ^ (l + 2) * S.pairCountScale) :=
    calc
      _ = S.tailScale ^ (l + 6) * D / η ^ 𝔰.k / (S.tailScale ^ (l + 2) * S.pairCountScale) := by
        field_simp
        ring
      _ ≤ _ := by gcongr
  grw [← ofReal_mul' (by positivity), hq.termSize_mul_le hη h_gain hD hD', h_const]

/-- The number `n³ + 1` of possible coranks is at most `τ = S.tailScale`. -/
lemma cube_add_one_le_tailScale {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    [S.IsAdmissible] : ((𝔰.n ^ 3 + 1 : ℕ) : ℝ) ≤ S.tailScale := by
  have hb : 2 ≤ S.b := two_le_b
  calc
    _ = (𝔰.n : ℝ) ^ 3 + 1 := by norm_cast
    _ ≤ S.b ^ 3 + S.b ^ 3 := by grw [S.succ_le_b, one_le_pow₀ (n := 3) S.one_le_b]
    _ ≤ S.b ^ 4 := by grw [← two_mul, hb, ← pow_succ']
    _ ≤ S.tailScale := pow_le_tailScale (le_mul_of_le_of_one_le (by lia) NeZero.one_le)

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
For all classes `c`, `c'` let `P c c'` be a set of near pairs over `c`, `c'`. Suppose that for each
pair, with a common lattice of corank `l` and discriminant `d`, there are `η > 0` and `D` such that
`(d η)²` is at most the product of the two gauges, `D` bounds the constants `S.cellRankSecondMoment`
of both cell ranks, and `τ ^ (l + 6) D η ^ (-k) ≤ B`, where `τ = S.tailScale`, `k = 𝔰.k` and
`B ≥ 0`. Then the products of the sizes `S.termSize` of the two terms add up to at most `τ B`. -/
lemma sum_termSize_mul_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] (P : S.Classes → S.Classes → Set (S.G E × S.G E))
    (h_nearPair : ∀ c c' : S.Classes, ∀ q ∈ P c c', S.IsNearPairOverAgreeingBlock c c' q)
    {B : ℝ} (hB : 0 ≤ B)
    (h_gain : ∀ (c c' : S.Classes) (γ γ' : S.G E), (γ, γ') ∈ P c c' → ∃ η D : ℝ, 0 < η ∧
      (S.pairDiscriminant c c' γ γ' * η) ^ 2 ≤
        S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ' ∧
      S.cellRankSecondMoment (S.cellRank γ) ≤ D ∧
      S.cellRankSecondMoment (S.cellRank γ') ≤ D ∧
      S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 6) * D / η ^ 𝔰.k ≤ B) :
    ∑ c : S.Classes, ∑ c' : S.Classes, ∑' q : P c c', ENNReal.ofReal
        (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) ≤
      .ofReal (S.tailScale * B) := by
  -- Sort the pairs by the corank `l ≤ n³`. By the count each value of `l` contributes at most `B`.
  have hτ : 0 < S.tailScale := zero_lt_one.trans_le one_le_tailScale
  have h_pairCountScale_pos : 0 < S.pairCountScale := pairCountScale_pos
  let weight (l : ℕ) (c c' : S.Classes) (q : S.G E × S.G E) : ℝ≥0∞ :=
    .ofReal (B / (S.tailScale ^ (l + 2) * S.pairCountScale)) *
      .ofReal (S.pairDiscriminant c c' q.1 q.2 ^ 𝔰.k)⁻¹
  have h_pair (c c' : S.Classes) (q : S.G E × S.G E) (hq : q ∈ P c c') :
      ENNReal.ofReal (S.termSize c c' q.1 * S.termSize c c' q.2) ≤
        ∑ l ∈ range (𝔰.n ^ 3 + 1), (S.boundedDiscNearPairs l c c').indicator (weight l c c') q := by
    obtain ⟨η, D, hη, h_sq, hD, hD', h_budget⟩ := h_gain c c' q.1 q.2 hq
    have hq_near : S.IsNearPairOverAgreeingBlock c c' (q.1, q.2) := h_nearPair c c' q hq
    set l : ℕ := 𝔰.k - finrank E (commonLink q.1 q.2)
    have hl : l ≤ 𝔰.n ^ 3 := hq_near.corank_le_and_pairDiscriminant_le.left
    calc
      _ ≤ weight l c c' q := hq_near.ofReal_termSize_mul_le hη h_sq hD hD' h_budget
      _ = (S.boundedDiscNearPairs l c c').indicator (weight l c c') q :=
        (Set.indicator_of_mem hq_near.mem_boundedDiscNearPairs _).symm
      _ ≤ _ := single_le_sum (f := fun l ↦
        (S.boundedDiscNearPairs l c c').indicator (weight l c c') q)
        (fun _ _ ↦ zero_le) (mem_range_succ_iff.2 hl)
  have h_corank (l : ℕ) (hl : l ∈ range (𝔰.n ^ 3 + 1)) :
      ∑ c, ∑ c', ∑' q : S.boundedDiscNearPairs l c c', weight l c c' q ≤ .ofReal B := by
    simp only [weight, ENNReal.tsum_mul_left, ← mul_sum]
    calc
      _ ≤ ENNReal.ofReal (B / (S.tailScale ^ (l + 2) * S.pairCountScale)) *
          .ofReal (S.tailScale ^ (l + 2) * S.pairCountScale) := by
        grw [sum_pairDiscriminant_inv_le (mem_range_succ_iff.1 hl)]
      _ = .ofReal B := by rw [← ofReal_mul (by positivity), div_mul_cancel₀ _ (by positivity)]
  calc
    _ ≤ ∑ c, ∑ c', ∑ l ∈ range (𝔰.n ^ 3 + 1),
        ∑' q : S.boundedDiscNearPairs l c c', weight l c c' q := by
      gcongr with c _ c' _
      -- Bound each pair by its weights, then extend the sum from `P c c'` to all pairs.
      simp only [_root_.tsum_subtype]
      rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
      refine (ENNReal.tsum_le_tsum fun q : P c c' ↦ h_pair c c' q q.property).trans ?_
      exact tsum_comp_le_tsum_of_injective Subtype.val_injective fun q ↦
        ∑ l ∈ range (𝔰.n ^ 3 + 1), (S.boundedDiscNearPairs l c c').indicator (weight l c c') q
    _ = ∑ l ∈ range (𝔰.n ^ 3 + 1), ∑ c, ∑ c',
        ∑' q : S.boundedDiscNearPairs l c c', weight l c c' q := by
          simp only [sum_comm (t := range _)]
    _ ≤ ∑ _l ∈ range (𝔰.n ^ 3 + 1), .ofReal B := sum_le_sum h_corank
    _ = .ofReal ((𝔰.n ^ 3 + 1 : ℕ) * B) := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul, ofReal_mul (Nat.cast_nonneg _),
        ofReal_natCast]
    _ ≤ .ofReal (S.tailScale * B) := by grw [S.cube_add_one_le_tailScale]

/-- Two terms lie in the same link class if `𝗀 = S.termDisc` vanishes for neither and their links
(`New.link`) are equal. -/
def InSameLinkClass {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    (γ γ' : S.G E) : Prop :=
  S.termDisc γ ≠ 0 ∧ S.termDisc γ' ≠ 0 ∧ link γ = link γ'

/-- Let `S` be data of the filling theorem that satisfy the standing hypotheses `S.IsAdmissible`.
The second moment `S.cellRankSecondMoment j` of every cell rank `j` is at most `S.mainSecondMoment`,
the second moment of the top cell rank `ϱ + 1`. -/
lemma cellRankSecondMoment_le_mainSecondMoment {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [S.IsAdmissible] (j : Fin (𝔰.ϱ + 2)) :
    S.cellRankSecondMoment j ≤ S.mainSecondMoment := by
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  unfold cellRankSecondMoment
  split_ifs
  · rfl
  · calc
      S.identitySecondMoment / S.tailScale ^ 16 ≤ S.identitySecondMoment :=
        div_le_self h_id (one_le_pow₀ hτ)
      _ ≤ S.tailScale ^ 44 * S.identitySecondMoment := le_mul_of_one_le_left h_id (one_le_pow₀ hτ)
      _ ≤ S.mainSecondMoment := tailScale_pow_mul_identitySecondMoment_le

/-- Let `E` be a CM field, and let `S` be data of the filling theorem over `E` that satisfy the
standing hypotheses `S.IsAdmissible`. For `i ≥ 1` and `l ≤ i + 1` we have `τ ^ (l + 6) 𝒟_main
(M / 2) ^ (-i f k) ≤ τ ^ (-10) 𝒟_id`. This serves pairs whose links intersect in codimension `i` and
whose common lattice has corank `l`. -/
lemma pow_mul_mainSecondMoment_div_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [ok : S.IsAdmissible] {i l : ℕ} (hi : i ≠ 0) (hl : l ≤ i + 1) :
    S.tailScale ^ (l + 6) * S.mainSecondMoment / ((S.M / 2) ^ (i * numInfPlaces E)) ^ 𝔰.k ≤
      S.identitySecondMoment / S.tailScale ^ 10 := by
  -- Each unit of `i` gives the factor `x = τ (2 / M) ^ (k f) ≤ 1`; one such factor and the upper
  -- bound for `𝒟_main / 𝒟_id` give `τ ^ 7 x 𝒟_main ≤ τ ^ 8 (2 / b ^ 6) ^ (k f) 𝒟_id`.
  have hb : 2 ≤ S.b := two_le_b
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have hM : 2 ≤ S.M := two_le_M
  have h_main : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  set m : ℕ := 𝔰.k * numInfPlaces E
  set x : ℝ := S.tailScale * (2 / S.M) ^ m with hx
  have h_ratio : 2 * S.b ≤ S.M :=
    calc
      2 * S.b ≤ S.b ^ 2 := by grw [hb, ← sq]
      _ ≤ S.b ^ 19 := pow_le_pow_right₀ S.one_le_b (by norm_num)
      _ ≤ (S.M : ℝ) := S.le_M
  have hx_le : x ≤ 1 :=
    calc x ≤ S.tailScale ^ 4 * (2 / S.M) ^ m := by grw [hx, ← le_self_pow₀ hτ four_ne_zero]
      _ = (2 * S.b / S.M) ^ m := by
        rw [tailScale_pow_four]
        ring
      _ ≤ 1 := pow_le_one₀ (by positivity) (div_le_one_of_le₀ h_ratio (by positivity))
  calc
    _ ≤ S.tailScale ^ (i + 1 + 6) * S.mainSecondMoment / ((S.M / 2) ^ (i * numInfPlaces E)) ^
      𝔰.k := by
      gcongr
    _ = S.tailScale ^ 7 * x ^ i * S.mainSecondMoment := by
      rw [hx, ← inv_div 2 (S.M : ℝ), inv_pow, inv_pow, div_inv_eq_mul]
      ring
    _ ≤ S.tailScale ^ 7 * x * ((S.M / S.b ^ 6) ^ m * S.identitySecondMoment) := by
      grw [pow_le_of_le_one (by positivity) hx_le hi, ok.mainSecondMoment_le]
    _ = (S.tailScale ^ 4) ^ 2 * (2 / S.b ^ 6) ^ m * S.identitySecondMoment := by
      simp only [hx, div_pow]
      field_simp
    _ ≤ (S.tailScale ^ 4) ^ 2 * (S.b / S.b ^ 6) ^ m * S.identitySecondMoment := by gcongr
    _ = S.identitySecondMoment / (S.tailScale ^ 4) ^ 3 := by
      rw [tailScale_pow_four, div_pow]
      field_simp
      ring
    _ ≤ S.identitySecondMoment / S.tailScale ^ 10 := by
      grw [← pow_mul, pow_le_pow_right₀ hτ (by norm_num : 10 ≤ 4 * 3)]

/-- **Remaining terms, pairs that do not lie in the same link class.** Let `E` be a CM field with a
primitive root of unity of order 5040, and let `S` be data of the filling theorem over `E` that
satisfy the standing hypotheses `S.IsAdmissible`. Sum over all classes `c`, `c'` and all near pairs
over them whose links (`New.link`) differ or for one of which `𝗀 = S.termDisc` vanishes. The
products of the sizes of the two terms add up to at most `b ^ (-k f) 𝒟_id`. -/
theorem sum_termSize_mul_not_inSameLinkClass_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] :
    ∑ c : S.Classes, ∑ c' : S.Classes,
      ∑' q : {q : S.G E × S.G E |
        S.IsNearPairOverAgreeingBlock c c' q ∧ ¬S.InSameLinkClass q.1 q.2},
        ENNReal.ofReal
          (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) ≤
      .ofReal (S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E)) := by
  -- Apply `sum_termSize_mul_le` with `B = τ ^ (-10) 𝒟_id`, according to the corank of the links.
  have hM : 2 ≤ S.M := two_le_M
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have h_const : S.tailScale * (S.identitySecondMoment / S.tailScale ^ 10) ≤
      S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E) :=
    calc
      _ = S.identitySecondMoment / S.tailScale ^ 9 := by field_simp
      _ ≤ S.identitySecondMoment / S.tailScale ^ 4 := by
        grw [pow_le_pow_right₀ hτ (by norm_num : 4 ≤ 9)]
      _ = _ := by rw [tailScale_pow_four]
  have hB : 0 ≤ S.identitySecondMoment / S.tailScale ^ 10 := by positivity
  refine (sum_termSize_mul_le _ (fun c c' q hq ↦ hq.left) hB ?_).trans (ofReal_le_ofReal h_const)
  rintro c c' γ γ' ⟨hq, h_class : ¬S.InSameLinkClass γ γ'⟩
  set j : Fin (𝔰.ϱ + 2) := S.cellRank γ
  set j' : Fin (𝔰.ϱ + 2) := S.cellRank γ'
  set i : ℕ := S.linkCorank γ γ'
  have h_gain : S.pairDiscriminant c c' γ γ' ^ 2 ≤ (2 / S.M) ^ (2 * i * numInfPlaces E) *
      (S.levelGauge j c c' γ * S.levelGauge j' c c' γ') := hq.pairDiscriminant_sq_le
  obtain ⟨⟨-, h_cell : S.HasCellRank j γ⟩, ⟨-, h_cell' : S.HasCellRank j' γ'⟩, -⟩ := hq
  have h_corank : 𝔰.k ≤ finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) :=
    le_finrank_commonLink_add h_cell γ'
  rcases eq_or_ne i 0 with hi | hi
  · -- Equal links: `𝗀` vanishes for both terms, so both lie below the top cell rank, corank `0`.
    have h_link : link γ = link γ' := linkCorank_eq_zero_iff.1 hi
    have h_both : S.termDisc γ = 0 ↔ S.termDisc γ' = 0 :=
      termDisc_eq_zero_iff_of_link_eq h_cell h_cell' h_link
    have h_disc : S.termDisc γ = 0 :=
      by_contra fun h_ne ↦ h_class ⟨h_ne, mt h_both.2 h_ne, h_link⟩
    have h_low : ¬𝔰.ϱ < j := fun h_top ↦ h_cell.lt_iff_termDisc_ne_zero.1 h_top h_disc
    have h_low' : ¬𝔰.ϱ < j' := fun h_top ↦
      h_cell'.lt_iff_termDisc_ne_zero.1 h_top (h_both.1 h_disc)
    have h_full : 𝔰.k - finrank E (commonLink γ γ') = 0 := by lia
    have h_one : (S.pairDiscriminant c c' γ γ' * 1) ^ 2 ≤
        S.levelGauge j c c' γ * S.levelGauge j' c c' γ' := by simpa [hi] using h_gain
    have h_moment : S.cellRankSecondMoment j = S.identitySecondMoment / S.tailScale ^ 16 :=
      ite_eq_right h_low
    have h_moment' : S.cellRankSecondMoment j' = S.identitySecondMoment / S.tailScale ^ 16 :=
      ite_eq_right h_low'
    refine ⟨1, S.identitySecondMoment / S.tailScale ^ 16, one_pos, h_one, h_moment.le, h_moment'.le,
      le_of_eq ?_⟩
    rw [h_full, one_pow, zero_add]
    field_simp
  · -- Different links: the gain is `(M / 2) ^ (i f)`, and the corank is at most `i + 1`.
    have h_corank_le : 𝔰.k - finrank E (commonLink γ γ') ≤ i + 1 := by lia
    refine ⟨(S.M / 2) ^ (i * numInfPlaces E), S.mainSecondMoment, by positivity, ?_,
      cellRankSecondMoment_le_mainSecondMoment j, cellRankSecondMoment_le_mainSecondMoment j',
        pow_mul_mainSecondMoment_div_le hi h_corank_le⟩
    calc
      _ ≤ (2 / S.M) ^ (2 * i * numInfPlaces E) * (S.levelGauge j c c' γ * S.levelGauge j' c c' γ') *
          ((S.M / 2) ^ (i * numInfPlaces E)) ^ 2 := by grw [mul_pow, h_gain]
      _ = _ := by
        rw [← inv_div 2 (S.M : ℝ), inv_pow]
        field_simp
        ring

/-- **Remaining terms, pairs in the same link class.** Let `E` be a CM field with a primitive root
of unity of order 5040, and let `S` be data of the filling theorem over `E` that satisfy the
standing hypotheses `S.IsAdmissible`. Let `z ≠ 0`. Sum over all classes `c`, `c'` and all near pairs
over them with equal links (`New.link`), with `𝗀 = S.termDisc ≠ 0` for both terms, and whose
reduction `s` has `z ≤ S.meetNorm s`. The products of the sizes `S.termSize` of the two terms add up
to at most `(b ^ (2 f) / z) ^ k 𝒟_main`. -/
theorem sum_termSize_mul_inSameLinkClass_le {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible] {z : ℕ} (hz : z ≠ 0) :
    ∑ c : S.Classes, ∑ c' : S.Classes,
      ∑' q : {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧
        S.InSameLinkClass q.1 q.2 ∧ ∃ s : S.ResidueGL, z ≤ S.meetNorm s ∧ q.1 ∈ S.termsOver c s c'},
        ENNReal.ofReal
          (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) ≤
      .ofReal ((S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment) := by
  have hτ : 1 ≤ S.tailScale := one_le_tailScale
  have h_main : 0 ≤ S.mainSecondMoment := mainSecondMoment_nonneg
  have h_const : S.tailScale * (S.tailScale ^ 7 * S.mainSecondMoment / z ^ 𝔰.k) =
      (S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment := by
    rw [div_pow, ← pow_mul, mul_assoc, mul_comm _ 𝔰.k, pow_mul', ← tailScale_pow_four]
    ring
  rw [← h_const]
  refine sum_termSize_mul_le _ (fun c c' q hq ↦ hq.left) (by positivity) ?_
  rintro c c' γ γ' ⟨⟨⟨-, h_cell⟩, ⟨-, h_cell'⟩, s, h_agrees, h_over, h_over'⟩,
    ⟨h_disc, -, h_link⟩, s', h_meet, h_over_s'⟩
  obtain rfl : s' = s := eq_of_mem_termsOver h_over_s' h_over
  -- The links are equal and the cell rank is the top one: the gain is `z`, the corank `≤ 1`.
  have h_zero : S.linkCorank γ γ' = 0 := linkCorank_eq_zero_iff.2 h_link
  have h_top : 𝔰.ϱ < S.cellRank γ := h_cell.lt_iff_termDisc_ne_zero.2 h_disc
  have h_gain : (S.pairDiscriminant c c' γ γ' * z) ^ 2 ≤
      S.levelGauge (S.cellRank γ) c c' γ * S.levelGauge (S.cellRank γ') c c' γ' := by
    simpa [h_zero, h_top] using
      pairDiscriminant_sq_le h_agrees h_meet h_over h_over' h_cell h_cell'
  have h_corank : 𝔰.k - finrank E (commonLink γ γ') ≤ 1 := by
    have h_rank : 𝔰.k ≤ finrank E (commonLink γ γ') + S.linkCorank γ γ' +
        (S.cellRank γ - 𝔰.ϱ) := le_finrank_commonLink_add h_cell γ'
    lia
  have h_pow : S.tailScale ^ (𝔰.k - finrank E (commonLink γ γ') + 6) * S.mainSecondMoment /
      (z : ℝ) ^ 𝔰.k ≤ S.tailScale ^ 7 * S.mainSecondMoment / (z : ℝ) ^ 𝔰.k := by
    gcongr
    lia
  exact ⟨z, S.mainSecondMoment, by positivity, h_gain, cellRankSecondMoment_le_mainSecondMoment _,
    cellRankSecondMoment_le_mainSecondMoment _, h_pow⟩

/-- The pieces into which a block is split: one for each link, and one for `𝗀 = 0`. -/
abbrev Piece (E : Type) [Field E] (𝔰 : Shape) : Type :=
  Option (Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E))

open scoped Classical in
/-- The piece of a term `γ`: its link if `𝗀(γ) = S.termDisc γ ≠ 0`; the terms with `𝗀 = 0` form one
further piece. -/
noncomputable def piece {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
    (γ : S.G E) : Piece E 𝔰 :=
  if S.termDisc γ = 0 then none else some (link γ)

/-- The piece of `γ` is the submodule `Λ` if and only if `𝗀(γ) = S.termDisc γ` is not zero and the
link of `γ` is `Λ`. -/
lemma piece_eq_some_iff {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {γ : S.G E} {Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)} :
    S.piece γ = some Λ ↔ S.termDisc γ ≠ 0 ∧ link γ = Λ := by
  by_cases h_disc : S.termDisc γ = 0 <;> simp [piece, h_disc]

/-- The part `T ∩ S.piece ⁻¹' {κ}` of a stable set `T` in one piece `κ` is stable. A stable set is
one invariant on both sides under the rational points of the Bessel unipotent group. This holds
because `S.termDisc` and the link are invariant. -/
lemma IsStable.inter_piece {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    {T : Set (S.G E)} (hT : S.IsStable T) (κ : Piece E 𝔰) :
    S.IsStable (T ∩ S.piece ⁻¹' {κ}) := by
  classical
  intro u hu u' hu' γ
  have h_piece : S.piece (u⁻¹ * γ * u') = S.piece γ := by
    simp [piece, frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu hu',
      link_inv_mul_mul_of_mem_besselU hu hu']
  simp [hT u hu u' hu' γ, h_piece]

/-- A near representative of `T` over a block `(c, s, c')` (a chosen near term, that has a cell
rank, where `s` agrees) belongs to `T`. -/
lemma mem_of_mem_nearRepresentativesOver {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} {c c' : S.Classes} {T : Set (S.G E)} {s : S.ResidueGL}
    {p : S.G E} (hp : p ∈ S.nearRepresentativesOver T c s c') : p ∈ T :=
  hp.left.left

/-- A near representative of `T` over the block `(c, s, c')` is a term over this block. -/
lemma mem_termsOver_of_mem_nearRepresentativesOver {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} {c c' : S.Classes} {T : Set (S.G E)}
    {s : S.ResidueGL} {p : S.G E} (hp : p ∈ S.nearRepresentativesOver T c s c') :
    p ∈ S.termsOver c s c' :=
  hp.left.right

/-- Two near representatives over the same block `(c, s, c')` form a near pair over an agreeing
block, that is, two near representatives over one block whose reduction `s` agrees. -/
lemma isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} {c c' : S.Classes}
    {T T' : Set (S.G E)} {s : S.ResidueGL} {p p' : S.G E}
    (hp : p ∈ S.nearRepresentativesOver T c s c')
    (hp' : p' ∈ S.nearRepresentativesOver T' c s c') :
    S.IsNearPairOverAgreeingBlock c c' (p, p') := by
  obtain ⟨⟨-, h_over⟩, h_agrees, h_near⟩ := hp
  obtain ⟨⟨-, h_over'⟩, -, h_near'⟩ := hp'
  exact ⟨h_near, h_near', s, h_agrees, h_over, h_over'⟩

/-- Let `E` be a CM field with a primitive root of unity of order 5040, and let `S` be data of the
filling theorem over `E` that satisfy the standing hypotheses `S.IsAdmissible`. Let `T`, `T'` be
subsets of `Γ* = S.remainingTerms` that are stable, that is, invariant on both sides under the
rational points of the Bessel unipotent group. The product of the norms of the sums of the
amplitudes of their terms over `(c, s, c')` is at most the sum, over a near representative of `T`
and one of `T'`, of the square of the covolume `S.unipotentCovolume` times the product of the two
sizes.

A rational point `γ` lies over `(c, s, c')` if `h_c⁻¹ γ h_c'` (`h_c = S.classRep c`) is integral
with reduction `s`. Its amplitude is the integral over the archimedean points `y` of
`β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^*`, where `β_c = S.classCutoff c` and `W` is the cut Bessel
function, the Bessel function times a cutoff in the length `besselLength` at each infinite place. A
near representative of `T` over `(c, s, c')` is a `γ ∈ T` over `(c, s, c')` that is near (some
archimedean point `y` and `γ⁻¹ y` are both reduced and of bounded size, `S.boxedPoints`), is the
chosen element of its double coset under the groups `S.classUnipotent₀` and has a cell rank; there
are none unless `S.Agrees s`. The size `S.termSize c c' γ` is `τ² (D_j / (n_p G ^ k)) ^ (1 / 2)`,
where `j = S.cellRank γ` is the index of the cell of `γ`, `D_j = S.cellRankSecondMoment j`,
`G = S.levelGauge j c c' γ` is its gauge, `n_p = S.pairCountScale` and `τ = S.tailScale`. -/
lemma enorm_amplitudeSum_mul_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes} {T T' : Set (S.G E)}
    (hT : S.IsStable T) (hT' : S.IsStable T')
    (h_sub : T ⊆ S.remainingTerms) (h_sub' : T' ⊆ S.remainingTerms) {s : S.ResidueGL} :
    ‖S.amplitudeSum .cut T c s c'‖ₑ * ‖S.amplitudeSum .cut T' c s c'‖ₑ ≤
      ∑' q : S.nearRepresentativesOver T c s c' × S.nearRepresentativesOver T' c s c',
        .ofReal (S.unipotentCovolume ^ 2) *
        .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2) := by
  grw [enorm_amplitudeSum_le_tsum_termSize hT h_sub,
    enorm_amplitudeSum_le_tsum_termSize hT' h_sub']
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_prod]
  refine ENNReal.tsum_le_tsum fun ⟨p, p'⟩ ↦ le_of_eq ?_
  have h_size : 0 ≤ S.termSize c c' p := by
    unfold termSize orbitBound
    positivity
  simp only [ofReal_mul S.unipotentCovolume_pos.le, ofReal_pow S.unipotentCovolume_pos.le,
    ofReal_mul h_size]
  ring

/-- Let `E` be a CM field with a primitive root of unity of order 5040, and let `S` be data of the
filling theorem over `E` that satisfy the standing hypotheses `S.IsAdmissible`. Let
`T ⊆ Γ* = S.remainingTerms` be stable (invariant on both sides under the rational points of the
Bessel unipotent group). The squared norm of the sum of the amplitudes of the terms of `T` over
`(c, s, c')` is at most the sum over submodules `Λ` of the same squared norms for the terms of `T`
with `𝗀 = S.termDisc ≠ 0` and link `Λ`, plus `S.unipotentCovolume ^ 2` times the sum of the products
of the sizes over the pairs of near representatives of `T` whose links differ or for one of which
`𝗀` vanishes.

The link `link γ` is the module of pairs (class of `t`, class of `γ⁻¹ t`) in `X^⊥/X`,
`X = ⟨e₁, …, e_ϱ⟩`, `t ⊥ X, γ X`. A rational point `γ` lies over `(c, s, c')` if `h_c⁻¹ γ h_c'`
(`h_c = S.classRep c`) is integral with reduction `s`. Its amplitude is the integral over the
archimedean points `y` of `β_c(y) β_c'(γ⁻¹ y) W(y) ⊗ W(γ⁻¹ y)^*`, where `β_c = S.classCutoff c` and
`W` is the cut Bessel function, the Bessel function times a cutoff in the length `besselLength` at
each infinite place. A near representative of `T` over `(c, s, c')` is a `γ ∈ T` over `(c, s, c')`
that is near (some archimedean point `y` and `γ⁻¹ y` are both reduced and of bounded size,
`S.boxedPoints`), is the chosen element of its double coset under the groups `S.classUnipotent₀` and
has a cell rank; there are none unless `S.Agrees s`. The size `S.termSize c c' γ` is
`τ² (D_j / (n_p G ^ k)) ^ (1 / 2)`, where `j = S.cellRank γ` is the index of the cell of `γ`,
`D_j = S.cellRankSecondMoment j`, `G = S.levelGauge j c c' γ` is its gauge, `n_p = S.pairCountScale`
and `τ = S.tailScale`. -/
lemma enorm_amplitudeSum_sq_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] {c c' : S.Classes} {T : Set (S.G E)}
    (hT : S.IsStable T) (h_sub : T ⊆ S.remainingTerms) (s : S.ResidueGL) :
    ‖S.amplitudeSum .cut T c s c'‖ₑ ^ 2 ≤
      ∑' Λ : Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E),
        ‖S.amplitudeSum .cut (T ∩ {γ : S.G E | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}) c s c'‖ₑ ^ 2 +
      .ofReal (S.unipotentCovolume ^ 2) *
        ∑' q : {q ∈ S.nearRepresentativesOver T c s c' ×ˢ S.nearRepresentativesOver T c s c' |
            ¬S.InSameLinkClass q.1 q.2},
          .ofReal
            (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) := by
  -- Expand the square into pairs of pieces. The squares of the pieces with `𝗀 ≠ 0` stay; every
  -- other product is bounded by the sizes of pairs of near representatives that do not lie in the
  -- same link class.
  let part (κ : Piece E 𝔰) : ℝ≥0∞ := ‖S.amplitudeSum .cut (T ∩ S.piece ⁻¹' {κ}) c s c'‖ₑ
  let product (p : Piece E 𝔰 × Piece E 𝔰) : ℝ≥0∞ := part p.1 * part p.2
  let diagonal : Set (Piece E 𝔰 × Piece E 𝔰) := Set.range fun Λ ↦ (some Λ, some Λ)
  have h_diagonal : ∑' p : diagonal, product p =
      ∑' Λ, ‖S.amplitudeSum .cut (T ∩ {γ | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}) c s c'‖ₑ ^ 2 := by
    refine (tsum_range product fun Λ Λ' h ↦ by simpa using h).trans (tsum_congr fun Λ ↦ ?_)
    have h_set : T ∩ S.piece ⁻¹' {some Λ} = T ∩ {γ | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ} :=
      Set.ext fun γ ↦ by simp [piece_eq_some_iff, and_assoc]
    simp only [product, part, h_set, sq]
  let nearRepsOfPiece (κ : Piece E 𝔰) : Set (S.G E) :=
    S.nearRepresentativesOver (T ∩ S.piece ⁻¹' {κ}) c s c'
  let apart : Set (S.G E × S.G E) :=
    {q ∈ S.nearRepresentativesOver T c s c' ×ˢ S.nearRepresentativesOver T c s c' |
      ¬S.InSameLinkClass q.1 q.2}
  have h_nearReps_subset {κ : Piece E 𝔰} :
      nearRepsOfPiece κ ⊆ S.nearRepresentativesOver T c s c' :=
    fun q ⟨⟨⟨hγ, _⟩, h_over⟩, h_rest⟩ ↦ ⟨⟨hγ, h_over⟩, h_rest⟩
  have h_piece {κ : Piece E 𝔰} {q : S.G E} (hq : q ∈ nearRepsOfPiece κ) : S.piece q = κ :=
    (mem_of_mem_nearRepresentativesOver hq).right
  have h_mem (p : ↥diagonalᶜ) (q : nearRepsOfPiece p.val.1) (q' : nearRepsOfPiece p.val.2) :
      (q.val, q'.val) ∈ apart := by
    refine ⟨⟨h_nearReps_subset q.prop, h_nearReps_subset q'.prop⟩,
      fun ⟨h_disc, h_disc', h_link⟩ ↦ p.prop ?_⟩
    exact ⟨link q.val, by simp [Prod.ext_iff, ← h_piece q.prop, ← h_piece q'.prop, piece,
      h_disc, h_disc', h_link]⟩
  have h_others : ∑' p : ↥diagonalᶜ, product p ≤
      .ofReal (S.unipotentCovolume ^ 2) * ∑' q : apart, .ofReal
        (S.termSize c c' (q : S.G E × S.G E).1 * S.termSize c c' (q : S.G E × S.G E).2) := by
    -- One sum over a pair of pieces and a near representative of each; the terms determine the
    -- pieces.
    let pair (x : Σ p : ↥diagonalᶜ, nearRepsOfPiece p.val.1 × nearRepsOfPiece p.val.2) : apart :=
      ⟨(x.2.1, x.2.2), h_mem x.1 x.2.1 x.2.2⟩
    have h_injective : pair.Injective := by
      rintro ⟨⟨⟨κ₁, κ₁'⟩, _⟩, ⟨q, hq₁⟩, q', hq₁'⟩ ⟨⟨⟨κ₂, κ₂'⟩, _⟩, ⟨_, hq₂⟩, _, hq₂'⟩ ⟨⟩
      obtain rfl : κ₁ = κ₂ := (h_piece hq₁).symm.trans (h_piece hq₂)
      obtain rfl : κ₁' = κ₂' := (h_piece hq₁').symm.trans (h_piece hq₂')
      rfl
    let size (q : S.G E × S.G E) : ℝ≥0∞ :=
      .ofReal (S.unipotentCovolume ^ 2) * .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2)
    calc
      _ ≤ ∑' (p : ↥diagonalᶜ) (q : nearRepsOfPiece p.val.1 × nearRepsOfPiece p.val.2),
          size (q.1, q.2) :=
        ENNReal.tsum_le_tsum fun p ↦
          enorm_amplitudeSum_mul_le (hT.inter_piece p.val.1) (hT.inter_piece p.val.2)
            (Set.inter_subset_left.trans h_sub) (Set.inter_subset_left.trans h_sub)
      _ = ∑' x, size (pair x) := (ENNReal.tsum_sigma' fun x ↦ size (pair x)).symm
      _ ≤ ∑' q : apart, size q := tsum_comp_le_tsum_of_injective h_injective fun q ↦ size q
      _ = _ := ENNReal.tsum_mul_left
  calc
    _ ≤ (∑' κ, part κ) ^ 2 := by grw [enorm_amplitudeSum_le_tsum_fibre S.piece]
    _ = ∑' p : Piece E 𝔰 × Piece E 𝔰, product p := by
      simp_rw [product, sq, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_prod]
    _ = ∑' p : diagonal, product p + ∑' p : ↥diagonalᶜ, product p :=
      (ENNReal.summable.tsum_add_tsum_compl (s := diagonal) ENNReal.summable).symm
    _ ≤ _ := add_le_add h_diagonal.le h_others

/-- **Remaining terms, reduction to one link.** Let `E` be a CM field with a primitive root of unity
of order 5040, and let `S` be data of the filling theorem over `E` that satisfy the standing
hypotheses `S.IsAdmissible`. Let `Ω` be a set of reductions, `w ≥ 0` and `ν = S.unipotentCovolume`.
Suppose that the terms with `𝗀 = S.termDisc ≠ 0`, taken link by link, have sum of squared norms of
amplitude sums (`linkSecondMoment`) at most `w ν²` over `Ω`. Then the second moment over `Ω` of
`Γ* = S.remainingTerms`, for the cut Bessel function, is at most `w + b ^ (-k f) 𝒟_id`. -/
theorem secondMoment_remainingTerms_le {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] {w : ℝ} {Ω : Set S.ResidueGL} (hw : 0 ≤ w)
    (h_linkMoment : linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0} Ω ≤
      ENNReal.ofReal (w * S.unipotentCovolume ^ 2)) :
    secondMoment (S.amplitudeSum .cut S.remainingTerms) Ω ≤
      w + S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E) := by
  -- Bound each block by `enorm_amplitudeSum_sq_le`, and sum over the pairs that do not satisfy
  -- `InSameLinkClass` by `sum_termSize_mul_not_inSameLinkClass_le`.
  classical
  set T : Set (S.G E) := S.remainingTerms with hT
  have h_inter : T ∩ {γ | S.termDisc γ ≠ 0} = {γ | S.termDisc γ ≠ 0} :=
    Set.inter_eq_right.2 fun γ hγ ↦ .inl hγ
  rw [← h_inter] at h_linkMoment
  have h_id : 0 ≤ S.identitySecondMoment := identitySecondMoment_nonneg
  have hν : 0 < S.unipotentCovolume := S.unipotentCovolume_pos
  have hb_pos : 0 < S.b := b_pos
  let size (c c' : S.Classes) (q : S.G E × S.G E) : ℝ≥0∞ :=
    .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2)
  let apartOver (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) : Set (S.G E × S.G E) :=
    {q ∈ S.nearRepresentativesOver T c s c' ×ˢ S.nearRepresentativesOver T c s c' |
      ¬S.InSameLinkClass q.1 q.2}
  let apart (c c' : S.Classes) : Set (S.G E × S.G E) :=
    {q | S.IsNearPairOverAgreeingBlock c c' q ∧ ¬S.InSameLinkClass q.1 q.2}
  have h_mem {c c' : S.Classes} {s : S.ResidueGL} : apartOver c s c' ⊆ apart c c' :=
    fun q ⟨⟨hq, hq'⟩, h_class⟩ ↦ ⟨isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver hq hq',
      h_class⟩
  -- A pair of terms determines its `s`.
  have h_blocks (c c' : S.Classes) :
      ∑' s : Ω, ∑' q : apartOver c s c', size c c' q ≤ ∑' q : apart c c', size c c' q := by
    let pair (x : Σ s : Ω, apartOver c s c') : apart c c' := ⟨x.2, h_mem x.2.prop⟩
    have h_injective : pair.Injective := by
      rintro ⟨⟨s, _⟩, q, ⟨hq, _⟩, _⟩ ⟨⟨s', _⟩, q', ⟨hq', _⟩, _⟩ ⟨⟩
      obtain rfl : s = s' := eq_of_mem_termsOver (mem_termsOver_of_mem_nearRepresentativesOver hq)
        (mem_termsOver_of_mem_nearRepresentativesOver hq')
      rfl
    exact (ENNReal.tsum_sigma' fun x ↦ size c c' (pair x)).symm.trans_le
      (tsum_comp_le_tsum_of_injective h_injective fun q ↦ size c c' q)
  have h_block (c c' : S.Classes) (s : Ω) : ‖S.amplitudeSum .cut T c s c'‖ₑ ^ 2 ≤
      ∑' Λ, ‖S.amplitudeSum .cut (T ∩ {γ | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}) c s c'‖ₑ ^ 2 +
        .ofReal (S.unipotentCovolume ^ 2) * ∑' q : apartOver c s c', size c c' q :=
    enorm_amplitudeSum_sq_le isStable_remainingTerms hT.subset s
  suffices ENNReal.ofReal (∑ c, ∑ c', ∑ s with s ∈ Ω, ‖S.amplitudeSum .cut T c s c'‖ ^ 2) ≤
      .ofReal ((w + S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E)) * S.unipotentCovolume ^
        2) by
    simp_rw [secondMoment, ← Finset.sum_div]
    rwa [div_le_iff₀ (by positivity), ← ofReal_le_ofReal_iff (by positivity)]
  calc
    _ = ∑ c, ∑ c', ∑' s : Ω, ‖S.amplitudeSum .cut T c s c'‖ₑ ^ 2 := by
      simp (disch := (intros; positivity)) [← sum_subtype_eq_sum_filter, ofReal_sum_of_nonneg]
    _ ≤ linkSecondMoment (T ∩ {γ | S.termDisc γ ≠ 0}) Ω + .ofReal (S.unipotentCovolume ^ 2) *
        ∑ c, ∑ c', ∑' s : Ω, ∑' q : apartOver c s c', size c c' q := by
      grw [h_block]
      simp [linkSecondMoment, sum_add_distrib, mul_sum]
    _ ≤ .ofReal (w * S.unipotentCovolume ^ 2) + .ofReal (S.unipotentCovolume ^ 2) *
        .ofReal (S.identitySecondMoment / S.b ^ (𝔰.k * numInfPlaces E)) := by
      grw [h_blocks, h_linkMoment]
      gcongr
      exact sum_termSize_mul_not_inSameLinkClass_le
    _ = _ := by
      rw [add_mul, ofReal_add (by positivity) (by positivity),
        mul_comm (S.identitySecondMoment / _), ofReal_mul (sq_nonneg S.unipotentCovolume)]

/-- **Remaining terms, one link at a time.** Let `E` be a CM field with a primitive root of unity of
order 5040, and let `S` be data of the filling theorem over `E` that satisfy the standing hypotheses
`S.IsAdmissible`. Let `Ω` be a set of reductions, that is, of elements of `S.ResidueGL`, the product
of the general linear groups over the residue fields at the chosen places above the level `M = S.M`.
A reduction `s` meets at a place above `M` if, modulo that place, the span of the frame and its
image under `s` share a nonzero vector; `S.meetNorm s` is the norm of the product of the places at
which `s` meets. Let `z ≠ 0` be a natural number with `z ≤ S.meetNorm s` for every `s ∈ Ω`.

Let `T` be the set of rational points `γ` of the unitary group with `S.termDisc γ ≠ 0`. For classes
`c`, `c'`, a reduction `s` and a submodule `Λ`, take the sum of the amplitudes of the `γ ∈ T` that
lie over `(c, s, c')` and have link `Λ`. The squared norms of these sums, added over all `c`, `c'`,
`s ∈ Ω` and `Λ`, give `linkSecondMoment T Ω`, and this is at most `(b ^ (2 f) / z) ^ k 𝒟_main ν²`.
Here `b = S.b` is the size parameter, `k = 𝔰.k` is the dimension of the definite space, `f` is the
number of infinite places of `E`, and `𝒟_main = S.mainSecondMoment` and the covolume
`ν = S.unipotentCovolume` are real constants attached to `S`. -/
theorem linkSecondMoment_le_of_le_meetNorm {E : Type} [Field E] [CMType E]
    {𝔰 : Shape} {S : Filling E 𝔰} [HasPrimitiveRoot5040 E] [S.IsAdmissible]
    {Ω : Set S.ResidueGL} {z : ℕ} (hz : z ≠ 0)
    (h_meet : ∀ s ∈ Ω, z ≤ S.meetNorm s) :
    linkSecondMoment {γ : S.G E | S.termDisc γ ≠ 0} Ω ≤
      ENNReal.ofReal ((S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment *
        S.unipotentCovolume ^ 2) := by
  -- The square of the block of one link is bounded by pairs of near representatives in the same
  -- link class.
  let Link : Type := Submodule E (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E)
  let terms (Λ : Link) : Set (S.G E) := {γ : S.G E | S.termDisc γ ≠ 0} ∩ link ⁻¹' {Λ}
  have h_stable (Λ : Link) : S.IsStable (terms Λ) := by
    intro u hu u' hu' γ
    simp [terms, frameDisc_frameGram_inv_mul_mul_of_mem_besselU hu hu',
      link_inv_mul_mul_of_mem_besselU hu hu']
  have h_sub (Λ : Link) : terms Λ ⊆ S.remainingTerms := fun γ ⟨h_disc, _⟩ ↦ .inl h_disc
  let nearRepsInLink (c c' : S.Classes) (p : Ω × Link) : Set (S.G E) :=
    S.nearRepresentativesOver (terms p.2) c p.1 c'
  let sameLinkPairs (c c' : S.Classes) : Set (S.G E × S.G E) :=
    {q : S.G E × S.G E | S.IsNearPairOverAgreeingBlock c c' q ∧ S.InSameLinkClass q.1 q.2 ∧
      ∃ s : S.ResidueGL, z ≤ S.meetNorm s ∧ q.1 ∈ S.termsOver c s c'}
  let size (c c' : S.Classes) (q : S.G E × S.G E) : ℝ≥0∞ :=
    .ofReal (S.termSize c c' q.1 * S.termSize c c' q.2)
  have h_mem {c c' : S.Classes} (p : Ω × Link) (q q' : nearRepsInLink c c' p) :
      (q.val, q'.val) ∈ sameLinkPairs c c' := by
    obtain ⟨⟨s, hs⟩, Λ⟩ := p
    obtain ⟨γ, hγ⟩ := q
    obtain ⟨γ', hγ'⟩ := q'
    obtain ⟨h_disc : S.termDisc γ ≠ 0, h_link : link γ = Λ⟩ := mem_of_mem_nearRepresentativesOver hγ
    obtain ⟨h_disc' : S.termDisc γ' ≠ 0, h_link' : link γ' = Λ⟩ :=
      mem_of_mem_nearRepresentativesOver hγ'
    have h_pair : S.IsNearPairOverAgreeingBlock c c' (γ, γ') :=
      isNearPairOverAgreeingBlock_of_mem_nearRepresentativesOver hγ hγ'
    have h_class : S.InSameLinkClass γ γ' := ⟨h_disc, h_disc', h_link.trans h_link'.symm⟩
    exact ⟨h_pair, h_class, s, h_meet s hs, mem_termsOver_of_mem_nearRepresentativesOver hγ⟩
  have h_blocks (c c' : S.Classes) :
      ∑' (s : Ω) (Λ : Link), ‖S.amplitudeSum .cut (terms Λ) c s c'‖ₑ ^ 2 ≤
        .ofReal (S.unipotentCovolume ^ 2) * ∑' q : sameLinkPairs c c', size c c' q := by
    -- A pair of terms determines its `s` and its link.
    let pair (x : Σ p : Ω × Link, nearRepsInLink c c' p × nearRepsInLink c c' p) :
        sameLinkPairs c c' :=
      ⟨(x.2.1, x.2.2), h_mem x.1 x.2.1 x.2.2⟩
    have h_injective : pair.Injective := by
      rintro ⟨⟨⟨s, _⟩, Λ⟩, ⟨q, hq⟩, q', _⟩ ⟨⟨⟨s', _⟩, Λ'⟩, ⟨_, hq'⟩, _, _⟩ ⟨⟩
      obtain rfl : s = s' := eq_of_mem_termsOver (mem_termsOver_of_mem_nearRepresentativesOver hq)
        (mem_termsOver_of_mem_nearRepresentativesOver hq')
      obtain ⟨-, h_link : link q = Λ⟩ := mem_of_mem_nearRepresentativesOver hq
      obtain ⟨-, h_link' : link q = Λ'⟩ := mem_of_mem_nearRepresentativesOver hq'
      obtain rfl : Λ = Λ' := h_link.symm.trans h_link'
      rfl
    calc
      _ = ∑' p : Ω × Link, ‖S.amplitudeSum .cut (terms p.2) c p.1 c'‖ₑ ^ 2 :=
        ENNReal.tsum_prod.symm
      _ ≤ ∑' (p : Ω × Link) (q : nearRepsInLink c c' p × nearRepsInLink c c' p),
          .ofReal (S.unipotentCovolume ^ 2) * size c c' (q.1, q.2) :=
        ENNReal.tsum_le_tsum fun p ↦ (sq _).trans_le
          (enorm_amplitudeSum_mul_le (h_stable p.2) (h_stable p.2) (h_sub p.2) (h_sub p.2))
      _ = ∑' x, .ofReal (S.unipotentCovolume ^ 2) * size c c' (pair x) :=
        (ENNReal.tsum_sigma' fun x ↦ .ofReal (S.unipotentCovolume ^ 2) * size c c' (pair x)).symm
      _ ≤ ∑' q : sameLinkPairs c c', .ofReal (S.unipotentCovolume ^ 2) * size c c' q :=
        tsum_comp_le_tsum_of_injective h_injective fun q ↦
          .ofReal (S.unipotentCovolume ^ 2) * size c c' q
      _ = _ := ENNReal.tsum_mul_left
  calc
    _ = ∑ c : S.Classes, ∑ c' : S.Classes,
        ∑' (s : Ω) (Λ : Link), ‖S.amplitudeSum .cut (terms Λ) c s c'‖ₑ ^ 2 := by
      simp only [linkSecondMoment, tsum_fintype (β := S.Classes), terms, Link]
    _ ≤ .ofReal (S.unipotentCovolume ^ 2) *
        ∑ c : S.Classes, ∑ c' : S.Classes, ∑' q : sameLinkPairs c c', size c c' q := by
      grw [h_blocks]
      simp only [mul_sum, le_refl]
    _ ≤ .ofReal (S.unipotentCovolume ^ 2) *
        .ofReal ((S.b ^ (2 * numInfPlaces E) / z) ^ 𝔰.k * S.mainSecondMoment) := by
      gcongr
      exact sum_termSize_mul_inSameLinkClass_le hz
    _ = _ := by rw [mul_comm _ (S.unipotentCovolume ^ 2), ofReal_mul (sq_nonneg _)]

end New.Filling

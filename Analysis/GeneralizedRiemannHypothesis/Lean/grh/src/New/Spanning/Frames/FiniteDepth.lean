import New.Spanning.Frames.BesselVector
import New.Spanning.Frames.OneFrame

/-!
# Depth, heads and far positions at the finite places

This file proves the facts about a large lattice datum at the finite places that bound the local
Bessel kernels: the sets 𝔡_a are fractional ideals, the heads of a nonvanishing form have integral
leading products, and a position far from the identity forces a small ideal. Here `R = integers` is
the ring of integers of `A`, K is the group of integral points of the unitary group (in statements,
`K : ℕ` is an exponent), K(g) is its principal congruence subgroup of level `g = F.levelUnit`, and
`n = 𝔰.n = ϱ + 1`. In the gauge `Γ` of scale `α` an element `a` has size `i` if `α ^ i * a ∈ R`, and
losses are powers of `Γ.loss = 2 / modulus α`.

## Main definitions and results

* `New.Floors.IntegralPlace.IsLargeLatticeData.exists_ideal_depth_eq`: at a near point the products
  with the stable vectors form an ideal of `R`, and the depth is its index.
* `New.Floors.IntegralPlace.IsLargeLatticeData.prod_mem_of_formMajorant_ne_zero`: the forms vanish
  unless the leading products of both heads are integral.
* `New.Floors.IntegralPlace.IsLargeLatticeData.exists_gauge_of_formMajorant_ne_zero`: a scale
  adapted to two heads.
* `New.Floors.IntegralPlace.IsLargeLatticeData.exists_volume_stableProducts_le`: a large denominator
  of `(x - 1) / g` forces a deep vector.

Notions from other files:
* `New.Floors.IntegralPlace.IsLargeLatticeData`: the place data is given by a lattice, in a
  unimodular unitary group of large rank; its box `F.boxSet` is K.
* `New.Floors.PlaceData.stableProducts`: the set 𝔡_a of the products of e_a with the vectors that
  are stable at two points `x` and `x * y`.
* `New.Floors.PlaceData.IsNear`: `x` is near at `j` if a translate of `x` by
  `T.partialUnitriangularGroup j` lies in the box.
* `New.Floors.PlaceData.IntermediateGroup.besselVector`: for a group `Z` with K(g) ≤ Z ≤ K, the
  vector whose coordinate at the coset K(g) z is `extendedBesselChar F.levelUnit (y * z⁻¹)`.
* `New.Floors.PlaceData.formMajorant`: an integral of moduli of orbital integrals that bounds the
  form of two heads.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Fintype FloorGroups InnerProductSpace Subgroup
  IntegralPlace Place Set PlaceData Size SemilocalField QuotientGroup Finset

variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] [P : IntegralPlace A]
  [Fintype ι] [DecidableEq ι] {m : ℕ} {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]

variable {F : PlaceData ι T (m + 1)} {x y : T.G} (Z : F.IntermediateGroup)

namespace IntegralPlace.IsLargeLatticeData

variable [h : IsLargeLatticeData F]

/-- Let `F` be a large lattice datum, `R = integers` the ring of integers of `A` and `P.intUnits`
its set of units. The hypothesis `hB` has two parts: `B` is at least `2`, and the non-units of `R`
have volume at most `B⁻¹`. Then the group `K = unitaryLevel integers 1 T.splitGram` of integral
points of the unitary group has measure at least `2⁻¹ ^ 𝔰.n` for the measure `F.groupMeasure`. -/
theorem inv_two_pow_le_groupMeasure {B : ℝ≥0∞}
    (hB : 2 ≤ B ∧ volume ((P.integers : Set A) \ P.intUnits) ≤ B⁻¹) :
    2⁻¹ ^ 𝔰.n ≤ F.groupMeasure (unitaryLevel integers 1 T.splitGram) := by
  -- The non-units of `R` have volume at most `B⁻¹ ≤ 2⁻¹` and `R` has volume `1`.
  obtain ⟨hB_two, hB_volume⟩ := hB
  have h_units : 2⁻¹ ≤ volume P.intUnits :=
    calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := one_sub_inv_two.symm
      _ ≤ volume (P.integers : Set A) - volume (P.integers \ P.intUnits) := by
        rw [SemilocalField.volume_O]
        gcongr
        exact hB_volume.trans (ENNReal.inv_le_inv.2 hB_two)
      _ ≤ volume (P.integers \ (P.integers \ P.intUnits)) := le_measure_sdiff
      _ ≤ volume P.intUnits := measure_mono sdiff_sdiff_le
  -- The integral group is the box, of measure at least `volume P.intUnits ^ 𝔰.n`.
  grw [h_units, ← h.box_eq]
  exact h.le_partialGroupMeasure_boxSet 𝔰.ϱ 0 (zero_add _)

/-- For a large lattice datum, the set 𝔡_a = `F.stableProducts a x y` (the coordinates at the dual
of e_a of the vectors that are stable, `F.IsStable a`, at the points x and x y) is c R for some unit
c of A, where R = `integers`. -/
theorem exists_stableProducts_eq_unit_mul_integers (a : Fin 𝔰.ϱ) (x y : T.G) :
    ∃ c : Aˣ, F.stableProducts a x y = {t : A | c⁻¹.val * t ∈ integers} := by
  -- A stable vector `w` with second lift `w + d` is a point `(w, d)` of the lattice on which `X`
  -- is integral. The weight `wt` makes the coordinate of `w` at `e*_a` the leading one: larger
  -- weights belong to the `e*_b`, `b < a`, and to the coordinates of `d` off the `e_b`, `b < a`.
  let M (z : T.G) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := z
  let X : Matrix (𝔰.BesselIndex ⊕ 𝔰.BesselIndex) (𝔰.BesselIndex ⊕ 𝔰.BesselIndex) A :=
    fromBlocks (M x⁻¹) 0 (F.levelUnit⁻¹.val • (M x⁻¹ - M (x * y)⁻¹))
      (-F.levelUnit⁻¹.val • M (x * y)⁻¹)
  let wt : 𝔰.BesselIndex ⊕ 𝔰.BesselIndex → ℕ :=
    BesselIndex.level ⊕ᵥ fun k ↦ if BesselIndex.level k < a then 0 else 2 * 𝔰.ϱ + 1
  have hX : HasLeftInv X := by
    refine ⟨fromBlocks (M x) 0 (M (x * y) - M x) (-F.levelUnit.val • M (x * y)), ?_⟩
    simp [X, M, fromBlocks_multiply, smul_smul, mul_sub, sub_mul, mul_assoc]
  have h_close (w d : 𝔰.BesselIndex → A) : X *ᵥ (w ⊕ᵥ d) ∈ intVectors P.integers _ ↔
      (M x⁻¹ *ᵥ w, M (x * y)⁻¹ *ᵥ (w + d)) ∈ F.closePairs := by
    simp [closePairs_eq, X, fromBlocks_mulVec, smul_mulVec, sub_mulVec, neg_mulVec, mulVec_add,
      intVectors, mul_sub, sub_add_eq_sub_sub, ← sub_eq_add_neg]
  have h_zero (w d : 𝔰.BesselIndex → A) :
      (∀ l : 𝔰.BesselIndex ⊕ 𝔰.BesselIndex, wt (.inl (eStar a)) < wt l → (w ⊕ᵥ d) l = 0) ↔
        IsOrthogonalBelow a w ∧ CongrBelow a w (w + d) := by
    simp only [wt, IsOrthogonalBelow, CongrBelow, BesselIndex.level, Sum.forall, Sum.elim_inl,
      Sum.elim_inr, Pi.add_apply]
    grind
  have h_alone : ∀ l : 𝔰.BesselIndex ⊕ 𝔰.BesselIndex,
      wt l = wt (.inl (eStar a)) → l = .inl (eStar a) := by
    simp only [wt, BesselIndex.level, Sum.forall, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq]
    grind
  obtain ⟨c, hc⟩ : ∃ c : Aˣ, ∀ t : A,
      (∃ v : 𝔰.BesselIndex ⊕ 𝔰.BesselIndex → A, X *ᵥ v ∈ intVectors P.integers _ ∧
        (∀ l, wt (.inl (eStar a)) < wt l → v l = 0) ∧
        v (.inl (eStar a)) = t) ↔ c⁻¹.val * t ∈ integers :=
    exists_unit_leadingCoord_iff_mem_integers hX wt (.inl (eStar a)) h_alone
  refine ⟨c, Set.ext fun t ↦ Iff.trans ?_ (hc t)⟩
  constructor
  · rintro ⟨w, ⟨h_orth, w', h_congr, hw⟩, rfl⟩
    have h_add : w + (w' - w) = w' := add_sub_cancel w w'
    refine ⟨w ⊕ᵥ (w' - w), (h_close w (w' - w)).2 ?_, (h_zero w (w' - w)).2 ⟨h_orth, ?_⟩, rfl⟩
    · rwa [h_add]
    · rwa [h_add]
  · rintro ⟨v, hv_int, hv_zero, rfl⟩
    rw [← Sum.elim_comp_inl_inr v] at hv_int hv_zero
    obtain ⟨h_orth, h_congr⟩ :
        IsOrthogonalBelow a (v ∘ .inl) ∧ CongrBelow a (v ∘ .inl) (v ∘ .inl + v ∘ .inr) :=
      (h_zero (v ∘ .inl) (v ∘ .inr)).1 hv_zero
    exact ⟨v ∘ .inl,
      ⟨h_orth, v ∘ .inl + v ∘ .inr, h_congr, (h_close (v ∘ .inl) (v ∘ .inr)).1 hv_int⟩, rfl⟩

/-- For a large lattice datum, let x be near at a + 1. Then the set 𝔡_a = `F.stableProducts a x y`,
the coordinates at the dual of e_a of the vectors that are stable at x and x y, lies in the ring of
integers. -/
theorem stableProducts_subset {a : Fin 𝔰.ϱ} (h_near : F.IsNear (a + 1) x) :
    F.stableProducts a x y ⊆ P.integers := by
  -- If `ξ x` is integral, so is `ξ w = (ξ x) (x⁻¹ w)`, which has the same product with `e_a`.
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ T.partialUnitriangularGroup (a + 1), ξ * x ∈ F.boxSet := h_near
  rintro _ ⟨w, ⟨h_orth, w', -, hw⟩, rfl⟩
  rw [closePairs_eq] at hw
  have hw_int : x⁻¹.val.val *ᵥ w ∈ intVectors integers 𝔰.BesselIndex := hw.left
  obtain ⟨hξx_int, -⟩ : ξ * x ∈ unitaryLevel integers 1 T.splitGram := box_eq.le h_box
  have h_int : (ξ.val.val *ᵥ w) (eStar a) ∈ integers := by
    simpa [mul_assoc] using hξx_int.isIntMatrix.mulVec hw_int (eStar a)
  rwa [partialUnitriangularGroup_mulVec_eStar hξ a.val.lt_succ_self h_orth] at h_int

/-- **Depth at the finite places.** For a large lattice datum, let x be near at a + 1. Then the set
𝔡_a = `F.stableProducts a x y`, the coordinates at the dual of e_a of the vectors that are stable at
x and x y, is an ideal of the ring of integers, and the depth of e_a, the inverse of the volume of
this set, is the index of this ideal. -/
theorem exists_ideal_depth_eq {a : Fin 𝔰.ϱ} (h_near : F.IsNear (a + 1) x) (y : T.G) :
    ∃ I : Ideal P.integers,
      (∀ t : P.integers, t ∈ I ↔ ↑t ∈ F.stableProducts a x y) ∧ F.depth a x y = I.cardQuot := by
  obtain ⟨c, hc⟩ : ∃ c : Aˣ, F.stableProducts a x y = {t : A | c⁻¹.val * t ∈ integers} :=
    exists_stableProducts_eq_unit_mul_integers a x y
  have hc_mem : c.val ∈ P.integers := stableProducts_subset h_near (hc.ge (by simp))
  obtain ⟨I, -, hI_image, hI_card⟩ : ∃ I : Ideal P.integers, I.cardQuot ≠ 0 ∧
      integers.subtype '' I = {t : A | c⁻¹.val * t ∈ integers} ∧ I.cardQuot = (P.modulus c)⁻¹ :=
    exists_ideal_cardQuot_eq c hc_mem
  refine ⟨I, fun t ↦ ?_, ?_⟩
  · rw [hc, ← hI_image]
    exact integers.subtype_injective.mem_set_image.symm
  · rw [depth, hc, volume_setOf_mul_mem, modulus_inv, inv_inv, hI_card]

/-- For a large lattice datum and a group Z between the congruence subgroup K(g) and the integral
group K, if the finite Bessel vectors `Z.besselVector` at two points x and z are not orthogonal,
then for each a and each y the set 𝔡_a = `F.stableProducts a x y` contains a unit c of A lying in
the ring `integers`, and has volume at most the modulus of c. -/
theorem exists_unit_mem_stableProducts (a : Fin 𝔰.ϱ) {z : T.G} (y : T.G)
    (h_inner : ⟪Z.besselVector x, Z.besselVector z⟫_ℂ ≠ 0) :
    ∃ c : Aˣ, c.val ∈ integers ∧ c.val ∈ F.stableProducts a x y ∧
      volume (F.stableProducts a x y) ≤ P.modulus c := by
  obtain ⟨c, hc⟩ : ∃ c : Aˣ, F.stableProducts a x y = {t : A | c⁻¹.val * t ∈ integers} :=
    exists_stableProducts_eq_unit_mul_integers a x y
  obtain ⟨u, hu, v, hv, hux, -⟩ : ∃ u ∈ besselU, ∃ v ∈ besselU,
      u * x ∈ unitaryLevel integers 1 T.splitGram ∧ (u * x)⁻¹ * (v * z) ∈ F.congruenceSubgroup :=
    exists_mem_congruenceSubgroup_of_inner_ne_zero Z h_inner
  have h_near : F.IsNear (a + 1) x := ⟨u, mem_partialUnitriangularGroup_of_mem_besselU hu,
    box_eq.ge hux⟩
  have hc_mem : c.val ∈ F.stableProducts a x y := hc.ge (by simp)
  have h_volume : volume (F.stableProducts a x y) = P.modulus c := by
    rw [hc, volume_setOf_mul_mem, modulus_inv, inv_inv]
  exact ⟨c, stableProducts_subset h_near hc_mem, hc_mem, h_volume.le⟩

/-- Let `F` be a large lattice datum with level unit `F.levelUnit`. Let `Z` be a group between the
congruence subgroup K(g) and the integral group K. Let `Γ` be a gauge, a notion of size together
with a scale. If the finite Bessel vectors `Z.besselVector x` and `Z.besselVector y` are not
orthogonal, there are u, v in the Bessel unipotent group `besselU` with (a) u x and v y in the box
`F.boxSet` of integral points, and (b) `Γ.HasMatrixSize 2` holding for (v y − u
x) / `F.levelUnit`. -/
theorem exists_mem_boxSet_hasMatrixSize_of_inner_ne_zero {Γ : Gauge F}
    (h_inner : ⟪Z.besselVector x, Z.besselVector y⟫_ℂ ≠ 0) :
    ∃ u ∈ besselU, ∃ v ∈ besselU,
      -- (a)
      u * x ∈ F.boxSet ∧ v * y ∈ F.boxSet ∧
      -- (b)
      Γ.HasMatrixSize 2 (F.levelUnit⁻¹.val • ((v * y).val.val - (u * x).val.val)) := by
  obtain ⟨u, hu, v, hv, hux, h_close⟩ : ∃ u ∈ besselU, ∃ v ∈ besselU,
      u * x ∈ unitaryLevel integers 1 T.splitGram ∧ (u * x)⁻¹ * (v * y) ∈ F.congruenceSubgroup :=
    exists_mem_congruenceSubgroup_of_inner_ne_zero Z h_inner
  -- `(v y - u x) / g = u x · ((u x)⁻¹ v y - 1) / g` is a product of integral matrices.
  have h_int : IsIntMatrix integers (F.levelUnit⁻¹.val • ((v * y).val.val - (u * x).val.val)) := by
    obtain ⟨hux_int, -⟩ := hux
    obtain ⟨-, h_congr⟩ := h_close
    simpa [mul_sub, mul_assoc, Units.smul_def] using hux_int.isIntMatrix.mul h_congr
  have hvy : v * y ∈ unitaryLevel integers 1 T.splitGram := by
    simpa [mul_assoc] using mul_mem hux (unitaryLevel_le_unitaryLevel_one h_close)
  -- The box is the integral group, and an integral column `ω` has size `1`, as `(ω, ω)` is a
  -- close pair.
  have h_size (ω : 𝔰.BesselIndex → A) (hω : ω ∈ intVectors P.integers 𝔰.BesselIndex) :
      ω ∈ Γ.vecsOfSize 1 := by
    have h_pair : (ω, ω) ∈ F.closePairs := closePairs_eq.ge ⟨hω, by simp⟩
    exact (Γ.mem_vecsOfSize_of_mem_closePairs h_pair).1
  exact ⟨u, hu, v, hv, box_eq.ge hux, box_eq.ge hvy,
    fun i j ↦ mem_ofSize_mono (h_size _ (fun k ↦ h_int k j) i)⟩

/-- Let `F` be a large lattice datum, `Z` a group between the congruence subgroup K(g) and the
integral group K, `j ≤ ϱ`, and let `p`, `q` be sequences of units. If the majorant `F.formMajorant`
of their form of floor `j` (an integral of moduli of orbital integrals of the Bessel vector of `Z`)
is nonzero at a point `x`, then the products `p 0 ⋯ p (l - 1)` and `q 0 ⋯ q (l - 1)`, `l ≤ j`, lie
in the ring `integers`. -/
theorem prod_mem_of_formMajorant_ne_zero (Z : F.IntermediateGroup) {j : ℕ}
    (hj : j ≤ 𝔰.ϱ) {p q : ℕ → Aˣ} {x : T.G}
    (hx : F.formMajorant j p q Z.besselVector x ≠ 0) {l : ℕ} (hl : l ≤ j) :
    (∏ a ∈ Finset.range l, p a).val ∈ integers ∧ (∏ a ∈ Finset.range l, q a).val ∈ integers := by
  -- Where the integrand is not zero, the frames `y`, `y * x` and their translates by the inverses
  -- of the Weyl elements of `p` and of `q` respectively are near at `j`.
  obtain ⟨y, -, hy⟩ :
      ∃ y ∈ floorGroup 0,
        F.pivotL1Norm j (frameCorrelation Z.besselVector 1) y (y * x) *
          F.pivotL1Norm j (frameCorrelation Z.besselVector (weylRatio j p q))
            ((weylElem j p)⁻¹ * y) ((weylElem j p)⁻¹ * y * x) ≠ 0 :=
    exists_ne_zero_of_ae ae_partialGroupMeasure_mem hx
  obtain ⟨σ, hσ, h_first⟩ : ∃ σ ∈ floorGroup j,
      ⟪Z.besselVector (σ * y), Z.besselVector (1 * (σ * (y * x)))⟫_ℂ ≠ 0 :=
    exists_ne_zero_of_pivotL1Norm_ne_zero (left_ne_zero_of_mul hy)
  obtain ⟨τ, hτ, h_second⟩ : ∃ τ ∈ floorGroup j,
      ⟪Z.besselVector (τ * ((weylElem j p)⁻¹ * y)),
        Z.besselVector (weylRatio j p q * (τ * ((weylElem j p)⁻¹ * y * x)))⟫_ℂ ≠ 0 :=
    exists_ne_zero_of_pivotL1Norm_ne_zero (right_ne_zero_of_mul hy)
  have h_near {ρ z : T.G} (hρ : ρ ∈ floorGroup j) (hz : Z.besselVector (ρ * z) ≠ 0) :
      F.IsNear j z :=
    ((isCut_besselVector Z).isNear_of_ne_zero hz).of_floorGroup_mul hρ le_rfl
  have h_pair {ρ z z' : T.G} (hρ : ρ ∈ floorGroup j)
      (hz : ⟪Z.besselVector (ρ * z), Z.besselVector (ρ * z')⟫_ℂ ≠ 0) :
      F.IsNear j z ∧ F.IsNear j z' :=
    ⟨h_near hρ fun h_zero ↦ hz (by rw [h_zero, inner_zero_left]),
      h_near hρ fun h_zero ↦ hz (by rw [h_zero, inner_zero_right])⟩
  obtain ⟨h_y, h_yx⟩ : F.IsNear j y ∧ F.IsNear j (y * x) := h_pair hσ (by simpa using h_first)
  obtain ⟨h_py, h_qyx⟩ :
      F.IsNear j ((weylElem j p)⁻¹ * y) ∧ F.IsNear j ((weylElem j q)⁻¹ * (y * x)) :=
    h_pair hτ (by simpa [weylRatio, mul_assoc, ← (weylElem_mul_left_comm hτ).2] using h_second)
  -- In the gauge of scale `1` every size means integral.
  have h_minor {r : ℕ → Aˣ} {z : T.G} (hz : F.IsNear j z)
      (hrz : F.IsNear j ((weylElem j r)⁻¹ * z)) :
      (∏ a ∈ Finset.range l, r a).val ∈ integers := by
    obtain ⟨ξ, hξ⟩ : F.IsNear j z := hz
    simpa using head_products_mem_ofSize (h.gauge 1 (one_mem integers)
      (star_one A)).hasMatrixSize_boxSet hj hrz
      hξ l hl
  exact ⟨h_minor h_y h_py, h_minor h_yx h_qyx⟩

/-- Let `r` be a sequence of units of `A` all of whose products `r 0 ⋯ r (l - 1)`, `l ≤ j`, are
integral. Then some unit `β` of `A` lying in `integers` is an integral multiple of each of them and
of each `r i`, `i < j`, and the weight `finHeadWeight K j r` equals `√(genIndex β) ^ K`. Here
`genIndex β` is the inverse of the factor by which `β` scales Haar measure, and the weight is the
product of the numbers `√(genIndex (r 0 ⋯ r l)) ^ K` over `l < j`. -/
theorem exists_unit_multiple_of_prod_mem (j K : ℕ) (r : ℕ → Aˣ)
    (h_minor : ∀ l ≤ j, (∏ a ∈ Finset.range l, r a).val ∈ integers) :
    ∃ β : Aˣ, β.val ∈ integers ∧
      (∀ l ≤ j, (β / ∏ a ∈ Finset.range l, r a).val ∈ integers) ∧
      (∀ i < j, (β / r i).val ∈ integers) ∧
      finHeadWeight K j r = √(genIndex β.val) ^ K := by
  let β : Aˣ := ∏ l ∈ Finset.range (j + 1), ∏ a ∈ Finset.range l, r a
  have h_weight : finHeadWeight K j r = √(genIndex β.val) ^ K := by
    unfold β
    induction j with
    | zero => simp [finHeadWeight]
    | succ j ih =>
      have h_last : (∏ a ∈ Finset.range (j + 1), r a).val ∈ integers := h_minor (j + 1) le_rfl
      rw [finHeadWeight, prod_range_succ, ← finHeadWeight,
        ih fun l hl ↦ h_minor l (hl.trans j.le_succ), prod_range_succ _ (j + 1)]
      simp [h_last, ← Units.coe_prod, genIndex_pos, le_of_lt, mul_pow]
  have h_int (l : ℕ) (hl : l ∈ Finset.range (j + 1)) : (∏ a ∈ Finset.range l, r a).val ∈ integers :=
    h_minor l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
  have hβ : β.val ∈ integers := by
    rw [Units.coe_prod]
    exact prod_mem h_int
  have h_div (l : ℕ) (hl : l ≤ j) : (β / ∏ a ∈ Finset.range l, r a).val ∈ integers := by
    rw [← prod_erase_eq_div (Finset.mem_range.2 (Nat.lt_succ_iff.2 hl)), Units.coe_prod]
    exact prod_mem fun i hi ↦ h_int i (Finset.mem_of_mem_erase hi)
  refine ⟨β, hβ, h_div, fun i hi ↦ ?_, h_weight⟩
  have h_quot : β / r i = β / (∏ a ∈ Finset.range (i + 1), r a) * ∏ a ∈ Finset.range i, r a := by
    rw [prod_range_succ, div_mul_eq_div_div_swap, div_mul_cancel]
  rw [h_quot, Units.val_mul]
  exact mul_mem (h_div (i + 1) hi) (h_minor i hi.le)

/-- Let `g`, `β`, `γ` be units of `A` lying in `integers`, and `α` a unit with `modulus α = modulus
g * (modulus β * modulus γ) ^ 2`. If `4 E ≤ K`, then `(2 / modulus α) ^ E` is at most
`(2 / modulus g) ^ K` times `√(genIndex β) ^ K * √(genIndex γ) ^ K`. -/
theorem two_div_modulus_pow_le_mul_sqrt_genIndex_pow {α g β γ : Aˣ} (hg : g.val ∈ P.integers)
    (hβ : β.val ∈ P.integers) (hγ : γ.val ∈ P.integers)
    (h_modulus : P.modulus α = P.modulus g * (P.modulus β * P.modulus γ) ^ 2) {E K : ℕ}
    (hE : 4 * E ≤ K) :
    (2 / P.modulus α) ^ E ≤
      (2 / P.modulus g) ^ K * ENNReal.ofReal (√(genIndex β.val) ^ K * √(genIndex γ.val) ^ K) := by
  let b : ℝ≥0∞ := ENNReal.ofReal √(genIndex β.val)
  let c : ℝ≥0∞ := ENNReal.ofReal √(genIndex γ.val)
  have hb : (P.modulus β)⁻¹ = b ^ 2 := inv_modulus_eq_sqrt_genIndex_sq β
  have hc : (P.modulus γ)⁻¹ = c ^ 2 := inv_modulus_eq_sqrt_genIndex_sq γ
  have h_base : 2 / P.modulus α = 2 / P.modulus g * (b * c) ^ 4 :=
    calc 2 / P.modulus α
      _ = 2 / P.modulus g * ((P.modulus β)⁻¹ * (P.modulus γ)⁻¹) ^ 2 := by
        simp [h_modulus, div_eq_mul_inv, ENNReal.mul_inv, sq, mul_assoc]
      _ = 2 / P.modulus g * (b * c) ^ 4 := by rw [hb, hc, ← mul_pow, ← pow_mul]
  -- Compare powers base by base: each base is at least 1, and `4 * E ≤ K`.
  have hg_base : 1 ≤ 2 / P.modulus g := one_le_two.trans (two_le_two_div_modulus hg)
  have hb_base : 1 ≤ b := by simp [b, one_le_genIndex, hβ]
  have hc_base : 1 ≤ c := by simp [c, one_le_genIndex, hγ]
  have hE_le : E ≤ K := by lia
  calc (2 / P.modulus α) ^ E
    _ = (2 / P.modulus g) ^ E * (b * c) ^ (4 * E) := by rw [h_base, mul_pow, ← pow_mul]
    _ ≤ (2 / P.modulus g) ^ K * (b * c) ^ K :=
      mul_le_mul' (pow_le_pow_right₀ hg_base hE_le)
        (pow_le_pow_right₀ (one_le_mul hb_base hc_base) hE)
    _ = _ := by simp [b, c, mul_pow]

/-- Let `F` be a large lattice datum with level unit `g = F.levelUnit`, let `Z` be a group between
the congruence subgroup of level `g` and the group of integral points, let `j ≤ 𝔰.ϱ`, and let `p`,
`q` be sequences of units of `A`. Suppose that the majorant `F.formMajorant` of their form of floor
`j`, for the Bessel vector of `Z`, is not zero at some point. Then there is a unit `α` of `A`, lying
in `integers` and fixed by the involution, with the following properties in the gauge `Γ` of scale
`α`. The inverses of the products `p 0 ⋯ p (l - 1)` and `q 0 ⋯ q (l - 1)`, `l ≤ j`, have size 1
(`Γ.IsHead`); so have `g⁻¹` if `j ≠ 0` and `1 / p i - 1 / q i` for `i < j`; and if `4 E ≤ K`, then
`Γ.loss ^ E` is at most `(2 / modulus g) ^ K` times the weights `New.finHeadWeight K j` of `p` and
`q`. -/
theorem exists_gauge_of_formMajorant_ne_zero {F : PlaceData ι T (m + 1)} [h : IsLargeLatticeData F]
    (Z : F.IntermediateGroup) {j : ℕ} (hj : j ≤ 𝔰.ϱ) (K : ℕ) (p q : ℕ → Aˣ)
    (h_ne : ∃ x : T.G, F.formMajorant j p q Z.besselVector x ≠ 0) :
    ∃ (α : Aˣ) (hα_mem : α.val ∈ integers) (hα_star : star α.val = α.val),
      let Γ : Gauge F := h.gauge α hα_mem hα_star
      Γ.IsHead j p ∧
      Γ.IsHead j q ∧
      (j ≠ 0 → F.levelUnit⁻¹.val ∈ Γ.ofSize 1) ∧
      (∀ i : ℕ, i < j → (p i)⁻¹.val - (q i)⁻¹.val ∈ Γ.ofSize 1) ∧
      ∀ E : ℕ, 4 * E ≤ K →
        Γ.loss ^ E ≤
          (2 / P.modulus F.levelUnit) ^ K * ENNReal.ofReal
            (finHeadWeight K j p * finHeadWeight K j q) := by
  -- The leading products of `p` and `q` are integral. With common multiples `β` of those of `p`
  -- and `γ` of those of `q`, the scale `α = g * star (β * γ) * β * γ` has all the properties.
  have hg : F.levelUnit.val ∈ integers := by
    obtain ⟨-, -, hg, -⟩ := h.integral_data
    exact hg
  obtain ⟨x, hx⟩ : ∃ x : T.G, F.formMajorant j p q Z.besselVector x ≠ 0 := h_ne
  have h_minors (l : ℕ) (hl : l ≤ j) :
      (∏ a ∈ Finset.range l, p a).val ∈ integers ∧ (∏ a ∈ Finset.range l, q a).val ∈ integers :=
    prod_mem_of_formMajorant_ne_zero Z hj hx hl
  obtain ⟨β, hβ, hβ_minor, hβ_entry, hβ_weight⟩ : ∃ β : Aˣ, β.val ∈ integers ∧
      (∀ l ≤ j, (β / ∏ a ∈ Finset.range l, p a).val ∈ integers) ∧
        (∀ i < j, (β / p i).val ∈ integers) ∧
      finHeadWeight K j p = √(genIndex β.val) ^ K :=
    exists_unit_multiple_of_prod_mem j K p fun l hl ↦ (h_minors l hl).left
  obtain ⟨γ, hγ, hγ_minor, hγ_entry, hγ_weight⟩ : ∃ γ : Aˣ, γ.val ∈ integers ∧
      (∀ l ≤ j, (γ / ∏ a ∈ Finset.range l, q a).val ∈ integers) ∧
        (∀ i < j, (γ / q i).val ∈ integers) ∧
      finHeadWeight K j q = √(genIndex γ.val) ^ K :=
    exists_unit_multiple_of_prod_mem j K q fun l hl ↦ (h_minors l hl).right
  have h_star : (star (β * γ)).val ∈ integers := isAdelic.toIsStarStable.star_mem (mul_mem hβ hγ)
  let α : Aˣ := F.levelUnit * star (β * γ) * β * γ
  have hα_mem : α.val ∈ integers := mul_mem (mul_mem (mul_mem hg h_star) hβ) hγ
  have hα_star : star α.val = α.val := by
    simp [α, star_levelUnit, mul_comm, mul_left_comm, mul_assoc]
  let Γ : Gauge F := h.gauge α hα_mem hα_star
  have h_size (z : A) : z ∈ Γ.ofSize 1 ↔ α.val * z ∈ integers := by simp [Γ]
  -- A unit that divides `β` or `γ` divides `α`, and so does `g`.
  have h_dvd_left (u : Aˣ) (hu : (β / u).val ∈ integers) : α.val * u⁻¹.val ∈ integers := by
    have h_quot : α * u⁻¹ = F.levelUnit * star (β * γ) * γ * (β / u) := by
      simp only [α, div_eq_mul_inv, mul_assoc, mul_left_comm]
    rw [← Units.val_mul, h_quot]
    exact mul_mem (mul_mem (mul_mem hg h_star) hγ) hu
  have h_dvd_right (u : Aˣ) (hu : (γ / u).val ∈ integers) : α.val * u⁻¹.val ∈ integers := by
    have h_quot : α * u⁻¹ = F.levelUnit * star (β * γ) * β * (γ / u) := by
      simp only [α, div_eq_mul_inv, mul_assoc]
    rw [← Units.val_mul, h_quot]
    exact mul_mem (mul_mem (mul_mem hg h_star) hβ) hu
  have h_dvd_g : α.val * F.levelUnit⁻¹.val ∈ integers := by
    have h_quot : α * F.levelUnit⁻¹ = star (β * γ) * β * γ := by
      rw [mul_comm]
      simp only [α, mul_assoc, inv_mul_cancel_left]
    rw [← Units.val_mul, h_quot]
    exact mul_mem (mul_mem h_star hβ) hγ
  have h_close (i : ℕ) (hi : i < j) : α.val * ((p i)⁻¹.val - (q i)⁻¹.val) ∈ integers := by
    rw [mul_sub]
    exact sub_mem (h_dvd_left (p i) (hβ_entry i hi)) (h_dvd_right (q i) (hγ_entry i hi))
  -- The involution keeps the modulus.
  have h_modulus : P.modulus α = P.modulus F.levelUnit * (P.modulus β * P.modulus γ) ^ 2 := by
    simp only [α, Units.val_mul, Units.coe_star, map_mul, modulus_star, sq, mul_assoc]
  have hp_head : Γ.IsHead j p := fun l hl ↦ (h_size _).2 (h_dvd_left _ (hβ_minor l hl))
  have hq_head : Γ.IsHead j q := fun l hl ↦ (h_size _).2 (h_dvd_right _ (hγ_minor l hl))
  refine ⟨α, hα_mem, hα_star, hp_head, hq_head, fun _ ↦ (h_size _).2 h_dvd_g,
    fun i hi ↦ (h_size _).2 (h_close i hi), fun E hE ↦ ?_⟩
  change (2 / P.modulus α) ^ E ≤ _
  rw [hβ_weight, hγ_weight]
  exact two_div_modulus_pow_le_mul_sqrt_genIndex_pow hg hβ hγ h_modulus hE

/-- Let `F` be a large lattice datum with level unit `g`, let `Z` be a group between the congruence
subgroup K(g) = `F.congruenceSubgroup` and the group of integral points, and let `p`, `q` be any two
sequences of units. A point `x` at which the majorant `F.formMajorant` of their form of floor `j`,
for the Bessel vector of `Z`, does not vanish lies in `F.positions`, the set of products of a
conjugate of an element of the Bessel unipotent group `besselU` and an element of K(g). -/
theorem mem_positions_of_formMajorant_ne_zero {F : PlaceData ι T (m + 1)} {x : T.G}
    (Z : F.IntermediateGroup) [h : IsLargeLatticeData F] {j : ℕ} {p q : ℕ → Aˣ}
    (hx : F.formMajorant j p q Z.besselVector x ≠ 0) :
    x ∈ F.positions := by
  -- Some frames `σ * y` and `σ * y * x` pair; by
  -- `PlaceData.exists_mem_congruenceSubgroup_of_inner_ne_zero`, `x` is then a conjugate by `σ * y`
  -- of an element of `besselU`, times an element of `F.congruenceSubgroup`, which is the form of a
  -- position.
  obtain ⟨y, -, hy⟩ :
      ∃ y ∈ floorGroup 0,
        F.pivotL1Norm j (frameCorrelation Z.besselVector 1) y (y * x) *
          F.pivotL1Norm j (frameCorrelation Z.besselVector (weylRatio j p q))
            ((weylElem j p)⁻¹ * y) ((weylElem j p)⁻¹ * y * x) ≠ 0 :=
    exists_ne_zero_of_ae ae_partialGroupMeasure_mem hx
  obtain ⟨σ, -, h_pair⟩ :
      ∃ σ ∈ floorGroup j, ⟪Z.besselVector (σ * y), Z.besselVector (1 * (σ * (y * x)))⟫_ℂ ≠ 0 :=
    exists_ne_zero_of_pivotL1Norm_ne_zero (left_ne_zero_of_mul hy)
  rw [one_mul] at h_pair
  obtain ⟨u, hu, v, hv, -, h_lev⟩ :
      ∃ u ∈ besselU, ∃ v ∈ besselU,
        u * (σ * y) ∈ unitaryLevel integers 1 T.splitGram ∧
        (u * (σ * y))⁻¹ * (v * (σ * (y * x))) ∈ F.congruenceSubgroup :=
    exists_mem_congruenceSubgroup_of_inner_ne_zero Z h_pair
  have h_positions (z : T.G) : z ∈ F.positions ↔
      ∃ a : T.G, (∃ s : T.G, ∃ w ∈ besselU, s⁻¹ * w * s = a) ∧ ∃ k ∈ F.congruenceSubgroup,
        a * k = z := by
    obtain ⟨-, -, -, -, h_eq⟩ := h.volume_le_and_boxSet_closePairs_positions_eq
    rw [h_eq]
    exact Set.mem_mul
  have h_factor :
      (σ * y)⁻¹ * (v⁻¹ * u) * (σ * y) * ((u * (σ * y))⁻¹ * (v * (σ * (y * x)))) = x := by
    simp [mul_assoc]
  exact (h_positions x).2 ⟨_, ⟨σ * y, v⁻¹ * u, mul_mem (inv_mem hv) hu, rfl⟩, _, h_lev, h_factor⟩

/-- Let `d i`, `i < ϱ`, be units of `A` lying in `integers`, and let `σ ≤ 1` satisfy `σ ^ 2 ≤ |d i|`
for `j ≤ i`. Then the `d i` with `j ≤ i` have a common multiple `C` in `integers`, a unit of `A`
fixed by the involution, of modulus at least `σ ^ (4 n)`. -/
theorem exists_star_eq_common_multiple {j : ℕ} {d : Fin 𝔰.ϱ → Aˣ}
    (hd_int : ∀ i : Fin 𝔰.ϱ, (d i).val ∈ P.integers) {σ : ℝ≥0∞} (hσ_le : σ ≤ 1)
    (hd_modulus : ∀ i : Fin 𝔰.ϱ, j ≤ i → σ ^ 2 ≤ P.modulus (d i)) :
    ∃ C : Aˣ, C.val ∈ P.integers ∧ star C.val = C.val ∧
      (∀ i : Fin 𝔰.ϱ, j ≤ i → (C / d i).val ∈ P.integers) ∧
      σ ^ (4 * 𝔰.n) ≤ P.modulus C := by
  have hd_star (i : Fin 𝔰.ϱ) : star (d i).val ∈ P.integers :=
    isAdelic.toIsStarStable.star_mem (hd_int i)
  let C : Aˣ := ∏ i : Fin 𝔰.ϱ with j ≤ i.val, d i * star (d i)
  have hC : C.val ∈ P.integers := by simp [C, hd_int, hd_star, prod_mem, mul_mem]
  have hC_star : star C.val = C.val := by simp [C, mul_comm]
  have hC_div (i : Fin 𝔰.ϱ) (hi : j ≤ i) : (C / d i).val ∈ P.integers := by
    have h_quot : C / d i = (∏ k ∈ ({k : Fin 𝔰.ϱ | j ≤ k.val} : Finset (Fin 𝔰.ϱ)).erase i, d k) *
        ∏ k : Fin 𝔰.ϱ with j ≤ k.val, star (d k) := by
      simp [C, hi, prod_mul_distrib, mul_div_right_comm, prod_erase_eq_div]
    simp [h_quot, hd_int, hd_star, prod_mem, mul_mem]
  have h_card : 2 * 2 * #{i : Fin 𝔰.ϱ | j ≤ i.val} ≤ 4 * 𝔰.n := by grind [card_finset_fin_le]
  refine ⟨C, hC, hC_star, hC_div, ?_⟩
  calc σ ^ (4 * 𝔰.n)
    _ ≤ ∏ i : Fin 𝔰.ϱ with j ≤ i.val, (σ ^ 2) ^ 2 := by
      simpa [← pow_mul] using pow_le_pow_right_of_le_one' hσ_le h_card
    _ ≤ ∏ i : Fin 𝔰.ϱ with j ≤ i.val, P.modulus (d i) ^ 2 :=
      prod_le_prod fun i hi ↦ pow_le_pow_left' (hd_modulus i (by simpa using hi)) 2
    _ = P.modulus C := by simp [C, sq]

/-- Let `F` be a large lattice datum with level unit `g`, let `Z` be a group between the congruence
subgroup of level `g` and the group of integral points, let `n = 𝔰.n`, and let `Γ` be the gauge of
scale `α`, in which size 1 means that `α` times the element lies in `integers` and
`Γ.loss = 2 / modulus α`. Let `c` divide every common denominator in `integers` of the entries of
`(x - 1) / g`, let `σ < 1` satisfy `modulus c * Γ.loss ^ (10 n · 99 n) ≤ σ ^ (400 n²)`, let `p`, `q`
be heads of length `j ≤ ϱ` for `Γ`, and let `g⁻¹` have size 1 if `j ≠ 0`. Suppose that the Bessel
vectors of `Z` at `y` and `y * x` are not orthogonal and that these two points, moved back by the
Weyl elements `weylElem j p` and `weylElem j q`, are near at `j`. Then for some `i ≥ j` the set
`F.stableProducts i y x`, the coordinates at the dual of e_i of the vectors that are stable at `y`
and `y * x`, has volume at most `σ ^ 2`. -/
theorem exists_volume_stableProducts_le {F : PlaceData ι T (m + 1)} [h : IsLargeLatticeData F]
    {x y : T.G} (Z : F.IntermediateGroup) {j : ℕ} {p q : ℕ → Aˣ} {Γ : Gauge F} (hj : j ≤ 𝔰.ϱ)
    {α : Aˣ} {hα_mem : α.val ∈ integers} {hα_star : star α.val = α.val}
    (hΓ : Γ = h.gauge α hα_mem hα_star) (hp_head : Γ.IsHead j p) (hq_head : Γ.IsHead j q)
    (hg_size : j ≠ 0 → F.levelUnit⁻¹.val ∈ Γ.ofSize 1) {c : Aˣ} {σ : ℝ≥0∞} (hσ_lt : σ < 1)
    (hσ_bound : P.modulus c * Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n)) ≤ σ ^ (400 * 𝔰.n ^ 2))
    (h_den : ∀ ε : A, ε ∈ integers →
      (∀ i k : 𝔰.BesselIndex, ε * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈ integers) →
        c⁻¹.val * ε ∈ integers)
    (h_pair : ⟪Z.besselVector y, Z.besselVector (y * x)⟫_ℂ ≠ 0)
    (hp_near : F.IsNear j ((weylElem j p)⁻¹ * y))
    (hq_near : F.IsNear j ((weylElem j q)⁻¹ * (y * x))) :
    ∃ i : Fin 𝔰.ϱ, j ≤ i ∧ volume (F.stableProducts i y x) ≤ σ ^ 2 := by
  by_contra! h_large
  -- Each ideal holds a unit `d i` lying in `integers` whose modulus bounds the volume of the ideal.
  have h_units (i : Fin 𝔰.ϱ) : ∃ d : Aˣ, d.val ∈ integers ∧ d.val ∈ F.stableProducts i y x ∧
      volume (F.stableProducts i y x) ≤ P.modulus d :=
    exists_unit_mem_stableProducts Z i x h_pair
  choose d hd_int hd_mem hd_vol using h_units
  obtain ⟨C, hC, hC_star, hC_div, hC_md⟩ : ∃ C : Aˣ, C.val ∈ P.integers ∧ star C.val = C.val ∧
      (∀ i : Fin 𝔰.ϱ, j ≤ i → (C / d i).val ∈ P.integers) ∧ σ ^ (4 * 𝔰.n) ≤ P.modulus C :=
    exists_star_eq_common_multiple hd_int hσ_lt.le fun i hi ↦
      (h_large i hi).le.trans (hd_vol i)
  -- In the gauge of scale `α ^ (10 * 𝔰.n) * C` every `(d i)⁻¹`, `j ≤ i`, has size 1, so by
  -- `Gauge.hasMatrixSize_sub_one_of_stableProducts` the matrix `(x - 1) / g` has size `99 * 𝔰.n`.
  have h_scale : (α ^ (10 * 𝔰.n) * C).val ∈ integers := mul_mem (pow_mem hα_mem _) hC
  let Γ' : Gauge F :=
    h.gauge (α ^ (10 * 𝔰.n) * C) h_scale (by simp [hα_star, hC_star, mul_comm])
  have h_subset : Γ.ofSize (10 * 𝔰.n) ⊆ Γ'.ofSize 1 := by
    intro b hb
    have hb_int : α.val ^ (10 * 𝔰.n) * b ∈ integers := by simpa [hΓ] using hb
    simpa [Γ', mul_left_comm C.val, mul_assoc] using mul_mem hC hb_int
  have hd_inv (i : Fin 𝔰.ϱ) (hi : j ≤ i) : (d i)⁻¹.val ∈ Γ'.ofSize 1 := by
    simpa [Γ', mul_assoc, div_eq_mul_inv] using mul_mem (pow_mem hα_mem _) (hC_div i hi)
  have h_size : Γ'.HasMatrixSize (99 * 𝔰.n) (F.levelUnit⁻¹.val • (x.val.val - 1)) :=
    Γ'.hasMatrixSize_sub_one_of_stableProducts Γ hj hp_head hq_head hg_size (fun _ ↦ h_subset)
      (exists_mem_boxSet_hasMatrixSize_of_inner_ne_zero Z h_pair) hp_near hq_near
      fun i hi ↦ ⟨d i, hd_mem i, hd_inv i hi⟩
  -- That power of the scale is then a common denominator, so `c` divides it.
  have h_entries (i k : 𝔰.BesselIndex) :
      (α ^ (10 * 𝔰.n) * C).val ^ (99 * 𝔰.n) * (F.levelUnit⁻¹.val • (x.val.val - 1)) i k ∈
        integers :=
    h_size i k
  have h_dvd : c⁻¹.val * (α ^ (10 * 𝔰.n) * C).val ^ (99 * 𝔰.n) ∈ integers :=
    h_den _ (pow_mem h_scale _) h_entries
  have h_md : P.modulus (c⁻¹ * C ^ (99 * 𝔰.n)).val ≤ Γ.loss ^ (10 * 𝔰.n * (99 * 𝔰.n)) := by
    refine Γ.modulus_le _ _ ?_
    simpa [hΓ, ← pow_mul, mul_left_comm c⁻¹.val, mul_pow] using h_dvd
  -- Compare moduli: `4 * 99 < 400` leaves a spare factor `σ < 1`.
  let X : ℝ≥0∞ := P.modulus (C ^ (99 * 𝔰.n)).val
  have hX_zero : X ≠ 0 := by simp [X]
  have hX_top : X ≠ ∞ := by simp [X]
  have hX_lt : X < X :=
    calc X = P.modulus c * P.modulus (c⁻¹ * C ^ (99 * 𝔰.n)).val := by simp [X, ← map_mul]
      _ ≤ σ ^ (400 * 𝔰.n ^ 2) := by grw [h_md, hσ_bound]
      _ ≤ σ * (σ ^ (4 * 𝔰.n)) ^ (99 * 𝔰.n) := by
        simpa only [← pow_mul, ← pow_succ'] using pow_le_pow_right_of_le_one' hσ_lt.le (by lia)
      _ ≤ σ * X := by grw [hC_md, ← map_pow, ← C.val_pow_eq_pow_val]
      _ < X := by simpa using ENNReal.mul_lt_mul_left hX_zero hX_top hσ_lt
  exact hX_lt.false

end IntegralPlace.IsLargeLatticeData

end New.Floors

end

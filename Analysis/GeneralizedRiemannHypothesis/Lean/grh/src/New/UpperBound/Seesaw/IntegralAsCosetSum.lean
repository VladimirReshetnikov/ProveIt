import Lib.Weil.Periods.BesselIntegral

/-!
# Integrals over a quotient as finite sums over cosets with controlled multiplicity

A finite set of cosets serves as a weighted fundamental domain. For subgroups `S`, `A`, `J` of `H`
and a finite `T ⊆ H ⧸ J`:
* `New.Seesaw.coverMultiplicity`: the number of classes in `S ⧸ (S ⊓ A)` that have a
  representative `r` with `t ∈ r • T` (zero if infinite).
* `New.Seesaw.exists_finset_coverMultiplicity_dvd_pow`: for `H = New.Gf E ι`, levels `J ≤ A` and a
  compact `D` on which the `q ^ n`-th powers of conjugates of `J` fall into `A`, a `T` stable under
  `S ⊓ A` whose multiplicities divide powers of `q` at the points of `T` and at the points with a
  given property that forces their `S`-orbit to meet `D`.
* `New.Grading.exists_integral_eq_sum_over_cut`: if the periods of a function over the Bessel
  subgroup factor over `T` and the multiplicities are non-zero on its support, its integral over the
  quotient of the adelic group `New.G E ε` by the rational points of `New.Grading.besselGroup` is a
  constant times a sum over `T` weighted by the inverse multiplicities.

In these names, a "cut" is such a finite set `T` of cosets.

Notions from other files:
* `New.G E ε = New.GInf E ε × New.Gf E ι`: the adelic unitary group, with its infinite and finite
  parts.
* `New.IsLevel J`: `J` is an open subgroup of the compact open subgroup `New.stdLevel E ι` of
  integral points of `New.Gf E ι`; its index there is `New.stdLevelIndex J`.
* `New.Grading.besselGroup`: the Bessel (Fourier–Jacobi) subgroup of `New.G E ε` attached to a
  grading, with finite part `New.Grading.besselFin` and rational points `New.Grading.ratBessel`.
* `Subgroup.quotMeasure`: the measure on a group that computes integrals over the quotient by a
  subgroup acting on the left; `New.Grading.besselMeasure` is this measure for the quotient of the
  Bessel subgroup by its rational points.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

open MeasureTheory Measure Subgroup QuotientGroup MulAction Set Pointwise ProbabilityTheory

namespace New.Seesaw

section Group

variable {H : Type*} [Group H] {S A J : Subgroup H} (T : Finset (H ⧸ J))

variable (S A) in
/-- The multiplicity with which the translates of `T` under `S`, counted modulo `S ⊓ A`, cover `t`:
the number of classes in `S ⧸ (S ⊓ A)` that have a representative `r` with `r⁻¹ • t ∈ T`, and zero
if there are infinitely many. -/
noncomputable def coverMultiplicity (t : H ⧸ J) : ℕ :=
  (QuotientGroup.mk (s := A.subgroupOf S) '' {r : S | r⁻¹ • t ∈ T}).ncard

/-- The number `coverMultiplicity S A T t` of classes of `r ∈ S` modulo `S ⊓ A` with `r⁻¹ • t ∈ T`
is constant on the `S`-orbit of the coset `t ∈ H ⧸ J`. -/
lemma coverMultiplicity_smul (p : S) (t : H ⧸ J) :
    coverMultiplicity S A T (p • t) = coverMultiplicity S A T t := by
  -- Left translation by `p⁻¹` carries the classes counted at `p • t` to those counted at `t`.
  rw [coverMultiplicity, coverMultiplicity, ← ncard_smul_set p⁻¹,
    ← image_smul_comm _ _ _ (by simp)]
  simp [← preimage_smul, mul_smul]

/-- If the `q ^ n`-th power of every element lies in a subgroup `K` of finite index, then the index
of `K` divides a power of `q`: in the finite quotient by the normal core of `K`, the order of every
element divides `q ^ n`. -/
lemma exists_index_dvd_pow_of_pow_mem {G : Type*} [Group G] {K : Subgroup G} [K.FiniteIndex]
    {q n : ℕ} (h_pow : ∀ g : G, g ^ q ^ n ∈ K) :
    ∃ j : ℕ, K.index ∣ q ^ j := by
  have h_pgroup : IsPGroup q (G ⧸ K.normalCore) := by
    rintro ⟨g⟩
    have h_core : g ^ q ^ n ∈ K.normalCore := fun c ↦ by simpa using h_pow (c * g * c⁻¹)
    exact ⟨n, (eq_one_iff _).mpr h_core⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, K.normalCore.index ∣ q ^ j := isPGroup_iff_card_dvd_pow.mp h_pgroup
  exact ⟨j, (index_dvd_of_le (normalCore_le K)).trans hj⟩

/-- Let `C ⊆ H ⧸ J` meet each `S`-orbit in at most one point, and let `T` be the union of the
translates of `C` under `S ⊓ A`. At a point `t` of `C`, the number `coverMultiplicity S A T t` of
classes of `r ∈ S` modulo `S ⊓ A` with `r⁻¹ • t ∈ T` is the index of `Z ⊓ A` in the stabiliser `Z`
of `t` in `S`. -/
lemma coverMultiplicity_eq_index_stabilizer {C : Set (H ⧸ J)} (hC : InjOn (orbit S) C)
    (hT : ∀ t : H ⧸ J, t ∈ T ↔ ∃ p : S, ↑p ∈ A ∧ p⁻¹ • t ∈ C) {t : H ⧸ J} (ht : t ∈ C) :
    coverMultiplicity S A T t = ((A.subgroupOf S).subgroupOf (stabilizer S t)).index := by
  set Z : Subgroup S := stabilizer S t
  -- The classes counted at `t` are the `Z`-orbit of the trivial class in `S ⧸ (S ⊓ A)`.
  have h_classes : mk '' {r : S | r⁻¹ • t ∈ T} = orbit Z ((1 : S) : S ⧸ A.subgroupOf S) := by
    refine Subset.antisymm ?_ ?_
    · -- If `p⁻¹ • r⁻¹ • t ∈ C` then it is `t`, the only point of `C` in its orbit.
      rintro _ ⟨r, hr, rfl⟩
      obtain ⟨p, hp, hpt⟩ : ∃ p : S, ↑p ∈ A ∧ p⁻¹ • r⁻¹ • t ∈ C := (hT _).1 hr
      have h_mem : (p⁻¹ * r⁻¹) • t ∈ C := by rwa [mul_smul]
      have h_fix : p⁻¹ * r⁻¹ ∈ Z := hC h_mem ht (orbit_smul (p⁻¹ * r⁻¹) t)
      have h_coset : (((p⁻¹ * r⁻¹)⁻¹ * 1 : S) : S ⧸ A.subgroupOf S) = r :=
        QuotientGroup.eq.2 (by simpa [mem_subgroupOf] using hp)
      exact ⟨⟨(p⁻¹ * r⁻¹)⁻¹, inv_mem h_fix⟩, h_coset⟩
    · rintro _ ⟨⟨z, hz⟩, rfl⟩
      have h_fix : z⁻¹ • t = t := mem_stabilizer_iff.1 (inv_mem hz)
      have h_mem : z⁻¹ • t ∈ T := (hT _).2 ⟨1, one_mem _, by simpa [h_fix]⟩
      exact ⟨z, h_mem, congrArg QuotientGroup.mk (mul_one z).symm⟩
  have h_stab : stabilizer Z ((1 : S) : S ⧸ A.subgroupOf S) = (A.subgroupOf S).subgroupOf Z := by
    ext z
    change ↑z ∈ stabilizer S ((1 : S) : S ⧸ A.subgroupOf S) ↔ ↑z ∈ A.subgroupOf S
    rw [stabilizer_quotient]
  rw [coverMultiplicity, h_classes, ← index_stabilizer, h_stab]

/-- A union of `n ≥ 1` left cosets of a measurable subgroup `J` has measure `n * μ J` for any left
invariant measure `μ`. -/
lemma measure_union_cosets [MeasurableSpace H] [MeasurableMul H] {μ : Measure H}
    [IsMulLeftInvariant μ] (hJ : MeasurableSet (J : Set H)) {s : Set (H ⧸ J)} (hs : ncard s ≠ 0) :
    μ (QuotientGroup.mk (s := J) ⁻¹' s) = s.ncard * μ J := by
  lift s to Finset (H ⧸ J) using finite_of_ncard_ne_zero hs
  have h_class (t : H ⧸ J) :
      MeasurableSet (mk (s := J) ⁻¹' {t}) ∧ μ (mk (s := J) ⁻¹' {t}) = μ J := by
    obtain ⟨g, rfl⟩ := mk_surjective t
    -- The fibre over the class of `g` is the coset `g • J`.
    rw [show mk (s := J) ⁻¹' {↑g} = g • (J : Set H) from eq_class_eq_leftCoset J g, measure_smul]
    exact ⟨hJ.const_smul g, rfl⟩
  simp [← sum_measure_preimage_singleton _ fun t _ ↦ (h_class t).1, h_class]

end Group

section Levels

variable {E ι : Type*} [Field E] [CMType E] [Fintype ι] [DecidableEq ι]

/-- Let `S`, `A` and `J ≤ A` be subgroups of the finite adelic unitary group `Gf E ι` with `A` a
level, and suppose `(x * u * x⁻¹) ^ q ^ n ∈ A` for all `u ∈ J`. Then the index of `Z ⊓ A` in the
stabiliser `Z` in `S` of the coset `x J` divides a power of `q`. -/
lemma exists_index_stabilizer_dvd_pow {S A J : Subgroup (Gf E ι)} [hA : IsLevel A] (hJA : J ≤ A)
    {x : Gf E ι} {q n : ℕ} (hx : ∀ u ∈ J, (x * u * x⁻¹) ^ q ^ n ∈ A) :
    ∃ j : ℕ, ((A.subgroupOf S).subgroupOf (stabilizer S (x : Gf E ι ⧸ J))).index ∣ q ^ j := by
  set Z : Subgroup S := stabilizer S (x : Gf E ι ⧸ J)
  have h_conj {z : S} (hz : z ∈ Z) : x⁻¹ * z * x ∈ J := by
    have h_coset : (x : Gf E ι ⧸ J) = (z * x : Gf E ι) := (mem_stabilizer_iff.1 hz).symm
    simpa [mul_assoc] using QuotientGroup.eq.1 h_coset
  -- The index is finite: `Z` lies in the compact group `A' = x A x⁻¹` and `A` is open.
  have h_finite : ((A.subgroupOf S).subgroupOf Z).FiniteIndex := by
    set A' : Subgroup (Gf E ι) := MulAut.conj x • A
    have hZ_le : Z ≤ A'.subgroupOf S := by
      intro z hz
      rw [mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa using hJA (h_conj hz)
    have hA'_compact : IsCompact (A' : Set (Gf E ι)) := hA.isCompact.smul (ConjAct.toConjAct x)
    have h_relIndex : (A.subgroupOf S).relIndex (A'.subgroupOf S) ≠ 0 :=
      relIndex_comap_ne_zero S.subtype (hA'_compact.relIndex_ne_zero hA.isOpen)
    exact ⟨fun h_zero ↦ h_relIndex (relIndex_eq_zero_of_le_right hZ_le h_zero)⟩
  refine exists_index_dvd_pow_of_pow_mem (n := n) fun ⟨z, hz⟩ ↦ ?_
  have h_pow : (z : Gf E ι) ^ q ^ n ∈ A := by simpa [mul_assoc] using hx _ (h_conj hz)
  simpa [mem_subgroupOf] using h_pow

/-- Let `S` and `J ≤ A ≤ B` be subgroups of the finite adelic unitary group `Gf E ι` with `J` and
`A` levels, and `q` a natural number. Let `D` be compact, such that each `x ∈ D` lies in `B` and has
an `n` with `(x * u * x⁻¹) ^ q ^ n ∈ A` for all `u ∈ J`. Let `W` be a property of points that forces
their `S`-orbit to meet `D`: if `W x` then `r * x ∈ D` for some `r ∈ S`. Then some finite set `T` of
cosets of `J` (a "cut") has three properties: (a) it is stable under `S ⊓ A`; (b) every `x` with
`x J ∈ T` lies in `B`; (c) whenever `x J ∈ T` or `W x`, the multiplicity
`coverMultiplicity S A T x`, the number of classes of `r ∈ S` modulo `S ⊓ A` with `r⁻¹ x J ∈ T`,
divides a power of `q`. -/
lemma exists_finset_coverMultiplicity_dvd_pow {S A J : Subgroup (Gf E ι)} [hA : IsLevel A]
    [hJ : IsLevel J]
    (hJA : J ≤ A) {D : Set (Gf E ι)} {q : ℕ} {B : Subgroup (Gf E ι)} (hD_compact : IsCompact D)
    {W : Gf E ι → Prop} (hAB : A ≤ B)
    (hD_mem_pow : ∀ x ∈ D, x ∈ B ∧ ∃ n : ℕ, ∀ u ∈ J, (x * u * x⁻¹) ^ q ^ n ∈ A)
    (hW_orbit : ∀ x : Gf E ι, W x → ∃ r ∈ S, r * x ∈ D) :
    ∃ T : Finset (Gf E ι ⧸ J),
      (∀ p : S, ↑p ∈ A → ∀ t : Gf E ι ⧸ J, t ∈ T ↔ p • t ∈ T) ∧
      (∀ ⦃x : Gf E ι⦄, ↑x ∈ T → x ∈ B) ∧
      ∀ x : Gf E ι, ↑x ∈ T ∨ W x → ∃ j : ℕ, coverMultiplicity S A T x ∣ q ^ j := by
  -- Let `C` be a set of representatives of the `S`-orbits that meet the image of `D` modulo `J`,
  -- and `T` its saturation under `S ⊓ A`. At a coset `x J` in `C` the multiplicity is the index of
  -- `Z ⊓ A` in its stabiliser `Z` in `S`, and `hD_mem_pow` makes it divide a power of `q`.
  obtain ⟨C, hC, h_reps⟩ : ∃ C ⊆ mk (s := J) '' D, BijOn (orbit S) C (orbit S '' (mk '' D)) :=
    exists_subset_bijOn (mk '' D) (orbit S)
  -- `T` is finite: it lies in the image of the compact set `A * D` modulo the open subgroup `J`.
  obtain ⟨T, mem_T⟩ : ∃ T : Finset (Gf E ι ⧸ J),
      ∀ t : Gf E ι ⧸ J, t ∈ T ↔ ∃ p : S, ↑p ∈ A ∧ p⁻¹ • t ∈ C := by
    refine Finite.exists_finset
      ((finite_quotient_image_of_isCompact hJ.isOpen (hA.isCompact.mul hD_compact)).subset ?_)
    intro t ⟨p, hp, hpt⟩
    obtain ⟨d, hd, hd_eq⟩ := hC hpt
    exact ⟨p * d, mul_mem_mul hp hd, eq_inv_smul_iff.1 hd_eq⟩
  refine ⟨T, fun p hp t ↦ ?_, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · -- Substitute `r ↦ p * r` in the description of `T`.
    rw [mem_T, mem_T]
    refine (Equiv.mulLeft p).exists_congr fun r ↦ ?_
    simp [mul_mem_cancel_left hp, mul_smul]
  · -- Here `x ∈ r * d * J` with `r ∈ A ≤ B`, `d ∈ D ⊆ B` and `J ≤ B`.
    obtain ⟨r, hr, hrx⟩ : ∃ r : S, ↑r ∈ A ∧ r⁻¹ • (x : Gf E ι ⧸ J) ∈ C := (mem_T x).1 hx
    obtain ⟨d, hd, hd_eq⟩ : ∃ d ∈ D, (d : Gf E ι ⧸ J) = ((r : Gf E ι)⁻¹ * x : Gf E ι) := hC hrx
    have h_mem : d⁻¹ * ((r : Gf E ι)⁻¹ * x) ∈ B := hAB (hJA (QuotientGroup.eq.1 hd_eq))
    exact (mul_mem_cancel_left (inv_mem (hAB hr))).1
      ((mul_mem_cancel_left (inv_mem (hD_mem_pow d hd).1)).1 h_mem)
  · -- In both cases `y` lies in the `S`-orbit of some `t ∈ C`.
    obtain ⟨t, ht, h_orbit⟩ : ∃ t ∈ C, orbit S t = orbit S (y : Gf E ι ⧸ J) := by
      rcases hy with hy | hy
      · obtain ⟨r, -, hr⟩ : ∃ r : S, ↑r ∈ A ∧ r⁻¹ • (y : Gf E ι ⧸ J) ∈ C := (mem_T y).1 hy
        exact ⟨r⁻¹ • y, hr, orbit_smul r⁻¹ _⟩
      · obtain ⟨r, hr, hry⟩ : ∃ r ∈ S, r * y ∈ D := hW_orbit y hy
        exact h_reps.surjOn
          ⟨↑(r * y), mem_image_of_mem _ hry, orbit_smul (⟨r, hr⟩ : S) (y : Gf E ι ⧸ J)⟩
    obtain ⟨r, hr⟩ : ∃ r : S, r • t = y := orbit_eq_iff.1 h_orbit.symm
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ D, (x : Gf E ι ⧸ J) = t := hC ht
    rw [← hr, coverMultiplicity_smul, coverMultiplicity_eq_index_stabilizer T h_reps.injOn mem_T ht]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ u ∈ J, (x * u * x⁻¹) ^ q ^ n ∈ A := (hD_mem_pow x hx).2
    exact exists_index_stabilizer_dvd_pow hJA hn

/-- Let `A` and `J` be levels in the finite adelic unitary group `Gf E ι`, let `η` be a left
invariant measure on the subgroup `S` giving `S ⊓ A` mass one, and let the finite set `T` of cosets
of `J` be stable under `S ⊓ A`. Let `m x = coverMultiplicity S A T x` be the number of classes of
`r ∈ S` modulo `S ⊓ A` with `r⁻¹ • x ∈ T`. The function equal to `1 / m` on `T` and zero off `T`,
evaluated at `u⁻¹ • t` and integrated over `u` in `S` against `η`, gives one if `m t ≠ 0` and zero
otherwise. -/
lemma lintegral_indicator_inv_coverMultiplicity {S A J : Subgroup (Gf E ι)} [hA : IsLevel A]
    [hJ : IsLevel J] {T : Finset (Gf E ι ⧸ J)} {η : Measure S} [IsMulLeftInvariant η]
    (hη : η (A.subgroupOf S) = 1)
    (hT : ∀ p : S, ↑p ∈ A → ∀ t : Gf E ι ⧸ J, t ∈ T ↔ p • t ∈ T) (t : Gf E ι ⧸ J) :
    ∫⁻ u : S, (indicator T (fun x : Gf E ι ⧸ J ↦ (coverMultiplicity S A T x : NNReal)⁻¹) (u⁻¹ • t) :
      NNReal) ∂η =
      {x : Gf E ι ⧸ J | coverMultiplicity S A T x ≠ 0}.indicator 1 t := by
  have : DiscreteTopology (Gf E ι ⧸ J) := discreteTopology hJ.isOpen
  set R : Set S := {u | u⁻¹ • t ∈ T}
  have hR_meas : MeasurableSet R := (T.finite_toSet.isClosed.preimage
    ((continuous_subtype_val.comp continuous_inv).smul continuous_const)).measurableSet
  -- The multiplicity is constant on the orbit of `t`, so the integrand is the constant
  -- `1 / coverMultiplicity S A T t` on `R` and zero off `R`.
  trans ((coverMultiplicity S A T t : NNReal)⁻¹ : NNReal) * η R
  · rw [← lintegral_indicator_const hR_meas]
    refine lintegral_congr fun u ↦ ?_
    by_cases hu : u⁻¹ • t ∈ T <;> simp [R, hu, coverMultiplicity_smul]
  by_cases h_ne : coverMultiplicity S A T t ≠ 0
  · -- `R` is a union of `coverMultiplicity S A T t` cosets of `S ⊓ A`, each of mass one.
    have hR_sat : R = QuotientGroup.mk (s := A.subgroupOf S) ⁻¹' (QuotientGroup.mk '' R) := by
      refine (subset_preimage_image _ R).antisymm fun r ⟨s, hs, hsr⟩ ↦ ?_
      have h_mem : r⁻¹ * s ∈ A.subgroupOf S := QuotientGroup.eq.mp hsr.symm
      simpa [R, mul_smul] using (hT (r⁻¹ * s) h_mem _).mp hs
    have hR_mass : η R = coverMultiplicity S A T t := by
      rw [hR_sat, measure_union_cosets hA.isOpen.preimage_val.measurableSet h_ne, hη, mul_one,
        coverMultiplicity]
    simp [hR_mass, h_ne, ENNReal.inv_mul_cancel]
  · simp [not_not.mp h_ne]

/-- Let `J` be a level in the finite adelic unitary group `Gf E ι` (an open subgroup of the group
`stdLevel E ι` of integral points, which has volume one), `T` a finite set of cosets of `J`, and
`c`, `b` functions on `Gf E ι ⧸ J`. The integral over `Gf E ι` of `c • b` cut off to `T` is its sum
over `T` divided by the index `stdLevelIndex J` of `J` in `stdLevel E ι`. -/
lemma integral_indicator_smul_quotient {J : Subgroup (Gf E ι)} [hJ : IsLevel J]
    (T : Finset (Gf E ι ⧸ J)) (c : Gf E ι ⧸ J → NNReal) (b : Gf E ι ⧸ J → ℂ) :
    ∫ g : Gf E ι, indicator T c (g : Gf E ι ⧸ J) • b g =
      (stdLevelIndex J : ℂ)⁻¹ * ∑ t ∈ T, c t * b t := by
  have : DiscreteTopology (Gf E ι ⧸ J) := discreteTopology hJ.isOpen
  have h_index : stdLevelIndex J ≠ 0 := isCompact_stdLevel.relIndex_ne_zero hJ.isOpen
  -- `stdLevel E ι` has volume one, so `J` has volume one over its index.
  have h_vol : volume (J : Set (Gf E ι)) = (↑(stdLevelIndex J))⁻¹ := by
    simpa [inter_eq_left.mpr hJ.le, stdLevelIndex] using
      measure_inter_eq_inv_relIndex (H := J) isCompact_stdLevel hJ.isOpen volume (by simp)
  -- Push forward to `Gf E ι ⧸ J`, where each point has mass `volume J`.
  set μ : Measure (Gf E ι ⧸ J) := volume.map QuotientGroup.mk with hμ
  have h_mass (t : Gf E ι ⧸ J) : μ {t} = (↑(stdLevelIndex J))⁻¹ := by
    simp [hμ, map_apply measurable_coe, measure_union_cosets hJ.isOpen.measurableSet, h_vol]
  have h_int : IntegrableOn (fun t : Gf E ι ⧸ J ↦ c t • b t) T μ := by
    rw [← biUnion_of_singleton (T : Set (Gf E ι ⧸ J))]
    exact (integrableOn_finite_biUnion T.finite_toSet).2 fun t _ ↦
      integrableOn_singleton (hx := by simp [h_mass, h_index.pos])
  calc
    _ = ∫ t : Gf E ι ⧸ J, indicator T c t • b t ∂μ :=
      (integral_map measurable_coe.aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))).symm
    _ = ∫ t in T, c t • b t ∂μ := by
      simp only [← indicator_smul_apply_left, integral_indicator T.measurableSet]
    _ = _ := by
      rw [setIntegral_finset _ h_int, T.mul_sum]
      simp [real_def, h_mass, NNReal.smul_def]

end Levels

section Bessel

variable {E ι X : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X]
  [DecidableEq X] {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} {Y : Grading V N X s}

omit [Fintype X] in
/-- Let `Y` be a grading of the hermitian space `V`, `Y.besselGroup` its Bessel subgroup of `G E ε`
with Haar measure `haar`, and `Y.besselFin` the group of `u ∈ Gf E ι` with `(1, u)` in
`Y.besselGroup`. Let `β` be measurable on `G E ε`, of integral one over each orbit of
`Y.besselGroup`, let `η` be a left invariant measure on `Y.besselFin`, and let `φ` be measurable on
`Gf E ι`. The integral of the weight `g ↦ (∫ u, β (g.1, u) ∂η) * φ g.2` over the orbit of `t` under
`Y.besselGroup` is the integral of `u ↦ φ (u⁻¹ * t.2)` against `η`. -/
lemma lintegral_besselGroup_cutoff_mul {β : G E ε → ENNReal} (hβ_meas : Measurable β)
    (hβ : ∀ g : G E ε, ∫⁻ r : Y.besselGroup, β (r * g) ∂haar = 1) (η : Measure Y.besselFin)
    [SFinite η] [IsMulLeftInvariant η] {φ : Gf E ι → ENNReal} (hφ : Measurable φ) (t : G E ε) :
    ∫⁻ r : Y.besselGroup, (∫⁻ u : Y.besselFin, β ((r * t : G E ε).1, u) ∂η) * φ (r * t : G E ε).2
        ∂haar =
      ∫⁻ u : Y.besselFin, φ ((u : Gf E ι)⁻¹ * t.2) ∂η :=
  -- Substitute `r ↦ (1, u⁻¹) * r`, then `u ↦ r.2 * u`: this moves `r` from `φ` to `β`, whose orbit
  -- integral is one.
  calc
    _ = ∫⁻ u : Y.besselFin, ∫⁻ r : Y.besselGroup,
        β ((r * t : G E ε).1, u) * φ (r * t : G E ε).2 ∂haar ∂η := by
      rw [← lintegral_lintegral_swap (by fun_prop)]
      exact lintegral_congr fun r ↦ (lintegral_mul_const _ (by fun_prop)).symm
    _ = ∫⁻ u : Y.besselFin, ∫⁻ r : Y.besselGroup,
        β ((r * t : G E ε).1, u) * φ ((u : Gf E ι)⁻¹ * (r * t : G E ε).2) ∂haar ∂η := by
      refine lintegral_congr fun ⟨u, hu⟩ ↦ ?_
      rw [← lintegral_mul_left_eq_self _ (⟨(1, u⁻¹), Y.besselFin.inv_mem hu⟩ : Y.besselGroup)]
      simp [mul_assoc]
    _ = ∫⁻ r : Y.besselGroup, ∫⁻ u : Y.besselFin,
        β (r * (t.1, (u : Gf E ι))) * φ ((u : Gf E ι)⁻¹ * t.2) ∂η ∂haar := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      refine lintegral_congr fun ⟨r, hr⟩ ↦ ?_
      rw [← lintegral_mul_left_eq_self _ (⟨r.2, Y.snd_mem_besselFin hr⟩ : Y.besselFin)]
      simp [mul_assoc, Prod.mul_def]
    _ = _ := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      refine lintegral_congr fun u ↦ ?_
      rw [lintegral_mul_const _ (by fun_prop), hβ, one_mul]

/-- Let `Y` be a grading of the hermitian space `V`, `Y.besselGroup` its Bessel subgroup of the
adelic unitary group `G E ε = GInf E ε × Gf E ι`, and `Y.ratBessel` the rational points of that
subgroup. Let `w` be a measurable weight on `G E ε` such that the integral of `r ↦ w (r * t)` over
`Y.besselGroup`, against its Haar measure `haar`, is one for `t` in the measurable set `U` and zero
otherwise. Let `f` vanish off `U` and be measurable, left invariant (`FixesLeft`) under
`Y.ratBessel` and integrable on the quotient of `G E ε` by it. Then the integral of `f` over this
quotient is the `w`-weighted integral over `t` of the period of `r ↦ f (r * t)` over `Y.besselGroup`
modulo `Y.ratBessel`. -/
lemma integral_quotMeasure_eq_integral_withDensity {w : G E ε → ENNReal} (hw : Measurable w)
    {U : Set (G E ε)} (hU : MeasurableSet U)
    (h_orbit : ∀ t : G E ε, ∫⁻ r : Y.besselGroup, w (r * t) ∂haar = U.indicator 1 t)
    {f : G E ε → ℂ} (hf_meas : Measurable f) (hf_rat : Y.ratBessel.FixesLeft f)
    (hf_int : Integrable f Y.ratBessel.quotMeasure) (hf_supp : ∀ g : G E ε, g ∉ U → f g = 0) :
    ∫ g : G E ε, f g ∂Y.ratBessel.quotMeasure =
      ∫ t : G E ε, ∫ r : Y.besselGroup, f (r * t) ∂Y.besselMeasure ∂volume.withDensity w := by
  -- The map `(t, r) ↦ r * t` carries the weighted measure times Haar measure to the measure on `U`.
  have h_push : MeasurePreserving (fun p : G E ε × Y.besselGroup ↦ (p.2 : G E ε) * p.1)
      ((volume.withDensity w).prod haar) (volume.restrict U) := by
    rw [← withDensity_indicator_one hU, ← funext h_orbit]
    simpa only [Measure.inv_eq_self, Subgroup.smul_def, smul_eq_mul] using
      measurePreserving_smul_prod (ν := (haar : Measure Y.besselGroup)) (μ := volume) hw
  have h_restrict :
      Y.ratBessel.quotMeasure.restrict U = Y.ratBessel.quotMeasure (volume.restrict U) :=
    restrict_withDensity' U _
  -- Unfold in stages along the inclusion of `Y.besselGroup`, with `h_push` as the fibration.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf_supp, h_restrict]
  refine (integral_quotMeasure_stages _ haar id Y.besselGroup.subtype_injective h_push
    (map_subgroupOf_eq_of_le inf_le_right) hf_meas hf_rat ?_).2
  simpa only [h_restrict] using hf_int.restrict (s := U)

/-- For a product weight `α g.1 * ψ g.2` on `G E ε = GInf E ε × Gf E ι`, the weighted integral of a
product function `a g.1 * b g.2` is the product of the weighted integrals over the two factors. -/
lemma integral_withDensity_mul_eq_mul {α : GInf E ε → ENNReal} (hα : Measurable α)
    {ψ : Gf E ι → NNReal} (hψ : Measurable ψ) (a : GInf E ε → ℂ) (b : Gf E ι → ℂ) :
    ∫ t : G E ε, a t.1 * b t.2 ∂volume.withDensity (fun g : G E ε ↦ α g.1 * ψ g.2) =
      (∫ g : GInf E ε, a g ∂volume.withDensity α) * ∫ g : Gf E ι, ψ g • b g := by
  rw [volume_eq_prod, ← prod_withDensity hα hψ.coe_nnreal_ennreal, integral_prod_mul,
    integral_withDensity_eq_integral_smul hψ]

/-- Let `Y` be a grading of the hermitian space `V`, with Bessel subgroup `Y.besselGroup` of
`G E ε`, finite part `Y.besselFin` and rational points `Y.ratBessel`. Given a level `A` and a
function `a` on `GInf E ε`, there is a constant `κ` with the following property. For every level
`J`, finite set `T ⊆ Gf E ι ⧸ J` (the "cut"), function `f` on `G E ε` and function `b` on
`Gf E ι ⧸ J`, the integral of `f` over the quotient of `G E ε` by `Y.ratBessel` is
`κ * ∑ t ∈ T, b t / m t`, where `m t = coverMultiplicity Y.besselFin A T t` counts the classes of
`r ∈ Y.besselFin` modulo `A` with `r⁻¹ • t ∈ T`, whenever:
* `hf_cont`, `hf_rat`, `hf_int`: `f` is continuous, left invariant under `Y.ratBessel` (`FixesLeft`)
  and integrable for `Y.ratBessel.quotMeasure`, the measure of integration over the quotient;
* `hT_stable`: `T` is stable under `Y.besselFin ⊓ A`;
* `hf_supp`: `m ≠ 0` at the finite part of each point where `f ≠ 0`;
* `h_period`: at each `t` with finite part in `T`, the integral of `r ↦ f (r * t)` over
  `Y.besselGroup` modulo `Y.ratBessel` is the index `stdLevelIndex J` of `J` in `stdLevel E ι` times
  `a t.1 * b t.2`. -/
lemma _root_.New.Grading.exists_integral_eq_sum_over_cut (A : Subgroup (Gf E ι)) [hA : IsLevel A]
    (a : GInf E ε → ℂ) :
    ∃ κ : ℂ, ∀ {J : Subgroup (Gf E ι)} [IsLevel J] {T : Finset (Gf E ι ⧸ J)} {f : G E ε → ℂ}
      (b : Gf E ι ⧸ J → ℂ) (_hf_cont : Continuous f) (_hf_rat : Y.ratBessel.FixesLeft f)
      (_hf_int : Integrable f Y.ratBessel.quotMeasure)
      (_hT_stable : ∀ p : Y.besselFin, ↑p ∈ A → ∀ t : Gf E ι ⧸ J, t ∈ T ↔ p • t ∈ T)
      (_hf_supp : ∀ g : G E ε, f g ≠ 0 → coverMultiplicity Y.besselFin A T g.2 ≠ 0)
      (_h_period : ∀ t : G E ε, ↑t.2 ∈ T → ∫ r : Y.besselGroup, f (r * t) ∂Y.besselMeasure =
        stdLevelIndex J * (a t.1 * b t.2)),
      ∫ g : G E ε, f g ∂Y.ratBessel.quotMeasure =
        κ * ∑ t ∈ T, (coverMultiplicity Y.besselFin A T t : ℂ)⁻¹ * b t := by
  -- From a cutoff `β` for `Y.besselGroup` acting on `G E ε` we build a weight `α g.1 * ψ g.2`
  -- whose integral over each orbit is `1` on `U = {coverMultiplicity ≠ 0}` and `0` off it.
  -- Unfolding in stages turns the integral into the weighted integral of the period; this
  -- factors, and the finite part is a sum over `T`.
  -- `η` is the Haar measure on `Y.besselFin` that gives `Y.besselFin ⊓ A` mass one.
  let K : TopologicalSpace.PositiveCompacts Y.besselFin :=
    ⟨⟨A.subgroupOf Y.besselFin, hA.isCompact.preimage_val⟩,
      ⟨1, hA.isOpen.preimage_val.interior_eq.ge A.one_mem⟩⟩
  let η : Measure Y.besselFin := haarMeasure K
  obtain ⟨β, hβ_meas, hβ⟩ : ∃ β : G E ε → ENNReal, Measurable β ∧
      ∀ g : G E ε, ∫⁻ r : Y.besselGroup, β (r * g) ∂haar = 1 :=
    (hasCutoff_of_proper : HasCutoff (haar : Measure Y.besselGroup) (G E ε)).out
  let α (g : GInf E ε) : ENNReal := ∫⁻ u : Y.besselFin, β (g, u) ∂η
  refine ⟨∫ g, a g ∂volume.withDensity α, ?_⟩
  intro J hJ T f b hf_cont hf_rat hf_int hT_stable hf_supp h_period
  have : DiscreteTopology (Gf E ι ⧸ J) := discreteTopology hJ.isOpen
  let ψ : Gf E ι ⧸ J → NNReal :=
    indicator T fun t ↦ (coverMultiplicity Y.besselFin A T t : NNReal)⁻¹
  have hψ_meas : Measurable fun g : Gf E ι ↦ ψ g := Continuous.measurable (by fun_prop)
  let w (g : G E ε) : ENNReal := α g.1 * ψ g.2
  have hw_meas : Measurable w := by fun_prop
  let U : Set (G E ε) := {g | coverMultiplicity Y.besselFin A T g.2 ≠ 0}
  have hU : MeasurableSet U := (isOpen_ne_fun (by fun_prop) continuous_const).measurableSet
  have h_orbit (t : G E ε) : ∫⁻ r : Y.besselGroup, w (r * t) ∂haar = U.indicator 1 t :=
    calc
      _ = ∫⁻ u : Y.besselFin, ψ (u⁻¹ • (t.2 : Gf E ι ⧸ J)) ∂η :=
        lintegral_besselGroup_cutoff_mul hβ_meas hβ η hψ_meas.coe_nnreal_ennreal t
      _ = _ := lintegral_indicator_inv_coverMultiplicity haarMeasure_self hT_stable t.2
  have h_index : stdLevelIndex J ≠ 0 := isCompact_stdLevel.relIndex_ne_zero hJ.isOpen
  have h_finite_part : ∫ g : Gf E ι, ψ g • b g = (stdLevelIndex J : ℂ)⁻¹ *
      ∑ t ∈ T, (coverMultiplicity Y.besselFin A T t : ℂ)⁻¹ * b t :=
    (integral_indicator_smul_quotient T _ b).trans (by simp)
  calc
    _ = ∫ t : G E ε, ∫ r : Y.besselGroup, f (r * t) ∂Y.besselMeasure ∂volume.withDensity w :=
      integral_quotMeasure_eq_integral_withDensity hw_meas hU h_orbit hf_cont.measurable hf_rat
        hf_int fun g hg ↦ not_imp_comm.1 (hf_supp g) hg
    -- The weight vanishes unless `t.2 ∈ T`, where `h_period` gives the period.
    _ = ∫ t : G E ε, (stdLevelIndex J : ℂ) * (a t.1 * b t.2) ∂volume.withDensity w := by
      refine integral_congr_ae ((ae_withDensity_iff hw_meas).2 (.of_forall fun t ht ↦ ?_))
      exact h_period t (by_contra fun h ↦ ht (by simp [w, ψ, h]))
    _ = stdLevelIndex J * ((∫ g, a g ∂volume.withDensity α) * ∫ g : Gf E ι, ψ g • b g) := by
      rw [integral_const_mul, integral_withDensity_mul_eq_mul (by fun_prop) hψ_meas a fun g ↦ b g]
    _ = _ := by
      rw [h_finite_part]
      field_simp

end Bessel

end New.Seesaw

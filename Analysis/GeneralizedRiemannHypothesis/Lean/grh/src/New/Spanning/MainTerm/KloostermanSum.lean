import New.Spanning.Frames.BesselVector

/-!
# The orbital integral at the finite places is a Kloosterman sum

Let `𝖴` be the unipotent group `New.Shape.Form.besselU` over a finite place, or a product of finite
places, let `K(M)` be the principal congruence subgroup of a level `M`, and let `ψ_𝖴` be the
character of `𝖴`. The finite Bessel function `χ` is `ψ_𝖴(u)` on `u K(M)` and zero off `𝖴 K(M)`.

* `New.Floors.PlaceData.kloostermanSum`: the sum of `ψ_𝖴(u) conj ψ_𝖴(u')` over the pairs `u`, `u'`
  in `𝖴 / (𝖴 ∩ K(M))` with `u⁻¹ x u' ∈ s K(M)`.
* `New.Floors.IntegralPlace.IsLargeLatticeData.besselOrbitalIntegral_besselVector_apply`: the entry
  `(a, b)` of the orbital integral of the finite Bessel vector at `x` is the volume of `K(M)` times
  the Kloosterman sum of `x` at `s = a b⁻¹`.

Notions from other files:
* `New.Shape.Form.splitGram`: the Gram matrix of `𝔰.ϱ` hyperbolic planes and a middle space with
  Gram matrix `T`. The group `T.G` is its unitary group.
* `New.Floors.PlaceData ι T (m + 1)`: the data of a place. They include the level `M = F.levelUnit`
  and a basis of the middle space made of `m + 2` hyperbolic pairs and orthonormal vectors indexed
  by `ι`.
* `New.Floors.IntegralPlace.IsLargeLatticeData`: these data come from the lattice of vectors
  integral over `P.integers`, with conditions on the rank, the character of the place and the group.
* `New.Floors.IntegralPlace.extendedBesselChar`: the finite Bessel function `χ`.
* `New.Floors.PlaceData.IntermediateGroup.besselVector`: for a group `Z` between `K(M)` and the
  integral points, the vector of the translates of `χ` by the cosets of `K(M)` in `Z`.
* `New.besselOrbitalIntegral μ W x`: the orbital integral of `W(y) ⊗ W(x⁻¹ y)^*` over `y`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

open MeasureTheory Measure Function

/-- Let `μ` be a left invariant measure on a group `G` and `J` an open subgroup of finite volume.
The integral of a function on the cosets `y J` is the volume of `J` times its sum over the cosets.
If the sum does not converge, both sides are zero. -/
lemma New.integral_comp_quotientMk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] {J : Subgroup G} (hJ : IsOpen (J : Set G)) (_h_fin : μ J ≠ ⊤)
    (f : G ⧸ J → ℂ) : ∫ y : G, f y ∂μ = μ.real J • ∑' q : G ⧸ J, f q := by
  -- The image of `μ` on the countable discrete quotient is `μ J` times the counting measure.
  have : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJ
  have : Countable (G ⧸ J) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let : MeasurableSpace (G ⧸ J) := ⊤
  have h_meas : Measurable (QuotientGroup.mk : G → G ⧸ J) := fun s _ ↦
    ((isOpen_discrete s).preimage QuotientGroup.continuous_mk).measurableSet
  have h_map : μ.map QuotientGroup.mk = μ J • (count : Measure (G ⧸ J)) := by
    refine ext_of_singleton fun q ↦ ?_
    obtain ⟨a : G, rfl⟩ := QuotientGroup.mk_surjective q
    have h_coset : QuotientGroup.mk ⁻¹' {(a : G ⧸ J)} = (fun y : G ↦ a⁻¹ * y) ⁻¹' J :=
      Set.ext fun y ↦ by simp [eq_comm (b := (a : G ⧸ J)), QuotientGroup.eq]
    simp [map_apply h_meas (measurableSet_singleton _), h_coset]
  have h_count : ∫ q : G ⧸ J, f q ∂count = ∑' q : G ⧸ J, f q := by
    by_cases hf : Integrable f count
    · simp [integral_countable hf]
    · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
      rwa [← summable_norm_iff, ← integrable_count_iff]
  rw [← integral_map h_meas.aemeasurable measurable_from_top.aestronglyMeasurable, h_map,
    integral_smul_measure, h_count, Measure.real]

lemma New.inv_mul_out_coe_mem {G : Type*} [Group G] (J : Subgroup G) (y : G) :
    y⁻¹ * (y : G ⧸ J).out ∈ J :=
  QuotientGroup.eq.1 (y : G ⧸ J).out_eq'.symm

namespace New.Floors

open IntegralPlace PlaceData

variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype ι]
  [DecidableEq ι] {m : ℕ} {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] (F : PlaceData ι T (m + 1))

/-- The cosets `u (𝖴 ∩ K(M))` in the unipotent group `𝖴 = T.besselU`, where
`K(M) = F.congruenceSubgroup` is the principal congruence subgroup of the place data `F`. In the
type of `F`, `ι` and `m + 1` give the shape of the basis of the middle space in `F`: `m + 2`
hyperbolic pairs and orthonormal vectors indexed by `ι`. -/
abbrev PlaceData.UnipotentCosets : Type := T.besselU ⧸ F.congruenceSubgroup.subgroupOf T.besselU

open scoped Classical in
/-- The Kloosterman sum of `x` at `s`: the sum of `χ(u) conj χ(u')` over the pairs of cosets
`u`, `u'` in `𝖴 / (𝖴 ∩ K(M))` with `u⁻¹ x u' ∈ s K(M)`, each coset being read through its chosen
representative. Here `𝖴 = T.besselU` is the Bessel unipotent group, `K(M) = F.congruenceSubgroup` is
the principal congruence subgroup of level `M = F.levelUnit`, and
`χ = extendedBesselChar F.levelUnit` is the finite Bessel function, which on `𝖴` is the character
`ψ_𝖴`. -/
def PlaceData.kloostermanSum (x s : T.G) : ℂ :=
  ∑' w : F.UnipotentCosets × F.UnipotentCosets,
    if s⁻¹ * ((w.1.out : T.G)⁻¹ * x * (w.2.out : T.G)) ∈ F.congruenceSubgroup then
      extendedBesselChar F.levelUnit (w.1.out : T.G) * star
        (extendedBesselChar F.levelUnit (w.2.out : T.G))
    else 0

variable {F}

lemma PlaceData.inv_mul_out_mem (u : T.besselU) :
    (u : T.G)⁻¹ * ((u : F.UnipotentCosets).out : T.G) ∈ F.congruenceSubgroup :=
  Subgroup.mem_subgroupOf.1 (inv_mul_out_coe_mem (F.congruenceSubgroup.subgroupOf T.besselU) u)

/-- Let `𝖴 = T.besselU` be the Bessel unipotent group (the block upper unitriangular elements of the
unitary group `T.G`) and `K(M) = F.congruenceSubgroup` the principal congruence subgroup of level
`M = F.levelUnit`. Two cosets in `F.UnipotentCosets = 𝖴 / (𝖴 ∩ K(M))` whose chosen representatives
lie in one left coset of `K(M)` in `T.G` are equal. -/
lemma PlaceData.unipotentCosets_eq_of_inv_mul_mem {w w' : F.UnipotentCosets}
    (h_mem : (w.out : T.G)⁻¹ * (w'.out : T.G) ∈ F.congruenceSubgroup) : w = w' := by
  rwa [← w.out_eq', ← w'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]

/-- Let `𝖴 = T.besselU` be the Bessel unipotent group and `K(M) = F.congruenceSubgroup` the
principal congruence subgroup of level `M = F.levelUnit`. If `y ∈ 𝖴 K(M)`, then `y ∈ w K(M)` for the
chosen representative `w` of some coset in `F.UnipotentCosets = 𝖴 / (𝖴 ∩ K(M))`. -/
lemma PlaceData.exists_out_inv_mul_mem {y : T.G}
    (hy : ∃ u ∈ T.besselU, u⁻¹ * y ∈ F.congruenceSubgroup) :
    ∃ w : F.UnipotentCosets, (w.out : T.G)⁻¹ * y ∈ F.congruenceSubgroup := by
  obtain ⟨u, hu, huy⟩ := hy
  exact ⟨(⟨u, hu⟩ : T.besselU),
    by simpa [mul_assoc] using mul_mem (inv_mem (inv_mul_out_mem ⟨u, hu⟩)) huy⟩

/-- An integral point `s` of the unitary group normalises `K(M) = F.congruenceSubgroup`, so the
cosets `s K(M)` and `K(M) s` agree. -/
lemma PlaceData.inv_mul_mem_congruenceSubgroup_iff {s z : T.G}
    (hs : s ∈ unitaryLevel P.integers 1 T.splitGram) :
    s⁻¹ * z ∈ F.congruenceSubgroup ↔ z * s⁻¹ ∈ F.congruenceSubgroup :=
  ⟨fun h ↦ by simpa [mul_assoc] using conj_mem_unitaryLevel hs h,
    fun h ↦ by simpa [mul_assoc] using conj_mem_unitaryLevel (inv_mem hs) h⟩

/-- If `s⁻¹ a b⁻¹` lies in `K(M) = F.congruenceSubgroup` and `a`, `b` are integral points of the
unitary group, then `s` is an integral point. -/
lemma PlaceData.mem_unitaryLevel_one_of_inv_mul_mul_inv_mem {s a b : T.G}
    (ha : a ∈ unitaryLevel P.integers 1 T.splitGram)
    (hb : b ∈ unitaryLevel P.integers 1 T.splitGram)
    (hab : s⁻¹ * a * b⁻¹ ∈ F.congruenceSubgroup) : s ∈ unitaryLevel P.integers 1 T.splitGram := by
  simpa [mul_assoc] using
    mul_mem (mul_mem ha (inv_mem hb)) (inv_mem (unitaryLevel_le_unitaryLevel_one hab))

omit [IsHermitianUnit T.splitGram] in
/-- For a unit `g` let `K(g)` be the subgroup of points integral over `P.integers` and congruent to
`1` modulo `g`, and let `𝖴 = T.besselU` be the Bessel unipotent group. The finite Bessel function
`extendedBesselChar g` is zero off `𝖴 K(g)`; at a point of `𝖴 K(g)`, written as `u k` with a chosen
`u` in `𝖴`, its value is `ψ(σ(u) / g)`, where `ψ = P.ψ` is the additive character of the place and
`σ(u)` is the sum of the entries of `u` at the simple roots. It takes the same value at two points
of a coset `y K(g)`. -/
lemma IntegralPlace.extendedBesselChar_eq_of_inv_mul_mem {g : Aˣ} {y z : T.G}
    (hyz : y⁻¹ * z ∈ unitaryLevel P.integers g T.splitGram) :
      extendedBesselChar g z = extendedBesselChar g y := by
  rw [← extendedBesselChar_mul_of_mem_unitaryLevel (y := y) hyz, mul_inv_cancel_left]

/-- Let `F` be place data for `T` at the finite place `P`, with level `M = F.levelUnit`, principal
congruence subgroup `K(M) = F.congruenceSubgroup` and finite Bessel function
`χ = extendedBesselChar F.levelUnit`. Let `x` be a point of `T.G` and `s` an integral point. Then
the sum of `χ(y s⁻¹) conj χ(x⁻¹ y)` over the cosets `y K(M)`, with `y` the chosen representative, is
the Kloosterman sum of `x` at `s`: the sum of `χ(u) conj χ(u')` over the pairs `u`, `u'` in
`𝖴 / (𝖴 ∩ K(M))` with `u⁻¹ x u' ∈ s K(M)`. -/
lemma PlaceData.tsum_extendedBesselChar_mul_star_extendedBesselChar {F : PlaceData ι T (m + 1)}
    (x : T.G) {s : T.G} (hs : s ∈ unitaryLevel P.integers 1 T.splitGram) :
    ∑' q : T.G ⧸ F.congruenceSubgroup, extendedBesselChar F.levelUnit (q.out * s⁻¹) * star
      (extendedBesselChar F.levelUnit (x⁻¹ * q.out)) =
      F.kloostermanSum x s := by
  classical
  -- A term is zero unless `y K(M) = u s K(M) = x u' K(M)` with `u`, `u'` in `𝖴`. These are unique
  -- modulo `𝖴 ∩ K(M)`, and the value is `ψ_𝖴(u) conj ψ_𝖴(u')`. So `(u, u') ↦ x u' K(M)` is a
  -- bijection between the supports of the two sums that preserves the terms.
  refine tsum_eq_tsum_of_ne_zero_bij (fun w ↦ (x * (w.val.2.out : T.G) : T.G)) ?_ ?_ ?_
  · -- The map is injective.
    rintro ⟨⟨w₁, w₁'⟩, hw₁⟩ ⟨⟨w₂, w₂'⟩, hw₂⟩ h_eq
    obtain rfl : w₁' = w₂' :=
      unipotentCosets_eq_of_inv_mul_mem (by simpa [mul_assoc] using QuotientGroup.eq.1 h_eq)
    -- Both `w₁⁻¹ x w₁' s⁻¹` and `w₂⁻¹ x w₁' s⁻¹` lie in `K(M)`.
    simp only [mem_support, ite_ne_right_iff, inv_mul_mem_congruenceSubgroup_iff hs] at hw₁ hw₂
    obtain rfl : w₁ = w₂ :=
      unipotentCosets_eq_of_inv_mul_mem (by simpa [mul_assoc] using mul_mem hw₁.1 (inv_mem hw₂.1))
    rfl
  · -- Every coset with a nonzero term is in the image.
    intro q hq
    obtain ⟨w, h_left : (w.out : T.G)⁻¹ * (q.out * s⁻¹) ∈ F.congruenceSubgroup⟩ :=
      exists_out_inv_mul_mem (exists_besselU_of_extendedBesselChar_ne_zero (left_ne_zero_of_mul hq))
    obtain ⟨w', h_right : (w'.out : T.G)⁻¹ * (x⁻¹ * q.out) ∈ F.congruenceSubgroup⟩ :=
      exists_out_inv_mul_mem
        (exists_besselU_of_extendedBesselChar_ne_zero (star_ne_zero.1 (right_ne_zero_of_mul hq)))
    have h_cond : s⁻¹ * ((w.out : T.G)⁻¹ * x * (w'.out : T.G)) ∈ F.congruenceSubgroup := by
      rw [← mul_assoc, ← inv_mul_mem_congruenceSubgroup_iff hs] at h_left
      simpa [mul_assoc] using mul_mem h_left (inv_mem h_right)
    have h_coset : ((x * (w'.out : T.G) : T.G) : T.G ⧸ F.congruenceSubgroup) = q :=
      (QuotientGroup.eq.2 (by simpa [mul_assoc] using h_right)).trans q.out_eq'
    refine ⟨⟨(w, w'), ?_⟩, h_coset⟩
    rwa [mem_support, ite_eq_left h_cond, ← extendedBesselChar_eq_of_inv_mul_mem h_left,
      ← extendedBesselChar_eq_of_inv_mul_mem h_right]
  · -- The terms agree.
    rintro ⟨⟨w, w'⟩, hw⟩
    have h_cond : s⁻¹ * ((w.out : T.G)⁻¹ * x * (w'.out : T.G)) ∈ F.congruenceSubgroup :=
      (ite_ne_right_iff.1 hw).1
    let y : T.G := ((x * (w'.out : T.G) : T.G) : T.G ⧸ F.congruenceSubgroup).out
    have h_right : (w'.out : T.G)⁻¹ * (x⁻¹ * y) ∈ F.congruenceSubgroup := by
      simpa [mul_assoc] using inv_mul_out_coe_mem F.congruenceSubgroup (x * (w'.out : T.G))
    have h_left : (w.out : T.G)⁻¹ * (y * s⁻¹) ∈ F.congruenceSubgroup := by
      rw [← mul_assoc, ← inv_mul_mem_congruenceSubgroup_iff hs]
      simpa [mul_assoc] using mul_mem h_cond h_right
    rw [ite_eq_left h_cond, extendedBesselChar_eq_of_inv_mul_mem h_left,
      extendedBesselChar_eq_of_inv_mul_mem h_right]

/-- Assume `P.IsLargeLatticeData F`, which says, with `R = P.integers`, that: the form is unimodular
over `R`, and the basis and the level `M = F.levelUnit` are integral;
* the compact set, the close pairs, the positions and the measures of `F` are those given by the
lattice of integral vectors, and some isotropic vector is dual to the last frame vector;
* the rank is large: `ζ_R(m) ^ 𝔰.n ≤ 1 + 2⁻¹ ^ 𝔰.n` for the ideal zeta function `ζ_R`,
`m < 9 * 𝔰.n`, and `ι` has at least `53 * 𝔰.n` elements;
* the character of the place is trivial on traces, and the unitary group `T.G` is unimodular.

Then `μ = F.groupMeasure`, the measure on `T.G` built from `F`, is a Haar measure. Let `Z` be a
group between the principal congruence subgroup `K(M) = F.congruenceSubgroup` and the integral
points, and `a`, `b` cosets of `K(M)` in `Z` whose representatives satisfy `a b⁻¹ ∈ s K(M)`. Let `W`
be the Bessel vector of `Z`, with coordinates `W_a(y) = χ(y a⁻¹)` for the finite Bessel function
`χ = extendedBesselChar F.levelUnit`. Then `∫ W_a(y) conj W_b(x⁻¹ y) dμ(y)` is `μ(K(M))` times the
Kloosterman sum of `x` at `s`. -/
theorem IntegralPlace.IsLargeLatticeData.besselOrbitalIntegral_besselVector_apply
    [hF : P.IsLargeLatticeData F] (Z : F.IntermediateGroup) (x : T.G) {s : T.G} {a b : Z.Cosets}
    (hab : s⁻¹ * (a.out : T.G) * (b.out : T.G)⁻¹ ∈ F.congruenceSubgroup) :
    besselOrbitalIntegral F.groupMeasure Z.besselVector x (a, b) =
      F.groupMeasure.real F.congruenceSubgroup • F.kloostermanSum x s := by
  have hZ : (Z : Subgroup T.G) ≤ unitaryLevel P.integers 1 T.splitGram := Z.property.2
  have hs : s ∈ unitaryLevel P.integers 1 T.splitGram :=
    mem_unitaryLevel_one_of_inv_mul_mul_inv_mem (hZ a.out.property) (hZ b.out.property) hab
  -- Put `y b` for `y`. The integrand is then constant on the cosets `y K(M)`.
  let Φ (q : T.G ⧸ F.congruenceSubgroup) : ℂ := extendedBesselChar F.levelUnit (q.out * s⁻¹) * star
    (extendedBesselChar F.levelUnit (x⁻¹ * q.out))
  have h_coset (y : T.G) :
      extendedBesselChar F.levelUnit (y * (b.out : T.G) * (a.out : T.G)⁻¹) * star
        (extendedBesselChar F.levelUnit (x⁻¹ * y)) = Φ y := by
    let z : T.G := (y : T.G ⧸ F.congruenceSubgroup).out
    have hz : y⁻¹ * z ∈ F.congruenceSubgroup := inv_mul_out_coe_mem _ y
    have h_first : (y * (b.out : T.G) * (a.out : T.G)⁻¹)⁻¹ * (z * s⁻¹) ∈ F.congruenceSubgroup := by
      simpa [mul_assoc] using conj_mem_unitaryLevel hs (mul_mem hab hz)
    have h_second : (x⁻¹ * y)⁻¹ * (x⁻¹ * z) ∈ F.congruenceSubgroup := by simpa [mul_assoc] using hz
    rw [← extendedBesselChar_eq_of_inv_mul_mem h_first,
      ← extendedBesselChar_eq_of_inv_mul_mem h_second]
  have h_open : IsOpen (F.congruenceSubgroup : Set T.G) := unitaryLevel_open_compact.1
  have h_fin : F.groupMeasure F.congruenceSubgroup ≠ ⊤ :=
    groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one
  calc
    _ = ∫ y : T.G, extendedBesselChar F.levelUnit (y * (a.out : T.G)⁻¹) *
          star (extendedBesselChar F.levelUnit (x⁻¹ * y * (b.out : T.G)⁻¹)) ∂F.groupMeasure := by
      simp [besselOrbitalIntegral, IntermediateGroup.besselVector]
    _ = ∫ y : T.G, extendedBesselChar F.levelUnit (y * (b.out : T.G) * (a.out : T.G)⁻¹) *
          star (extendedBesselChar F.levelUnit (x⁻¹ * y)) ∂F.groupMeasure := by
      rw [← integral_mul_right_eq_self _ (b.out : T.G)]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    _ = ∫ y : T.G, Φ y ∂F.groupMeasure := by simp only [h_coset]
    _ = F.groupMeasure.real F.congruenceSubgroup • ∑' q : T.G ⧸ F.congruenceSubgroup, Φ q :=
      integral_comp_quotientMk F.groupMeasure h_open h_fin Φ
    _ = _ := by rw [tsum_extendedBesselChar_mul_star_extendedBesselChar x hs]

end New.Floors

end

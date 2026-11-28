import New.Spanning.Frames.Densities
import New.Spanning.Frames.StandardLevel

/-!
# The Bessel vector at the finite places

Let `A` collect finitely many finite places, with integers `R` and character `ψ`, and let `F` be a
large lattice datum of modulus `g` for the unitary group `T.G`. Write `𝖴 = T.besselU`, `K(g)` for
the principal congruence subgroup and `K = K(1)`, and let `K(g) ≤ Z ≤ K`. This file constructs a cut
Bessel function from the translates of the Bessel character by the cosets of `K(g)` in `Z`, and
computes its correlations and norms.

## Main definitions and results

* `New.Floors.IntegralPlace.extendedBesselChar`: the Bessel character of `𝖴`, extended to `𝖴 K(g)`
  and by zero outside it.
* `New.Floors.PlaceData.IntermediateGroup.besselVector`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.isCut_besselVector`: the vector of its translates by
  the cosets of `K(g)` in `Z`; it is a cut Bessel function.
* `New.Floors.IntegralPlace.IsLargeLatticeData.unipotentMass_mul_inner_besselVector`: its
  correlations as integrals over `𝖴` of the extended character, cut off by `Z`.
* `New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_enorm_sq_besselVector`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.pairingNormSq_mul_le_massRatio`: its norms.

Notions from other files:
* `New.Shape.Form.besselU`: the Bessel unipotent group `𝖴` of the block upper unitriangular
  isometries of `T.splitGram`.
* `New.simpleRootSum`: the sum `σ(s)` of the entries of `s` just above the diagonal of its block on
  the frame vectors.
* `New.unitaryLevel`: `unitaryLevel R g J` is the group `K(g)` of integral isometries of `J` that
  are congruent to `1` modulo the unit `g`.
* `New.Floors.PlaceData`: the data `F` of a place, among them the modulus `F.levelUnit`, the compact
  set `F.boxSet` and the measures whose product over all floors is `F.groupMeasure`.
* `New.Floors.PlaceData.IsCut`: a Bessel function of frequency `F.levelUnit⁻¹` that vanishes off the
  translates of `F.boxSet` by `𝖴`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Fintype FloorGroups InnerProductSpace Subgroup
  IntegralPlace Place Set PlaceData Size SemilocalField QuotientGroup Finset

variable {A ι : Type} {𝔰 : Shape} [SemilocalField A] [StarRing A] [P : IntegralPlace A]
  [Fintype ι] [DecidableEq ι] {m : ℕ} {T : 𝔰.Form A}

section Phase

open scoped Classical in
/-- The function χ_g on the unitary group: equal to ψ(σ(u) / g) on u K(g) for `u` in the Bessel
unipotent group 𝖴 = `besselU`, and to 0 off 𝖴 K(g). Here ψ is the character of the place,
σ = `simpleRootSum` is the sum of the entries at the simple roots, and K(g) is the principal
congruence subgroup of level `g`. The value does not depend on the chosen `u`: see
`extendedBesselChar_eq`. -/
def IntegralPlace.extendedBesselChar (g : Aˣ) (z : T.G) : ℂ :=
  if h : ∃ u ∈ T.besselU, u⁻¹ * z ∈ unitaryLevel integers g T.splitGram then
    P.ψ (g⁻¹.val * simpleRootSum h.choose)
  else
    0

/-- The function χ_g = `extendedBesselChar g` vanishes off 𝖴 K(g), the product of the Bessel
unipotent group and the principal congruence subgroup of level `g`. -/
theorem IntegralPlace.extendedBesselChar_eq_zero {y : T.G} {g : Aˣ}
    (hy : ¬∃ u ∈ T.besselU, u⁻¹ * y ∈ unitaryLevel integers g T.splitGram) :
      extendedBesselChar g y = 0 :=
  dite_eq_right hy

/-- A point where χ_g = `extendedBesselChar g` does not vanish lies in 𝖴 K(g), the product of the
Bessel unipotent group and the principal congruence subgroup of level `g`. -/
theorem IntegralPlace.exists_besselU_of_extendedBesselChar_ne_zero {y : T.G} {g : Aˣ}
    (hy : extendedBesselChar g y ≠ 0) :
    ∃ u ∈ T.besselU, u⁻¹ * y ∈ unitaryLevel integers g T.splitGram :=
  by_contra fun h_none ↦ hy (extendedBesselChar_eq_zero h_none)

/-- The values of χ_g = `extendedBesselChar g` have absolute value at most 1. -/
theorem IntegralPlace.norm_extendedBesselChar_le_one {y : T.G} {g : Aˣ} :
    ‖extendedBesselChar g y‖ ≤ 1 := by
  fun_cases extendedBesselChar
  · exact (P.norm_psi _).le
  · simp

/-- If `y` lies in u K(g), with `u` in the Bessel unipotent group and K(g) the principal congruence
subgroup, then χ_g = `extendedBesselChar g` has the value ψ(σ(u) / g) at `y`, where σ =
`simpleRootSum`. -/
lemma IntegralPlace.extendedBesselChar_eq {y u : T.G} {g : Aˣ} (hu : u ∈ T.besselU)
    (huy : u⁻¹ * y ∈ unitaryLevel integers g T.splitGram) :
    extendedBesselChar g y = P.ψ (g⁻¹.val * simpleRootSum u) := by
  -- `extendedBesselChar` is defined with a chosen `v` in place of `u`; the two differ by an element
  -- of K(g).
  have hex : ∃ v ∈ T.besselU, v⁻¹ * y ∈ unitaryLevel integers g T.splitGram := ⟨u, hu, huy⟩
  rw [extendedBesselChar, dite_eq_left hex]
  set v : T.G := hex.choose
  obtain ⟨hv, hvy⟩ : v ∈ T.besselU ∧ v⁻¹ * y ∈ unitaryLevel integers g T.splitGram :=
    hex.choose_spec
  have h_lev : v⁻¹ * u ∈ unitaryLevel integers g T.splitGram := by
    simpa using mul_mem hvy (inv_mem huy)
  -- The character `ψ` is trivial on the integers, which are self-dual.
  have h_int : g⁻¹.val * simpleRootSum (v⁻¹ * u) ∈ integers := inv_mul_simpleRootSum_mem h_lev
  have h_triv : P.ψ (g⁻¹.val * simpleRootSum (v⁻¹ * u)) = 1 := by
    simpa using (self_dual _).2 h_int 1 (one_mem _)
  have h_add : simpleRootSum u = simpleRootSum v + simpleRootSum (v⁻¹ * u) := by
    rw [← simpleRootSum_mul (mem_partialUnitriangularGroup_of_mem_besselU hv)
      (mem_partialUnitriangularGroup_of_mem_besselU (mul_mem (inv_mem hv) hu)), mul_inv_cancel_left]
  rw [h_add, mul_add, P.ψ.map_add_eq_mul, h_triv, mul_one]

/-- Let `x` lie in the Bessel subgroup `besselS`, which contains and normalises the Bessel unipotent
group 𝖴, and in u K(g), with `u` in 𝖴 and K(g) the principal congruence subgroup. Then left
translation by `x` multiplies χ_g = `extendedBesselChar g` by ψ(σ(u) / g). -/
theorem IntegralPlace.extendedBesselChar_besselS_mul {x y u : T.G} {g : Aˣ} (hx : x ∈ T.besselS)
    (hu : u ∈ T.besselU) (hux : u⁻¹ * x ∈ unitaryLevel integers g T.splitGram) :
    extendedBesselChar g (x * y) = P.ψ (g⁻¹.val * simpleRootSum u) * extendedBesselChar g y := by
  -- `x` normalises `besselU`, so `y ∈ v K(g)` gives `x * y ∈ (x * v * x⁻¹ * u) K(g)`, and
  -- conversely.
  by_cases hy : ∃ v ∈ T.besselU, v⁻¹ * y ∈ unitaryLevel integers g T.splitGram
  · obtain ⟨v, hv, hvy⟩ := hy
    have h_conj : x * v * x⁻¹ ∈ T.besselU := (besselS_le_normalizer_besselU hx v).1 hv
    have h_lev : (x * v * x⁻¹ * u)⁻¹ * (x * y) ∈ unitaryLevel integers g T.splitGram := by
      simpa [mul_assoc] using mul_mem hux hvy
    -- `simpleRootSum` is additive on `besselS`, hence unchanged by conjugation.
    have hvS : v ∈ T.besselS := mem_partialUnitriangularGroup_of_mem_besselU hv
    have h_inv : simpleRootSum (x * v * x⁻¹) = simpleRootSum v := by
      apply add_right_cancel (b := simpleRootSum x)
      rw [← simpleRootSum_mul (mul_mem (mul_mem hx hvS) (inv_mem hx)) hx, inv_mul_cancel_right,
        simpleRootSum_mul hx hvS, add_comm]
    have h_add : simpleRootSum (x * v * x⁻¹ * u) = simpleRootSum u + simpleRootSum v := by
      rw [simpleRootSum_mul (mem_partialUnitriangularGroup_of_mem_besselU h_conj)
        (mem_partialUnitriangularGroup_of_mem_besselU hu), h_inv, add_comm]
    rw [extendedBesselChar_eq (mul_mem h_conj hu) h_lev, extendedBesselChar_eq hv hvy, h_add,
      mul_add, P.ψ.map_add_eq_mul]
  · have hxy : ¬∃ v ∈ T.besselU, v⁻¹ * (x * y) ∈ unitaryLevel integers g T.splitGram := by
      rintro ⟨v, hv, hvxy⟩
      refine hy ⟨x⁻¹ * (v * u⁻¹) * x, ?_, ?_⟩
      · simpa using (besselS_le_normalizer_besselU (inv_mem hx) _).1 (mul_mem hv (inv_mem hu))
      · simpa [mul_assoc] using mul_mem (inv_mem hux) hvxy
    rw [extendedBesselChar_eq_zero hy, extendedBesselChar_eq_zero hxy, mul_zero]

/-- The function χ_g = `extendedBesselChar g` is invariant under right translation by the principal
congruence subgroup K(g). -/
theorem IntegralPlace.extendedBesselChar_mul_of_mem_unitaryLevel {y k : T.G} {g : Aˣ}
    (hk : k ∈ unitaryLevel integers g T.splitGram) :
      extendedBesselChar g (y * k) = extendedBesselChar g y := by
  classical
  simp only [extendedBesselChar, ← mul_assoc, mul_mem_cancel_right hk]

/-- Left translation by an element `u` of the Bessel unipotent group multiplies χ_g =
`extendedBesselChar g` by ψ(σ(u) / g), where ψ is the character of the place and σ =
`simpleRootSum`. -/
theorem IntegralPlace.extendedBesselChar_besselU_mul {y u : T.G} {g : Aˣ} (hu : u ∈ T.besselU) :
    extendedBesselChar g (u * y) = P.ψ (g⁻¹.val * simpleRootSum u) * extendedBesselChar g y :=
  extendedBesselChar_besselS_mul (mem_partialUnitriangularGroup_of_mem_besselU hu) hu (by simp)

/-- The function χ_g = `extendedBesselChar g`, the Bessel character extended to 𝖴 K(g) and by zero
outside it, is continuous. -/
@[fun_prop]
theorem IntegralPlace.continuous_extendedBesselChar {g : Aˣ} :
    Continuous (extendedBesselChar (T := T) g) := by
  -- `extendedBesselChar g` is fixed by right translation by the open subgroup K(g), so it is
  -- locally constant.
  have h_fix : ∀ᶠ k : T.G in nhds 1, ∀ y : T.G,
    extendedBesselChar g (y * k) = extendedBesselChar g y := by
    filter_upwards [unitaryLevel_open_compact.1.mem_nhds (one_mem _)] with k hk y
    exact extendedBesselChar_mul_of_mem_unitaryLevel hk
  exact (isLocallyConstant_of_eventually_mul h_fix).continuous

/-- The principal congruence subgroup K(g) = `unitaryLevel integers g T.splitGram` of level `g` lies
in the integral unitary group K(1) = `unitaryLevel integers 1 T.splitGram`. -/
theorem IntegralPlace.unitaryLevel_le_unitaryLevel_one {g : Aˣ} :
    unitaryLevel integers g T.splitGram ≤ unitaryLevel integers 1 T.splitGram := by
  rintro k ⟨hk_int, -⟩
  rw [unitaryLevel_one]
  exact hk_int

end Phase

variable [IsHermitianUnit T.splitGram]

/-- The type of all subgroups Z with K(g) ≤ Z ≤ K. Here K(g) = `F.congruenceSubgroup` is the
principal congruence subgroup of the place datum `F` and K is the integral unitary group. -/
abbrev PlaceData.IntermediateGroup (F : PlaceData ι T (m + 1)) : Type :=
  ↥(Set.Icc F.congruenceSubgroup (unitaryLevel integers 1 T.splitGram))

/-- The product fl over the floors l < ϱ of the volumes `F.floorModulus l`. At a large lattice datum
it is the mass of 𝖴 ∩ K(g) in the Bessel unipotent group 𝖴, where K(g) = `F.congruenceSubgroup`. -/
abbrev PlaceData.unipotentMass (F : PlaceData ι T (m + 1)) : ℝ≥0∞ :=
  ∏ l ∈ Finset.range 𝔰.ϱ, F.floorModulus l

/-- The number ϰ(Z) = ∫_G |∫_Z χ_g(y x y⁻¹) dy|² dx for a subgroup `Z` of the unitary group G, both
integrals for the measure `F.groupMeasure`, with χ_g = `New.Floors.IntegralPlace.extendedBesselChar
F.levelUnit`. -/
def PlaceData.massIntegral (F : PlaceData ι T (m + 1)) (Z : Subgroup T.G) : ℝ≥0∞ :=
  ∫⁻ x : T.G, ‖∫ y : T.G in Z, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2
    ∂F.groupMeasure

variable {F : PlaceData ι T (m + 1)} {x y : T.G} (Z : F.IntermediateGroup)

/-- Every intermediate group `Z` of the place datum `F` lies in
`unitaryLevel integers 1 T.splitGram`, the group of unitary elements with integral entries. -/
theorem PlaceData.IntermediateGroup.le_unitaryLevel_one (Z : F.IntermediateGroup) :
    Z.val ≤ unitaryLevel integers 1 T.splitGram :=
  Z.prop.2

/-- The cosets K(g) a of K(g) = `F.congruenceSubgroup` in a group `Z` with K(g) ≤ Z ≤ K, for a in
`Z`. -/
def PlaceData.IntermediateGroup.Cosets (Z : F.IntermediateGroup) : Type :=
  Quotient (rightRel (F.congruenceSubgroup.subgroupOf Z))

/-- The group K(g) has finitely many cosets in `Z`. -/
instance : Fintype Z.Cosets :=
  -- The open subgroup K(g) has finite index in the compact integral group, hence in `Z`.
  letI : Fintype (Z ⧸ F.congruenceSubgroup.subgroupOf Z) :=
    fintypeOfIndexNeZero fun h_zero ↦
      unitaryLevel_open_compact.2.relIndex_ne_zero unitaryLevel_open_compact.1
        (relIndex_eq_zero_of_le_right Z.le_unitaryLevel_one h_zero)
  fintypeQuotientRightRel

/-- The number vol(Z) · vol(K(g)) / fl² for a group `Z` with K(g) ≤ Z ≤ K, where
vol = `F.groupMeasure`, K(g) = `F.congruenceSubgroup` and fl = `F.unipotentMass`. -/
def PlaceData.IntermediateGroup.massRatio (Z : F.IntermediateGroup) : ℝ≥0∞ :=
  F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup / F.unipotentMass ^ 2

/-- The finite Bessel vector of `y`: its coordinate at the coset K(g) z in `Z` is χ_g(y z⁻¹), with
χ_g = `extendedBesselChar F.levelUnit`. The definition uses a chosen representative z of each
coset. -/
def PlaceData.IntermediateGroup.besselVector (y : T.G) : EuclideanSpace ℂ Z.Cosets :=
  WithLp.toLp 2 fun c ↦ extendedBesselChar F.levelUnit (y * c.out.val⁻¹)

/-- The product `F.unipotentMass` of the floor volumes of a place datum `F` is positive and
finite. -/
@[simp]
lemma PlaceData.unipotentMass_ne_zero_and_ne_top : F.unipotentMass ≠ 0 ∧ F.unipotentMass ≠ ∞ := by
  simp [unipotentMass, floorModulus, prod_eq_zero_iff, prod_ne_top, mul_eq_top]

/-- Let `Z` be a group with K(g) ≤ Z ≤ K. If the values at `x` and `y` of the finite Bessel vector
of `Z` are not orthogonal, there are `u`, `v` in the Bessel unipotent group such that `u x` lies in
K and `v y` lies in the coset `u x K(g)`. -/
theorem PlaceData.exists_mem_congruenceSubgroup_of_inner_ne_zero (Z : F.IntermediateGroup)
    (h_inner : ⟪Z.besselVector x, Z.besselVector y⟫_ℂ ≠ 0) :
    ∃ u ∈ T.besselU, ∃ v ∈ T.besselU,
      u * x ∈ unitaryLevel integers 1 T.splitGram ∧ (u * x)⁻¹ * (v * y) ∈ F.congruenceSubgroup := by
  -- Some coset `c` contributes a nonzero term to the inner product: neither vector vanishes there.
  obtain ⟨c, -, hc⟩ : ∃ c ∈ (Finset.univ : Finset Z.Cosets),
      ⟪extendedBesselChar F.levelUnit (x * c.out.val⁻¹),
        extendedBesselChar F.levelUnit (y * c.out.val⁻¹)⟫_ℂ ≠ 0 :=
    exists_ne_zero_of_sum_ne_zero h_inner
  obtain ⟨u, hu, hux⟩ : ∃ u ∈ T.besselU, u⁻¹ * (x * c.out.val⁻¹) ∈ F.congruenceSubgroup :=
    exists_besselU_of_extendedBesselChar_ne_zero fun h_zero ↦ hc (by rw [h_zero, inner_zero_left])
  obtain ⟨v, hv, hvy⟩ : ∃ v ∈ T.besselU, v⁻¹ * (y * c.out.val⁻¹) ∈ F.congruenceSubgroup :=
    exists_besselU_of_extendedBesselChar_ne_zero fun h_zero ↦ hc (by rw [h_zero, inner_zero_right])
  -- The representative of `c` is integral, so it normalises K(g).
  have hc_int : c.out.val ∈ unitaryLevel integers 1 T.splitGram := Z.le_unitaryLevel_one c.out.prop
  refine ⟨u⁻¹, inv_mem hu, v⁻¹, inv_mem hv, ?_, ?_⟩
  · simpa [mul_assoc] using mul_mem (unitaryLevel_le_unitaryLevel_one hux) hc_int
  · simpa [mul_assoc] using conj_mem_unitaryLevel (inv_mem hc_int) (mul_mem (inv_mem hux) hvy)

/-- A group `Z` with K(g) ≤ Z ≤ K is open, since it contains the open subgroup K(g). -/
theorem PlaceData.IntermediateGroup.isOpen : Z.val.IsOpen :=
  isOpen_mono Z.prop.1 unitaryLevel_open_compact.1

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let K(g) ≤ Z ≤ K, with K(g) = `F.congruenceSubgroup`. For `y` in `Z` there is exactly one coset
`c` of K(g) in `Z` whose chosen representative `c.out` satisfies `y * c.out⁻¹ ∈ K(g)`. -/
theorem PlaceData.IntermediateGroup.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq
    (Z : F.IntermediateGroup) (hy : y ∈ Z.val) :
    ∃ d : Z.Cosets, ∀ c : Z.Cosets, y * c.out.val⁻¹ ∈ F.congruenceSubgroup ↔ c = d := by
  -- `d` is the coset of `y` itself.
  refine ⟨⟦⟨y, hy⟩⟧, fun c ↦ Iff.symm ?_⟩
  calc c = ⟦⟨y, hy⟩⟧ ↔ rightRel (F.congruenceSubgroup.subgroupOf Z) c.out ⟨y, hy⟩ :=
         Quotient.eq_mk_iff_out
    _ ↔ ⟨y, hy⟩ * c.out⁻¹ ∈ F.congruenceSubgroup.subgroupOf Z.val := rightRel_apply
    _ ↔ y * c.out.val⁻¹ ∈ F.congruenceSubgroup := mem_subgroupOf

/-- The inverse modulus of a unit `u` is its generalised index `genIndex u` (the inverse of the
factor by which `u` scales Haar measure), written as the square of its square root. -/
theorem IntegralPlace.inv_modulus_eq_sqrt_genIndex_sq (u : Aˣ) :
    (P.modulus u)⁻¹ = (ENNReal.ofReal √(genIndex u.val)) ^ 2 := by
  simp [modulus_eq_inv_genIndex, ← ofReal_pow, genIndex_pos, le_of_lt]

/-- Leading coordinates of a lattice. Let the matrix `X` over `A` have a left inverse, and let the
index `i` be alone in its weight `wt i`. Consider the vectors `v` that vanish at the indices of
larger weight and such that `X *ᵥ v` has entries in the ring of integers R = `integers`. Their
coordinates at `i` form the set c R for some unit c of `A`. -/
theorem IntegralPlace.exists_unit_leadingCoord_iff_mem_integers {n κ : Type} [Fintype n] [Fintype κ]
    [DecidableEq n] [DecidableEq κ] {X : Matrix n κ A} (hX : HasLeftInv X) (wt : κ → ℕ) (i : κ)
    (hi : ∀ l : κ, wt l = wt i → l = i) :
    ∃ c : Aˣ, ∀ t : A,
      (∃ v : κ → A, X *ᵥ v ∈ intVectors P.integers n ∧ (∀ l : κ, wt i < wt l → v l = 0) ∧ v i = t) ↔
        c⁻¹.val * t ∈ P.integers := by
  -- The lattice of the `v` with `X *ᵥ v` integral has a triangular basis `b`, and the diagonal
  -- entry `b i i` is the unit sought.
  obtain ⟨b, hb_tri, hXb, L, hL, hLXb⟩ : ∃ b : GL κ A, b.val.BlockTriangular wt ∧
      IsIntMatrix integers (X * b.val) ∧ ∃ L : Matrix κ n A,
        IsIntMatrix integers L ∧ L * (X * b.val) = 1 :=
    isValuationPair.exists_isPrimitiveMatrix_mul hX wt
  have h_col (l : κ) (hl : wt i < wt l) : b.val l i = 0 := hb_tri hl
  -- On vectors that vanish at the larger weights the row `i` of `b⁻¹` sees only the entry `i`.
  have h_row (v : κ → A) (hv : ∀ l : κ, wt i < wt l → v l = 0) :
      (b⁻¹.val *ᵥ v) i = b⁻¹.val i i * v i := by
    have h_inv_tri : b⁻¹.val.BlockTriangular wt := by
      simpa using blockTriangular_inv_of_blockTriangular hb_tri
    refine sum_eq_single i (fun l _ hl ↦ ?_) (by simp)
    obtain h_lt | h_gt : wt l < wt i ∨ wt i < wt l := Nat.lt_or_gt_of_ne (mt (hi l) hl)
    · exact mul_eq_zero_of_left (h_inv_tri h_lt) _
    · exact mul_eq_zero_of_right _ (hv l h_gt)
  have h_unit : b.val i i * b⁻¹.val i i = 1 := by
    have h_one : (b⁻¹.val * b.val) i i = b⁻¹.val i i * b.val i i := h_row (b.val.col i) h_col
    rw [mul_comm, ← h_one, Units.inv_mul, one_apply_eq]
  let c : Aˣ := .mkOfMulEqOne (b.val i i) (b⁻¹.val i i) h_unit
  refine ⟨c, fun t ↦ ⟨?_, fun ht ↦ ?_⟩⟩
  · -- For `v` in the lattice `b⁻¹ *ᵥ v = L *ᵥ X *ᵥ v` is integral.
    rintro ⟨v, hv_int, hv, rfl⟩
    have h_inv : b⁻¹.val = L * X := by
      rw [coe_units_inv, inv_eq_left_inv ((L.mul_assoc X b.val).trans hLXb)]
    change b⁻¹.val i i * v i ∈ integers
    rw [← h_row v hv, h_inv, ← mulVec_mulVec]
    exact hL.mulVec hv_int i
  · -- Conversely, `t` is the coordinate of the multiple `c⁻¹ * t` of the column `i` of `b`.
    refine ⟨(c⁻¹.val * t) • b.val.col i, fun k ↦ ?_, fun l hl ↦ by simp [h_col l hl], ?_⟩
    · rw [mulVec_smul]
      change c⁻¹.val * t * (X * b.val) k i ∈ integers
      exact mul_mem ht (hXb k i)
    · change c⁻¹.val * t * c.val = t
      rw [mul_right_comm, Units.inv_mul, one_mul]

namespace IntegralPlace.IsLargeLatticeData

variable [h : IsLargeLatticeData F]

/-- The compact set `F.boxSet` of a large lattice datum is the integral unitary group. -/
theorem box_eq : F.boxSet = unitaryLevel integers 1 T.splitGram := by
  obtain ⟨-, h_box, -⟩ := h.volume_le_and_boxSet_closePairs_positions_eq
  exact h_box

/-- For a large lattice datum `F` (hypothesis `IsLargeLatticeData F`), a subgroup `S` of the
integral unitary group `unitaryLevel integers 1 T.splitGram` has finite measure `F.groupMeasure S`,
for the convolution measure `F.groupMeasure` on the unitary group. -/
theorem groupMeasure_ne_top {S : Subgroup (U T.splitGram)}
    (hS : S ≤ unitaryLevel integers 1 T.splitGram) :
    F.groupMeasure S ≠ ∞ :=
  (measure_lt_top_mono hS unitaryLevel_open_compact.2.measure_lt_top).ne

/-- For a large lattice datum and K(g) ≤ Z ≤ K, the number `Z.massRatio` = vol(Z) · vol(K(g)) / fl²,
with fl = `F.unipotentMass`, is positive and finite. -/
theorem massRatio_ne_zero_and_ne_top : Z.massRatio ≠ 0 ∧ Z.massRatio ≠ ∞ := by
  -- `Z` and K(g) are open, so of positive Haar measure, and integral, so of finite measure.
  have hZ_pos : F.groupMeasure Z ≠ 0 := Z.isOpen.measure_ne_zero _ ⟨1, one_mem _⟩
  have hK_pos : F.groupMeasure F.congruenceSubgroup ≠ 0 :=
    unitaryLevel_open_compact.1.measure_ne_zero _ ⟨1, one_mem _⟩
  have hZ_fin : F.groupMeasure Z ≠ ∞ := groupMeasure_ne_top Z.le_unitaryLevel_one
  have hK_fin : F.groupMeasure F.congruenceSubgroup ≠ ∞ :=
    groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one
  simp [IntermediateGroup.massRatio, hZ_pos, hK_pos, hZ_fin, hK_fin, div_eq_top, mul_eq_top]

/-- For a large lattice datum `F` (hypothesis `IsLargeLatticeData F`) and a group `Z` with
K(g) ≤ Z ≤ K, the contribution of K(g) = `F.congruenceSubgroup` to the integral `F.massIntegral Z`
is vol(Z)² · vol(K(g)), where vol = `F.groupMeasure`. -/
theorem setLIntegral_congruenceSubgroup_integral_sq :
    ∫⁻ x : T.G in F.congruenceSubgroup,
        ‖∫ y : T.G in Z, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2
          ∂F.groupMeasure =
      F.groupMeasure Z ^ 2 * F.groupMeasure F.congruenceSubgroup := by
  -- For `x` in K(g) the integrand is a constant of modulus `1` on `Z`, as `Z` normalises K(g).
  have h_const (x : T.G) (hx : x ∈ F.congruenceSubgroup) (y : T.G) (hy : y ∈ Z.val) :
      extendedBesselChar F.levelUnit (y * x * y⁻¹) = P.ψ
        (F.levelUnit⁻¹.val * simpleRootSum (1 : T.G)) := by
    have h_conj : y * x * y⁻¹ ∈ F.congruenceSubgroup :=
      conj_mem_unitaryLevel (Z.le_unitaryLevel_one hy) hx
    exact extendedBesselChar_eq (one_mem _) (by simpa using h_conj)
  have h_inner (x : T.G) (hx : x ∈ F.congruenceSubgroup) :
      ‖∫ y : T.G in Z, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure‖ₑ ^ 2 =
        F.groupMeasure Z ^ 2 := by
    rw [setIntegral_congr_fun Z.isOpen.measurableSet (h_const x hx)]
    simp [Measure.real, ← ofReal_norm, groupMeasure_ne_top Z.le_unitaryLevel_one]
  rw [setLIntegral_congr_fun measurableSet_unitaryLevel h_inner, setLIntegral_const]

/-- For a large lattice datum `F` (hypothesis `IsLargeLatticeData F`) and `Z` with K(g) ≤ Z ≤ K, the
finite Bessel vector W = `Z.besselVector` is a cut Bessel function (`F.IsCut`). That is: W is
bounded and measurable; W(u x) = ψ(σ(u) / g) W(x) for u in the Bessel unipotent group 𝖴, where
σ = `simpleRootSum` and g = `F.levelUnit`; and W vanishes off the translates by 𝖴 of the compact set
`F.boxSet`. -/
theorem isCut_besselVector : F.IsCut Z.besselVector := by
  -- Each coordinate has norm at most `1`.
  have h_bdd (x : T.G) : ‖Z.besselVector x‖ ≤ √(∑ _ : Z.Cosets, 1 ^ 2) := by
    grw [EuclideanSpace.norm_eq, IntermediateGroup.besselVector, norm_extendedBesselChar_le_one]
  have h_meas : StronglyMeasurable Z.besselVector := by fun_prop [IntermediateGroup.besselVector]
  have h_law (u : T.G) (hu : u ∈ T.besselU) (x : T.G) :
      Z.besselVector (u * x) = P.ψ (F.levelUnit⁻¹.val * simpleRootSum u) • Z.besselVector x := by
    ext c
    simp [IntermediateGroup.besselVector, extendedBesselChar_besselU_mul hu, mul_assoc]
  have h_supp {x : T.G} (hx : Z.besselVector x ≠ 0) : ∃ u ∈ T.besselU, u * x ∈ F.boxSet := by
    obtain ⟨u, hu, -, -, hux, -⟩ : ∃ u ∈ T.besselU, ∃ v ∈ T.besselU,
        u * x ∈ unitaryLevel integers 1 T.splitGram ∧ (u * x)⁻¹ * (v * x) ∈ F.congruenceSubgroup :=
      exists_mem_congruenceSubgroup_of_inner_ne_zero Z (inner_self_ne_zero.2 hx)
    exact ⟨u, hu, box_eq.ge hux⟩
  exact { toIsBoundedMeasurable := ⟨h_meas, _,
    h_bdd⟩, map_unipotent_mul := h_law, exists_mul_mem_box := h_supp }

/-- For a large lattice datum and K(g) ≤ Z ≤ K, let the orbital integral J(γ) = ∫_G W(y) ⊗ W(γ⁻¹y)^*
dy (`besselOrbitalIntegral`, for the Haar measure `F.groupMeasure`) of the finite Bessel vector
`W = Z.besselVector` be non-zero. Then all leading minors of `T.frameGram γ`, the matrix of the
products h(f_a, γ f_b) of the frame vectors f_a under the form h = `T.splitGram`, are integral. -/
theorem leadingMinor_mem_of_besselOrbitalIntegral_ne_zero (Z : F.IntermediateGroup) {γ : T.G}
    (hγ : besselOrbitalIntegral F.groupMeasure Z.besselVector γ ≠ 0) (j : Fin (𝔰.n + 1)) :
    leadingMinor (T.frameGram γ.val.val) j ∈ P.integers := by
  -- For the gauge of scale `1`, having any given size means being integral.
  let Γ : Gauge F := h.gauge 1 (one_mem P.integers) (star_one A)
  have h_size : leadingMinor (T.frameGram γ.val.val) j ∈ Γ.ofSize (9 * 𝔰.n) :=
    Γ.leadingMinor_mem_ofSize_of_besselOrbitalIntegral_ne_zero (isCut_besselVector Z) hγ j
  simpa [Γ, gauge] using h_size

/-- The pairing of two translates of the finite Bessel vector as an integral over the Bessel
unipotent group 𝖴. For a large lattice datum and K(g) ≤ Z ≤ K, let fl = `F.unipotentMass` be the
mass of 𝖴 ∩ K(g), let W_Z = `Z.besselVector`, and let χ_g = `extendedBesselChar F.levelUnit` be the
Bessel character of 𝖴, extended to 𝖴 K(g) and by zero outside it. Then fl·⟨W_Z(y), W_Z(yx)⟩ is the
integral of 1_Z(uy)·χ_g(uyx(uy)⁻¹) over u for `ascConv heisenbergMeasure (𝔰.ϱ + 2)`. This is the
convolution η_0 ∗ ⋯ ∗ η_{ϱ+1} of the measures η_l = `heisenbergMeasure l`, where ϱ = `𝔰.ϱ` is the
number of hyperbolic planes of the shape 𝔰. It is carried by 𝖴. -/
theorem unipotentMass_mul_inner_besselVector (y x : T.G) :
    F.unipotentMass.toReal * ⟪Z.besselVector y, Z.besselVector (y * x)⟫_ℂ =
      ∫ u : T.G, Set.indicator Z (fun z : T.G ↦ extendedBesselChar F.levelUnit (z * x * z⁻¹))
        (u * y)
        ∂ascConv heisenbergMeasure (𝔰.ϱ + 2) := by
  classical
  -- On `besselU` the integrand is the sum over the cosets `c` of `a c` times the indicator of a set
  -- `S c`, and `S c` has mass `F.unipotentMass` whenever `a c` does not vanish.
  let ν : Measure T.G := ascConv heisenbergMeasure (𝔰.ϱ + 2)
  let S : Z.Cosets → Set T.G := fun c ↦ {u : T.G | u * (y * c.out.val⁻¹) ∈ F.congruenceSubgroup}
  let a : Z.Cosets → ℂ := fun c ↦ Z.besselVector (y * x) c * star (Z.besselVector y c)
  have hS_meas (c : Z.Cosets) : MeasurableSet (S c) :=
    measurable_mul_const _ measurableSet_unitaryLevel
  have hg : F.levelUnit.val ∈ integers ∧ star F.levelUnit.val = F.levelUnit := h.integral_data.2.2
  have h_mass (c : Z.Cosets) : ν (S c) = F.unipotentMass *
      dirac 1 {z : T.G | ∃ u ∈ T.besselU, u * (z * (y * c.out.val⁻¹)) ∈ F.congruenceSubgroup} := by
    simpa only [mconv_dirac_one] using h.ascConv_mconv_unitaryLevel_coset (θ := dirac 1) hg
  have h_integrand (u : T.G) (hu : u ∈ T.besselU) :
      Set.indicator Z (fun z : T.G ↦ extendedBesselChar F.levelUnit (z * x * z⁻¹)) (u * y) =
        ∑ c : Z.Cosets, (S c).indicator (fun _ ↦ a c) u := by
    by_cases huy : u * y ∈ Z.val
    · -- `u` lies in exactly one `S d`; there the characters of `u⁻¹` in the two factors cancel.
      obtain ⟨d, hS⟩ : ∃ d : Z.Cosets, ∀ c : Z.Cosets, u ∈ S c ↔ c = d := by
        simpa [S, mul_assoc] using Z.exists_forall_mul_inv_mem_congruenceSubgroup_iff_eq huy
      have hu_mem : u * (y * d.out.val⁻¹) ∈ F.congruenceSubgroup := (hS d).2 rfl
      have h_right : Z.besselVector y d = P.ψ (F.levelUnit⁻¹.val * simpleRootSum u⁻¹) :=
        extendedBesselChar_eq (inv_mem hu) (by simpa using hu_mem)
      have h_left : Z.besselVector (y * x) d =
          P.ψ (F.levelUnit⁻¹.val * simpleRootSum u⁻¹) * extendedBesselChar F.levelUnit
            (u * y * x * (u * y)⁻¹) := by
        rw [← extendedBesselChar_mul_of_mem_unitaryLevel hu_mem,
          ← extendedBesselChar_besselU_mul (inv_mem hu)]
        simp [IntermediateGroup.besselVector, mul_assoc]
      have h_cancel : a d = extendedBesselChar F.levelUnit (u * y * x * (u * y)⁻¹) := by
        simp [a, h_left, h_right, mul_comm (P.ψ _), mul_assoc, Complex.conj_mul']
      simpa [huy, hS, Set.indicator] using h_cancel.symm
    · -- `u` lies in no `S c`, as K(g) ≤ `Z`.
      obtain ⟨h_lower, -⟩ : F.congruenceSubgroup ≤ Z.val ∧ Z.val ≤ unitaryLevel integers 1
        T.splitGram :=
        Z.prop
      have hS (c : Z.Cosets) : u ∉ S c := fun hc ↦
        huy (by simpa [mul_assoc] using mul_mem (h_lower hc) c.out.prop)
      simp [huy, hS]
  have h_ae : ∀ᵐ u : T.G ∂ν, Set.indicator Z
    (fun z : T.G ↦ extendedBesselChar F.levelUnit (z * x * z⁻¹)) (u * y) =
      ∑ c : Z.Cosets, (S c).indicator (fun _ ↦ a c) u :=
    ae_ascConv_mem_unipotentBelow.mono fun u hu ↦ h_integrand u (unipotentBelow_le_besselU hu)
  have h_fin (c : Z.Cosets) : ν (S c) ≠ ∞ := by
    rw [h_mass]
    exact ENNReal.mul_ne_top unipotentMass_ne_zero_and_ne_top.2 (measure_ne_top _ _)
  rw [integral_congr_ae h_ae,
    integral_finsetSum _ fun c _ ↦ (integrableOn_const (h_fin c)).integrable_indicator (hS_meas c),
    PiLp.inner_apply, mul_sum]
  refine sum_congr rfl fun c _ ↦ ?_
  by_cases hc : Z.besselVector y c = 0
  · simp [a, hc]
  -- Otherwise `y c⁻¹ ∈ u K(g)` for some `u`, so the Dirac mass in `h_mass` is `1`.
  obtain ⟨u, hu, huy⟩ : ∃ u ∈ T.besselU, u⁻¹ * (y * c.out.val⁻¹) ∈ F.congruenceSubgroup :=
    exists_besselU_of_extendedBesselChar_ne_zero hc
  have h_one : (1 : T.G) ∈ {z : T.G | ∃ u ∈ T.besselU, u * (z *
    (y * c.out.val⁻¹)) ∈ F.congruenceSubgroup} :=
    ⟨u⁻¹, inv_mem hu, by simpa using huy⟩
  rw [integral_indicator_const _ (hS_meas c), Measure.real, h_mass, dirac_apply_of_mem h_one,
    mul_one]
  simp [a, Complex.real_smul]

/-- For a large lattice datum `F` and a group `Z` with K(g) ≤ Z ≤ K, the Haar measure of `Z` is the
number of cosets of K(g) = `F.congruenceSubgroup` in `Z` times the measure of K(g). -/
theorem card_cosets_mul_groupMeasure :
    card Z.Cosets * F.groupMeasure F.congruenceSubgroup = F.groupMeasure Z := by
  obtain ⟨h_lower, h_upper⟩ : F.congruenceSubgroup ≤ Z.val ∧ Z.val ≤ unitaryLevel integers 1
    T.splitGram :=
    Z.prop
  have h_compact : IsCompact (Z.val : Set T.G) :=
    unitaryLevel_open_compact.2.of_isClosed_subset (Z.val.isClosed_of_isOpen Z.isOpen) h_upper
  have h_card : card Z.Cosets = F.congruenceSubgroup.relIndex Z.val := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (quotientRightRelEquivQuotientLeftRel _)
  rw [h_card, ← relIndex_mul_measure_inf h_compact unitaryLevel_open_compact.1,
    inf_of_le_left h_lower]

/-- For a large lattice datum `F` and a group `Z` with K(g) ≤ Z ≤ K, the set of `u` with `u y ∈ Z`
has mass at most one for the convolution of the measures `heisenbergMeasure`, which is carried by
the Bessel unipotent group 𝖴. -/
theorem ascConv_setOf_mul_mem_le_one (y : T.G) :
    ascConv heisenbergMeasure (𝔰.ϱ + 2) {u : T.G | u * y ∈ Z.val} ≤ 1 := by
  -- `Z` lies in the integral points, and at level `1` the floor volumes are `1`.
  calc ascConv heisenbergMeasure (𝔰.ϱ + 2) {u : T.G | u * y ∈ Z.val}
    _ ≤ (∏ l ∈ Finset.range 𝔰.ϱ, F.floorModulus l 1) * 1 := by
      grw [Z.le_unitaryLevel_one, ← mconv_dirac_one (ascConv heisenbergMeasure (𝔰.ϱ + 2)),
        h.ascConv_mconv_unitaryLevel_coset (by simp), prob_le_one]
    _ = 1 := by simp [floorModulus]

/-- For a large lattice datum and K(g) ≤ Z ≤ K, let `fl = F.unipotentMass` be the mass of 𝖴 ∩ K(g)
and `W_Z = Z.besselVector`. Then `fl ‖W_Z y‖²` is the mass of the `u` with `u y ∈ Z` for
`ascConv heisenbergMeasure (𝔰.ϱ + 2)`. This is the convolution η_0 ∗ ⋯ ∗ η_{ϱ+1} of the measures
η_l = `heisenbergMeasure l`, where ϱ = `𝔰.ϱ` is the number of hyperbolic planes of the shape 𝔰. It
is carried by the Bessel unipotent group 𝖴. -/
theorem enorm_sq_besselVector_mul_unipotentMass (y : T.G) :
    ‖Z.besselVector y‖ₑ ^ 2 * F.unipotentMass =
      ascConv heisenbergMeasure (𝔰.ϱ + 2) {u : T.G | u * y ∈ Z.val} := by
  -- This is `unipotentMass_mul_inner_besselVector` at `x = 1`, where the extended Bessel character
  -- is constant.
  let ν : Measure T.G := ascConv heisenbergMeasure (𝔰.ϱ + 2)
  have h_meas : MeasurableSet {u : T.G | u * y ∈ Z.val} :=
    measurable_mul_const y Z.isOpen.measurableSet
  have h_phase : ‖extendedBesselChar F.levelUnit (1 : T.G)‖ₑ = 1 := by
    rw [extendedBesselChar_eq (one_mem _) (by simp), ← ofReal_norm]
    simp
  have h_indicator (u : T.G) : Set.indicator Z
    (fun z : T.G ↦ extendedBesselChar F.levelUnit (z * 1 * z⁻¹)) (u * y) =
      {u : T.G | u * y ∈ Z.val}.indicator (fun _ ↦ extendedBesselChar F.levelUnit (1 : T.G)) u := by
    by_cases huy : u * y ∈ Z.val
    · simp [huy]
    · simp [huy]
  have h_unfold : F.unipotentMass.toReal * ⟪Z.besselVector y, Z.besselVector y⟫_ℂ =
      ν.real {u : T.G | u * y ∈ Z.val} • extendedBesselChar F.levelUnit (1 : T.G) := by
    rw [← integral_indicator_const _ h_meas]
    simpa only [mul_one y, h_indicator] using unipotentMass_mul_inner_besselVector Z y 1
  calc ‖Z.besselVector y‖ₑ ^ 2 * F.unipotentMass
    _ = ‖F.unipotentMass.toReal * ⟪Z.besselVector y, Z.besselVector y⟫_ℂ‖ₑ := by
      -- `toReal_prod` would expand the product `F.unipotentMass`.
      simp [← ofReal_norm, mul_comm F.unipotentMass, -toReal_prod]
    _ = ν {u : T.G | u * y ∈ Z.val} := by
      rw [h_unfold, enorm_smul, h_phase, mul_one, Real.enorm_of_nonneg measureReal_nonneg,
        ofReal_measureReal ((ascConv_setOf_mul_mem_le_one Z y).trans_lt one_lt_top).ne]

/-- For a large lattice datum `F` and a group `Z` with K(g) ≤ Z ≤ K, the normalised Bessel vector
`√fl W_Z` has norm at most one at every point, where `fl = F.unipotentMass` is the mass of 𝖴 ∩ K(g)
and `W_Z = Z.besselVector`. -/
theorem enorm_sq_besselVector_mul_le_one (y : T.G) :
    ‖Z.besselVector y‖ₑ ^ 2 * F.unipotentMass ≤ 1 :=
  (enorm_sq_besselVector_mul_unipotentMass Z y).trans_le (ascConv_setOf_mul_mem_le_one Z y)

/-- For a large lattice datum `F` and a group `Z` with K(g) ≤ Z ≤ K, let `fl = F.unipotentMass` be
the mass of 𝖴 ∩ K(g) and `W_Z = Z.besselVector`. The squared norm of `√fl W_Z` on 𝖴∖G is the measure
of `Z`; by `card_cosets_mul_groupMeasure` this is the number of cosets of K(g) in `Z` times the
measure of K(g). Functions on 𝖴∖G are integrated against `F.quotientMeasureFrom 0`, the product of
the measures of all floors. -/
theorem lintegral_enorm_sq_besselVector :
    F.unipotentMass * ∫⁻ y : T.G, ‖Z.besselVector y‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 =
      F.groupMeasure Z := by
  let ν : Measure T.G := ascConv heisenbergMeasure (𝔰.ϱ + 2)
  have h_conv : F.groupMeasure = ν ∗ₘ F.quotientMeasureFrom 0 := F.partialGroupMeasure_zero_eq
  obtain ⟨-, h_top⟩ : F.unipotentMass ≠ 0 ∧ F.unipotentMass ≠ ∞ :=
    unipotentMass_ne_zero_and_ne_top
  calc F.unipotentMass * ∫⁻ y : T.G, ‖Z.besselVector y‖ₑ ^ 2 ∂F.quotientMeasureFrom 0
    _ = ∫⁻ y : T.G, ‖Z.besselVector y‖ₑ ^ 2 * F.unipotentMass ∂F.quotientMeasureFrom 0 := by
      rw [mul_comm, lintegral_mul_const' _ _ h_top]
    _ = ∫⁻ y : T.G, ν {u : T.G | u * y ∈ Z.val} ∂F.quotientMeasureFrom 0 :=
      lintegral_congr (enorm_sq_besselVector_mul_unipotentMass Z)
    _ = (ν ∗ₘ F.quotientMeasureFrom 0) Z := (mconv_apply_eq_lintegral Z.isOpen.measurableSet).symm
    _ = F.groupMeasure Z := by rw [h_conv]

/-- For a large lattice datum `F` and a group `Z` with K(g) ≤ Z ≤ K, let `fl = F.unipotentMass` be
the mass of 𝖴 ∩ K(g) and `W_Z = Z.besselVector`. For fixed `x`, the integral of |⟨W_Z(x), W_Z(y)⟩|²
over `y` in 𝖴∖G, that is against `F.quotientMeasureFrom 0`, times fl², is at most
‖W_Z(x)‖² · vol(K(g)). -/
theorem lintegral_inner_besselVector_sq_mul_le (x : T.G) :
    (∫⁻ y : T.G, ‖⟪Z.besselVector x, Z.besselVector y⟫_ℂ‖ₑ ^ 2 ∂F.quotientMeasureFrom 0) *
        F.unipotentMass * F.unipotentMass ≤
      ‖Z.besselVector x‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup := by
  classical
  -- Only the `y` in a set `S` of mass vol(K(g)) / fl count, and `√fl ‖W_Z y‖ ≤ 1` bounds
  -- `√fl |⟨W_Z x, W_Z y⟩|` by `‖W_Z x‖`.
  let θ : Measure T.G := F.quotientMeasureFrom 0
  have h_conv : F.groupMeasure = ascConv heisenbergMeasure (𝔰.ϱ + 2) ∗ₘ θ :=
    F.partialGroupMeasure_zero_eq
  by_cases hx : Z.besselVector x = 0
  · simp [hx]
  obtain ⟨u, hu, hux⟩ : ∃ u ∈ T.besselU, u * x ∈ F.boxSet :=
    (isCut_besselVector Z).exists_mul_mem_box hx
  let S : Set T.G := {y : T.G | ∃ v ∈ T.besselU, v * (y * (u * x)⁻¹) ∈ F.congruenceSubgroup}
  -- By right invariance K(g) has the measure of the coset K(g) `u * x`; unfold along `besselU`.
  have h_mass : F.groupMeasure F.congruenceSubgroup = F.unipotentMass * θ S := by
    have hg : F.levelUnit.val ∈ integers ∧ star F.levelUnit.val = F.levelUnit := h.integral_data.2.2
    calc F.groupMeasure F.congruenceSubgroup
      _ = F.groupMeasure {z : T.G | z * (u * x)⁻¹ ∈ F.congruenceSubgroup} :=
        (measure_preimage_mul_right _ (u * x)⁻¹ _).symm
      _ = F.unipotentMass * θ S := by
        rw [h_conv]
        exact h.ascConv_mconv_unitaryLevel_coset hg
  -- The pairing vanishes outside `S`: the integral point `u * x` normalises K(g).
  have h_supp (y : T.G) (hy : ⟪Z.besselVector x, Z.besselVector y⟫_ℂ ≠ 0) : y ∈ S := by
    obtain ⟨v, hv, w, hw, -, h_close⟩ : ∃ v ∈ besselU, ∃ w ∈ besselU,
        v * x ∈ unitaryLevel integers 1 T.splitGram ∧ (v * x)⁻¹ * (w * y) ∈ F.congruenceSubgroup :=
      exists_mem_congruenceSubgroup_of_inner_ne_zero Z hy
    refine ⟨u * v⁻¹ * w, mul_mem (mul_mem hu (inv_mem hv)) hw, ?_⟩
    simpa [mul_assoc] using conj_mem_unitaryLevel (box_eq.le hux) h_close
  have h_bound (y : T.G) :
      ‖⟪Z.besselVector x, Z.besselVector y⟫_ℂ‖ₑ ^ 2 * F.unipotentMass ≤
        S.indicator (fun _ ↦ ‖Z.besselVector x‖ₑ ^ 2) y := by
    by_cases hy : ⟪Z.besselVector x, Z.besselVector y⟫_ℂ = 0
    · simp [hy]
    have h_schwarz : ‖⟪Z.besselVector x, Z.besselVector y⟫_ℂ‖ₑ ≤
        ‖Z.besselVector x‖ₑ * ‖Z.besselVector y‖ₑ :=
      coe_le_coe.2 (nnnorm_inner_le_nnnorm _ _)
    rw [Set.indicator_of_mem (h_supp y hy)]
    grw [h_schwarz, mul_pow, mul_assoc, enorm_sq_besselVector_mul_le_one, mul_one]
  calc
    _ ≤ (∫⁻ y : T.G, S.indicator (fun _ ↦ ‖Z.besselVector x‖ₑ ^ 2) y ∂θ) * F.unipotentMass := by
      grw [lintegral_mul_const_le, lintegral_mono h_bound]
    _ ≤ ‖Z.besselVector x‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup := by
      grw [lintegral_indicator_const_le, h_mass, mul_assoc, mul_comm F.unipotentMass]

/-- For a large lattice datum `F` and a group `Z` with K(g) ≤ Z ≤ K, let `fl = F.unipotentMass` be
the mass of 𝖴 ∩ K(g) and `W_Z = Z.besselVector`. The integral `F.pairingNormSq` of |⟨W_Z(x),
W_Z(y)⟩|² over (𝖴∖G)², times fl, is at most `Z.massRatio`, the number vol(Z) · vol(K(g)) / fl² for
the Haar measure vol = `F.groupMeasure`. -/
theorem pairingNormSq_mul_le_massRatio :
    F.pairingNormSq Z.besselVector * F.unipotentMass ≤ Z.massRatio := by
  -- Bound the integral over `y`, then integrate over `x` by `lintegral_enorm_sq_besselVector`.
  let θ : Measure T.G := F.quotientMeasureFrom 0
  let I : T.G → ℝ≥0∞ := fun x ↦ ∫⁻ y : T.G, ‖⟪Z.besselVector x, Z.besselVector y⟫_ℂ‖ₑ ^ 2 ∂θ
  have h_le : F.pairingNormSq Z.besselVector * F.unipotentMass * F.unipotentMass ≤
      ∫⁻ x : T.G, ‖Z.besselVector x‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup ∂θ :=
    calc (∫⁻ x : T.G, I x ∂θ) * F.unipotentMass * F.unipotentMass
      _ ≤ ∫⁻ x : T.G, I x * F.unipotentMass * F.unipotentMass ∂θ := by
        grw [lintegral_mul_const_le, lintegral_mul_const_le]
      _ ≤ ∫⁻ x : T.G, ‖Z.besselVector x‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup ∂θ :=
        lintegral_mono (lintegral_inner_besselVector_sq_mul_le Z)
  have h_sq_ne_zero : F.unipotentMass ^ 2 ≠ 0 := by simp
  have h_sq_ne_top : F.unipotentMass ^ 2 ≠ ∞ := by simp
  rw [IntermediateGroup.massRatio,
    ENNReal.le_div_iff_mul_le (.inl h_sq_ne_zero) (.inl h_sq_ne_top)]
  calc F.pairingNormSq Z.besselVector * F.unipotentMass * F.unipotentMass ^ 2
    _ = F.unipotentMass * (F.pairingNormSq Z.besselVector * F.unipotentMass * F.unipotentMass) := by
      ring
    _ ≤ F.unipotentMass *
        ∫⁻ x : T.G, ‖Z.besselVector x‖ₑ ^ 2 * F.groupMeasure F.congruenceSubgroup ∂θ := by
      grw [h_le]
    _ = F.groupMeasure Z * F.groupMeasure F.congruenceSubgroup := by
      rw [lintegral_mul_const' _ _ (groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one),
        ← mul_assoc, lintegral_enorm_sq_besselVector]

/-- For a large lattice datum `F`, a group `Z` with K(g) ≤ Z ≤ K and `x` in the unitary group `T.G`,
write χ_g = `extendedBesselChar F.levelUnit` and W_Z = `Z.besselVector`. The absolute value of ∫_Z
χ_g(y x y⁻¹) dy for `F.groupMeasure`, the inner integral of `F.massIntegral Z`, is the absolute
value of an integral times the mass `F.unipotentMass` of 𝖴 ∩ K(g). That integral is the integral of
⟨W_Z(z), W_Z(z x)⟩ over z for `F.quotientMeasureFrom 0`. -/
theorem enorm_integral_extendedBesselChar_eq_enorm_mul :
    ‖∫ y : T.G in Z, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure‖ₑ =
      ‖F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1 x‖ₑ * F.unipotentMass := by
  let ν : Measure T.G := ascConv heisenbergMeasure (𝔰.ϱ + 2)
  let θ : Measure T.G := F.quotientMeasureFrom 0
  have h_conv : F.groupMeasure = ν ∗ₘ θ := F.partialGroupMeasure_zero_eq
  let f : T.G → ℂ := Set.indicator Z fun z : T.G ↦ extendedBesselChar F.levelUnit (z * x * z⁻¹)
  have h_on : IntegrableOn (fun z : T.G ↦ extendedBesselChar F.levelUnit (z * x * z⁻¹)) Z
    F.groupMeasure :=
    integrableOn_of_bounded (groupMeasure_ne_top Z.le_unitaryLevel_one) (by fun_prop)
      (.of_forall fun _ ↦ norm_extendedBesselChar_le_one)
  have h_int : Integrable f (ν ∗ₘ θ) := by
    rw [← h_conv]
    exact h_on.integrable_indicator Z.isOpen.measurableSet
  have h_pairing : F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1 x =
      ∫ y : T.G, ⟪Z.besselVector y, Z.besselVector (y * x)⟫_ℂ ∂θ := by
    simp [partialCorrelation, θ]
  -- Integrate `unipotentMass_mul_inner_besselVector` over `y` against `θ`.
  have h_unfold : ∫ y : T.G in Z, extendedBesselChar F.levelUnit (y * x * y⁻¹) ∂F.groupMeasure =
      F.unipotentMass.toReal * F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1 x :=
    calc
      _ = ∫ z : T.G, f z ∂(ν ∗ₘ θ) := by rw [← integral_indicator Z.isOpen.measurableSet, h_conv]
      _ = ∫ y : T.G, ∫ u : T.G, f (u * y) ∂ν ∂θ :=
        (integral_mconv h_int).trans (integral_integral_swap (h_int.comp_measurable measurable_mul))
      _ = ∫ y : T.G, F.unipotentMass.toReal * ⟪Z.besselVector y, Z.besselVector (y * x)⟫_ℂ ∂θ := by
        simp only [unipotentMass_mul_inner_besselVector Z, f, ν]
      _ = F.unipotentMass.toReal * F.partialCorrelation 0 (frameCorrelation Z.besselVector 1) 1
        x := by
        rw [integral_const_mul, h_pairing]
  -- `toReal_prod` would expand the product `F.unipotentMass`.
  simp [h_unfold, mul_comm F.unipotentMass, ← ofReal_norm, -toReal_prod]

end IntegralPlace.IsLargeLatticeData

end New.Floors

end

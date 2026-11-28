import Lib.CM.Sigma.ThetaSections

/-!
# CM lattices as multiples of fractional ideals, and good reduction of CM curves

Let `K = ℚ(√-d) ⊂ ℂ` (`New.QuadField`), where `d` is a prime `≡ 7 mod 8` (`New.PrimeSevenModEight`).
We show that the lattice of every datum `New.CMLattice d` is a multiple `u 𝔞` of a fractional ideal
of `K` and that every ideal gives one, and we compute the covolumes. We then follow isogenies of
degree two through the class group. This shows that the discriminant of a CM lattice, normalised by
`℘''(t) = 2`, is a unit at every prime, as it is for a curve with good reduction.

## Main definitions and results

* `New.CMLattice.latticeModule`: the lattice of a datum as an `𝓞 K`-module;
  `New.QuadField.scaledIdeal`: `(u, 𝔞) ↦ u 𝔞`.
* `New.CMLattice.exists_latticeModule_eq_scaledIdeal`: the lattice of every datum has the form
  `u 𝔞`.
* `New.QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal`: every `𝔞` has a multiple `u 𝔞` that
  is the lattice of a datum.
* `New.QuadField.area_eq_of_eq_scaledIdeal`: the covolume of `u 𝔞` is `|u|² N(𝔞) √d / 2`.
* `PeriodPair.IsOrderTwo.scaledDisc_sum_prod`, `PeriodPair.IsOrderTwo.scaledDisc_mul_of_isogeny`:
  identities for the discriminants `s(u)` of a lattice scaled to `℘''(u) = 2` at the points `u` of
  order two.
* `New.CMLattice.norm_scaledDisc_le_one`, `New.CMLattice.prod_scaledDisc_t`: for a family of data,
  one in each ideal class, the numbers `s(u)` are integral, and those at the points `t` have the
  product `±1`.
* `New.CMLattice.norm_disc_eq_one`: the discriminant `a₁⁴ - 64` of a CM lattice is a unit at every
  prime.

Notions from other files:
* `New.CMLattice d`: a period lattice `Λ` stable under `𝓞 K`, with a point `t` of order two and a
  number `a₁`.
* `PeriodPair.area`: the area `|Im(ω̄₁ω₂)|` of the fundamental parallelogram spanned by the periods
  `ω₁`, `ω₂` of a period pair.

## Relation to the literature

Known result: lattices stable under `𝓞 K` are the multiples of fractional ideals. Source: Silverman,
Advanced topics in the arithmetic of elliptic curves.

Known result: Siegel units. For a torsion point `u`, the twelfth power of Klein's form at `u` times
the discriminant is an algebraic integer, and a unit if two different primes of `K` divide the
annihilator of `u`. The file proves the case of the point `t`, whose annihilator is `(2)`; there the
number is the discriminant `a₁⁴ - 64`. Source: Kubert, Lang, Modular Units. Up to sign the numbers
`s(u)` are the 24-th powers of Weber's functions. Source: Birch, Weber's class invariants, 1969.
-/

noncomputable section

/-!
## CM lattices and multiples of fractional ideals

A datum `New.CMLattice d` is a lattice `Λ` stable under `𝓞 K` with a point `t` of order two such
that `ω t, ω̄ t ∉ Λ`, scaled to `℘''(t) = 2`, and a square root `a₁` of `12 ℘(t)`. The number
`ω = (1 + √-d) / 2` is `New.quadGen` in `ℂ` and `New.QuadField.betaK` in `𝓞 K`; `quadInt d` is the
image of `𝓞 K` in `ℂ`.
-/

namespace New

open Complex Set PeriodPair NumberField Module FractionalIdeal nonZeroDivisors Submodule CMLattice
  QuadField RingOfIntegers NeZero Basis

variable {d : ℕ}

/-- The lattice Λ of a CM datum regarded as an 𝒪_K-submodule of ℂ. -/
def CMLattice.latticeModule [PrimeSevenModEight d]
    (C : CMLattice d) : Submodule (𝓞 (QuadField d)) ℂ where
  toAddSubmonoid := C.Λ.1
  smul_mem' y _ hx := C.mul_mem_of_quadInt ⟨y, rfl⟩ hx

/-- The monoid homomorphism (u, 𝔞) ↦ u𝔞 from pairs of a nonzero complex number and a nonzero
fractional ideal of K to 𝓞_K-submodules of ℂ. -/
def QuadField.scaledIdeal (d : ℕ) :
    ℂˣ × (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ →* Submodule (𝓞 (QuadField d)) ℂ :=
  MonoidHom.coprod
    -- `u` goes to the span of `u`
    ((Submodule.spanSingleton (𝓞 (QuadField d))).toMonoidHom.comp (Units.coeHom ℂ))
    -- `𝔞` goes to its image in `ℂ`
    (MonoidHom.comp
      ((mapHom (IsScalarTower.toAlgHom (𝓞 (QuadField d)) (QuadField d) ℂ)).comp
        (coeSubmoduleHom (𝓞 (QuadField d))⁰ (QuadField d))).toMonoidHom
      (Units.coeHom _))

variable {C : CMLattice d}
  {x : ℂˣ × (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ}

/-- Membership in `u 𝔞`, for `x = (u, 𝔞)`: `z = u y` for some `y` in `𝔞`. -/
lemma QuadField.mem_scaledIdeal {x : ℂˣ × (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ}
    {z : ℂ} : z ∈ scaledIdeal d x ↔ ∃ y ∈ x.2.val, (x.1 : ℂ) * (y : QuadField d) = z := by
  simp [scaledIdeal, mem_span_singleton_mul]
/-- For a ℤ-basis b₀, b₁ of a fractional ideal of K = ℚ(√−d) and a nonzero complex number c, the
numbers cb₀, cb₁ are linearly independent over ℝ. -/
lemma QuadField.linearIndependent_mul_basis [PrimeSevenModEight d]
    {𝔠 : (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ} (b : Basis (Fin 2) ℤ 𝔠.1) (c : ℂˣ) :
    LinearIndependent ℝ ![(c * b 0 : ℂ), c * b 1] := by
  -- If `b 0 / b 1` were real, so would be `ω = ω b 1 / b 1`.
  suffices h_not_real : ∀ a : ℝ, (a : ℂ) * b 1 ≠ b 0 by
    simpa [linearIndependent_fin2, b.ne_zero, field] using h_not_real
  intro a ha
  -- the coordinates of `ω b 1`, an element of the ideal, are integers
  obtain ⟨m, n, h_repr⟩ : ∃ m n : ℤ, betaK d • b 1 = m • b 0 + n • b 1 :=
    ⟨_, _, (b.sum_repr (betaK d • b 1)).symm.trans (Fin.sum_univ_two _)⟩
  have h_omega : quadGen d * b 1 = m * b 0 + n * b 1 := by
    have h_two : ((2 : QuadField d) : ℂ) = 2 := map_ofNat (QuadField d).val 2
    simpa [Algebra.smul_def, quadGen, h_two] using
      congrArg (fun y : 𝔠.1 ↦ ((y : QuadField d) : ℂ)) h_repr
  have h_real : quadGen d = m * a + n := mul_right_cancel₀ (b := (b 1 : ℂ))
    (by simp [b.ne_zero]) (by linear_combination h_omega - m * ha)
  simpa [quadGen, NeZero.ne] using congrArg im h_real

/-- If the real part of a is that of ω = (1 + √−d)/2, then multiplication by a/2 does not map a
lattice into itself. -/
lemma QuadField.not_lattice_le_comap_half (L : PeriodPair) {a : ℂ} (ha : a.re = (quadGen d).re) :
    ¬L.lattice ≤ L.lattice.comap (.mulLeft ℤ (a / 2)) := by
  -- If `a / 2` maps the lattice into itself, so does `a / 2 + 1`, and both have integral norm; but
  -- the norms differ by `re a + 1 = 3 / 2`.
  intro h_le
  have h_add_one : ∀ z ∈ L.lattice, (a / 2 + 1) * z ∈ L.lattice := fun z hz ↦ by
    simpa [add_one_mul] using L.lattice.add_mem (h_le hz) hz
  obtain ⟨(N : ℕ), -, hN⟩ := exists_isIsogeny_of_mul_mem_lattice (a := a / 2) fun _ hz ↦ h_le hz
  obtain ⟨(N' : ℕ), -, hN'⟩ := exists_isIsogeny_of_mul_mem_lattice h_add_one
  have h_normSq : (normSq a : ℂ) = 2 ^ 2 * N := by simpa [mul_conj, ne_of_gt, field] using hN
  have h_parity : (2 ^ 2 * N + 2 ^ 2 + 2 : ℂ) = 2 ^ 2 * N' := by
    rw [← h_normSq]
    simpa [mul_conj, ha, quadGen, normSq_add, -map_add, ne_of_gt, field] using hN'
  norm_cast at h_parity
  lia

/-- If `L' = c L` for lattices `L`, `L'` and `c ≠ 0`, then `℘_{L'}(c z) = c⁻² ℘_L(z)`. -/
lemma weierstrassP_mul_eq_of_mul_mem_iff {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x ∈ L.lattice) (z : ℂ) :
    ℘[L'] (c * z) = ℘[L] z * (c ^ 2)⁻¹ := by
  let e : L.lattice ≃ L'.lattice := (Equiv.mulLeft₀ c hc).subtypeEquiv fun x ↦ (hL' x).symm
  have he (l : L.lattice) : (e l : ℂ) = c * l := rfl
  rw [weierstrassP, weierstrassP, ← e.tsum_eq, ← tsum_mul_right]
  exact tsum_congr fun l ↦ by simp [he, ← mul_sub, mul_pow, field]

/-- If `L' = c L` for lattices `L`, `L'` and `c ≠ 0`, then `g₂(L') = c⁻⁴ g₂(L)`. -/
lemma g₂_eq_of_mul_mem_iff {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x ∈ L.lattice) : L'.g₂ = L.g₂ * (c ^ 4)⁻¹ := by
  let e : L.lattice ≃ L'.lattice := (Equiv.mulLeft₀ c hc).subtypeEquiv fun x ↦ (hL' x).symm
  have he (l : L.lattice) : (e l : ℂ) = c * l := rfl
  rw [g₂, g₂, PeriodPair.G, PeriodPair.G, ← e.tsum_eq, mul_assoc, ← tsum_mul_right]
  simp [he, mul_pow, mul_comm]

/-- Every lattice `L` has a point `l` such that neither `ω l / 2` nor `ω̄ l / 2` lies in `L`, where
`ω = (1 + √-d) / 2` is `quadGen d`. -/
lemma exists_mem_lattice_quadGen_mul_half_notMem (L : PeriodPair) :
    ∃ l ∈ L.lattice,
      quadGen d * (l / 2) ∉ L.lattice ∧ starRingEnd ℂ (quadGen d) * (l / 2) ∉ L.lattice := by
  -- A group is not the union of two proper subgroups.
  have h_half : ¬L.lattice ≤ L.lattice.comap (.mulLeft ℤ (quadGen d / 2)) :=
    not_lattice_le_comap_half L rfl
  have h_half_conj : ¬L.lattice ≤ L.lattice.comap (.mulLeft ℤ (starRingEnd ℂ (quadGen d) / 2)) :=
    not_lattice_le_comap_half L (conj_re (quadGen d))
  simpa [not_subset, mul_comm_div] using
    AddSubgroupClass.subset_union.not.2 (not_or_intro h_half h_half_conj)

/-- For `d` a prime ≡ 7 mod 8 and `K = ℚ(√-d)`, every nonzero fractional ideal 𝔠 of K has a multiple
u𝔠, u ∈ ℂ^×, that is the lattice of a CM datum. Such a datum is a lattice stable under 𝓞_K with a
point t of order two such that ℘''(t) = 2 and ωt, ω̄t are not in it, where ω = (1 + √-d)/2, together
with a square root of 12℘(t). -/
lemma QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal [PrimeSevenModEight d]
    (𝔠 : (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ) :
    ∃ (C : CMLattice d) (u : ℂˣ), latticeModule C = scaledIdeal d (u, 𝔠) := by
  -- `𝔠` is a lattice `L 1` in `ℂ`. Neither `ω / 2` nor `ω̄ / 2` preserves it, so some `t = l / 2`,
  -- `l ∈ L 1`, has `ω t, ω̄ t ∉ L 1`. Then `℘''(t) ≠ 0`, and scaling the lattice makes
  -- `℘''(t) = 2`.
  have b : Basis (Fin 2) ℤ 𝔠.1 :=
    finBasisOfFinrankEq ℤ 𝔠 (by rw [fractionalIdeal_rank, rank, finrank_eq_two])
  let L (c : ℂˣ) : PeriodPair := ⟨c * b 0, c * b 1, linearIndependent_mul_basis b c⟩
  have mem_iff (c : ℂˣ) (z : ℂ) : z ∈ (L c).lattice ↔ z ∈ scaledIdeal d (c, 𝔠) := by
    trans ∃ y : 𝔠.1, (c : ℂ) * y = z
    · refine mem_lattice.trans (.trans ?_ b.equivFun.symm.surjective.exists.symm)
      simp [L, field, Fin.exists_fin_succ_pi]
    · simp [mem_scaledIdeal]
  have h_smul (c : ℂˣ) (y : 𝓞 (QuadField d)) (z : ℂ) (hz : z ∈ (L c).lattice) :
      y • z ∈ (L c).lattice := (mem_iff c _).2 (smul_mem _ y ((mem_iff c z).1 hz))
  obtain ⟨l, hl, h_om, h_conj⟩ := exists_mem_lattice_quadGen_mul_half_notMem (d := d) (L 1)
  -- `ω` is the image of the integer `betaK d`, so with `t` also `ω t` would be in the lattice.
  have ht : l / 2 ∉ (L 1).lattice := fun h ↦ h_om (h_smul 1 (betaK d) _ h)
  -- `℘''(t) / 2 = 3 ℘(t)² - g₂ / 4 ≠ 0`, as `℘(t)` is a simple root of the cubic `4x³ - g₂x - g₃`.
  -- Scaling by a fourth root `c` of this number makes `℘''(t) = 2`.
  obtain ⟨c, hc⟩ : ∃ c, c ^ 4 = 3 * ℘[L 1] (l / 2) ^ 2 - (L 1).g₂ / 4 :=
    IsSepClosed.exists_pow_nat_eq _ 4
  have h_ne : 3 * ℘[L 1] (l / 2) ^ 2 - (L 1).g₂ / 4 ≠ 0 := by
    have h_cubic : 4 * ℘[L 1] (l / 2) ^ 3 - (L 1).g₂ * ℘[L 1] (l / 2) - (L 1).g₃ = 0 := by
      rw [← (L 1).derivWeierstrassP_sq _ ht,
        (derivWeierstrassP_eq_zero_iff (L 1) ht).2 (by rwa [add_halves]), zero_pow two_ne_zero]
    -- a common root of the cubic and its derivative `12 x² - g₂` would kill its discriminant
    grind [weierstrass_disc_ne_zero (L 1)]
  lift c to ℂˣ using (ne_zero_pow four_ne_zero (hc.trans_ne h_ne)).isUnit
  -- The lattice, `℘` and `g₂` scale with `c`.
  have h_mem (z : ℂ) : c * z ∈ (L c).lattice ↔ z ∈ (L 1).lattice := by
    simp [mem_iff, mem_scaledIdeal]
  have h_g₂_eq : (L c).g₂ = 12 * ℘[L c] (c * (l / 2)) ^ 2 - 4 := by
    rw [g₂_eq_of_mul_mem_iff c.ne_zero h_mem, weierstrassP_mul_eq_of_mul_mem_iff c.ne_zero h_mem]
    grind [c.ne_zero]
  let C : CMLattice d :=
    { periodPair := L c
      t := c * (l / 2)
      a₁ := (12 * ℘[L c] (c * (l / 2))) ^ (2⁻¹ : ℂ)
      g₂_eq := h_g₂_eq
      mul_mem_of_quadInt := by
        rintro _ _ ⟨y, rfl⟩
        exact h_smul c y
      two_t_mem := by rwa [← mul_add, add_halves, h_mem]
      t_notMem := (h_mem _).not.2 ht
      quadGen_mul_t_notMem := by simp [mul_left_comm _ (c : ℂ), h_mem, h_om, h_conj]
      a₁_sq := cpow_ofNat_inv_pow _ 2 }
  exact ⟨C, c, Submodule.ext (mem_iff c)⟩

/-- If the fractional ideal 𝔠 has trivial class, then every 𝓞_K-submodule N of ℂ equals u𝔠N for
some u ∈ ℂ^×. -/
lemma QuadField.exists_eq_scaledIdeal_mul_of_mk_eq_one
    {𝔠 : (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ}
    (h𝔠 : ClassGroup.mk (QuadField d) 𝔠 = 1) (N : Submodule (𝓞 (QuadField d)) ℂ) :
    ∃ u : ℂˣ, N = scaledIdeal d (u, 𝔠) * N := by
  -- `𝔠` is principal, generated by `γ`; take `u = γ⁻¹`.
  obtain ⟨γ, hγ⟩ :
      ∃ γ : (QuadField d)ˣ, toPrincipalIdeal (𝓞 (QuadField d)) (QuadField d) γ = 𝔠 := by
    simpa using congrArg (ClassGroup.equiv (QuadField d)) h𝔠
  use γ⁻¹.map (QuadField d).val
  simp [scaledIdeal, ← hγ, map_span, span_mul_span, ← one_eq_span]

variable [PrimeSevenModEight d]

/-- The lattice of a CM datum is `u 𝔞` for some `u` in `ℂˣ` and nonzero fractional ideal `𝔞`. -/
lemma CMLattice.exists_latticeModule_eq_scaledIdeal (C : CMLattice d) :
    ∃ x : ℂˣ × (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ,
      latticeModule C = scaledIdeal d x := by
  -- Write `ω ω₂ = m ω₁ + n ω₂`. Then `ω₂ = ω₁ * (m / (ω - n))`, so the lattice is `ω₁` times the
  -- fractional ideal spanned by `1` and `m / (ω - n)`.
  obtain ⟨m, n, hmn⟩ : ∃ m n : ℤ, m * C.ω₁ + n * C.ω₂ = quadGen d * C.ω₂ :=
    mem_lattice.1 (C.mul_mem_of_quadInt quadGen_mem_quadInt C.ω₂_mem_lattice)
  have hn : quadGen d ≠ n := by simp [quadGen, Complex.ext_iff, NeZero.ne]
  have hω₂ : C.ω₁ * (m / (quadGen d - n)) = C.ω₂ := by grind
  have hω₁ : C.ω₁ ≠ 0 := C.indep.ne_zero 0
  use (.mk0 C.ω₁ hω₁, .mk0 (spanFinset _ {1, m / ((betaK d).1 - n)} id) (by simp))
  have h_span : latticeModule C = span (𝓞 (QuadField d)) {C.ω₁, C.ω₂} :=
    C.latticeModule.span_eq.symm.trans (span_span_of_tower ..)
  have h_coe : (((betaK d).1 : QuadField d) : ℂ) = quadGen d := rfl
  rw [h_span, ← hω₂]
  simp [scaledIdeal, map_span, span_mul_span, h_coe]

/-- For a nonzero fractional ideal `𝔠` and a CM datum with lattice `Λ`, some multiple `u 𝔠 Λ`,
`u` in `ℂˣ`, is the lattice of a CM datum. -/
lemma CMLattice.exists_latticeModule_eq_scaledIdeal_mul
    (𝔠 : (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ) (C : CMLattice d) :
    ∃ (D : CMLattice d) (u : ℂˣ), latticeModule D = scaledIdeal d (u, 𝔠) * latticeModule C := by
  -- if `C` has the lattice `Λ = v 𝔞` and `D` the lattice `u 𝔠 𝔞`, the latter is `(u / v) 𝔠 Λ`
  obtain ⟨⟨v, 𝔞⟩, hC⟩ := C.exists_latticeModule_eq_scaledIdeal
  obtain ⟨D, u, hD⟩ := QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal (𝔠 * 𝔞)
  exact ⟨D, u / v, by simp [hC, hD, ← map_mul]⟩

/-- If the lattice Λ of C is u𝔞, with x = (u, 𝔞), then multiplication by u is an additive
isomorphism 𝔞 ≅ Λ. -/
def QuadField.latticeEquiv (h : latticeModule C = scaledIdeal d x) : x.2 ≃+ C.Λ :=
  AddEquiv.ofBijective
    (AddHom.mk (fun y ↦ ⟨x.1 * y, h.ge (mem_scaledIdeal.2 ⟨y, y.2, rfl⟩)⟩)
      (fun y z ↦ Subtype.ext (by simp [mul_add])))
    ⟨fun y z hyz ↦ Subtype.ext (by simpa using congrArg Subtype.val hyz),
      fun z ↦ by simpa [mem_scaledIdeal, Subtype.ext_iff] using h.le z.2⟩

/-- Let d be a prime ≡ 7 mod 8. If the lattice of C equals u𝔞, with x = (u, 𝔞), u ∈ ℂ^× and 𝔞 a
nonzero fractional ideal of K = ℚ(√−d), then its area is |u|²·N(𝔞)·√d/2. -/
lemma QuadField.area_eq_of_eq_scaledIdeal {C : CMLattice d}
    {x : ℂˣ × (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ}
    (hC : latticeModule C = scaledIdeal d x) :
    C.area = ‖x.1.val‖ ^ 2 * absNorm x.2.val * √d / 2 := by
  -- `1, betaK d` is a `ℤ`-basis `B` of the ring of integers.
  obtain ⟨P, hP_gen, hP_dim⟩ : ∃ P : PowerBasis ℤ (𝓞 (QuadField d)), P.gen = betaK d ∧ P.dim = 2 :=
    ⟨.ofAdjoinEqTop' (.of_finite ..) (different_eq_span_and_adjoin_betaK d).2,
      by simp [← PowerBasis.finrank, RingOfIntegers.rank, finrank_eq_two]⟩
  let B : Basis (Fin 2) ℤ (𝓞 (QuadField d)) := P.basis.reindex (finCongr hP_dim)
  have hB (i : Fin 2) : B i = betaK d ^ (i : ℕ) := by simp [B, hP_gen]
  let BK : Basis (Fin 2) ℚ (QuadField d) := B.localizationLocalization ℚ ℤ⁰ (QuadField d)
  -- `f` is division by `u = x.1`; it carries the lattice basis to a basis of the ideal `x.2`,
  -- whose determinant against `B` is the norm of the ideal up to sign.
  let f : C.Λ ≃+ x.2 := (latticeEquiv hC).symm
  have h_norm : |BK.det (Subtype.val ∘ C.latticeBasis.map f.toIntLinearEquiv)| = absNorm x.2.1 :=
    abs_det_basis_change B x.2.1 _
  have h_equiv (y : x.2.val) : (latticeEquiv hC y : ℂ) = x.1 * y := rfl
  have h_coord (z : C.Λ) : z.1 = x.1 * (BK.repr (f z) 0 + BK.repr (f z) 1 * quadGen d) := by
    have h_sum : z.1 = x.1 * ((∑ i, BK.repr (f z) i • BK i : QuadField d) : ℂ) := by
      rw [BK.sum_repr, ← h_equiv, AddEquiv.apply_symm_apply]
    have h_two : ((2 : QuadField d) : ℂ) = 2 := map_ofNat (QuadField d).val 2
    simpa [Fin.sum_univ_two, BK, hB, Rat.smul_def, h_two, quadGen] using h_sum
  rw [area, ← latticeBasis_zero, ← latticeBasis_one, ← h_norm, ← sq_eq_sq₀ (by simp) (by bound)]
  -- Compare squares. In coordinates `zⱼ = u (aⱼ + bⱼ ω)` one has
  -- `im (conj z₀ * z₁) = |u|² (a₀ b₁ - a₁ b₀) im ω`, and `im ω = √d / 2`.
  simp [h_coord, BK, det, Matrix.det_succ_row_zero, toMatrix, div_eq_mul_inv, field, quadGen,
    normSq, Complex.sq_norm, -Real.sq_sqrt]
  ring

end New

/-!
## Good reduction of the CM curve

For a point `u` of order two, `s(u)` is the discriminant of the lattice scaled to `℘''(u) = 2`. Here
`t` is the point `C.t` of a datum `C`, and `ω = (1 + √-d) / 2` is `quadGen d`.
-/

section GoodReduction

open NumberField Finset ComplexConjugate nonZeroDivisors

namespace PeriodPair
open New
variable {L L' : PeriodPair} {u u₁ u₂ u₃ : ℂ}

/-- `u` represents a point of order two on `ℂ / L`. -/
structure IsOrderTwo (L : PeriodPair) (u : ℂ) : Prop where
  /-- The point is not the origin. -/
  notMem : u ∉ L.lattice
  /-- Twice the point is the origin. -/
  add_self_mem : u + u ∈ L.lattice

/-- The number `s(u) = 288 ℘(u)² / ℘''(u) - 64`. For a point `u` of order two it is the
discriminant of the lattice after the scaling that makes `℘''(u) = 2`. -/
noncomputable def scaledDisc (L : PeriodPair) (u : ℂ) : ℂ := 288 * ℘[L] u ^ 2 / deriv ℘'[L] u - 64

/-- Off the lattice, `℘''(u)` is six times the sum of `(l - u)⁻⁴` over the lattice. -/
lemma deriv_derivWeierstrassP_eq_sumInvPow (hu : u ∉ L.lattice) :
    deriv ℘'[L] u = 6 * L.sumInvPow u 4 := by
  rw [← L.derivWeierstrassPExcept_of_notMem u hu, deriv_derivWeierstrassPExcept_self]

lemma weierstrassP_congr (h_sub : u₁ - u₂ ∈ L.lattice) : ℘[L] u₁ = ℘[L] u₂ := by
  simpa only [add_sub_cancel] using L.weierstrassP_add_coe u₂ ⟨u₁ - u₂, h_sub⟩

lemma scaledDisc_congr (hu₁ : u₁ ∉ L.lattice) (h_sub : u₁ - u₂ ∈ L.lattice) :
    L.scaledDisc u₁ = L.scaledDisc u₂ := by
  have hu₂ : u₂ ∉ L.lattice := fun h ↦ hu₁ (by simpa using add_mem h_sub h)
  simp [scaledDisc, deriv_derivWeierstrassP, hu₁, hu₂, weierstrassP_congr h_sub]

lemma IsOrderTwo.weierstrassP_cubic_eq_zero (hu : L.IsOrderTwo u) :
    4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := by
  rw [← L.derivWeierstrassP_sq u hu.notMem,
    (derivWeierstrassP_eq_zero_iff L hu.notMem).2 hu.add_self_mem, zero_pow two_ne_zero]

/-- If `u₁`, `u₂`, `u₃` are points of order two whose sum is a period, then `℘(u₁) ≠ ℘(u₂)`. -/
lemma IsOrderTwo.weierstrassP_ne (h₁ : L.IsOrderTwo u₁) (h₂ : L.IsOrderTwo u₂)
    (h₃ : L.IsOrderTwo u₃) (h_sum : u₁ + u₂ + u₃ ∈ L.lattice) : ℘[L] u₁ ≠ ℘[L] u₂ := by
  intro h_eq
  have h_add : u₁ + u₂ ∉ L.lattice := fun h ↦ h₃.notMem (by simpa using sub_mem h_sum h)
  have h_sub : u₁ - u₂ ∉ L.lattice := fun h ↦ h_add (by simpa using add_mem h h₂.add_self_mem)
  have h_sigma : L.σ (u₁ + u₂) * L.σ (u₁ - u₂) = 0 := by
    simp [sigma_add_mul_sigma_sub h₁.notMem h₂.notMem, h_eq]
  simp [sigma_eq_zero_iff, h_add, h_sub] at h_sigma

/-- Let `u₁`, `u₂`, `u₃` be points of order two of `ℂ / L` whose sum is a period, with
`eᵢ = ℘(uᵢ)`. The `eᵢ` are the three roots of the cubic `4 X³ - g₂ X - g₃`, so their sum is `0`
and `℘''(u₁) = 2 (e₁ - e₂) (e₁ - e₃)`. -/
lemma IsOrderTwo.sum_eq_zero_and_deriv_derivWeierstrassP_eq (h₁ : L.IsOrderTwo u₁)
    (h₂ : L.IsOrderTwo u₂) (h₃ : L.IsOrderTwo u₃) (h_sum : u₁ + u₂ + u₃ ∈ L.lattice) :
    ℘[L] u₁ + ℘[L] u₂ + ℘[L] u₃ = 0 ∧
    deriv ℘'[L] u₁ = 2 * (℘[L] u₁ - ℘[L] u₂) * (℘[L] u₁ - ℘[L] u₃) := by
  have h₁₂ : ℘[L] u₁ ≠ ℘[L] u₂ := h₁.weierstrassP_ne h₂ h₃ h_sum
  have h₁₃ : ℘[L] u₁ ≠ ℘[L] u₃ := h₁.weierstrassP_ne h₃ h₂ (by rwa [add_right_comm])
  have h₂₃ : ℘[L] u₂ ≠ ℘[L] u₃ := h₂.weierstrassP_ne h₃ h₁ (by rwa [add_rotate] at h_sum)
  have hg₂ {v : ℂ} (hv : L.IsOrderTwo v) (h_ne : ℘[L] u₁ ≠ ℘[L] v) :
      L.g₂ = 4 * (℘[L] u₁ ^ 2 + ℘[L] u₁ * ℘[L] v + ℘[L] v ^ 2) :=
    mul_left_cancel₀ (sub_ne_zero.2 h_ne)
      (by linear_combination hv.weierstrassP_cubic_eq_zero - h₁.weierstrassP_cubic_eq_zero)
  have h_zero : ℘[L] u₁ + ℘[L] u₂ + ℘[L] u₃ = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 h₂₃) (by linear_combination (hg₂ h₃ h₁₃ - hg₂ h₂ h₁₂) / 4)
  refine ⟨h_zero, ?_⟩
  rw [deriv_derivWeierstrassP _ h₁.notMem, hg₂ h₂ h₁₂]
  linear_combination (2 * ℘[L] u₁ - 2 * ℘[L] u₂) * h_zero

/-- Let `u₁`, `u₂`, `u₃` be points of order two whose sum is a period, with `eᵢ = ℘(uᵢ)`. With
`δ₁ = e₂ - e₃`, `δ₂ = e₃ - e₁`, `δ₃ = e₁ - e₂` we have `s(u₁) = -16 δ₁² / (δ₂ δ₃)`, where `s` is
`scaledDisc`. -/
lemma IsOrderTwo.scaledDisc_eq (h₁ : L.IsOrderTwo u₁) (h₂ : L.IsOrderTwo u₂)
    (h₃ : L.IsOrderTwo u₃) (h_sum : u₁ + u₂ + u₃ ∈ L.lattice) :
    L.scaledDisc u₁ =
      -16 * (℘[L] u₂ - ℘[L] u₃) ^ 2 / ((℘[L] u₃ - ℘[L] u₁) * (℘[L] u₁ - ℘[L] u₂)) := by
  obtain ⟨h_zero, h_deriv⟩ := h₁.sum_eq_zero_and_deriv_derivWeierstrassP_eq h₂ h₃ h_sum
  have h₃₁ : ℘[L] u₃ ≠ ℘[L] u₁ := h₃.weierstrassP_ne h₁ h₂ (by rwa [add_rotate])
  have h₁₂ : ℘[L] u₁ ≠ ℘[L] u₂ := h₁.weierstrassP_ne h₂ h₃ h_sum
  rw [scaledDisc, h_deriv]
  grind

/-- For three points `uᵢ` of order two of `ℂ / L` whose sum is a period, the numbers `s(uᵢ)` (see
`scaledDisc`) have the sum `-48` and the product `-2¹²`. -/
lemma IsOrderTwo.scaledDisc_sum_prod (h₁ : L.IsOrderTwo u₁) (h₂ : L.IsOrderTwo u₂)
    (h₃ : L.IsOrderTwo u₃) (h_sum : u₁ + u₂ + u₃ ∈ L.lattice) :
    L.scaledDisc u₁ + L.scaledDisc u₂ + L.scaledDisc u₃ = -48 ∧
    L.scaledDisc u₁ * L.scaledDisc u₂ * L.scaledDisc u₃ = -2 ^ 12 := by
  have h_sum₂ : u₂ + u₃ + u₁ ∈ L.lattice := by rwa [add_rotate] at h_sum
  have h_sum₃ : u₃ + u₁ + u₂ ∈ L.lattice := by rwa [add_rotate] at h_sum₂
  have h₂₃ : ℘[L] u₂ ≠ ℘[L] u₃ := h₂.weierstrassP_ne h₃ h₁ h_sum₂
  have h₃₁ : ℘[L] u₃ ≠ ℘[L] u₁ := h₃.weierstrassP_ne h₁ h₂ h_sum₃
  have h₁₂ : ℘[L] u₁ ≠ ℘[L] u₂ := h₁.weierstrassP_ne h₂ h₃ h_sum
  rw [h₁.scaledDisc_eq h₂ h₃ h_sum, h₂.scaledDisc_eq h₃ h₁ h_sum₂, h₃.scaledDisc_eq h₁ h₂ h_sum₃]
  -- The sum is `-48` as the differences `δᵢ` of the `℘(uⱼ)` satisfy `δ₁³ + δ₂³ + δ₃³ = 3 δ₁ δ₂ δ₃`.
  exact ⟨by field, by field⟩

/-- If `c⁻¹ L'` is the union of the cosets `L - u` and `L`, with `u ∉ L`, then the sum
`L'.sumInvPow (c y) 4` of `(l - c y)⁻⁴` over `l ∈ L'` is `c⁻⁴` times the total of the sums of
`(l - (u + y))⁻⁴` and of `(l - y)⁻⁴` over `l ∈ L`. -/
lemma sumInvPow_four_of_two_cosets {c : ℂ} (hc : c ≠ 0) (hu : u ∉ L.lattice)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x + u ∈ L.lattice ∨ x ∈ L.lattice) (y : ℂ) :
    L'.sumInvPow (c * y) 4 = (L.sumInvPow (u + y) 4 + L.sumInvPow y 4) / c ^ 4 := by
  classical
  let f (M : PeriodPair) (z : ℂ) : ℂ → ℂ := (M.lattice : Set ℂ).indicator fun l ↦ ((l - z) ^ 4)⁻¹
  have h_sum (M : PeriodPair) (z : ℂ) : HasSum (f M z) (M.sumInvPow z 4) :=
    hasSum_subtype_iff_indicator.1 (M.hasSum_sumInvPow z (by norm_num))
  -- Pull the sum over `L'` back along `x ↦ c x`, and compare it term by term with the two sums
  -- over `L`, the first of them shifted by `u`.
  have h_left : HasSum (f L' (c * y) ∘ Equiv.mulLeft₀ c hc) (L'.sumInvPow (c * y) 4) :=
    (Equiv.mulLeft₀ c hc).hasSum_iff.2 (h_sum L' (c * y))
  have h_shift : HasSum (f L (u + y) ∘ Equiv.addRight u) (L.sumInvPow (u + y) 4) :=
    (Equiv.addRight u).hasSum_iff.2 (h_sum L (u + y))
  refine h_left.unique (((h_shift.add (h_sum L y)).div_const (c ^ 4)).congr_fun fun x ↦ ?_)
  have h_not (h : x + u ∈ L.lattice) : x ∉ L.lattice := fun h' ↦ hu (by simpa using sub_mem h h')
  have h_term : ((c * x - c * y) ^ 4)⁻¹ = ((x - y) ^ 4)⁻¹ / c ^ 4 := by
    rw [← mul_sub, mul_pow, mul_inv, div_eq_inv_mul]
  simp only [f, Function.comp_apply, Equiv.mulLeft₀_apply, Equiv.coe_addRight, Set.indicator,
    SetLike.mem_coe, hL', add_comm u y, add_sub_add_right_eq_sub, h_term]
  -- The point `x` lies in at most one of the two cosets.
  grind

/-- If `c⁻¹ L'` is the union of `L - u` and `L`, with `u ∉ L`, then, away from the lattices,
`℘''_{L'}(c y) = c⁻⁴ (℘''(u + y) + ℘''(y))`. -/
lemma deriv_derivWeierstrassP_of_two_cosets {c : ℂ} (hc : c ≠ 0) (hu : u ∉ L.lattice)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x + u ∈ L.lattice ∨ x ∈ L.lattice) {y : ℂ}
    (hcy : c * y ∉ L'.lattice) (huy : u + y ∉ L.lattice) (hy : y ∉ L.lattice) :
    deriv ℘'[L'] (c * y) = (deriv ℘'[L] (u + y) + deriv ℘'[L] y) / c ^ 4 := by
  rw [deriv_derivWeierstrassP_eq_sumInvPow hcy, sumInvPow_four_of_two_cosets hc hu hL',
    deriv_derivWeierstrassP_eq_sumInvPow huy, deriv_derivWeierstrassP_eq_sumInvPow hy]
  ring

/-- If `c⁻¹ L'` is the union of `L - u` and `L`, with `u ∉ L`, then
`g₂(L') = c⁻⁴ (g₂(L) + 10 ℘''(u))`. -/
lemma g₂_eq_of_two_cosets {c : ℂ} (hc : c ≠ 0) (hu : u ∉ L.lattice)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x + u ∈ L.lattice ∨ x ∈ L.lattice) :
    L'.g₂ = (L.g₂ + 10 * deriv ℘'[L] u) / c ^ 4 := by
  have h_split : L'.G 4 = (L.sumInvPow u 4 + L.G 4) / c ^ 4 := by
    simpa only [mul_zero, add_zero, sumInvPow_zero] using
      sumInvPow_four_of_two_cosets hc hu hL' 0
  rw [g₂, g₂, h_split, deriv_derivWeierstrassP_eq_sumInvPow hu]
  ring

/-- Let `u₁, u₂, u₃` be points of order two modulo `L` whose sum is a period, and let `c ≠ 0` be
such that `L' = c (L + ℤ u₁)`, that is, `c x ∈ L'` if and only if `x + u₁` or `x` lies in `L`. Write
`s(u) = 288 ℘(u)² / ℘''(u) - 64` (`scaledDisc`), computed with the ℘-function of the lattice in
question. Then `s(u₁)` for `L` and `s(c u₂)` for `L'` have the product `2¹²`. -/
lemma IsOrderTwo.scaledDisc_mul_of_isogeny {L L' : PeriodPair} {u₁ u₂ u₃ : ℂ}
    (h₁ : L.IsOrderTwo u₁) (h₂ : L.IsOrderTwo u₂)
    (h₃ : L.IsOrderTwo u₃) (h_sum : u₁ + u₂ + u₃ ∈ L.lattice) {c : ℂ} (hc : c ≠ 0)
    (hL' : ∀ x : ℂ, c * x ∈ L'.lattice ↔ x + u₁ ∈ L.lattice ∨ x ∈ L.lattice) :
    L.scaledDisc u₁ * L'.scaledDisc (c * u₂) = 2 ^ 12 := by
  have h_sum₂ : u₂ + u₃ + u₁ ∈ L.lattice := by rwa [add_rotate] at h_sum
  have h_sum₃ : u₃ + u₁ + u₂ ∈ L.lattice := by rwa [add_rotate] at h_sum₂
  have h₁₂ : u₁ + u₂ - u₃ ∈ L.lattice := by
    simpa only [add_sub_add_right_eq_sub] using sub_mem h_sum h₃.add_self_mem
  have h₁₂' : u₁ + u₂ ∉ L.lattice := fun h ↦
    h₃.notMem (by simpa only [add_sub_cancel_left] using sub_mem h_sum h)
  have h₂' : c * u₂ ∉ L'.lattice := by simp [hL', add_comm u₂, h₁₂', h₂.notMem]
  obtain ⟨h_zero, h_deriv₁⟩ := h₁.sum_eq_zero_and_deriv_derivWeierstrassP_eq h₂ h₃ h_sum
  have h_deriv₂ : deriv ℘'[L] u₂ = 2 * (℘[L] u₂ - ℘[L] u₃) * (℘[L] u₂ - ℘[L] u₁) :=
    (h₂.sum_eq_zero_and_deriv_derivWeierstrassP_eq h₃ h₁ h_sum₂).2
  have h_deriv₃ : deriv ℘'[L] u₃ = 2 * (℘[L] u₃ - ℘[L] u₁) * (℘[L] u₃ - ℘[L] u₂) :=
    (h₃.sum_eq_zero_and_deriv_derivWeierstrassP_eq h₁ h₂ h_sum₃).2
  have h_root₃ : ℘[L] u₃ = -(℘[L] u₁ + ℘[L] u₂) := eq_neg_of_add_eq_zero_right h_zero
  have hδ₁ : ℘[L] u₂ - ℘[L] u₃ ≠ 0 := sub_ne_zero.2 (h₂.weierstrassP_ne h₃ h₁ h_sum₂)
  have hδ₂ : ℘[L] u₃ - ℘[L] u₁ ≠ 0 := sub_ne_zero.2 (h₃.weierstrassP_ne h₁ h₂ h_sum₃)
  have hδ₃ : ℘[L] u₁ - ℘[L] u₂ ≠ 0 := sub_ne_zero.2 (h₁.weierstrassP_ne h₂ h₃ h_sum)
  -- For `L'` the second derivative of `℘` at `c u₂` is `c⁻⁴ (℘''(u₃) + ℘''(u₂))`.
  have h_deriv' : deriv ℘'[L'] (c * u₂) = 2 * (℘[L] u₂ - ℘[L] u₃) ^ 2 / c ^ 4 := by
    have h_deriv₁₂ : deriv ℘'[L] (u₁ + u₂) = deriv ℘'[L] u₃ := by
      rw [deriv_derivWeierstrassP _ h₁₂', deriv_derivWeierstrassP _ h₃.notMem,
        weierstrassP_congr h₁₂]
    rw [deriv_derivWeierstrassP_of_two_cosets hc h₁.notMem hL' h₂' h₁₂' h₂.notMem, h_deriv₁₂,
      h_deriv₂, h_deriv₃]
    ring
  -- With `g₂(L') = c⁻⁴ (g₂(L) + 10 ℘''(u₁))` and `℘'' = 6 ℘² - g₂ / 2` for both lattices, this
  -- gives `℘_{L'}(c u₂)² = c⁻⁴ (2 ℘(u₁))²`.
  have h_sq : ℘[L'] (c * u₂) ^ 2 = (2 * ℘[L] u₁) ^ 2 / c ^ 4 := by
    have h_deriv_L : deriv ℘'[L] u₁ = 6 * ℘[L] u₁ ^ 2 - L.g₂ / 2 :=
      deriv_derivWeierstrassP L h₁.notMem
    have h_deriv_L' := deriv_derivWeierstrassP L' h₂'
    rw [h_deriv', g₂_eq_of_two_cosets hc h₁.notMem hL', h_root₃] at h_deriv_L'
    rw [h_root₃] at h_deriv₁
    linear_combination -h_deriv_L' / 6 + (h_deriv_L / 6 + 2 / 3 * h_deriv₁) / c ^ 4
  rw [h₁.scaledDisc_eq h₂ h₃ h_sum, scaledDisc, h_deriv', h_sq]
  field_simp
  rw [h_root₃]
  ring

end PeriodPair

namespace New

open PeriodPair QuadField Submodule
variable {p : ℕ} [Fact p.Prime] {x y : ℂ_[p]}

/-- The difference of two integral elements of `ℂ_[p]` is integral. -/
lemma norm_sub_le_one (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  simpa [sub_eq_add_neg] using
    (IsUltrametricDist.norm_add_le_max x (-y)).trans (max_le hx (by rwa [norm_neg]))

/-- If two elements `x, y` of `ℂ_[p]` have an integral sum and a product of norm `> 1`, then the
norm of that product is `‖x‖²` (the two norms are equal). -/
lemma norm_sq_eq_of_norm_add_le_one (h_add : ‖x + y‖ ≤ 1) (h_mul : 1 < ‖x * y‖) :
    ‖x‖ ^ 2 = ‖x * y‖ := by
  have h_eq : ‖x‖ = ‖y‖ := by
    by_contra h_ne
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne, max_le_iff] at h_add
    rw [norm_mul] at h_mul
    exact h_mul.not_ge ((mul_le_of_le_one_left (norm_nonneg y) h_add.1).trans h_add.2)
  simp [h_eq, sq]

/-- Let `s, s', s₀` be functions with values in `ℂ_[p]` on a finite group such that, for all `c`,
`s(c) + s'(c) + s₀(c)` and `s(c) s'(g c)` are integral and `s(g c) s₀(g c) = -s(c)`. Then `s` is
integral: a norm `‖s(c)‖ > 1` would be replaced by its square root at each step `c ↦ g c`, and the
steps return to `c`. -/
lemma norm_le_one_of_cycle {G : Type*} [Group G] [Finite G] (g : G) {s s' s₀ : G → ℂ_[p]}
    (h_sum : ∀ c : G, ‖s c + s' c + s₀ c‖ ≤ 1) (h_dual : ∀ c : G, ‖s c * s' (g * c)‖ ≤ 1)
    (h_step : ∀ c : G, s (g * c) * s₀ (g * c) = -s c) (c : G) : ‖s c‖ ≤ 1 := by
  have halve (c : G) (hc : 1 < ‖s c‖) : ‖s (g * c)‖ ^ 2 = ‖s c‖ := by
    have hs' : ‖s' (g * c)‖ ≤ 1 := by
      nlinarith [norm_mul (s c) (s' (g * c)), h_dual c, norm_nonneg (s' (g * c))]
    have h_add : ‖s (g * c) + s₀ (g * c)‖ ≤ 1 := by
      simpa [add_right_comm _ (s' _)] using norm_sub_le_one (h_sum (g * c)) hs'
    have h_mul : 1 < ‖s (g * c) * s₀ (g * c)‖ := by rwa [h_step, norm_neg]
    rw [norm_sq_eq_of_norm_add_le_one h_add h_mul, h_step, norm_neg]
  by_contra! hc
  have iterate (i : ℕ) : ‖s (g ^ i * c)‖ ^ 2 ^ i = ‖s c‖ := by
    induction i with
    | zero => simp
    | succ i ih =>
      have h_gt : 1 < ‖s (g ^ i * c)‖ :=
        lt_of_pow_lt_pow_left₀ (2 ^ i) (norm_nonneg _) (by rwa [one_pow, ih])
      rw [pow_succ' g, mul_assoc, pow_succ' 2, pow_mul, halve _ h_gt, ih]
  -- At `i = orderOf g` this says `‖s c‖ ^ 2 ^ i = ‖s c‖`.
  exact (lt_self_pow₀ hc (Nat.one_lt_two_pow (orderOf_pos g).ne')).ne'
    (by simpa only [pow_orderOf_eq_one, one_mul] using iterate (orderOf g))

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) {D : CMLattice d} {b : ℂ}

lemma isOrderTwo_t : C.IsOrderTwo C.t := ⟨C.t_notMem, C.two_t_mem⟩

/-- At the point `t` of a CM lattice the number `s` (see `scaledDisc`) is `a₁⁴ - 64`, where `a₁` is
the chosen square root of `12 ℘(t)`. -/
lemma scaledDisc_t : C.scaledDisc C.t = C.a₁ ^ 4 - 64 := by
  rw [scaledDisc, deriv_derivWeierstrassP _ C.t_notMem, C.g₂_eq]
  linear_combination -(C.a₁ ^ 2 + 12 * ℘[C.periodPair] C.t) * C.a₁_sq

/-- If `b` is `ω = (1 + √-d) / 2` or `ω̄`, then so is `1 - b`. -/
lemma one_sub_eq_quadGen_or_conj (hb : b = quadGen d ∨ b = conj (quadGen d)) :
    1 - b = quadGen d ∨ 1 - b = conj (quadGen d) := by
  rw [conj_quadGen] at hb ⊢
  obtain rfl | rfl := hb <;> simp

variable [PrimeSevenModEight d]

lemma mem_quadInt_of_eq_quadGen_or_conj (hb : b = quadGen d ∨ b = conj (quadGen d)) :
    b ∈ quadInt d := by
  obtain rfl | rfl := hb
  exacts [quadGen_mem_quadInt, conj_mem_quadInt quadGen_mem_quadInt]

/-- For a CM lattice with point `t`, the points `ω t` and `ω̄ t` have order two; here
`ω = (1 + √-d) / 2` is `quadGen d`. -/
lemma isOrderTwo_mul_t (hb : b = quadGen d ∨ b = conj (quadGen d)) : C.IsOrderTwo (b * C.t) where
  notMem := by
    obtain rfl | rfl := hb
    exacts [C.quadGen_mul_t_notMem.1, C.quadGen_mul_t_notMem.2]
  add_self_mem := by
    rw [← mul_add]
    exact C.mul_mem_of_quadInt (mem_quadInt_of_eq_quadGen_or_conj hb) C.two_t_mem

/-- For `b = ω` or `ω̄`, where `ω = (1 + √-d) / 2`, the points of order two of a CM lattice are
`b t`, `(1 - b) t` and `t`. So their numbers `scaledDisc` have the sum `-48` and the product
`-2¹²`. -/
lemma scaledDisc_sum_prod (hb : b = quadGen d ∨ b = conj (quadGen d)) :
    C.scaledDisc (b * C.t) + C.scaledDisc ((1 - b) * C.t) + C.scaledDisc C.t = -48 ∧
    C.scaledDisc (b * C.t) * C.scaledDisc ((1 - b) * C.t) * C.scaledDisc C.t = -2 ^ 12 :=
  (C.isOrderTwo_mul_t hb).scaledDisc_sum_prod
    (C.isOrderTwo_mul_t (one_sub_eq_quadGen_or_conj hb)) C.isOrderTwo_t
    (by simpa only [← add_mul, add_sub_cancel, one_mul] using C.two_t_mem)

/-- The fractional ideal generated by `1` and `e / 2`. For `e = ω̄` it is the inverse of the prime
`(2, ω)` above `2`, and for `e = ω` the inverse of the prime `(2, ω̄)`. -/
noncomputable def halfIdeal (e : 𝓞 (QuadField d)) :
    (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ :=
  .mk0 (1 + .spanSingleton (𝓞 (QuadField d))⁰ ((e : QuadField d) / 2))
    (zero_lt_one.trans_le le_self_add).ne'

/-- Let `b` be `ω` or `ω̄`, given by the integer `e` of `ℚ(√-d)`. If the lattice `Λ'` of `D` is `c`
times the product of `halfIdeal e = (1, b / 2)` and the lattice `Λ` of `C`, then `c z ∈ Λ'` if and
only if `z + b t` or `z` lies in `Λ`: indeed `Λ + (b / 2) Λ = Λ + ℤ b t`. Here
`ω = (1 + √-d) / 2`, `t` is the distinguished point of order two of `C` and `scaledIdeal d (c, 𝔞)`
is the module `c 𝔞`. -/
lemma mul_mem_iff_of_halfIdeal (hb : b = quadGen d ∨ b = conj (quadGen d)) {e : 𝓞 (QuadField d)}
    (he : ((e : QuadField d) : ℂ) = b) {c : ℂˣ}
    (hD : D.latticeModule = scaledIdeal d (c, halfIdeal e) * C.latticeModule) (z : ℂ) :
    c * z ∈ D.Λ ↔ z + b * C.t ∈ C.Λ ∨ z ∈ C.Λ := by
  trans ∃ l ∈ C.Λ, ∃ m ∈ C.Λ, l + b / 2 * m = z
  · have h_mem : c * z ∈ D.Λ ↔ c * z ∈ scaledIdeal d (c, halfIdeal e) * C.latticeModule :=
      SetLike.ext_iff.1 hD (c * z)
    -- `using!`, as `latticeModule` has by definition the points of the lattice as elements
    simpa [scaledIdeal, halfIdeal, map_span, one_eq_span, Submodule.sup_mul, mul_assoc,
      mem_span_singleton_mul, he, -map_div₀] using! h_mem
  constructor
  · rintro ⟨l, hl, m, hm, rfl⟩
    -- Modulo `Λ`, multiplication by `b` sends the point `m / 2` to `0` or to `b t`.
    obtain h | h := C.mul_mem_or_mul_sub_t_mem hb (m / 2) (by rwa [add_halves])
    · exact .inr (by simpa [div_mul_eq_mul_div, mul_div_assoc] using add_mem hl h)
    · have h_eq : l + b / 2 * m + b * C.t =
          l + b * (m / 2 - C.t) + (b * C.t + b * C.t) := by ring
      rw [h_eq]
      exact .inl (add_mem (add_mem hl h) (C.isOrderTwo_mul_t hb).add_self_mem)
  · rintro (h | h)
    · exact ⟨z + b * C.t, h, -(C.t + C.t), neg_mem C.two_t_mem, by ring⟩
    · exact ⟨z, h, 0, zero_mem C.Λ, by ring⟩

/-- Let `b` be `ω` or `ω̄` and let multiplication by `c` be an isogeny of degree two from `C` to `D`
with kernel generated by `b t`, that is, `c z` is in the lattice of `D` if and only if `z + b t` or
`z` is in that of `C`. Then `s_C(b t) s_D((1 - b) t) = 2¹²` and `s_D(b t) s_D(t) = -s_C(b t)`,
where `s` is `scaledDisc` and `t` denotes the point of the datum in question. -/
lemma scaledDisc_two_isogeny (hb : b = quadGen d ∨ b = conj (quadGen d)) {c : ℂ} (hc : c ≠ 0)
    (hD : ∀ z : ℂ, c * z ∈ D.Λ ↔ z + b * C.t ∈ C.Λ ∨ z ∈ C.Λ) :
    C.scaledDisc (b * C.t) * D.scaledDisc ((1 - b) * D.t) = 2 ^ 12 ∧
    D.scaledDisc (b * D.t) * D.scaledDisc D.t = -C.scaledDisc (b * C.t) := by
  have hb' : 1 - b = quadGen d ∨ 1 - b = conj (quadGen d) := one_sub_eq_quadGen_or_conj hb
  have h₂ : C.IsOrderTwo ((1 - b) * C.t) := C.isOrderTwo_mul_t hb'
  have h_notMem : c * ((1 - b) * C.t) ∉ D.Λ := by
    simp [hD, ← add_mul, C.t_notMem, h₂.notMem]
  -- The point `(1 - b) t` of `C` goes to the point `(1 - b) t` of `D`.
  have h_point : c * ((1 - b) * C.t) - (1 - b) * D.t ∈ D.Λ := by
    have h_two : c * C.t + c * C.t ∈ D.Λ := by
      simpa only [← mul_add, hD] using Or.inr C.two_t_mem
    have h_cases : (1 - b) * (c * C.t) ∈ D.Λ ∨ (1 - b) * (c * C.t - D.t) ∈ D.Λ :=
      D.mul_mem_or_mul_sub_t_mem hb' (c * C.t) h_two
    simpa only [mul_sub (1 - b), mul_left_comm (1 - b) c, h_notMem, false_or] using h_cases
  have h_dual : C.scaledDisc (b * C.t) * D.scaledDisc ((1 - b) * D.t) = 2 ^ 12 := by
    rw [← scaledDisc_congr h_notMem h_point]
    exact (C.isOrderTwo_mul_t hb).scaledDisc_mul_of_isogeny h₂ C.isOrderTwo_t
      (by simpa only [← add_mul, add_sub_cancel, one_mul] using C.two_t_mem) hc hD
  have h_ne : D.scaledDisc ((1 - b) * D.t) ≠ 0 :=
    right_ne_zero_of_mul (h_dual.trans_ne (by norm_num))
  -- The second identity follows from the product of the three numbers of `D`.
  refine ⟨h_dual, mul_right_cancel₀ h_ne ?_⟩
  have h_prod : D.scaledDisc (b * D.t) * D.scaledDisc ((1 - b) * D.t) * D.scaledDisc D.t =
      -2 ^ 12 := (D.scaledDisc_sum_prod hb).2
  linear_combination h_prod + h_dual

/-- The lattice of `C` is a multiple of a fractional ideal in the class `𝒞`. -/
def IsInClass (𝒞 : ClassGroup (𝓞 (QuadField d))) : Prop :=
  ∃ (c : ℂˣ) (𝔞 : (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ),
    ClassGroup.mk (QuadField d) 𝔞 = 𝒞 ∧ C.latticeModule = scaledIdeal d (c, 𝔞)

/-- There is a family of CM lattices indexed by the ideal classes, with the lattice of index `𝒞`
a multiple of an ideal in the class `𝒞` (`IsInClass`), that contains the given lattice `C`. -/
lemma exists_forall_isInClass : ∃ D : ClassGroup (𝓞 (QuadField d)) → CMLattice d,
    (∀ 𝒞 : ClassGroup (𝓞 (QuadField d)), (D 𝒞).IsInClass 𝒞) ∧
    ∃ 𝒞 : ClassGroup (𝓞 (QuadField d)), D 𝒞 = C := by
  obtain ⟨⟨c, 𝔞⟩, hC⟩ := C.exists_latticeModule_eq_scaledIdeal
  classical
  have h_choice (𝒞 : ClassGroup (𝓞 (QuadField d))) : ∃ D : CMLattice d, D.IsInClass 𝒞 := by
    refine ClassGroup.induction (QuadField d) (fun 𝔟 ↦ ?_) 𝒞
    obtain ⟨D, u, hD⟩ := QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal 𝔟
    exact ⟨D, u, 𝔟, rfl, hD⟩
  choose D hD using h_choice
  -- Replace the datum in the class of `C` by `C`.
  refine ⟨Function.update D (ClassGroup.mk (QuadField d) 𝔞) C, ?_, _, Function.update_self ..⟩
  exact (Function.forall_update_iff D fun 𝒞 D' ↦ D'.IsInClass 𝒞).2
    ⟨⟨c, 𝔞, rfl, hC⟩, fun 𝒞 _ ↦ hD 𝒞⟩

variable {C} in
/-- If the ideal class of the CM lattice `D` (in the sense of `IsInClass`) is that of `C` times the
class of the fractional ideal `𝔟`, then the lattice of `D` is a multiple of `𝔟` times the lattice
of `C`. -/
lemma IsInClass.exists_eq_scaledIdeal_mul {𝒞 : ClassGroup (𝓞 (QuadField d))}
    {𝔟 : (FractionalIdeal (𝓞 (QuadField d))⁰ (QuadField d))ˣ} (hC : C.IsInClass 𝒞)
    (hD : D.IsInClass (ClassGroup.mk (QuadField d) 𝔟 * 𝒞)) :
    ∃ c : ℂˣ, D.latticeModule = scaledIdeal d (c, 𝔟) * C.latticeModule := by
  -- `u 𝔞` is the lattice of `C` and `v 𝔞'` that of `D`.
  obtain ⟨u, 𝔞, rfl, hC⟩ := hC
  obtain ⟨v, 𝔞', h𝔞', hD⟩ := hD
  have h_class : ClassGroup.mk (QuadField d) (𝔟 * 𝔞 / 𝔞') = 1 := by
    rw [map_div, map_mul, h𝔞', div_self']
  -- The ideal `𝔟 𝔞 / 𝔞'` is principal, so a multiple of it fixes the lattice of `D`.
  obtain ⟨w, hw⟩ := exists_eq_scaledIdeal_mul_of_mk_eq_one h_class D.latticeModule
  refine ⟨w * v / u, ?_⟩
  calc D.latticeModule
      = scaledIdeal d (w, 𝔟 * 𝔞 / 𝔞') * scaledIdeal d (v, 𝔞') := by
        rw [← hD]
        exact hw
    _ = scaledIdeal d (w * v, 𝔟 * 𝔞) := by
        rw [← map_mul, Prod.mk_mul_mk, div_mul_cancel]
    _ = scaledIdeal d (w * v / u, 𝔟) * C.latticeModule := by
        rw [hC, ← map_mul, Prod.mk_mul_mk, div_mul_cancel]

/-- For `b = ω` or `ω̄`, with `ω = (1 + √-d) / 2`, there is an ideal class `𝔤` such that, for any CM
lattices `C` in a class `𝒞` and `D` in the class `𝔤 𝒞`, we have `s_C(b t) s_D((1 - b) t) = 2¹²` and
`s_D(b t) s_D(t) = -s_C(b t)`, where `s` is `scaledDisc` and `t` is the point of order two of the
datum in question. -/
lemma exists_class_scaledDisc_mul (hb : b = quadGen d ∨ b = conj (quadGen d)) :
    ∃ 𝔤 : ClassGroup (𝓞 (QuadField d)), ∀ {C D : CMLattice d} {𝒞 : ClassGroup (𝓞 (QuadField d))},
      C.IsInClass 𝒞 → D.IsInClass (𝔤 * 𝒞) →
      C.scaledDisc (b * C.t) * D.scaledDisc ((1 - b) * D.t) = 2 ^ 12 ∧
      D.scaledDisc (b * D.t) * D.scaledDisc D.t = -C.scaledDisc (b * C.t) := by
  obtain ⟨e, he⟩ : ∃ e : 𝓞 (QuadField d), ((e : QuadField d) : ℂ) = b :=
    mem_quadInt_of_eq_quadGen_or_conj hb
  -- The isogeny of degree two with kernel generated by `b t` multiplies the class by that of
  -- `halfIdeal e`.
  refine ⟨ClassGroup.mk (QuadField d) (halfIdeal e), fun {C D 𝒞} hC hD ↦ ?_⟩
  obtain ⟨c, hc⟩ := hC.exists_eq_scaledIdeal_mul hD
  exact C.scaledDisc_two_isogeny hb c.ne_zero (C.mul_mem_iff_of_halfIdeal hb he hc)

section Family

variable {D : ClassGroup (𝓞 (QuadField d)) → CMLattice d}

/-- Let `d` be a prime `≡ 7 mod 8`, `ι : ℂ →+* ℂ_[p]` an embedding for a prime `p`, and `D 𝒞` a CM
lattice in each ideal class `𝒞`, with its point `t` of order two. Then
`scaledDisc u = 288 ℘(u)² / ℘''(u) - 64` for the lattice of `D 𝒞` satisfies `‖ι (scaledDisc u)‖ ≤ 1`
at the three points `u = ω t, ω̄ t, t` of order two, where `ω = (1 + √-d) / 2`. At a point of order
two, `scaledDisc` is the discriminant of the lattice after rescaling so that `℘''(u) = 2`. -/
lemma norm_scaledDisc_le_one {p : ℕ} [Fact p.Prime] {d : ℕ} [PrimeSevenModEight d]
    {D : ClassGroup (𝓞 (QuadField d)) → CMLattice d}
    (hD : ∀ 𝒞 : ClassGroup (𝓞 (QuadField d)), (D 𝒞).IsInClass 𝒞)
    (ι : ℂ →+* ℂ_[p]) (𝒞 : ClassGroup (𝓞 (QuadField d))) :
    (∀ b : ℂ, b = quadGen d ∨ b = conj (quadGen d) →
      ‖ι ((D 𝒞).scaledDisc (b * (D 𝒞).t))‖ ≤ 1) ∧
    ‖ι ((D 𝒞).scaledDisc (D 𝒞).t)‖ ≤ 1 := by
  have h48 : ‖ι (-48)‖ ≤ 1 := by
    simpa [map_ofNat] using IsUltrametricDist.norm_natCast_le_one ℂ_[p] 48
  have h2 : ‖ι (2 ^ 12)‖ ≤ 1 := by
    simpa [map_ofNat] using
      pow_le_one₀ (n := 12) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one ℂ_[p] 2)
  have h_int (b : ℂ) (hb : b = quadGen d ∨ b = conj (quadGen d)) :
      ‖ι ((D 𝒞).scaledDisc (b * (D 𝒞).t))‖ ≤ 1 := by
    obtain ⟨𝔤, h𝔤⟩ := exists_class_scaledDisc_mul (d := d) hb
    let s (a : ℂ) (𝒞' : ClassGroup (𝓞 (QuadField d))) : ℂ_[p] :=
      ι ((D 𝒞').scaledDisc (a * (D 𝒞').t))
    let s₀ (𝒞' : ClassGroup (𝓞 (QuadField d))) : ℂ_[p] := ι ((D 𝒞').scaledDisc (D 𝒞').t)
    have h_sum (𝒞') : ‖s b 𝒞' + s (1 - b) 𝒞' + s₀ 𝒞'‖ ≤ 1 := by
      simpa only [s, s₀, ← map_add, ((D 𝒞').scaledDisc_sum_prod hb).1] using h48
    have h_dual (𝒞') : ‖s b 𝒞' * s (1 - b) (𝔤 * 𝒞')‖ ≤ 1 := by
      simpa only [s, ← map_mul, (h𝔤 (hD 𝒞') (hD _)).1] using h2
    have h_step (𝒞') : s b (𝔤 * 𝒞') * s₀ (𝔤 * 𝒞') = -s b 𝒞' := by
      simp only [s, s₀, ← map_mul, (h𝔤 (hD 𝒞') (hD _)).2, map_neg]
    exact norm_le_one_of_cycle 𝔤 h_sum h_dual h_step 𝒞
  refine ⟨h_int, ?_⟩
  have hω : quadGen d = quadGen d ∨ quadGen d = conj (quadGen d) := .inl rfl
  -- `s(t) = -48 - s(ω t) - s((1 - ω) t)`
  rw [eq_sub_of_add_eq' ((D 𝒞).scaledDisc_sum_prod hω).1, ← sub_sub, map_sub, map_sub]
  exact norm_sub_le_one (norm_sub_le_one h48 (h_int _ hω))
    (h_int _ (one_sub_eq_quadGen_or_conj hω))

/-- For a family `D` of CM lattices, the lattice `D 𝒞` being a multiple of an ideal in the class `𝒞`
(`IsInClass`), the numbers `s = scaledDisc` at their distinguished points `t` of order two
have the product `±1`, the sign being `(-1)` to the class number. -/
lemma prod_scaledDisc_t (hD : ∀ 𝒞 : ClassGroup (𝓞 (QuadField d)), (D 𝒞).IsInClass 𝒞) :
    ∏ 𝒞 : ClassGroup (𝓞 (QuadField d)), (D 𝒞).scaledDisc (D 𝒞).t =
      (-1) ^ Fintype.card (ClassGroup (𝓞 (QuadField d))) := by
  -- Multiply `s_D(ω t) s_D(t) = -s_C(ω t)` over all classes; the numbers at the `ω t` cancel.
  obtain ⟨𝔤, h𝔤⟩ := exists_class_scaledDisc_mul (d := d) (b := quadGen d) (.inl rfl)
  set s : ClassGroup (𝓞 (QuadField d)) → ℂ := fun 𝒞 ↦ (D 𝒞).scaledDisc (quadGen d * (D 𝒞).t)
  set s₀ : ClassGroup (𝓞 (QuadField d)) → ℂ := fun 𝒞 ↦ (D 𝒞).scaledDisc (D 𝒞).t
  have h_dual (𝒞 : ClassGroup (𝓞 (QuadField d))) :
      s 𝒞 * (D (𝔤 * 𝒞)).scaledDisc ((1 - quadGen d) * (D (𝔤 * 𝒞)).t) = 2 ^ 12 :=
    (h𝔤 (hD 𝒞) (hD _)).1
  have h_step (𝒞 : ClassGroup (𝓞 (QuadField d))) : s (𝔤 * 𝒞) * s₀ (𝔤 * 𝒞) = -s 𝒞 :=
    (h𝔤 (hD 𝒞) (hD _)).2
  have h_ne : ∏ 𝒞, s 𝒞 ≠ 0 := prod_ne_zero_iff.2 fun 𝒞 _ ↦
    left_ne_zero_of_mul ((h_dual 𝒞).trans_ne (by norm_num))
  apply mul_left_cancel₀ h_ne
  calc (∏ 𝒞, s 𝒞) * ∏ 𝒞, s₀ 𝒞
      = ∏ 𝒞, s (𝔤 * 𝒞) * s₀ (𝔤 * 𝒞) := by
        rw [← prod_mul_distrib]
        exact (Equiv.prod_comp (Equiv.mulLeft 𝔤) fun 𝒞 ↦ s 𝒞 * s₀ 𝒞).symm
    _ = (∏ 𝒞, s 𝒞) * (-1) ^ Fintype.card (ClassGroup (𝓞 (QuadField d))) := by
        simp [h_step, prod_neg, mul_comm]

end Family

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, normalised so that its point `t` of order two
has `℘''(t) = 2`, and let `ι` be a ring homomorphism `ℂ → ℂ_[p]`. Then `a₁⁴ - 64`, where
`a₁² = 12 ℘(t)`, has norm `1`. This number is the discriminant `g₂³ - 27 g₃²` of the lattice
(`disc_eq`).

This is the unit property of Siegel units (Ramachandra, Robert) at the point `t` of order two only,
expressed as norm 1 of the normalised discriminant under every ring homomorphism `ℂ → ℂ_[p]`. -/
lemma norm_disc_eq_one {p : ℕ} [Fact p.Prime] {d : ℕ} (C : CMLattice d) [PrimeSevenModEight d]
    (ι : ℂ →+* ℂ_[p]) : ‖ι C.a₁ ^ 4 - 64‖ = 1 := by
  -- The discriminants of a family of CM lattices, one in each ideal class, are integral and have
  -- the product `±1`.
  obtain ⟨D, hD, 𝒞₀, rfl⟩ := C.exists_forall_isInClass
  have h_le (𝒞) : ‖ι ((D 𝒞).scaledDisc (D 𝒞).t)‖₊ ≤ 1 := (norm_scaledDisc_le_one hD ι 𝒞).2
  have h_prod : ∏ 𝒞, ‖ι ((D 𝒞).scaledDisc (D 𝒞).t)‖₊ = 1 := by
    simp [← nnnorm_prod, ← map_prod, prod_scaledDisc_t hD]
  have h_unit : ‖ι ((D 𝒞₀).scaledDisc (D 𝒞₀).t)‖₊ = 1 :=
    (prod_eq_one_iff_of_le_one fun 𝒞 _ ↦ h_le 𝒞).1 h_prod 𝒞₀ (mem_univ _)
  simpa [scaledDisc_t, ← coe_nnnorm, map_ofNat] using h_unit

end CMLattice

/-- For a prime `p`, an element of `ℂ_[p]` of the form `x u + y v` with `x, y` integral and
`‖u‖, ‖v‖ < 1` has norm `< 1`. -/
lemma norm_lt_one_of_eq_mul_add_mul {p : ℕ} [Fact p.Prime] {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1)
    (hy : ‖y‖ ≤ 1) {u v z : ℂ_[p]} (hz : z = x * u + y * v) (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) :
    ‖z‖ < 1 := by
  subst hz
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
  · exact (norm_mul x u).trans_lt ((mul_le_of_le_one_left (norm_nonneg u) hx).trans_lt hu)
  · exact (norm_mul y v).trans_lt ((mul_le_of_le_one_left (norm_nonneg v) hy).trans_lt hv)

end New

end GoodReduction

end

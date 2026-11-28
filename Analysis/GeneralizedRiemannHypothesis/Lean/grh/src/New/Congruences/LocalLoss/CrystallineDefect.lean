import New.Congruences.LocalLoss.CrystallineCocycles
import New.Reduction.Data.Magnitudes

/-!
# The defect of the dual of a summand at a place above ℓ

This file bounds, at a place above ℓ, the normalised defect of the Tate dual of a summand whose
class is adapted to the summands of the data `D`. Here `New.Selmer.IsCompletionGroup` identifies Γ
with the Galois group of a completion of E, and `complexEmbeddingOf e g` is the complex embedding of
E read by g in G_ℓ. This file checks that the data satisfy the size conditions of the crystalline
bound, treats the tame case at the primes `D.levelPrime n`, and compares both bounds with the local
loss `New.Selmer.defectBound`.

## Main definitions and results

* `New.Selmer.IsSummandClass`: The lattices `L i` are the summands at a place above `ℓ`, and `F`,
  `K`, `U` are the data of a class `New.Lift.InClass F K U` adapted to them. The summand `L none` is
  the main summand, of rank `r` and with jumps `J g` at `coefficientEmbedding O g`; the summand
  `L (some c)` has the single jump `c < t`.
* `New.Selmer.summand_defect_le_at_place`: let `D` be the data, take the coefficient ring `O`
  sufficiently large, and consider summands consisting of one lattice of rank r, the main summand,
  and further lattices with a single jump each. If a summand lies in a tame or crystalline class
  adapted to the summands, then the defect of its dual is at most [G_ℓ :
  j(Γ)] · rank · `New.Selmer.defectBound` / x, where x = 1 for the main summand and x = D.t
  otherwise.

Notions from other files:
* `New.Lift.GalLattice`: A finite free O-module with a compatible ℤ_ℓ-module structure, together
  with an O-linear representation of the group Γ on it.
* `New.Period.IsPotentiallyCrystalline`: for a representation on T and the crystalline period ring
  B, the elements of B⊗T fixed by all g with j(g) near 1 span B⊗T over B.
* `New.Period.jump`: The multiplicity of the Hodge–Tate jump u at γ: the dimension over ℚ̄_ℓ (zero
  if infinite) of the space `New.Period.hodgeTateMaps`.
* `New.Data.t`: The natural number t = 5r, where r is the rank in the data.
* `New.Selmer.CrystallineSizes`: the size conditions of the crystalline bound on its eight
  parameters.

## Relation to the literature

See `New.Congruences.FirstOrder.RibetElement` for related work. See `Lib.PadicHodge.BlochKato` for
sources.
-/

section OnePlaceDefect

open New Period Lift CoeffRing Module Nat NeZero NumberField Data Finset

/-- The start of the far window at the embedding `σ` that holds the jumps near `∓ w_i`: it is
`D.natB` if the place of `σ` lies in `D.bPlaces` and `D.offWeight` otherwise, plus `i Δ + h₂ - 2 t`
with `Δ = D.gap`, `h₂ = D.halfGap` and `t = D.t`. -/
noncomputable abbrev New.Selmer.farWindowStart {P : Parameters} (D : Data P) (i : ℕ)
    (σ : D.E →+* ℂ) : ℕ :=
  ite (InfinitePlace.mk σ ∈ D.bPlaces)
  (h := Classical.dec (InfinitePlace.mk σ ∈ D.bPlaces)) D.natB D.offWeight +
    (i * D.gap + D.halfGap - 2 * D.t)

/-- Let `w_i = D.liftWeight i` be the `i`-th weight at the place of `σ`, and let `ε = cmSign σ` be
`1` if `σ` is in the CM type and `-1` otherwise. Let each member of `J` be low
(`Δ / 4 ≤ |u| ≤ 2 m Δ` with `Δ = D.gap`) or within `D.t` of `-ε w_i`, and let each member of `U` lie
in `J` or in `[0, t)`, with `t ≤ D.t`. Put `η = h₂² + 1` with `h₂ = D.halfGap`, and let
`S = farWindowStart D i σ`, which equals `w_i - 2 D.t`. Then `U` lies in the union of `[-η, η]` and
`-ε [S, S + 4 D.t]`, and the dual jumps `-u - 1` lie in the union of `[-η, η]` and
`ε [S, S + 4 D.t]`. -/
lemma New.Selmer.fitsWindows_and_image_neg_sub_one {P : Parameters} {D : Data P} {t i : ℕ}
    {σ : D.E →+* ℂ} {J : Multiset ℤ} {U : Finset ℤ} (ht : t ≤ D.t)
    (hJ : ∀ u ∈ J, D.gap ≤ 4 * u.natAbs ∧ u.natAbs ≤ 2 * D.m * D.gap ∨
      |cmSign σ * u + D.liftWeight i (InfinitePlace.mk σ)| ≤ D.t)
    (hU : ∀ u ∈ U, u ∈ J ∨ ∃ c < t, u = (c : ℕ)) :
    FitsWindows (D.halfGap ^ 2 + 1) (-cmSign σ) (farWindowStart D i σ) (4 * D.t) U ∧
      FitsWindows (D.halfGap ^ 2 + 1) (cmSign σ) (farWindowStart D i σ) (4 * D.t)
        (U.image fun u : ℤ ↦ -u - 1) := by
  have ht_pos : 0 < D.t := D.t_odd.pos
  have ht_small : 3 * D.t ≤ D.halfGap := D.nat_le_of_hasLogBound
  have h_low_le : 2 * D.m * D.gap ≤ D.halfGap ^ 2 := D.nat_le_of_hasLogBound
  set S : ℕ := farWindowStart D i σ with hS
  have hw : D.liftWeight i (.mk σ) = S + 2 * D.t := by
    simp only [hS, liftWeight_eq, weight_eq_ite, farWindowStart]
    split_ifs <;> omega
  -- A member of `U` is low, or `∓ u` lies within `D.t` of `w_i = S + 2 D.t`.
  have h_range (u : ℤ) (hu : u ∈ U) :
      u.natAbs ≤ D.halfGap ^ 2 ∨
      ((cmSign σ : ℤ) = 1 ∧ S + D.t ≤ -u ∧ -u ≤ S + 3 * D.t) ∨
      ((cmSign σ : ℤ) = -1 ∧ S + D.t ≤ u ∧ u ≤ S + 3 * D.t) := by
    obtain huJ | ⟨c, hc, rfl⟩ := hU u hu
    · obtain ⟨-, h_low⟩ | h_high := hJ u huJ
      · exact .inl (h_low.trans h_low_le)
      have hσ : (cmSign σ : ℤ) = 1 ∨ (cmSign σ : ℤ) = -1 := Int.isUnit_iff.1 (cmSign σ).isUnit
      rw [hw, abs_le] at h_high
      lia
    · rw [sq]
      have h_sq : D.halfGap ≤ D.halfGap * D.halfGap := D.halfGap.le_mul_self
      omega
  refine ⟨fun u hu ↦ ?_, forall_mem_image.2 fun u hu ↦ ?_⟩
  · specialize h_range u hu
    rw [Units.val_neg]
    omega
  · specialize h_range u hu
    omega

/-- If `2 ≤ h²`, the members `a` of `J` whose dual jump `-a - 1` lies in `[-h² - 1, h² + 1]` are
at most as many as those with `|a| ≤ 2 h²`, both counted with multiplicity. -/
lemma New.Selmer.sum_count_neg_sub_one_le {h : ℕ} (hh : 2 ≤ h ^ 2) (J : Multiset ℤ) :
    ∑ u ∈ Finset.Icc (-1 + -(h : ℤ) ^ 2) ((h : ℤ) ^ 2 + 1), Multiset.count (-u - 1) J ≤
      J.countP (·.natAbs ≤ 2 * h ^ 2) := by
  induction J using Multiset.induction with
  | empty => simp
  | cons a J ih =>
    -- The new member `a` is counted on the left at `u = -a - 1` only.
    have h_iff (u : ℤ) : -u - 1 = a ↔ u = -a - 1 := by omega
    simp only [Multiset.count_cons, Multiset.countP_cons, sum_add_distrib, h_iff, sum_ite_eq',
      mem_Icc]
    lia

/-- A relation between two letters determines the action on roots of unity: if `ζ` in `O` is a
primitive `N`-th root of unity and `g' ζ = (g ζ) ^ n`, then `g' g⁻¹` raises every `N`-th root of
unity to the power `n`. -/
lemma New.Selmer.smul_eq_pow_of_coefficientEmbedding_eq_pow {ℓ N n : ℕ} [ThePrime ℓ] [NeZero N]
    {O : CoeffRing ℓ} {ζ : ↑O} (hζ : IsPrimitiveRoot ζ N) {g g' : Gp ℓ}
    (h_pow : coefficientEmbedding O g' ζ = coefficientEmbedding O g ζ ^ n) :
    ∀ z : PadicAlgCl ℓ, z ^ N = 1 → (g' * g⁻¹) • z = z ^ n := by
  have h_prim : IsPrimitiveRoot (g ζ) N :=
    (IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ).map_of_injective g.injective
  have h_smul : (g' * g⁻¹) • g ζ = g ζ ^ n := by simpa [coefficientEmbedding, ← map_pow] using h_pow
  exact cyclotomicCharMod_eq_iff.mp (cyclotomicCharMod_eq_of_isPrimitiveRoot h_prim h_smul)

/-- Let `𝒥.toGp : Γ → G_ℓ` be an open embedding onto the elements of `G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` that
fix `e E`. Let `k` be a Kummer chart of `Γ` (a subring `W(𝔽_{ℓ^f})⟦z⟧` of `A_inf` adapted to `Γ`)
that is unramified, with `f = k.f`, and let `ζ` in `O` be a primitive `(ℓ ^ f - 1)`-th root of
unity. If `g ζ = g' ζ`, where `coefficientEmbedding O g` is the embedding `x ↦ g x` of `O ⊆ ℚ̄_ℓ`
into `ℂ_ℓ`, then `g` and `g'` give the same complex embedding of `E`. -/
lemma New.Selmer.complexEmbeddingOf_eq_of_coefficientEmbedding_eq {P : Parameters} {D : Data P}
    {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {Γ : Type} [Group Γ] [𝒥 : OverGp Γ ℓ] [TopologicalSpace Γ]
    {e : D.E →+* PadicAlgCl ℓ} (h_group : IsCompletionGroup e 𝒥.toGp) {k : KummerChart ⟨Γ⟩}
    (h_un : k.IsUnramified) {O : CoeffRing ℓ} {ζ : ↑O} (hζ : IsPrimitiveRoot ζ (ℓ ^ k.f.val - 1))
    {g g' : Gp ℓ} (h_eq : coefficientEmbedding O g ζ = coefficientEmbedding O g' ζ) :
    complexEmbeddingOf e g = complexEmbeddingOf e g' := by
  -- The element `g g'⁻¹` fixes the constants `W(𝔽_{ℓ^f})` of the chart (`FixesLambda`) and the
  -- image `theta k.z = -ℓ` of its variable, so it lies in the image of `Γ`.
  have h_roots : ∀ z : PadicAlgCl ℓ, z ^ (ℓ ^ k.f.val - 1) = 1 → (g * g'⁻¹) • z = z ^ 1 :=
    smul_eq_pow_of_coefficientEmbedding_eq_pow hζ (h_eq.trans (pow_one _).symm)
  have h_const : FixesLambda k.f (g * g'⁻¹) :=
    (fixes_roots_iff_fixesLambda _).mp (by simpa using h_roots)
  have h_z : (g * g'⁻¹) • theta k.z = theta k.z := by
    obtain ⟨hE : k.E = k.z + ℓ, -⟩ := h_un
    rw [← sub_eq_iff_eq_add.mpr hE]
    simp [k.theta_E]
  have h_mem : g * g'⁻¹ ∈ 𝒥.toGp.range := k.chart_isChartOf _ ⟨h_const, h_z⟩
  exact h_group.complexEmbeddingOf_eq_iff.mpr h_mem

/-- If a Frobenius `F` for `ℓ ^ f` (`IsFrob (intQpBar ℓ) (ℓ ^ f) F`) fixes a primitive `N`-th root
of unity `z`, then `z ^ ℓ ^ v` is an `(ℓ ^ f - 1)`-th root of unity. Here `v = N.factorization ℓ` is
the `ℓ`-adic valuation of `N`, so `z ^ ℓ ^ v` has order prime to `ℓ`. -/
lemma New.Selmer.pow_ordProj_pow_sub_one_eq_one {ℓ N : ℕ} [hp : ThePrime ℓ] [NeZero N] {f : ℕ+}
    {F : Gp ℓ} (hF : IsFrob (intQpBar ℓ) (ℓ ^ f.val) F) {z : PadicAlgCl ℓ}
    (hz : IsPrimitiveRoot z N) (h_fix : F z = z) :
    (z ^ ℓ ^ N.factorization ℓ) ^ (ℓ ^ f.val - 1) = 1 := by
  set ξ : PadicAlgCl ℓ := z ^ ℓ ^ N.factorization ℓ with hξ
  have h_prim : IsPrimitiveRoot ξ (N / ℓ ^ N.factorization ℓ) :=
    hz.pow_of_dvd (NeZero.ne _) (ordProj_dvd N ℓ)
  have h_frob : F ξ = ξ ^ ℓ ^ f.val :=
    apply_eq_pow_of_isFrob hF (not_dvd_ordCompl hp.out (NeZero.ne N)) h_prim.pow_eq_one
  have h_mul : ξ ^ (ℓ ^ f.val - 1) * ξ = ξ := by
    rw [pow_sub_one_mul (NeZero.ne _), ← h_frob, hξ, map_pow, h_fix]
  exact (mul_eq_right₀ (pow_ne_zero _ (hz.ne_zero (NeZero.ne N)))).1 h_mul

/-- No three b-places follow one another closely along `z ↦ z ^ ℓ`, for `ℓ ≤ D.k * D.t`. Here
`D.bPlaces` is the sparse set of infinite places of `E = D.E` of weight `D.natB`. Let `j : Γ → G_ℓ`
be an open embedding onto the elements that fix `e E`, let its image contain `F` acting as
`x ↦ x ^ ℓ ^ f` on the residue field of the valuation ring `intQpBar ℓ` of `ℚ̄_ℓ`, and let `ζ` in
`O` be a primitive `(ℓ ^ f - 1)`-th root of unity. Write `g ζ` for `coefficientEmbedding O g ζ`. If
`g₁ ζ = (g₀ ζ) ^ ℓ ^ a` and `g₂ ζ = (g₀ ζ) ^ ℓ ^ (a + b)` with `1 ≤ a, b ≤ ⌊log_ℓ (D.halfGap ^ 3)⌋`,
and the complex embeddings `complexEmbeddingOf e g` of `E` for `g = g₀` and `g = g₂` lie at places
in `D.bPlaces`, then that for `g = g₁` does not. -/
lemma New.Selmer.notMem_bPlaces_of_coefficientEmbedding_eq_pow {P : Parameters} {D : Data P} {ℓ : ℕ}
    [hp : ThePrime ℓ] [PadicIso ℓ] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {e : D.E →+* PadicAlgCl ℓ} {j : Γ →* Gp ℓ} (hj : IsCompletionGroup e j) {f : ℕ+} {F : Gp ℓ}
    (hF_mem : F ∈ j.range) (hF : IsFrob (intQpBar ℓ) (ℓ ^ f.val) F) (hℓ : ℓ ≤ D.k * D.t)
    {O : CoeffRing ℓ} {ζ : ↑O} (hζ : IsPrimitiveRoot ζ (ℓ ^ f.val - 1)) {a b : ℕ}
    (ha : a ∈ Icc 1 (ℓ.log (D.halfGap ^ 3))) (hb : b ∈ Icc 1 (ℓ.log (D.halfGap ^ 3)))
    {g₀ g₁ g₂ : Gp ℓ} (hg₁ : coefficientEmbedding O g₁ ζ = coefficientEmbedding O g₀ ζ ^ ℓ ^ a)
    (hg₂ : coefficientEmbedding O g₂ ζ = coefficientEmbedding O g₀ ζ ^ ℓ ^ (a + b))
    (h_mem₀ : InfinitePlace.mk (complexEmbeddingOf e g₀) ∈ D.bPlaces)
    (h_mem₂ : InfinitePlace.mk (complexEmbeddingOf e g₂) ∈ D.bPlaces) :
    InfinitePlace.mk (complexEmbeddingOf e g₁) ∉ D.bPlaces := by
  -- By `notMem_bPlaces_of_short_arc` it suffices that `g₂ g₀⁻¹` and `g₂ g₁⁻¹` raise `ξ` to the
  -- powers `ℓ ^ (a + b)` and `ℓ ^ b`, with `a + b < l₀`. Here `ξ` is the prime-to-`ℓ` part of the
  -- `q₁`-th root of unity `P.ζ D.towerExp`.
  let ξ : PadicAlgCl ℓ := e (P.ζ D.towerExp) ^ ℓ ^ (P.q₁ D.towerExp).factorization ℓ
  obtain ⟨-, h_range : ∀ g : Gp ℓ, g ∈ j.range ↔ ∀ x : D.E, g (e x) = e x⟩ := hj
  have hξ : ξ ^ (ℓ ^ f.val - 1) = 1 :=
    pow_ordProj_pow_sub_one_eq_one hF (P.isPrimitiveRoot_zeta.map_of_injective e.injective)
      ((h_range F).1 hF_mem _)
  have h_log : ℓ.log (D.halfGap ^ 3) ≤ D.towerExp * 12 := by
    have h_size : D.halfGap ^ 3 ≤ (2 ^ D.towerExp) ^ 12 := D.nat_le_of_hasLogBound
    simpa [← pow_mul 2] using log_mono .refl hp.out.one_lt h_size
  have hg₂₁ : coefficientEmbedding O g₂ ζ = coefficientEmbedding O g₁ ζ ^ ℓ ^ b := by
    rw [hg₂, hg₁, pow_add, pow_mul]
  obtain ⟨hb_pos, hb_lt, h_short⟩ : 0 < b ∧ b < a + b ∧ a + b ≤ 27 * D.towerExp := by
    rw [mem_Icc] at ha hb
    omega
  exact notMem_bPlaces_of_short_arc h_mem₀ h_mem₂
    (smul_eq_pow_of_coefficientEmbedding_eq_pow hζ hg₂ ξ hξ)
    (smul_eq_pow_of_coefficientEmbedding_eq_pow hζ hg₂₁ ξ hξ) hℓ hb_pos hb_lt
    (h_short.trans_lt (mul_lt_l₀ D.towerExp))

/-- Let `𝒥.toGp : Γ → G_ℓ` be an open embedding onto the elements of `G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` that
fix `e E`, where `E = D.E`, and put `Q = D.k * D.t`. For `O` large there are a Kummer chart of `Γ`
(a subring `W(𝔽_{ℓ^f})⟦z⟧` of `A_inf` adapted to `Γ`, of ramification `k.e` and with `f = k.f`) `k`,
an element `ζ` of `O` with `ζ ^ (ℓ ^ f - 1) = 1`, a predicate `T` and a sign `s` on `ℂ_ℓ` with the
following properties, the clauses of `LettersReadThick`. The degree `k.e * k.f` is `[G_ℓ : Γ]` and
`k.e ≤ h₂ = D.halfGap`. Write `g ζ` for `coefficientEmbedding O g ζ` and
`σ = complexEmbeddingOf e g`. The place of `σ` lies in the set `D.bPlaces` of places of weight
`D.natB` if and only if `T (g ζ)`, and the sign `cmSign σ` of `σ` for the CM type is `s (g ζ)`; this
holds for every `g` if `Q < ℓ`, and otherwise for the `g` at b-places. The chart is unramified with
`7 ≤ ℓ`, or else `ℓ ≤ Q` and `s` is constant. For `ℓ ≤ Q` no three values with `T` follow one
another at distances `≤ log_ℓ h₂³` along `z ↦ z ^ ℓ`. -/
lemma New.Selmer.eventually_exists_lettersReadThick {P : Parameters} {D : Data P} {ℓ : ℕ}
    [hp : ThePrime ℓ] [PadicIso ℓ] {Γ : Type} [Group Γ] [𝒥 : OverGp Γ ℓ] [TopologicalSpace Γ]
    {e : D.E →+* PadicAlgCl ℓ} (h_group : IsCompletionGroup e 𝒥.toGp) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
      ∃ (k : KummerChart ⟨Γ⟩) (ζ : k.LetterRoot (Γ := ⟨Γ⟩) O) (T : ℂ_[ℓ] → Prop) (s : ℂ_[ℓ] → ℤˣ),
        LettersReadThick k (fun g : Gp ℓ ↦ coefficientEmbedding O g ζ)
          (fun g : Gp ℓ ↦ InfinitePlace.mk (complexEmbeddingOf e g) ∈ D.bPlaces)
          (fun g : Gp ℓ ↦ cmSign (complexEmbeddingOf e g)) (D.k * D.t) D.halfGap T s := by
  -- The letter of `g` is `g ζ`, with `ζ` a primitive `(ℓ^f - 1)`-th root of unity. If `ℓ` is prime
  -- to the conductor, the chart is unramified and the letter determines the embedding of `g`.
  -- Otherwise `ℓ` is small and all b-place embeddings have the same sign.
  obtain ⟨k, -, h_index : k.e * k.f = 𝒥.toGp.range.index,
      h_unram : inertiaGroup (Gp ℓ) (intQpBar ℓ) ≤ 𝒥.toGp.range → k.IsUnramified,
      F, hF_mem : F ∈ 𝒥.toGp.range, hF : IsFrob (intQpBar ℓ) (ℓ ^ k.f.val) F⟩ :=
    exists_kummerChart Γ
  have h_small (h_cond : ℓ ∣ D.cyclotomicConductor) : ℓ ≤ D.k * D.t :=
    (le_of_dvd one_le (hp.out.dvd_of_dvd_pow (h_cond.trans P.q₁_mul_d_dvd_q₂))).trans
      D.nat_le_of_hasLogBound
  -- If `ℓ` is prime to the conductor, inertia fixes `E`, so the chart is unramified.
  have h_un (h_cond : ¬ℓ ∣ D.cyclotomicConductor) : k.IsUnramified :=
    h_unram fun g hg ↦ (h_group.2 g).mpr
      (fixes_emb_of_fixes_rootsOfUnity (apply_eq_self_of_mem_inertiaGroup h_cond hg))
  filter_upwards [eventually_exists_isPrimitiveRoot (ℓ ^ k.f.val - 1)] with O ⟨ζ, hζ⟩
  have h_root : ζ ^ Nat.card (k.Letter (Γ := ⟨Γ⟩)) = 1 := by
    simp [KummerChart.Letter, Nat.card_units, card_flatFq, hζ.pow_eq_one]
  let letter (g : Gp ℓ) : ℂ_[ℓ] := coefficientEmbedding O g ζ
  have h_emb (h_cond : ¬ℓ ∣ D.cyclotomicConductor) (g g' : Gp ℓ)
      (h_letter : letter g = letter g') :
      complexEmbeddingOf e g = complexEmbeddingOf e g' :=
    complexEmbeddingOf_eq_of_coefficientEmbedding_eq h_group (h_un h_cond) hζ h_letter
  -- A letter is a b-place letter if it is the letter of a `g` at a b-place. The sign of a letter
  -- `z` is read at a chosen `g` with `reads z g`.
  let reads (z : ℂ_[ℓ]) (g : Gp ℓ) : Prop :=
    if ℓ ∣ D.cyclotomicConductor then .mk (complexEmbeddingOf e g) ∈ D.bPlaces else letter g = z
  refine ⟨k, ⟨ζ, h_root⟩, fun z ↦ ∃ g : Gp ℓ,
    .mk (complexEmbeddingOf e g) ∈ D.bPlaces ∧ letter g = z,
    fun z ↦ cmSign (complexEmbeddingOf e (Classical.epsilon (reads z))),
    ⟨h_index, ?_, fun g hg ↦ ?_, fun g hg ↦ ?_, ?_, ?_⟩⟩
  · -- The index `e f` counts the embeddings in an orbit, so it is at most the degree of `E`.
    have h_card : Nat.card (D.E →+* ℂ) ≤ D.halfGap := by
      simpa [Embeddings.card, finrank_eq_two_mul_card_infinitePlace] using D.nat_le_of_hasLogBound
    grw [Nat.le_mul_of_pos_right k.e k.f.pos, h_index, h_group.index_eq_card_range,
      Finite.card_subtype_le, h_card]
  · -- The letters read whether `g` is a b-place: a `g` that is not a b-place has `Q < ℓ`, so its
    -- letter determines its embedding.
    refine ⟨fun h_thick ↦ ⟨g, h_thick, rfl⟩, fun ⟨g', h_thick, h_letter⟩ ↦ ?_⟩
    obtain h_thick' | hℓ := hg
    · exact h_thick'
    · rwa [← h_emb (fun h ↦ hℓ.not_ge (h_small h)) g' g h_letter]
  · -- The letters read the sign.
    by_cases h_cond : ℓ ∣ D.cyclotomicConductor
    · -- Here `ℓ` is small, so `g` is a b-place, and b-place embeddings have one sign.
      have h_thick : InfinitePlace.mk (complexEmbeddingOf e g) ∈ D.bPlaces :=
        hg.resolve_right (h_small h_cond).not_gt
      have h_reads : reads (letter g) (Classical.epsilon (reads (letter g))) :=
        Classical.epsilon_spec ⟨g, (ite_eq_left h_cond).mpr h_thick⟩
      exact cmSign_eq_of_mem_bPlaces h_thick ((ite_eq_left h_cond).mp h_reads) h_cond
    · -- Here the letter determines the embedding.
      have h_reads : reads (letter g) (Classical.epsilon (reads (letter g))) :=
        Classical.epsilon_spec ⟨g, (ite_eq_right h_cond).mpr rfl⟩
      rw [h_emb h_cond _ g ((ite_eq_right h_cond).mp h_reads)]
  · -- The chart is unramified, or all letters have one sign.
    by_cases h_cond : ℓ ∣ D.cyclotomicConductor
    · -- Here `reads z` does not depend on `z`.
      exact .inr ⟨h_small h_cond, by simp [reads, h_cond]⟩
    · -- The primes up to 7 divide the conductor.
      refine .inl ⟨h_un h_cond, le_of_not_ge fun h_le ↦ h_cond ?_⟩
      have h_dvd : ℓ ∣ P.q₀ := (hp.out.dvd_primorial_iff.mpr h_le).trans (.trans (by cbv) P.dvd_q₀)
      exact (h_dvd.mul_right _).mul_right _
  · -- No three letters of b-places are close.
    rintro hℓ z a ha b hb ⟨g₀, h_mem₀, rfl⟩ ⟨g₁, h_mem₁, hg₁⟩ ⟨g₂, h_mem₂, hg₂⟩
    exact notMem_bPlaces_of_coefficientEmbedding_eq_pow h_group hF_mem hF hℓ hζ ha hb hg₁ hg₂
      h_mem₀ h_mem₂ h_mem₁

/-- Let `j : Γ → Gp ℓ` identify `Γ` with the completion group of an embedding `e` of `D.E`
(`IsCompletionGroup e j`). If `ℓ ≡ 1` modulo `D.cyclotomicConductor`, then all of `Gp ℓ` fixes the
image of `E`, so `j` is onto. -/
lemma New.Selmer.mem_range_of_modEq_one {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {e : D.E →+* PadicAlgCl ℓ} {j : Γ →* Gp ℓ}
    (hj : IsCompletionGroup e j) (hℓ : ℓ ≡ 1 [MOD D.cyclotomicConductor]) (g : Gp ℓ) :
    g ∈ j.range := by
  refine (hj.2 g).2 (fixes_emb_of_fixes_rootsOfUnity fun z hz ↦ ?_)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, g z = z ^ ℓ ^ a :=
    exists_apply_eq_pow (P.not_dvd_q₁_mul_d_of_modEq_one hℓ) hz g
  simp [ha, pow_eq_pow_of_modEq (hℓ.pow a) hz]

/-- Every jump `u` of a main summand, that is every member of a multiset `J σ` that satisfies
`New.Selmer.IsMainSummandWeights`, has `|u| ≥ h₂ / 2` with `h₂ = D.halfGap`: either it is low, so
that `|u| ≥ Δ / 4` with `Δ = D.gap = 2 h₂`, or it lies within `D.t` of the weight `∓ w_i` of the
data, signed by the CM type (`cmSign`), and `w_i ≥ h₂ ≥ 3 D.t`. -/
lemma New.Selmer.IsMainSummandWeights.le_two_mul_natAbs {P : Parameters} {D : Data P} {r t : ℕ}
    {J : (D.E →+* ℂ) → Multiset ℤ} (hJ : IsMainSummandWeights D r t J) {σ : D.E →+* ℂ} {u : ℤ}
    (hu : u ∈ J σ) : D.halfGap ≤ 2 * u.natAbs := by
  obtain ⟨i, -, h_mem⟩ := hJ.low_or_high
  have ht_small : 3 * D.t ≤ D.halfGap := D.nat_le_of_hasLogBound
  have hw : D.halfGap ≤ D.liftWeight i (InfinitePlace.mk σ) := by grind
  obtain ⟨h_low, -⟩ | h_high := h_mem σ u hu
  · grind [Data.gap]
  · have ht_pos : 0 < D.t := D.t_odd.pos
    have h_lt : D.halfGap / 2 < u.natAbs := lt_natAbs_of_abs_add_liftWeight_le (by omega) h_high
    omega

/-- Let `ℓ = D.levelPrime n` be one of the two level primes of the data `D`, let `r = D.r` be the
rank, `t = D.t = 5 r` and `0 < x ≤ t`. The number `3 r² ((r + t) r + 1)² + 150 (h₂² + 4 t + 2)` is
the exponent of `ℓ` that `New.Lift.hasCupExponent_of_isTameType` gives at the sizes of the data.
Twice this number is at most `defectBound D ℓ / x`, with
`defectBound D ℓ = 10⁶ (m / k) (b v_ℓ(M) + λ)` in the nonnegative reals, where `m = D.m`,
`k = D.k = D.r + 1 - m`, `b = D.natB` is the weight at the b-places, `M = D.M` is the product of the
two level primes, and `λ = crystallineLoss h₂ b ℓ` is the `ℓ`-adic valuation of
`(2 b)! (∏ a) ^ h₂³`, with `a` over the positive integers in `(b - 30 h₂³, b + 30 h₂³]` and
`h₂ = D.halfGap = D.r ^ 8`. The term `10⁶ (m / k) b v_ℓ(M) / x` suffices. -/
lemma New.Selmer.two_mul_tame_exponent_le_defectBound {P : Parameters} (D : Data P) (n : Fin 2)
    {x : ℕ} (hx_pos : 0 < x) (hx_le : x ≤ D.t) :
    2 * ((3 * (D.r ^ 2 * ((D.r + D.t) * D.r + 1) ^ 2) +
      150 * (D.halfGap ^ 2 + 1 + 4 * D.t + 1) : ℕ) : NNReal) ≤
      defectBound D (D.levelPrime n) / x := by
  have h_val : 1 ≤ padicValNat (D.levelPrime n) D.M :=
    one_le_padicValNat_of_dvd out (by fin_cases n <;> simp [M])
  calc _ ≤ (10 ^ 6 * (D.m / D.k * (D.natB * 1)) / D.t : NNReal) := by
         -- A comparison of sizes, read off the logarithmic scales of the data.
         rify
         exact D.le_of_hasLogBound
    _ ≤ defectBound D (D.levelPrime n) / x := by
      grw [defectBound, ← h_val, ← le_self_add, hx_le]
      simp

/-- Let `t = D.t = 5 D.r` and `0 < x ≤ t`. Then
`10⁵ (ρ ⌊2 λ / (k t)⌋ m + ⌊ρ m / (k x)⌋ λ) ≤ ρ · defectBound D ℓ / x`, with
`defectBound D ℓ = 10⁶ (m / k) (b v_ℓ(M) + λ)` in the nonnegative reals, where `m = D.m`,
`k = D.k = D.r + 1 - m`, `b = D.natB` is the weight at the b-places, `M = D.M` is the product of the
two level primes, and `λ = crystallineLoss h₂ b ℓ` is the `ℓ`-adic valuation of
`(2 b)! (∏ a) ^ h₂³`, with `a` over the positive integers in `(b - 30 h₂³, b + 30 h₂³]` and
`h₂ = D.halfGap = D.r ^ 8`. The left side is the bound of
`New.Selmer.normLength_dualDefect_le_of_crystallineSizes` for a lattice of rank `ρ`, with `Q = k t`
and `μ = ⌊ρ m / (k x)⌋`. -/
lemma New.Selmer.crystalline_bound_le_defectBound {P : Parameters} (D : Data P) (ℓ ρ : ℕ) {x : ℕ}
    (hx_pos : 0 < x) (hx_le : x ≤ D.t) :
    ((10 ^ 5 * (ρ * (2 * crystallineLoss D.halfGap D.natB ℓ / (D.k * D.t) * D.m) +
      ρ * D.m / (D.k * x) * crystallineLoss D.halfGap D.natB ℓ) : ℕ) : NNReal) ≤
      ρ * (defectBound D ℓ / x) := by
  have hk_pos : 0 < D.k := D.k_pos
  set v : ℕ := crystallineLoss D.halfGap D.natB ℓ with hv
  have h_div : ((2 * v / (D.k * D.t) : ℕ) : NNReal) ≤ 2 * v / (D.k * x) := by
    grw [cast_div_le, ← hx_le]
    simp
  have h_low : ((ρ * D.m / (D.k * x) : ℕ) : NNReal) ≤ ρ * D.m / (D.k * x) :=
    cast_div_le.trans_eq (by simp)
  calc _ ≤ (10 ^ 5 * (ρ * (2 * v / (D.k * x) * D.m) + ρ * D.m / (D.k * x) * v) : NNReal) := by
         push_cast
         gcongr
         norm_num
    _ = 3 * 10 ^ 5 * ρ * D.m * v / (D.k * x) := by
      field_simp
      ring
    _ ≤ 10 ^ 6 * ρ * D.m * (D.natB * padicValNat ℓ D.M + v) / (D.k * x) := by
      grw [← le_add_self]
      gcongr
      norm_num
    _ = ρ * (defectBound D ℓ / x) := by
      rw [defectBound, ← hv]
      field_simp

/-- The lattices `L i` are the summands at a place above `ℓ`, and `F`, `K`, `U` are the data of a
class `New.Lift.InClass F K U` adapted to them. The summand `L none` is the main summand, of rank
`r` and with jumps `J g` at `coefficientEmbedding O g`; the summand `L (some c)` has the single jump
`c < t`. -/
structure New.Selmer.IsSummandClass {P : Parameters} (D : Data P) {ℓ : ℕ} [ThePrime ℓ] {Γ : Type}
    [Group Γ] [𝒥 : OverGp Γ ℓ] {O : CoeffRing ℓ} (r : ℕ) (J : Gp ℓ → Multiset ℤ) {t : ℕ}
    (L : Option (Fin t) → GalLattice O Γ) (F : Filter Γ) (K : Γ → Polynomial O → Prop)
    (U : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ) : Prop where
  /-- The class is tame, with `ℓ` one of the primes `D.levelPrime n`, or crystalline with no
  condition on inertia. -/
  tame_or_crystalline :
    (∃ n : Fin 2, ℓ = D.levelPrime n ∧
      ∀ s : Γ, IsWeilPair (𝒥.toGp s) 0 → IsTameType ℓ D.r ((D.r + D.t) * D.r) (K s)) ∨
    (F = ⊤ ∧ K = ⊥)
  /-- Every jump allowed by `U` is a jump of one of the summands. -/
  exists_jump_ne_zero (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (u : ℤ) (hu : u ∈ U γ) :
    ∃ i : Option (Fin t), jump (L i).ρ γ u ≠ 0
  /-- The main summand has the jumps `J`. -/
  hasJumps_none (g : Gp ℓ) : HasJumps (L none).ρ (coefficientEmbedding O g) (J g)
  /-- The summand `L (some c)` has the single jump `c`. -/
  hasJumps_some (c : Fin t) (g : Gp ℓ) : HasJumps (L (some c)).ρ (coefficientEmbedding O g)
    {(c : ℤ)}
  /-- The main summand has rank `r`. -/
  finrank_none : finrank O (L none) = r

/-- The data satisfy the size conditions `CrystallineSizes` with `Q = D.k * D.t`, `m = D.m`,
`h = D.halfGap`, `G = D.offWeight`, `b = D.natB`, `η = h² + 1`, `W = 4 D.t` and the shift
`δ = i D.gap + h - 2 D.t`, for `i ≤ D.m`; each condition is a comparison of logarithmic scales. -/
lemma New.Selmer.crystallineSizes_data {P : Parameters} (D : Data P) {i : ℕ} (hi : i ≤ D.m) :
    CrystallineSizes (D.k * D.t) D.m D.halfGap D.offWeight D.natB
      (i * D.gap + D.halfGap - 2 * D.t) (D.halfGap ^ 2 + 1) (4 * D.t) := by
  have h_shift : i * D.gap + D.halfGap - 2 * D.t < D.halfGap ^ 2 + 1 := by
    grw [sub_le, hi]
    exact D.nat_lt_of_hasLogBound
  exact ⟨D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound,
    D.nat_le_of_hasLogBound, D.lt_of_hasLogBound, h_shift, D.nat_le_of_hasLogBound⟩

/-- Put `h₂ = D.halfGap`, `m = D.m` and `k = D.k = D.r + 1 - m`. Let the multisets `J σ`, for the
complex embeddings `σ` of `D.E`, be the weights of a main summand. Let `L` be a potentially
crystalline lattice over the ring of integers `O` of a finite Galois extension of `ℚ_ℓ`, with an
action of `Γ → G_ℓ`, whose Hodge–Tate jumps at each embedding `γ` of `O`, with multiplicity
`jump L.ρ γ u`, are `J (σ γ)`. Let `U γ` consist of members of `J (σ γ)` and integers in `[0, t)`,
and `U' γ` of jumps of the Tate dual of `L`. Then the dual has few low jumps (`HasFewLowJumps`): the
negative members of `U γ` and `U' γ` are at most `-h₂ / 2`, and at most `⌊r m / k⌋` of its jumps at
`γ` lie in `[-h₂² - 1, h₂² + 1]`. -/
lemma New.Selmer.hasFewLowJumps_tateDual_of_isMainSummandWeights {P : Parameters} {D : Data P}
    {ℓ : ℕ} [ThePrime ℓ] {Γ : Type} [Group Γ] [OverGp Γ ℓ] {O : CoeffRing ℓ}
    {L : GalLattice O Γ} (hL : IsPotentiallyCrystalline L.ρ) {r t : ℕ}
    {J : (D.E →+* ℂ) → Multiset ℤ}
    (hJ : IsMainSummandWeights D r t J) {σ : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → D.E →+* ℂ}
    (h_jumps : ∀ (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (u : ℤ), jump L.ρ γ u = Multiset.count u (J (σ γ)))
    {U U' : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
    (hU : ∀ γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], ∀ u ∈ U γ, u ∈ J (σ γ) ∨ ∃ c < t, u = (c : ℕ))
    (hU' : ∀ γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], ∀ u ∈ U' γ, jump L.tateDual.ρ γ u ≠ 0) :
    HasFewLowJumps L.tateDual D.halfGap (r * D.m / D.k) (D.halfGap ^ 2 + 1) U U' := by
  refine ⟨fun γ u hu_neg h_mem ↦ ?_, fun γ ↦ ?_⟩
  · obtain hu | hu := h_mem
    · -- A negative member of `U γ` is a jump of the main summand.
      have h_main : u ∈ J (σ γ) := (hU γ u hu).resolve_right fun ⟨_, _, hc⟩ ↦ by omega
      have h_size : D.halfGap ≤ 2 * u.natAbs := hJ.le_two_mul_natAbs h_main
      omega
    · have h_main : -u - 1 ∈ J (σ γ) := by simpa [jump_tateDual hL, h_jumps] using hU' γ u hu
      have h_size : D.halfGap ≤ 2 * (-u - 1).natAbs := hJ.le_two_mul_natAbs h_main
      omega
  · have ht_small : 3 * D.t ≤ D.halfGap := D.nat_le_of_hasLogBound
    have h_sq : 2 ≤ D.halfGap ^ 2 := by nlinarith [D.t_odd.pos]
    suffices (∑ u ∈ Finset.Icc (-1 + -(D.halfGap : ℤ) ^ 2) ((D.halfGap : ℤ) ^ 2 + 1),
        Multiset.count (-u - 1) (J (σ γ))) * D.k ≤ r * D.m by
      simpa [jump_tateDual hL, h_jumps, le_div_iff_mul_le D.k_pos] using this
    grw [sum_count_neg_sub_one_le h_sq, hJ.card_small_le]

/-- If the lattice `L` is potentially crystalline with the single Hodge–Tate jump `c < D.t`, then
every jump of its Tate dual, which is `-c - 1`, lies in `[-h₂² - 1, 0]`, where `h₂ = D.halfGap`. -/
lemma New.Selmer.subset_Icc_of_jump_eq_single {P : Parameters} {D : Data P} {ℓ : ℕ} [ThePrime ℓ]
    {Γ : Type} [Group Γ] [OverGp Γ ℓ] {O : CoeffRing ℓ} {L : GalLattice O Γ}
    (hL : IsPotentiallyCrystalline L.ρ) {c : ℕ} (hc : c < D.t)
    (h_jumps : ∀ (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (u : ℤ), jump L.ρ γ u = Multiset.count u {(c : ℤ)})
    {γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]} {U : Finset ℤ} (hU : ∀ u ∈ U, jump L.tateDual.ρ γ u ≠ 0) :
    U ⊆ Finset.Icc (-(D.halfGap ^ 2 + 1 : ℕ) : ℤ) 0 := by
  intro u hu
  have hu_eq : -u - 1 = c := by simpa [jump_tateDual hL, h_jumps] using hU u hu
  have ht_small : 3 * D.t ≤ D.halfGap := D.nat_le_of_hasLogBound
  exact mem_Icc.2 ⟨by push_cast; nlinarith, by omega⟩

/-- The tame case, at one of the two level primes `ℓ = D.levelPrime n` of the data `D`. Here `D.r`
is the rank parameter of the data and `D.t = 5 D.r`; the rank of the lattice `L` is arbitrary.
Let `𝒥.toGp : Γ → G_ℓ` be an open embedding onto the elements of
`G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` that fix `e E`, where `E = D.E`. A lattice lies in `InClass F K U` if its
crystalline periods fixed on a neighbourhood of `1` that belongs to the filter `F` span, its
Hodge–Tate jumps at each embedding `γ` of `O` lie in `U γ`, and each polynomial allowed by `K s`
kills `s` on its periods, for `s` in inertia. Assume:
* `hL`: `L` lies in the class for `F`, `s ↦ K s⁻¹` and `U'`;
* `h_tame`: for each `s` in inertia (`IsWeilPair (𝒥.toGp s) 0`) the condition `K s` on polynomials
  holds for `X ^ e' - 1`, with `e'` the least common multiple of the `ℓ ^ a - 1` for `1 ≤ a ≤ D.r`,
  and for a monic polynomial over `ℤ_ℓ` of degree at most `(D.r + D.t) D.r` (`IsTameType`);
* `hU`, `hU'`: with `η = h₂² + 1`, the sign `ε = cmSign σ` of a complex embedding `σ` for the CM
  type, and `S = farWindowStart D i σ` (the `i`-th lift weight at `σ` minus `2 D.t`, `i ≤ D.m`),
  each `U γ` lies in `[-η, η] ∪ -ε · [S, S + 4 D.t]` and each `U' γ` in
  `[-η, η] ∪ ε · [S, S + 4 D.t]`.

Then the defect of `L` for the class `InClass F K U`, the length of the crystalline cocycles modulo
those orthogonal, under cup products, to the crystalline cocycles of the lattices in the class,
normalised so that `O / ℓ` has length `1`, is at most `[G_ℓ : Γ] · rank L · defectBound D ℓ / x` for
`0 < x ≤ D.t`. Here `defectBound D ℓ = 10⁶ (m / k) (b v_ℓ(M) + λ)` in the nonnegative reals, where
`m = D.m`, `k = D.k = D.r + 1 - m`, `b = D.natB` is the weight at the b-places, `M = D.M` is the
product of the two level primes, and `λ = crystallineLoss h₂ b ℓ` is the `ℓ`-adic valuation of
`(2 b)! (∏ a) ^ h₂³`, with `a` over the positive integers in `(b - 30 h₂³, b + 30 h₂³]` and
`h₂ = D.halfGap = D.r ^ 8`. -/
lemma New.Selmer.normLength_dualDefect_le_defectBound_of_isTameType {P : Parameters} {D : Data P}
    {n : Fin 2} [ThePrime (D.levelPrime n)] [PadicIso (D.levelPrime n)] {Γ : Type} [Group Γ]
    [𝒥 : OverGp Γ (D.levelPrime n)] [TopologicalSpace Γ]
    {e : D.E →+* PadicAlgCl (D.levelPrime n)} (h_group : IsCompletionGroup e 𝒥.toGp)
    {O : CoeffRing (D.levelPrime n)} {L : GalLattice O Γ} {F : Filter Γ}
    {K : Γ → Polynomial O → Prop} {U U' : (O →ₐ[ℤ_[D.levelPrime n]] ℂ_[D.levelPrime n]) → Finset ℤ}
    (hL : InClass F (fun s : Γ ↦ K s⁻¹) U' L)
    (h_tame : ∀ s : Γ, IsWeilPair (𝒥.toGp s) 0 →
      IsTameType (D.levelPrime n) D.r ((D.r + D.t) * D.r) (K s))
    {i : ℕ} (hi : i ≤ D.m) {σ : D.E →+* ℂ}
    (hU : ∀ γ : O →ₐ[ℤ_[D.levelPrime n]] ℂ_[D.levelPrime n],
      FitsWindows (D.halfGap ^ 2 + 1) (-cmSign σ) (farWindowStart D i σ) (4 * D.t) (U γ))
    (hU' : ∀ γ : O →ₐ[ℤ_[D.levelPrime n]] ℂ_[D.levelPrime n],
      FitsWindows (D.halfGap ^ 2 + 1) (cmSign σ) (farWindowStart D i σ) (4 * D.t) (U' γ))
    {x : ℕ} (hx_pos : 0 < x) (hx_le : x ≤ D.t) :
    O.normLength (dualDefect (InClass F K U) L) ≤
      𝒥.toGp.range.index * ↑(finrank O L * (defectBound D (D.levelPrime n) / x)) := by
  -- `ℓ` exceeds the bound that `hasCupExponent_of_isTameType` asks for, at b-places and at the
  -- other places.
  have h_large : farWindowStart D i σ + 6 * (4 * D.t + (D.halfGap ^ 2 + 1)) +
      D.r ^ 2 * ((D.r + D.t) * D.r + 1) ^ 2 + 2 < D.levelPrime n := by
    grw [farWindowStart, sub_le, hi]
    split_ifs <;> exact D.nat_lt_of_hasLogBound
  exact normLength_dualDefect_le_of_hasCupExponent hL.isPotentiallyCrystalline
    (by grw [two_mul_tame_exponent_le_defectBound D n hx_pos hx_le])
    (hasCupExponent_of_isTameType (Γ := ⟨Γ⟩) h_group.1
      (mem_range_of_modEq_one h_group (D.levelPrime_modEq_one n)) hL h_tame hU hU' h_large)

/-- The defect bound at one place above `ℓ`. Let `𝒥.toGp : Γ → G_ℓ` be an open embedding onto the
elements of `G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` that fix `e E`, where `E = D.E`; each `g` in `G_ℓ` gives a
complex embedding `complexEmbeddingOf e g` of `E`. Let the multisets `J σ` be the weights of a main
summand (`IsMainSummandWeights`): `1 ≤ r ≤ D.r`, `t ≤ D.t = 5 D.r`, each member `u` of `J σ` has
`h₂ / 2 ≤ |u| ≤ 4 m h₂` or lies within `D.t` of `∓ w_i(σ)` for one lift weight
`w_i = D.liftWeight i` with `i ≤ m`, at most `r m / k` members have `|u| ≤ 2 h₂²`, and at most `r`
members of `J σ` and `J σ̄` together are negative. Here `O` runs over the rings of integers of
finite Galois extensions of `ℚ_ℓ`, and large means containing a given one. Let `O` be large. A
lattice lies in `InClass F K U` if its crystalline periods fixed on a neighbourhood of `1` that
belongs to the filter `F` span, its Hodge–Tate jumps at each embedding `γ` of `O` lie in `U γ`, and
each polynomial allowed by `K s` kills `s` on its periods, for `s` in inertia. Let the class be
adapted to the lattices `L c` (`IsSummandClass`): it is tame with `ℓ` a level prime of `D`, or
crystalline (`F = ⊤`, `K = ⊥`); each member of `U γ` is a jump of some `L c`; the main summand
`L none` has rank `r` and jumps `J (complexEmbeddingOf e g)` at the embedding `a ↦ g a` of `O`; and
`L (some c)` has the single jump `c`. If `L c` lies in the class, then the defect of its Tate dual,
the length of the crystalline cocycles modulo those orthogonal, under cup products, to the
crystalline cocycles of the lattices in the class, normalised so that `O / ℓ` has length `1`, is at
most `[G_ℓ : Γ] · rank (L c) · defectBound D ℓ / x`, where `x = 1` for the main summand and
`x = D.t` otherwise. Here `defectBound D ℓ = 10⁶ (m / k) (b v_ℓ(M) + λ)` in the nonnegative reals,
where `m = D.m`, `k = D.k = D.r + 1 - m`, `b = D.natB` is the weight at the b-places, `M = D.M` is
the product of the two level primes, and `λ = crystallineLoss h₂ b ℓ` is the `ℓ`-adic valuation of
`(2 b)! (∏ a) ^ h₂³`, with `a` over the positive integers in `(b - 30 h₂³, b + 30 h₂³]` and
`h₂ = D.halfGap = D.r ^ 8`; the division by `x` is exact. -/
lemma New.Selmer.normLength_dualDefect_le_of_isSummandClass {P : Parameters} {ℓ : ℕ} {Γ : Type}
    {D : Data P} [hp : ThePrime ℓ] [PadicIso ℓ] [Group Γ] [𝒥 : OverGp Γ ℓ] [TopologicalSpace Γ]
    {e : D.E →+* PadicAlgCl ℓ} {r t : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ}
    (hJ : IsMainSummandWeights D r t J) (h_group : IsCompletionGroup e 𝒥.toGp) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
      ∀ {L : Option (Fin t) → GalLattice O Γ} {F : Filter Γ} {K : Γ → Polynomial O → Prop}
        {U : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ},
      IsSummandClass D r (fun g : Gp ℓ ↦ J (complexEmbeddingOf e g)) L F K U →
      ∀ c : Option (Fin t), InClass F K U (L c) →
        O.normLength (dualDefect (InClass F K U) (L c).tateDual) ≤
          𝒥.toGp.range.index *
            ↑(finrank O (L c) * (defectBound D ℓ / (if c = none then 1 else D.t : ℕ))) := by
  -- In the tame case the bound is `normLength_dualDefect_le_defectBound_of_isTameType`; in the
  -- crystalline case it is `normLength_dualDefect_le_of_crystallineSizes`, with the sizes of the
  -- data checked by `crystallineSizes_data`.
  filter_upwards [eventually_exists_lettersReadThick (D := D) h_group] with
    O h_chart L F K U ⟨h_type, h_jump, h_main, h_char, h_rank⟩ c h_in
  subst h_rank
  set x : ℕ := if c = none then 1 else D.t
  obtain ⟨i, hi, h_mem⟩ := hJ.low_or_high
  obtain ⟨hx_le, hx_pos⟩ : x ≤ D.t ∧ 0 < x := by have := D.t_odd.pos; lia
  -- Every coefficient embedding is given by an element of `G_ℓ`.
  choose lift h_lift using
    (coefficientEmbedding_surjective : ∀ γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], ∃ g : Gp ℓ,
      coefficientEmbedding O g = γ)
  let σ (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) : D.E →+* ℂ := complexEmbeddingOf e (lift γ)
  have h_count (b : Option (Fin t)) (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) (u : ℤ) :
      jump (L b).ρ γ u = Multiset.count u (b.elim (J (σ γ)) fun c : Fin t ↦ {↑c}) := by
    cases b with
    | none => simpa only [h_lift, Option.elim_none] using h_main (lift γ) u
    | some c => simpa only [h_lift, Option.elim_some] using h_char c (lift γ) u
  -- A jump of the class is a jump of the main summand or of one of the characters.
  have hU : ∀ γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], ∀ u ∈ U γ, u ∈ J (σ γ) ∨ ∃ c < t, u = (c : ℕ) := by
    simpa [h_count, Option.exists, Fin.exists_iff] using h_jump
  -- The jumps of the class and of its dual lie in opposite windows.
  have h_win (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) :
      FitsWindows (D.halfGap ^ 2 + 1) (-cmSign (σ γ)) (farWindowStart D i (σ γ)) (4 * D.t)
          (U γ) ∧
        FitsWindows (D.halfGap ^ 2 + 1) (cmSign (σ γ)) (farWindowStart D i (σ γ)) (4 * D.t)
          ((U γ).image fun u : ℤ ↦ -u - 1) :=
    fitsWindows_and_image_neg_sub_one hJ.t_le (h_mem (σ γ)) (hU γ)
  have h_dual : InClass F (fun s : Γ ↦ K s⁻¹)
      (fun γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] ↦ (U γ).image fun u : ℤ ↦ -u - 1) (L c).tateDual := h_in.dual
  obtain ⟨n, rfl, h_tame⟩ | ⟨rfl, rfl⟩ := h_type
  · -- Tame case, `ℓ = D.levelPrime n`. As `ℓ ≡ 1` modulo the conductor, all `g` read the same
    -- embedding.
    have h_emb (g : Gp (D.levelPrime n)) : complexEmbeddingOf e g = complexEmbeddingOf e 1 :=
      h_group.complexEmbeddingOf_eq_iff.2
        (mem_range_of_modEq_one h_group (D.levelPrime_modEq_one n) _)
    simp only [σ, h_emb] at h_win
    simpa only [finrank_linearMap_self] using
      normLength_dualDefect_le_defectBound_of_isTameType h_group h_dual h_tame hi
        (fun γ ↦ (h_win γ).1) (fun γ ↦ (h_win γ).2) hx_pos hx_le
  -- Crystalline case: `normLength_dualDefect_le_of_crystallineSizes` with `Q = k t`, `h = h₂`,
  -- `G = offWeight`, `b = natB` and at most `μ = rank · m / (k x)` low jumps.
  obtain ⟨k, ζ, T, s, h_reads⟩ := h_chart
  -- The class of the dual is kept with its true jumps only.
  let U' (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) : Finset ℤ :=
    ((U γ).image fun u : ℤ ↦ -u - 1).filter (jump (L c).tateDual.ρ γ · ≠ 0)
  have hU' (γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) : ∀ u ∈ U' γ, jump (L c).tateDual.ρ γ u ≠ 0 :=
    fun _ hu ↦ (mem_filter.1 hu).2
  have h_dual' : InClass ⊤ ⊥ U' (L c).tateDual := h_dual.imp_right (by simp +contextual [U'])
  have h_reads' : LettersReadThick k (fun γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] ↦ γ ζ)
      (fun γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] ↦ InfinitePlace.mk (σ γ) ∈ D.bPlaces)
      (fun γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ] ↦ cmSign (σ γ)) (D.k * D.t) D.halfGap T s :=
    { h_reads with
      thick_iff := fun γ hγ ↦ by simpa only [h_lift] using h_reads.thick_iff (lift γ) hγ
      sign_eq := fun γ hγ ↦ by simpa only [h_lift] using h_reads.sign_eq (lift γ) hγ }
  refine normLength_dualDefect_le_of_crystallineSizes (Γ := ⟨Γ⟩) (D.k * D.t) D.m D.halfGap
    (finrank O (L c) * D.m / (D.k * x)) (crystallineSizes_data D hi) (fun γ ↦ (h_win γ).1)
    (fun γ u hu ↦ (h_win γ).2 u (filter_subset _ _ hu)) h_dual' ?_ ?_ h_group.1 k ζ h_reads'
  · cases c with
    | none =>
      -- The main summand: the negative jumps are at most `-h₂ / 2`, and few jumps are low.
      refine .inl ?_
      simpa [x] using hasFewLowJumps_tateDual_of_isMainSummandWeights h_in.isPotentiallyCrystalline
        hJ (h_count none) hU hU'
    | some c =>
      -- A character: the only jump is `-c - 1`, which is low and negative.
      exact .inr fun γ ↦ subset_Icc_of_jump_eq_single h_in.isPotentiallyCrystalline
        (c.2.trans_le hJ.t_le) (h_count (some c)) (hU' γ)
  · simpa only [finrank_linearMap_self] using
      crystalline_bound_le_defectBound D ℓ (finrank O (L c)) hx_pos hx_le

/-- The bound of `New.Selmer.normLength_dualDefect_le_of_isSummandClass`, with the clauses of
`New.Selmer.IsSummandClass` as separate hypotheses. Let `𝒥.toGp : Γ → G_ℓ` be an open embedding onto
the elements of `G_ℓ = Gal(ℚ̄_ℓ / ℚ_ℓ)` that fix `e E`, where `E = D.E`. Let the multisets `J σ`,
for the complex embeddings `σ` of `E`, be the weights of a main summand (`IsMainSummandWeights`):
`1 ≤ r ≤ D.r`, `t ≤ D.t = 5 D.r`, each member `u` of `J σ` has `h₂ / 2 ≤ |u| ≤ 4 m h₂` or lies
within `D.t` of `∓ w_i(σ)` for one lift weight `w_i = D.liftWeight i` with `i ≤ m`, at most
`r m / k` members have `|u| ≤ 2 h₂²`, and at most `r` members of `J σ` and `J σ̄` together are
negative. Let the coefficient ring `O` be large. The class `InClass F K U` of lattices (given by
admissibility along `F`, polynomial conditions `K s` on inertia and allowed Hodge–Tate jumps `U γ`)
is crystalline without condition on inertia, or tame: `ℓ` is one of the two level primes
`D.levelPrime n`, and for each `s` in inertia (`IsWeilPair (𝒥.toGp s) 0`) the condition `K s` on
polynomials holds for `X ^ e' - 1`, with `e'` the least common multiple of the `ℓ ^ a - 1` for
`1 ≤ a ≤ D.r`, and for a monic polynomial over `ℤ_ℓ` of degree at most `(D.r + D.t) D.r`
(`IsTameType`). Each member of `U γ` is a jump of a summand `L i`. At the embedding
`coefficientEmbedding O g : a ↦ g a` of `O`, the main summand `L none`, of rank `r`, has the jumps
`J σ` for the complex embedding `σ = complexEmbeddingOf e g` given by `g`, and `L (some c)` has the
single jump `c`. If `L c` lies in the class, the defect of its Tate dual, the length of the
crystalline cocycles modulo those orthogonal, under cup products, to the crystalline cocycles of the
lattices in the class, normalised so that `O / ℓ` has length `1`, is at most
`[G_ℓ : Γ] · rank (L c) · defectBound D ℓ / x`, where `x = 1` for the main summand and `x = D.t`
otherwise. Here `defectBound D ℓ = 10⁶ (m / k) (b v_ℓ(M) + λ)` in the nonnegative reals, where
`m = D.m`, `k = D.k = D.r + 1 - m`, `b = D.natB` is the weight at the b-places, `M = D.M` is the
product of the two level primes, and `λ = crystallineLoss h₂ b ℓ` is the `ℓ`-adic valuation of
`(2 b)! (∏ a) ^ h₂³`, with `a` over the positive integers in `(b - 30 h₂³, b + 30 h₂³]` and
`h₂ = D.halfGap = D.r ^ 8`. -/
lemma New.Selmer.summand_defect_le_at_place {P : Parameters} {ℓ : ℕ} {Γ : Type} {D : Data P}
    [hp : ThePrime ℓ] [PadicIso ℓ] [Group Γ] [𝒥 : OverGp Γ ℓ] [TopologicalSpace Γ]
    {e : D.E →+* PadicAlgCl ℓ} {r t : ℕ} {J : (D.E →+* ℂ) → Multiset ℤ}
    (h_weights : IsMainSummandWeights D r t J) (h_group : IsCompletionGroup e 𝒥.toGp) :
    ∀ᶠ O : CoeffRing ℓ in Filter.atTop,
      ∀ {L : Option (Fin t) → GalLattice O Γ} {F : Filter Γ} {K : Γ → Polynomial O → Prop}
        {U : (O →ₐ[ℤ_[ℓ]] ℂ_[ℓ]) → Finset ℤ}
        (_h_tame_or_crystalline : (∃ n : Fin 2, ℓ = D.levelPrime n ∧
            ∀ s : Γ, IsWeilPair (𝒥.toGp s) 0 → IsTameType ℓ D.r ((D.r + D.t) * D.r) (K s)) ∨
          (F = ⊤ ∧ K = ⊥))
        (_h_class_jump : ∀ γ : O →ₐ[ℤ_[ℓ]] ℂ_[ℓ], ∀ u ∈ U γ,
          ∃ i : Option (Fin t), jump (L i).ρ γ u ≠ 0)
        (_h_jumps : ∀ (i : Option (Fin t)) (g : Gp ℓ), HasJumps (L i).ρ (coefficientEmbedding O g)
          (i.elim (J (complexEmbeddingOf e g)) fun c : Fin t ↦ {↑c}))
        (_h_rank : finrank O (L none) = r) (c : Option (Fin t)) (_h_mem : InClass F K U (L c)),
        O.normLength (dualDefect (InClass F K U) (L c).tateDual) ≤
          𝒥.toGp.range.index *
            ↑(finrank O (L c) * (defectBound D ℓ / (if c = none then 1 else D.t : ℕ))) := by
  filter_upwards [normLength_dualDefect_le_of_isSummandClass h_weights h_group] with
    O h_bound L F K U h_type h_jump h_jumps h_rank
  exact h_bound ⟨h_type, h_jump, h_jumps none, fun c ↦ h_jumps (some c), h_rank⟩

end OnePlaceDefect

import Lib.GaloisRep.Main.QuadraticStep
import Lib.Shimura.HeckeTower.Model

/-!
# Existence of PEL data at levels good at all safe places, with the form ξ and a Lagrangian

PEL data (`New.PEL`) are the arithmetic input of the moduli problem; this file constructs them.

* `New.Variety.exists_lagrangian`: an isotropic set lies in a self-annihilating subgroup.
* `New.Variety.IsSafeGoodPEL`: PEL data of given rank, level and `β`, good at all safe places.
* `New.Variety.exists_pel`: PEL data of any nonzero rank at every nonzero level divisible by some
  `N` that lies in none of the places of a given finite set `B`, good at all safe places.

Conventions: `CMBase E` is a CM type `Φ` together with a base place `v₀`; `Φ v` is the embedding the
CM type picks at `v`, `ψf` the standard character of the finite adeles, `xiForm ξ x y = ξ yᴴ x`,
`Ô E` the integral finite adeles, and `torsionClass` the quotient map onto
`AdelicTorsion E (Fin n)`, whose kernel is the vectors with entries in `Ô E`.

Notions from other files:
* `New.HasPrimitiveRoot5040`: `E` contains a primitive root of unity of order `7! = 5040`.
* `New.Variety.IsSafe 𝔑 w` (for `ℚ(√−d)` in `E`): the place u of ℚ(√−d) below w contains some
  (1 + √−d)/2 − b, b ∈ ℤ, that is coprime to its conjugate, and 𝔑 lies neither in w nor in any place
  above ū.

## Relation to the literature

Known; see `Lib.Shimura.IntegralModel.TowerExistence` for sources.
-/

namespace New.Variety

open NumberField InfinitePlace FractionalIdeal Algebra Ideal Nat ThetaNull AddSubgroup QuadField
  Quotient

/-- Existence of Lagrangians. For an alternating bimultiplicative pairing `e` on an abelian
group, every isotropic set lies in a subgroup equal to its own annihilator. -/
lemma exists_lagrangian {V G : Type*} [AddCommGroup V] [CommGroup G] (e : V → V → G)
    (h_sub_div : ∀ x y z : V, e (x - y) z = e x z / e y z ∧ e z (x - y) = e z x / e z y)
    (h_alt : ∀ x : V, e x x = 1) (S : Set V) (hS : IsChain (fun x y : V ↦ e x y = 1) S) :
    ∃ Λ : AddSubgroup V, S ⊆ Λ ∧ ∀ x : V, x ∈ Λ ↔ ∀ y ∈ Λ, e x y = 1 := by
  -- Take a maximal isotropic set `M` containing `S` (Zorn); it is its own annihilator.
  obtain ⟨M, h_max, hSM⟩ := hS.exists_maxChain
  have mem_iff (x : V) : x ∈ M ↔ ∀ y ∈ M, e x y = 1 := by
    refine ⟨fun hx y hy ↦ ?_, fun hx ↦ ?_⟩
    · -- A chain gives `e x y = 1` or `e y x = 1`; expanding `e (x - y) (x - y) = 1` links the two.
      grind [h_max.isChain hx hy, h_alt (x - y), div_eq_one]
    · -- An `x` that pairs trivially with `M` can be added to the chain, so lies in it already.
      exact (h_max.2 (h_max.isChain.insert (by tauto)) (M.subset_insert x)).ge (M.mem_insert x)
  -- An annihilator is closed under subtraction, since `e` is multiplicative.
  have h_sub : ∀ x ∈ M, ∀ y ∈ M, x + -y ∈ M := by grind [=_ sub_eq_add_neg, div_self']
  exact ⟨.ofSub M (h_max.nonempty_iff.mp ⟨0⟩) h_sub, hSM, mem_iff⟩

open Filter Fin Finset in
/-- For every integer `c` of the CM field `E`, all large enough natural numbers `r` admit a padding
of `c` (`New.Variety.HasPadding E r c`). A padding is a choice of `r - 3` integers `aₗ` of `E` that
span `𝓞 E` over `ℤ` and satisfy `r = c̄ c + 3 + ∑ₗ āₗ aₗ` in `𝓞 E`, where the bar is complex
conjugation. -/
lemma eventually_hasPadding {E : Type} [Field E] [NumberField E] [IsCMField E] (c : 𝓞 E) :
    ∀ᶠ r : ℕ in atTop, HasPadding E r c := by
  -- Let `v` list `c` and a `ℤ`-basis `b` (of length `d`), and write `∑ (1 - v̄ v) = ∑ n i * b i`.
  -- This sum is real, so the norms of `c`, `c`, the `b i` and the `b i + n i` add up to the integer
  -- `2 * (1 + d) + ∑ n i ^ 2`. Pad with `∑ n i ^ 2 + 1` zeros and any number `m` of ones.
  let b : Module.Basis (Fin (Module.finrank ℤ (𝓞 E))) ℤ (𝓞 E) := Module.finBasis ℤ (𝓞 E)
  let d : ℕ := Module.finrank ℤ (𝓞 E)
  let v : Fin (1 + d) → 𝓞 E := append ![c] b
  obtain ⟨n, hn⟩ : ∃ a : Fin (Module.finrank ℤ (𝓞 E)) → ℤ, b.equivFun.symm a = ∑ l : Fin (1 + d),
    (1 - star (v l) * v l) := b.equivFun.symm.surjective (∑ l, (1 - star (v l) * v l))
  have hn_star : star (b.equivFun.symm n) = star (∑ l : Fin (1 + d), (1 - star (v l) * v l)) := by
    rw [hn]
  let zeros : ℕ := (∑ i, (n i * n i).natAbs) + 1
  -- A large `r` is `m + (1 + d + (d + zeros) + 3)` for some `m`.
  rw [← map_add_atTop_eq_nat (1 + d + (d + zeros) + 3), eventually_map]
  filter_upwards with m
  refine ⟨append (m := m) 1 (append v (append (n := zeros) (fun i ↦ b i + n i) 0)), ?_, ?_⟩
  · -- The list contains the basis `b`, so it spans.
    refine top_unique (b.span_eq.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨natAdd _ (castAdd _ (natAdd _ i)), by simp [v]⟩
  -- `erw`: the list has index type `Fin (r - 3)`, which is `Fin (m + …)` only up to unfolding
  erw [sum_univ_add]
  -- Expand the norms of `b i + n i`: the cross terms `∑ n i * b i` and `∑ n i * star (b i)` are
  -- given by `hn` and `hn_star`, and they cancel the norms of `c` and of the `b i`.
  -- After this unfolding, the goal is an identity in `∑ n i * b i` and its conjugate.
  simp [v, d, zeros, sum_univ_add, sum_add_distrib, mul_add, add_mul, mul_comm] at hn hn_star ⊢
  rw [hn, hn_star]
  ring

/-- For `s ≠ 0` there is a purely imaginary `ξ` in the inverse different of `E`, with positive
imaginary parts under the CM type, that generates the inverse different at the primes of `s`. -/
lemma exists_star_eq_neg_and_im_pos {E : Type} [Field E] [CMBase E]
    [HasPrimitiveRoot5040 E] {s : ℕ} (hs : s ≠ 0) :
    ∃ (ξ : E) (c : 𝓞 E),
      -- (a) `ξ` is purely imaginary, in the upper half plane under the CM type
      star ξ = -ξ ∧ (∀ v : InfinitePlace E, 0 < (Φ v ξ).im) ∧
      -- (b) `ξ` lies in the inverse different
      (∀ u ∈ Ô E, ψf E (u * algebraMap E (𝔸f E) ξ) = 1) ∧
      -- (c) for some `m` in the different, `m ξ` is congruent to `-1` modulo `s`
      ∃ m ∈ differentIdeal ℤ (𝓞 E), algebraMap (𝓞 E) E (s * c - 1) = m • ξ := by
  -- With `F = E⁺` and `γ ^ 2 = -1`, take `ξ = a γ + s (z - star z)`, where `a` lies in the inverse
  -- different of `F` and generates it at the primes of `s`, and the integer `z` of `E` makes every
  -- imaginary part positive.
  let F : Subfield E := maximalRealSubfield E
  obtain ⟨γ, -, hγ_sq, hγ_star, -⟩ :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  let codiffF : FractionalIdeal (nonZeroDivisors (𝓞 F)) F := dual ℤ ℚ 1
  let codiffE : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := dual ℤ ℚ 1
  -- The ideal `(s)` and a principal multiple of the inverse different of `F` add up to `𝓞 F`.
  obtain ⟨μ₀, h_sum⟩ : ∃ μ₀ : F,
      coeIdeal (span {(s : 𝓞 F)}) + spanSingleton (nonZeroDivisors (𝓞 F)) μ₀ * codiffF = 1 :=
    IsDedekindDomain.exists_add_spanSingleton_mul_eq coeIdeal_le_one
      (by simpa [spanSingleton_eq_zero_iff]) (dual_ne_zero ℤ ℚ one_ne_zero)
  obtain ⟨c, a, ha, h_one⟩ : ∃ c : 𝓞 F, ∃ a ∈ codiffF, c • (s : F) + μ₀ * a = 1 := by
    simpa [mem_add, mem_singleton_mul, -Subtype.exists] using one_le.mp h_sum.ge
  -- `μ₀` times the inverse different lies in `𝓞 F`, so `μ₀` lies in the different.
  obtain ⟨μ, hμ, rfl⟩ : ∃ μ ∈ differentIdeal ℤ (𝓞 F), algebraMap (𝓞 F) F μ = μ₀ :=
    (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)).ge ((le_div_iff_mul_le (by simp [codiffF])).mpr
      (le_add_self.trans_eq h_sum) (mem_spanSingleton_self (nonZeroDivisors (𝓞 F)) μ₀))
  -- By `exists_hasFundDomain_toAdele`, every point of `ℂ ^ f` (`f` the number of infinite places)
  -- is moved by an integer into a ball of fixed radius `C`.
  obtain ⟨C, -, -, D, hD, -, -, h_fund⟩ := exists_hasFundDomain_toAdele (E := E)
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, ∀ v : InfinitePlace E,
      ‖Φ v (z : E) + (Φ v (a * γ / 2 / s : E) - ⟨0, C + 1⟩)‖ ≤ C := by
    obtain ⟨y, hy, -⟩ : ∃! y : E,
        toAdele.toAddMonoidHom y +
          (fun v : InfinitePlace E ↦ Φ v (a * γ / 2 / s) - { re := 0, im := C + 1 }, 0) ∈ D :=
      h_fund (fun v ↦ Φ v (a * γ / 2 / s) - ⟨0, C + 1⟩, 0)
    -- the point `y` is integral, and its shifted embeddings lie in the ball of radius `C`
    obtain ⟨hy_ball, hy_int⟩ := hD hy
    have hy_adele : algebraMap E (𝔸f E) y ∈ Ô E := by simpa using hy_int
    exact ⟨⟨y, algebraMap_mem_Ô.mp hy_adele⟩,
      fun v ↦ (norm_le_pi_norm _ v).trans (mem_closedBall_zero_iff.mp hy_ball)⟩
  refine ⟨a * γ + ↑(s * (z - star z)), μ • γ * (z - star z) + c • 1, ?_, fun v ↦ ?_, ?_,
    γ * algebraMap _ _ μ, ?_, ?_⟩
  · simp [← coe_star_ringOfIntegers, hγ_star, mem_maximalRealSubfield_iff_star_eq.mp, add_comm,
      mul_sub]
  · -- The shift by `(C + 1) i` forces `0 < Im (Φ v z) + Im (Φ v (a γ)) / (2 s)`, and
    -- `Im (Φ v ξ)` is `2 s` times this sum.
    have h_abs_im : |(Φ v (z : E) + (Φ v (a * γ / 2 / s : E) - ⟨0, C + 1⟩)).im| ≤ C :=
      (Complex.abs_im_le_norm _).trans (hz v)
    have h_im : -(C + 1) < (Φ v (z : E) + (Φ v (a * γ / 2 / s : E) - ⟨0, C + 1⟩)).im :=
      (neg_lt_neg (lt_add_one C)).trans_le (neg_le_of_abs_le h_abs_im)
    simp [field, map_ofNat] at h_im ⊢
    linarith
  · -- `ξ` lies in the inverse different of `E`: `a γ` does by transitivity, the rest is integral.
    have hξ : (a * γ + ↑(s * (z - star z)) : E) ∈ codiffE := by
      apply_rules [Submodule.add_mem, coe_mem_one, smul_mem_dual_one ℤ ℚ F _ _ E ha,
        one_le_dual_one]
    -- `ψf` is trivial on `x Ô` exactly when `x` times the different is integral.
    refine forall_ψf_mul_eq_one_iff.mpr fun e he ↦ ?_
    have he_inv : (e : E) ∈ codiffE⁻¹ := (coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)).le ⟨e, he, rfl⟩
    obtain ⟨w, -, hw⟩ : (e : E) * (a * γ + (↑(s * (z - star z)) : E)) ∈ (1 : FractionalIdeal
      (nonZeroDivisors (𝓞 E)) E) := (mem_inv_iff (by simp [codiffE])).mp he_inv _ hξ
    have h_int : IsIntegral ℤ (e * (a * γ + ↑(s * (z - star z))) : E) := by
      rw [← hw]
      exact w.prop
    rwa [← algebraMap_mem_Ô, map_mul] at h_int
  · -- Transitivity of the different; the relative different of `E / F` is trivial.
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]
    exact mul_mem_mul (by simp [F]) (mem_map_of_mem _ hμ)
  · -- The terms in `z - star z` agree; what is left follows from `c s + μ a = 1` and `γ ^ 2 = -1`.
    have h_one_E : ((c • (s : F) + algebraMap (𝓞 F) F μ * a : F) : E) = 1 := by
      rw [h_one, OneMemClass.coe_one]
    have hγ_sq_E : (γ : E) * γ = -1 := by simpa using congrArg (algebraMap (𝓞 E) E) hγ_sq
    linear_combination (norm := skip) h_one_E - ((μ • a : F) : E) * hγ_sq_E
    simp [smul_def, mul_sub, sub_eq_zero]
    ring!

/-- For an embedding `σ` of `E ⊇ QuadField d`, some CM type picks `σ` at its base place and, at
every other place, an embedding whose restriction to `QuadField d` differs from that of `σ`. -/
lemma exists_cmBase_restrict_ne {d : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E]
    [HasQuadSubfield d E] [HasPrimitiveRoot5040 E] (σ : E →+* ℂ) :
    ∃ Ψ : CMBase E,
      Ψ.Φ Ψ.v₀ = σ ∧
      ∀ v : InfinitePlace E, v ≠ Ψ.v₀ →
        (Ψ.Φ v).comp (algebraMap (QuadField d) E) ≠
          (Ψ.Φ Ψ.v₀).comp (algebraMap (QuadField d) E) := by
  classical
  let i : QuadField d →+* E := algebraMap (QuadField d) E
  -- Conjugate `v.embedding` exactly when its restriction to `QuadField d` is on the wrong side.
  use { v₀ := mk σ, mk_Φ := ?_
        Φ v := if (v.embedding.comp i = σ.comp i ↔ v ≠ mk σ) then star v.embedding
          else v.embedding }
  · -- `Φ v₀ = σ`, and at `v ≠ v₀` the chosen embedding restricts differently from `σ`;
    -- `dsimp +instances` unfolds `Φ` and `v₀` of the CM type just built, which is an instance
    dsimp +instances
    grind [mk_embedding, mk_eq_iff, ComplexEmbedding.conjugate_comp]
  · -- Conjugating an embedding does not change its place (`dsimp +instances` as above).
    dsimp +instances
    grind [mk_embedding, mk_eq_iff]

/-- On integers, the map `𝓞 (QuadField d) → 𝓞 E` induced by the inclusion is the algebra map. -/
private lemma mapRingHom_algebraMap_eq {d : ℕ} {E : Type} [Field E] [NumberField E]
    [HasQuadSubfield d E] :
    RingOfIntegers.mapRingHom (algebraMap (QuadField d) E) = algebraMap (𝓞 (QuadField d)) (𝓞 E) :=
  rfl

/-- PEL data with `β = (1 + √-d) / 2` are good at a place `w` that is safe for their level
(`New.Variety.IsSafe`) and contains neither `D.paddedNorm` nor the order of `D.dualTorsion`. -/
lemma pel_good_of_safe {d : ℕ} {E : Type} [Field E] [CMBase E]
    [HasQuadSubfield d E] [HasPrimitiveRoot5040 E] (D : PEL E)
    (hβ : D.β = algebraMap (𝓞 (QuadField d)) (𝓞 E) (betaK d)) {w : FinPlace E}
      (hw : IsSafe D.level w)
    (hr_notMem : ↑D.paddedNorm ∉ w.asIdeal) (hT_notMem : ↑(Nat.card D.dualTorsion) ∉ w.asIdeal) :
    D.IsGoodAt w.asIdeal := by
  -- Let `u` be the split place of `QuadField d` below `w`, of prime norm `p = u.q`, containing
  -- `betaK d - b`; a second place `v` of `E` lies over `u`.
  obtain ⟨h_split, hw𝔑, h_conj𝔑⟩ := hw
  let u : FinPlace (QuadField d) := w.below (QuadField d)
  obtain ⟨v, hv_below, hv_ne, -⟩ := h_split.exists_place_above_ne w w
  obtain ⟨hp, h_over⟩ :
      u.q.Prime ∧ ∀ u' : FinPlace (QuadField d), u' = u ∨ u' = star u ↔ ↑u.q ∈ u'.asIdeal :=
    h_split.isSplit_and_prime_q.2
  obtain ⟨b, hb, h_coprime⟩ :
      ∃ b : ℤ, betaK d - b ∈ u.asIdeal ∧ IsCoprime (betaK d - b) (star (betaK d - b)) := h_split
  have h_star : star D.β = 1 - algebraMap (𝓞 (QuadField d)) (𝓞 E) (betaK d) := by
    simpa [hβ] using D.star_beta
  have hp_mem : ↑u.q ∈ u.asIdeal := (h_over u).mp (.inl rfl)
  have hp_mem_w : (u.q : 𝓞 E) ∈ w.asIdeal := by simpa [u] using hp_mem
  refine ⟨⟨hr_notMem, hT_notMem⟩, u.q, b, hp, hp_mem_w, ?hβ_sub_mem, ?h_coprime_star, ?_, v,
    mt v.ext hv_ne, ?h_mem_v⟩
  case hβ_sub_mem => simpa [hβ, u, mapRingHom_algebraMap_eq] using hb
  case h_coprime_star => simpa [h_star, ← hβ] using h_coprime.map (algebraMap _ (𝓞 E))
  case h_mem_v => simpa [u, ← hv_below, hβ, mapRingHom_algebraMap_eq] using And.intro hp_mem hb
  -- No prime `P` contains both the level and `w * (p, star β - b)`.
  refine (coprime_of_no_prime_ge fun P h𝔑P h_prod hP ↦ ?_).sup_eq
  simp only [Submodule.span_singleton_le_iff_mem, span_insert, hP.mul_le, sup_le_iff] at h𝔑P h_prod
  obtain h_le | ⟨hpP, hbP⟩ := h_prod
  · exact hw𝔑 (by rwa [← w.isMaximal.eq_of_le hP.ne_top' h_le] at h𝔑P)
  -- `P` lies over `u` or `star u`, and not over `u`: `betaK d - b` is prime to its conjugate.
  let P' : FinPlace E := ⟨P, hP, fun h_bot ↦ D.level_ne_zero (h_bot.le h𝔑P)⟩
  obtain h_eq | h_eq : P'.below (QuadField d) = u ∨ P'.below (QuadField d) = star u :=
    (h_over _).mpr (by simpa)
  · have h_star_mem : star (betaK d - b) ∈ u.asIdeal := by
      simpa [u, ← h_eq, h_star, mapRingHom_algebraMap_eq] using hbP
    exact IsPrime.notMem_of_isCoprime_of_mem h_coprime hb h_star_mem
  · exact h_conj𝔑 P' h_eq h𝔑P

/-- If `ξ` lies in the inverse different, the `r`-torsion vectors are isotropic for the pairing
`ψf (r ^ 2 ξ yᴴ x)`. -/
lemma ψf_xiForm_eq_one_of_torsionClass_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {m : Type} [Fintype m] {ξ : E} (hξ : ∀ u ∈ Ô E, ψf E (u * algebraMap E (𝔸f E) ξ) = 1) {r : ℕ}
    {x y : m → 𝔸f E} (hx : torsionClass (r • x) = 0) (hy : torsionClass (r • y) = 0) :
    ψf E (xiForm (r ^ 2 * ξ) x y) = 1 := by
  have h_int : star (r • y) ⬝ᵥ r • x ∈ Ô E := sum_mem fun i _ ↦ by
    apply_rules [mul_mem, star_mem_Ô, torsionClass_eq_zero.mp]
  simpa [star_trivial, -nsmul_eq_mul, ← nsmul_eq_mul, sq, mul_assoc, mul_comm, xiForm] using
    hξ _ h_int

/-- A group of torsion vectors killed by `(s c - 1) (s + 1) ^ 2` has order prime to `s`. -/
lemma coprime_card_of_le_torsionBySet {E : Type} [Field E] [NumberField E] {m : Type} [Fintype m]
    {s : ℕ} {c : 𝓞 E} {T : AddSubgroup (AdelicTorsion E m)}
    (hT :
      T ≤ (Submodule.torsionBySet (𝓞 E) (AdelicTorsion E m)
          (span {(s * c - 1) * (s.succ : 𝓞 E) ^ 2})).toAddSubgroup) :
    s.Coprime (Nat.card T) := by
  -- The order of `T` divides a power of the norm of `κ`, and that norm is prime to `s`.
  set κ : 𝓞 E := (s * c - 1) * (s.succ : 𝓞 E) ^ 2 with hκ
  refine coprime_of_dvd fun p hp hps hpT ↦ ?_
  have h_norm : p ∣ Ideal.absNorm (span {κ}) := by
    by_cases h_bot : span {κ} = ⊥
    · simp [h_bot]
    · have h_dvd : Nat.card T ∣ Ideal.absNorm (span {κ}) ^ Fintype.card m :=
        (card_torsionBySet_adelicTorsion h_bot).subst (T.card_dvd_of_le hT)
      exact hp.dvd_of_dvd_pow (hpT.trans h_dvd)
  -- Take a prime `P ∣ κ` over `p`. As `p ∣ s`, `s ∈ P`, so `κ ≡ -1` modulo `P`; yet `κ ∈ P`.
  obtain ⟨P, hP_max, hP_under, hPκ⟩ : ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ under ℤ P = span {(p : ℤ)} ∧
    P ∣ span {κ} := exists_isMaximal_dvd_of_dvd_absNorm' hp _ h_norm
  have hs_zero : (s : 𝓞 E ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa [← Int.ofNat_dvd, ← mem_span_singleton (α := ℤ), ← hP_under] using hps
  have hκ_neg_one : Ideal.Quotient.mk P κ = -1 := by simp [hκ, hs_zero]
  have hκ_zero : Ideal.Quotient.mk P κ = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.dvd_span_singleton.mp hPκ)
  exact neg_ne_zero.mpr one_ne_zero (hκ_neg_one.symm.trans hκ_zero)

/-- Let `ξ` be purely imaginary (`star ξ = -ξ`) and lie in the inverse different, and let `r : ℕ`.
The pairing `ψf (r ^ 2 ξ yᴴ x)` on `Fin n → 𝔸f E` is alternating and the `r`-torsion vectors are
isotropic for it, so they lie in a subgroup `Λ` that is its own annihilator. -/
private lemma exists_lagrangian_xiForm {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n r : ℕ} {ξ : E} (hξ_star : star ξ = -ξ)
    (hξ_int : ∀ u ∈ Ô E, ψf E (u * algebraMap E (𝔸f E) ξ) = 1) :
    ∃ Λ : AddSubgroup (Fin n → 𝔸f E),
      {x : Fin n → 𝔸f E | torsionClass (r • x) = 0} ⊆ (Λ : Set (Fin n → 𝔸f E)) ∧
      ∀ x : Fin n → 𝔸f E, x ∈ Λ ↔ ∀ y ∈ Λ, ψf E (xiForm (r ^ 2 * ξ) x y) = 1 := by
  have h_alt (x : Fin n → 𝔸f E) : ψf E (xiForm (r ^ 2 * ξ) x x) = 1 := by
    -- `star` changes the sign of the value on `(x, x)`, and `ψf_inv_two_mul_add_star` averages over
    -- `star`.
    simp [← ψf_inv_two_mul_add_star, hξ_star, ← Matrix.star_dotProduct, xiForm]
  refine exists_lagrangian (fun x y : Fin n → 𝔸f E ↦ ψf E (xiForm (r ^ 2 * ξ) x y)) ?_ h_alt
    {x | torsionClass (r • x) = 0} ?_
  · -- the pairing is bimultiplicative
    simp [xiForm, mul_sub, AddChar.map_sub_eq_div]
  · intro x hx y hy _
    exact .inl (ψf_xiForm_eq_one_of_torsionClass_eq_zero hξ_int hx hy)

/-- The vectors `x` that pair trivially with every integral vector under `ψf (ξ zᴴ x)`: the dual of
the integral vectors for this pairing. -/
private noncomputable def dualOfIntegral {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (ξ : E) : AddSubgroup (Fin n → 𝔸f E) :=
  ofSub {x : Fin n → 𝔸f E | ∀ z : Fin n → 𝔸f E, torsionClass z = 0 → ψf E (xiForm ξ x z) = 1}
    ⟨0, by simp [xiForm]⟩
    (by simp +contextual [← sub_eq_add_neg, xiForm, mul_sub, AddChar.map_sub_eq_div])

/-- Let `m` lie in the different of `E` with `m ξ = s c - 1`. Then `(s c - 1) r ^ 2` kills the image
in `AdelicTorsion E (Fin n)` of the dual of the integral vectors for `ψf (r ^ 2 ξ zᴴ x)`. -/
private lemma map_dualOfIntegral_le_torsionBySet {E : Type} [Field E] [NumberField E] [IsCMField E]
    {n s r : ℕ} {ξ : E} {c m : 𝓞 E} (hm : m ∈ differentIdeal ℤ (𝓞 E))
    (hmξ : algebraMap (𝓞 E) E (s * c - 1) = m • ξ) :
    (dualOfIntegral n ((r : E) ^ 2 * ξ)).map torsionClass.toAddMonoidHom ≤
      (Submodule.torsionBySet (𝓞 E) (AdelicTorsion E (Fin n))
        (span {(s * c - 1) * (r : 𝓞 E) ^ 2})).toAddSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  refine (Submodule.torsionBySet_span_singleton_eq _).ge (torsionClass_eq_zero.mpr fun l ↦ ?_)
  simp_rw [mul_smul, ← algebraMap_smul E (_ - _), hmξ, smul_assoc]
  refine forall_ψf_mul_eq_one_iff.mp (fun u hu ↦ ?_) m hm
  -- Pair `x` with the integral vector that has `star u` at the index `l`.
  have h_int : torsionClass (Pi.single l (star u)) = 0 := by
    grind [star_mem_Ô, Subring.zero_mem, torsionClass_eq_zero]
  simpa [smul_def, mul_left_comm, mul_assoc, xiForm] using hx _ h_int

/-- A purely imaginary `ξ` (`star ξ = -ξ`) has real part `0` under every embedding `Φ v` of the
CM type. -/
private lemma re_Φ_eq_zero_of_star_eq_neg {E : Type} [Field E] [CMBase E] {ξ : E}
    (hξ_star : star ξ = -ξ) (v : InfinitePlace E) : (Φ v ξ).re = 0 := by
  have h_conj : (Φ v (star ξ)).re = (Φ v (-ξ)).re := by rw [hξ_star]
  exact self_eq_neg.mp (by simpa using h_conj)

/-- If `Φ v` and `Φ v₀` restrict to different embeddings of `QuadField d`, the two restrictions
are complex conjugate. -/
private lemma conjugate_comp_eq_of_comp_ne {d : ℕ} {E : Type} [Field E] [CMBase E]
    [HasQuadSubfield d E] {v : InfinitePlace E}
    (h_ne : (Φ v).comp (algebraMap (QuadField d) E) ≠ (Φ v₀).comp (algebraMap (QuadField d) E)) :
    ComplexEmbedding.conjugate ((Φ v).comp (algebraMap (QuadField d) E)) =
      (Φ v₀).comp (algebraMap (QuadField d) E) := by
  -- both restrictions give the one infinite place of `QuadField d`
  have h_mk : InfinitePlace.mk ((Φ v).comp (algebraMap (QuadField d) E)) =
      InfinitePlace.mk ((Φ v₀).comp (algebraMap (QuadField d) E)) := by
    subsingleton
  exact (mk_eq_iff.mp h_mk).resolve_left h_ne

/-- A finite place `w` whose norm divides `s` does not contain a natural number `N` prime to `s`:
otherwise `N` and the norm of `w`, which lies in `w`, would be coprime elements of `w`. -/
private lemma natCast_notMem_of_coprime {E : Type} [Field E] [NumberField E] {s N : ℕ}
    (w : FinPlace E) (h_dvd : w.q ∣ s) (h_coprime : s.Coprime N) :
    (N : 𝓞 E) ∉ w.asIdeal :=
  w.isPrime.notMem_of_isCoprime_of_mem (h_coprime.of_dvd_left h_dvd).cast w.asIdeal.absNorm_mem
/-- PEL data `D` as `exists_pel` supplies them at the level `𝔑`: rank `n`, level `𝔑`,
`β = (1 + √-d) / 2`, and good reduction (`New.PEL.IsGoodAt`) at every place `w` that is safe for
`𝔑` (`New.Variety.IsSafe 𝔑 w`). -/
structure IsSafeGoodPEL (d n : ℕ) {E : Type} [Field E] [CMBase E]
    [HasQuadSubfield d E] (𝔑 : 𝓞 E) (D : PEL E) : Prop where
  /-- The data have rank `n`. -/
  rank_eq : D.rank = n
  /-- The data have level `𝔑`. -/
  level_eq : D.level = 𝔑
  /-- The element `β` of the data is the image of `(1 + √-d) / 2`. -/
  beta_eq : D.β = algebraMap (𝓞 (QuadField d)) (𝓞 E) (betaK d)
  /-- The data are good at every place that is safe for the level. -/
  isGoodAt_of_isSafe : ∀ w : FinPlace E, IsSafe 𝔑 w → D.IsGoodAt w.asIdeal

/-- Let the CM type of `E` pick, at every infinite place `v ≠ v₀`, an embedding whose restriction to
`QuadField d` differs from that of `Φ v₀`. Then for a finite set `B` of places some `N ≠ 0` lies in
no place of `B`, and every nonzero level `𝔑` divisible by `N` carries PEL data of rank `n` that are
good at every place safe for `𝔑` (`IsSafeGoodPEL`). -/
private lemma exists_forall_dvd_exists_isSafeGoodPEL (n : ℕ) {d : ℕ} {E : Type} [Field E] [CMBase E]
    [HasQuadSubfield d E] [NeZero n] [HasPrimitiveRoot5040 E]
    (h_restrict : ∀ v : InfinitePlace E, v ≠ v₀ →
      (Φ v).comp (algebraMap (QuadField d) E) ≠ (Φ v₀).comp (algebraMap (QuadField d) E))
    (B : Finset (FinPlace E)) :
    ∃ N : ℕ+, (∀ w ∈ B, ↑N ∉ w.asIdeal) ∧
      ∀ 𝔑 : 𝓞 E, 𝔑 ≠ 0 → ↑N ∣ 𝔑 → ∃ D : PEL E, IsSafeGoodPEL d n 𝔑 D := by
  -- Take `s` a large factorial, `r = s + 1`, the form `r ^ 2 ξ` with `ξ` from
  -- `exists_star_eq_neg_and_im_pos`, its dual group `T`, a Lagrangian through the `r`-torsion, and
  -- `N = r ^ (j + 1) * #T`. The point is that `#T`, like `r`, is prime to `s`, hence odd and prime
  -- to the norms of the places in `B`.
  let incl : QuadField d →+* E := algebraMap (QuadField d) E
  let β : 𝓞 E := algebraMap (𝓞 (QuadField d)) (𝓞 E) (betaK d)
  have hβ : (β : E) = incl ((1 + sqrtNegD d) / 2) := rfl
  have h_star : star β = 1 - β := by
    simp [hβ, ← map_star_CM, RingOfIntegers.ext_iff, map_ofNat]
    ring
  obtain ⟨r₀, h_pad⟩ : ∃ r₀ : ℕ, ∀ r ≥ r₀, HasPadding E r 1 ∧ HasPadding E r β :=
    ((eventually_hasPadding 1).and (eventually_hasPadding β)).exists_forall_of_atTop
  let s : ℕ := (r₀ + B.sup FinPlace.q + 2)!
  have hs_large : r₀ + B.sup FinPlace.q + 2 ≤ s := self_le_factorial _
  let r : ℕ := s.succ
  obtain ⟨ξ, c, hξ_star, hξ_im, hξ_int, m, hm, hmξ⟩ :=
    exists_star_eq_neg_and_im_pos (E := E) (s := s) (by omega)
  -- The `r`-torsion is isotropic for the pairing `ψf (r ^ 2 ξ yᴴ x)`, and lies in a Lagrangian `Λ`.
  obtain ⟨Λ, hΛ_tors, hΛ⟩ := exists_lagrangian_xiForm (n := n) (r := r) hξ_star hξ_int
  have h_tors {x : Fin n → 𝔸f E} (hx : torsionClass x = 0) : torsionClass (r • x) = 0 := by
    rw [map_nsmul, hx, smul_zero]
  -- A subgroup that contains the integral vectors is the preimage of its image.
  have mem_map (A : AddSubgroup (Fin n → 𝔸f E)) (hA : ∀ x, torsionClass x = 0 → x ∈ A)
      (x : Fin n → 𝔸f E) :
      torsionClass x ∈ A.map torsionClass.toAddMonoidHom ↔ x ∈ A :=
    SetLike.ext_iff.1 (A.comap_map_eq_self (f := torsionClass.toAddMonoidHom) hA) x
  -- `T` is the image of the dual `T₀` of the integral vectors.
  let T₀ : AddSubgroup (Fin n → 𝔸f E) := dualOfIntegral n (r ^ 2 * ξ)
  let T : AddSubgroup (AdelicTorsion E (Fin n)) := T₀.map torsionClass.toAddMonoidHom
  -- The integer `(s c - 1) r ^ 2` kills `T`, as `m ξ = s c - 1` with `m` in the different.
  have hT_le : T ≤ (Submodule.torsionBySet (𝓞 E) (AdelicTorsion E (Fin n))
      (span {(s * c - 1) * (r : 𝓞 E) ^ 2})).toAddSubgroup :=
    map_dualOfIntegral_le_torsionBySet hm hmξ
  have h_card : s.Coprime (Nat.card T) := coprime_card_of_le_torsionBySet hT_le
  have h_odd : Odd (Nat.card T) :=
    (h_card.of_dvd_left (dvd_factorial two_pos le_add_self)).odd_of_left
  have h_finite : Finite T := (card_pos_iff.mp h_odd.pos).right
  -- `j` is the degree bound that the field `isCutDegree` of `PEL` asks for.
  obtain ⟨j, hj⟩ : ∃ j, IsCutDegree T j r (thetaRanks T r) := (eventually_isCutDegree ..).exists
  refine ⟨⟨r ^ j.succ * Nat.card T, by bound [h_odd.pos]⟩, fun w hw ↦ ?_, fun 𝔑 h𝔑 hN ↦ ?_⟩
  · -- The norm of `w` lies in `w` and divides `s`, which is prime to `N`.
    have h_dvd : w.q ∣ s := dvd_factorial w.one_lt_q.le (by grind [Finset.le_sup])
    exact natCast_notMem_of_coprime w h_dvd (.mul_right (by simp [r]) h_card)
  -- If `r ^ l • t ∈ T` with `l ≤ j`, then `r ^ l * #T` kills `t`, and it divides the level.
  have h_level (l : ℕ) (hl : l ≤ j) (t : AdelicTorsion E (Fin n)) (ht : r ^ l • t ∈ T) :
      t ∈ Submodule.torsionBy (𝓞 E) _ 𝔑 := by
    apply Submodule.torsionBy_le_torsionBy_of_dvd _ _
      ((mul_dvd_mul_right (pow_dvd_pow r hl.step) (Nat.card T)).natCast.trans hN)
    simpa [-cast_mul, cast_smul_eq_nsmul, mul_nsmul] using nsmul_relIndex_mem ⊥ ht
  -- Two distinct embeddings of the quadratic field `QuadField d` are conjugate.
  have h_conj (v : InfinitePlace E) (hv : v ≠ v₀) :
      ComplexEmbedding.conjugate ((Φ v).comp incl) = (Φ v₀).comp incl :=
    conjugate_comp_eq_of_comp_ne (h_restrict v hv)
  obtain ⟨h_pad_one, h_pad_beta⟩ := h_pad r (by omega)
  let D : PEL E :=
    { β, level := 𝔑, paddedNorm := r, dualTorsion := T, ξ := r ^ 2 * ξ, rank := n
      exponentBound := j
      lagrangian := Λ.map torsionClass.toAddMonoidHom
      star_beta := h_star, level_ne_zero := h𝔑, odd_card := h_odd, nonempty := ⟨0⟩
      three_le_paddedNorm := by omega
      isCutDegree := hj
      mem_torsionBy_level := h_level
      mem_dualTorsion := mem_map T₀ fun x hx z hz ↦
                  ψf_xiForm_eq_one_of_torsionClass_eq_zero hξ_int (h_tors hx) (h_tors hz)
      mem_lagrangian := by simpa only [mem_map Λ fun x hx ↦ hΛ_tors (h_tors hx)] using hΛ
      torsion_mem_lagrangian := Quot.ind fun x hx ↦ ⟨x, hΛ_tors hx, rfl⟩
      hasPadding_one := h_pad_one
      hasPadding_beta := h_pad_beta
      xi_im_pos v := by simpa [sq, re_Φ_eq_zero_of_star_eq_neg hξ_star] using hξ_im v
      xi_re_eq_zero v := by simp [sq, re_Φ_eq_zero_of_star_eq_neg hξ_star]
      emb_beta_eq_of_ne v hv := by
        simpa [hβ, h_star, map_ofNat] using
          congrArg star (DFunLike.congr_fun (h_conj v hv) (sqrtNegD d))
      emb_star_beta_ne := by simp [hβ, ← map_star_CM, neg_eq_self, Subtype.ext_iff, NeZero.ne] }
  refine ⟨D, rfl, rfl, rfl, fun w hw ↦ ?_⟩
  -- `r` and `#T` divide `N`, which divides the level, and the level is not in `w`.
  obtain ⟨-, h𝔑_notMem, -⟩ := id hw
  have h_units : ↑D.paddedNorm ∉ w.asIdeal ∧ ↑(Nat.card D.dualTorsion) ∉ w.asIdeal := by
    simpa [D, ← eq_zero_iff_mem] using h𝔑_notMem ∘ w.asIdeal.mem_of_dvd hN
  exact pel_good_of_safe D rfl hw h_units.left h_units.right

/-- Existence of PEL data. Let `d % 4 = 3`, let the CM field `E ⊇ QuadField d = ℚ(√-d)` satisfy
`HasPrimitiveRoot5040 E`, let `n ≠ 0`, `σ` an embedding `E →+* ℂ`, `B` a finite set of places. Some
CM type `Ψ` has `Ψ.Φ Ψ.v₀ = σ` and `Ψ.Φ v ≠ Ψ.Φ Ψ.v₀` on `QuadField d` for `v ≠ Ψ.v₀`, and some
`N ≠ 0` in no place of `B` is such that every nonzero level `𝔑` divisible by `N` carries PEL data as
in `IsSafeGoodPEL`: rank `n`, `β = (1 + √-d) / 2`, good at every place safe for `𝔑`. -/
lemma exists_pel (n : ℕ) {d : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E]
    [HasQuadSubfield d E] [NeZero n] [HasPrimitiveRoot5040 E] (σ : E →+* ℂ)
    (B : Finset (FinPlace E)) :
    ∃ Ψ : CMBase E,
      (Ψ.Φ Ψ.v₀ = σ ∧
       ∀ v : InfinitePlace E, v ≠ Ψ.v₀ →
         (Ψ.Φ v).comp (algebraMap (QuadField d) E) ≠
           (Ψ.Φ Ψ.v₀).comp (algebraMap (QuadField d) E)) ∧
      ∃ N : ℕ+, (∀ w ∈ B, ↑N ∉ w.asIdeal) ∧
        ∀ 𝔑 : 𝓞 E, 𝔑 ≠ 0 → ↑N ∣ 𝔑 → ∃ D : PEL E, IsSafeGoodPEL d n 𝔑 D := by
  obtain ⟨Ψ, hΨ_base, hΨ_restrict⟩ := exists_cmBase_restrict_ne (d := d) σ
  exact ⟨Ψ, ⟨hΨ_base, hΨ_restrict⟩, exists_forall_dvd_exists_isSafeGoodPEL n hΨ_restrict B⟩

end New.Variety

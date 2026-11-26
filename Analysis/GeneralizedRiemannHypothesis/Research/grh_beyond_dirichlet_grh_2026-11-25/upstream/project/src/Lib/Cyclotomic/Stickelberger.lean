import Lib.GaloisRep.Main.SelmerModules
import Lib.General.NumberTheory.FrobeniusOrbits

/-!
# A weak form of Stickelberger's theorem for Gauss sums, and a family of Jacobi-type quotients

Gauss sums over `𝔽_p` give a family of elements `J x` of `Ωˣ`, `Ω = ℚ̄`, indexed by torsion points
`x` of `ℚ/ℤ`, with a known Galois action and a distribution relation up to elements of finite order.

* `New.OddPart.floorDiff`, `New.OddPart.sum_floorDiff`: the integer `⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋` and its
  distribution relation (Hermite's identity).
* `New.OddPart.exists_galUnitsRep_gaussSum_eq`, `New.OddPart.stickelberger`: Galois action on Gauss
  sums, and their orders at a place `B` above `p`.
* `New.OddPart.exists_isJacobiFamily`: the family `J`, built from the quotients
  `j t = g(χ) ^ c / g(χ ^ c)` as `j t / j (-t)`.

Notions from other files:
* `Ω` is `ℚ̄`, and `DiscreteUnits Ω` is `Ωˣ` written additively: a sum is a product, `c • u` is
  `u ^ c`. `galUnitsRep σ` is the action of `σ ∈ Gal(Ω/ℚ)` on it.
* `ClosurePlace`: a valuation subring `B` of `Ω`; it lies above `p` when `B.valuation p < 1`, and
  `centrePrime Ω B` is the prime ideal of `𝓞 Ω` that it defines; `principalUnits B` is the subgroup
  of `DiscreteUnits Ω` of the `u` with `B.valuation (u - 1) < 1`, that is `u ≡ 1` at `B`.
* `ordRat ℚ B u`: the order of `u` at `B`, normalised so that a prime `p` below `B` has order one.
* `cyclotomicCharMod Ω N σ`: the cyclotomic character of `σ` modulo `N`, the unit `a` with
  `σ ζ = ζ ^ a` for every `N`-th root of unity `ζ`.
* `New.QZ`: the group `ℚ/ℤ`; `New.QZ.fracRep x = ⟨x⟩` is the representative in `[0, 1)`, and
  `New.QZ.ofZMod r b = b / r`.

## Relation to the literature

Known result: Stickelberger's factorisation of Gauss sums and the Davenport–Hasse product relation.
Here only prime fields are treated, and characters are named by the valuation of their Gauss sum.
The product relation is proved for Jacobi-type quotients of Gauss sums and only up to a root of
unity. Source: L. Washington, Introduction to Cyclotomic Fields, 2nd ed. 1997, 6.2 and Thm 15.1; for
the product relation, H. Davenport, H. Hasse, J. reine angew. Math. 172 (1935).
-/

namespace New.OddPart

open Int Finset NumberField IntermediateField AddChar MulChar AddMonoidHom QZ ZMod QuotientAddGroup
  HasEnoughRootsOfUnity Embeddings ComplexEmbedding ValuationSubring Cohomology NeZero Fact Ideal

variable {r m p : ℕ} [NeZero r] [hp : Fact p.Prime] {B : ClosurePlace}

/-- For `c : ℕ`, the integer `⌊c ⟨x⟩⌋ - ⌊c ⟨-x⟩⌋`, where `⟨x⟩` is the representative of `x ∈ ℚ/ℤ`
in `[0, 1)`. -/
noncomputable def floorDiff (c : ℕ) (x : QZ) : ℤ := ⌊c * x.fracRep⌋ - ⌊c * (-x).fracRep⌋

/-- The distribution relation for `floorDiff m`, with `m` prime to `r`: its sum over the translates
of `x` by the points `v b / r`, for a unit `v` mod `r`, is its value at `r • x`. -/
lemma sum_floorDiff (h_cop : m.Coprime r) (x : QZ) {v : ZMod r} (hv : IsUnit v) :
    ∑ b : ZMod r, floorDiff m (x + ofZMod r (v * b)) = floorDiff m (r • x) := by
  -- Hermite's identity: the representatives of `x + v b / r` in `[0, 1)` are, after the
  -- permutation `b ↦ ⌊r x⌋ + v b` of `ZMod r`, the numbers `(b + fract (r x)) / r`.
  have sum_lift (x : QZ) (v : ZMod r) (hv : IsUnit v) :
      ∑ b : ZMod r, QZ.fracRep (x + ofZMod r (v * b)) =
        ∑ b : ZMod r, (b.val + fract (r * x.fracRep)) / r := by
    refine Fintype.sum_equiv (hv.unit.mulLeft.trans (.addLeft ⌊r * x.fracRep⌋)) _ _ fun b ↦
      .trans ?_ (floor_add_fract _)
    -- Without the `↓` flags, or without `-natCast_val`, `simp` stops with `ZMod.lift` unevaluated.
    simp [← ofZMod_apply, -natCast_val, ofZMod, ← map_zsmul, add_assoc, ← div_eq_mul_inv, sub_div,
      ↓floor_div_natCast, ↓floor_natCast_add, ↓floor_fract, ediv_eq_zero_of_lt, val_lt,
      ← fracRep_mk, add_div, ← self_sub_fract, NeZero.ne]
  -- In `ℚ`, `⌊m ⟨y⟩⌋ = m ⟨y⟩ - ⟨m y⟩`, so `floorDiff m y = m ⟨y⟩ - ⟨m y⟩ - m ⟨-y⟩ + ⟨-(m y)⟩`.
  have hm : IsUnit (m : ZMod r) := (isUnit_iff_coprime m r).mpr h_cop
  qify
  simp [floorDiff, map_nsmul, ← nsmul_eq_mul, ← fracRep_mk, add_div, sum_add_distrib,
    ← self_sub_fract] at sum_lift ⊢
  -- Apply `sum_lift` to the four sums, with the units `v`, `m * v`, `-v`, `-(m * v)`; the constant
  -- `∑ b, b / r` occurs with the coefficients `m - 1 - m + 1 = 0`.
  simp [sum_lift, hm, hv, smul_comm r, ← map_neg, ← neg_mul, add_comm, mul_div_cancel₀, ← mul_sum,
    NeZero.ne, ← map_nsmul, ← mul_assoc]
  ring

/-- Kronecker's theorem in `Ω = ℚ̄`: an element of `Ω` that lies in every valuation ring of `Ω` and
has absolute value one in every complex embedding is a root of unity. -/
lemma isOfFinOrder_of_norm_eq_one {x : Ω} (h_mem : ∀ A : ClosurePlace, x ∈ A)
    (h_norm : ∀ τ : Ω →+* ℂ, ‖τ x‖ = 1) : IsOfFinOrder x := by
  -- Apply Mathlib's Kronecker theorem to the generator of the number field `ℚ⟮x⟯`.
  -- The integral closure of `ℤ` is the intersection of the valuation subrings.
  have h_int : IsIntegral ℤ x :=
    (integralClosure ℤ Ω).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge (by simp [h_mem])
  have : NumberField ℚ⟮x⟯ := { to_finiteDimensional := adjoin.finiteDimensional h_int.tower_top }
  -- Every embedding of `ℚ⟮x⟯` into `ℂ` extends to `Ω`.
  have h_gen (φ : ℚ⟮x⟯ →+* ℂ) : ‖φ (AdjoinSimple.gen ℚ x)‖ = 1 := by
    rw [← lift_algebraMap_apply Ω φ]
    exact h_norm _
  obtain ⟨n, hn_pos, h_pow⟩ := pow_eq_one_of_norm_eq_one ℚ⟮x⟯ ℂ (coe_isIntegral_iff.mp h_int) h_gen
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn_pos, by simpa [Subtype.ext_iff] using h_pow⟩

/-! ### Gauss sums -/

/-- Galois action on Gauss sums. Let `ψ` be an additive character of `𝔽_p`, let `t ↦ χ t` be a
homomorphism from `ZMod r` to the multiplicative characters of `𝔽_p`, and let the unit `g t` of
`Ω` be the Gauss sum of `χ t` and `ψ`. There are homomorphisms `K σ : ZMod r → Ωˣ` with
`σ (g t) = K σ (a t) * g (a t)`, where `a` is the cyclotomic character of `σ` modulo `r`; in the
additive notation of `DiscreteUnits Ω` the right side is `(K σ + g) (a * t)`. -/
lemma exists_galUnitsRep_gaussSum_eq {ψ : AddChar (ZMod p) (𝓞 Ω)}
    {χ : AddChar (ZMod r) (MulChar (ZMod p) (𝓞 Ω))}
    (g : ZMod r → DiscreteUnits Ω) (hg : ∀ t : ZMod r, (g t).toMul.val = gaussSum (χ t) ψ) :
    ∃ K : Gal(Ω/ℚ) → ZMod r →+ DiscreteUnits Ω, ∀ (σ : Gal(Ω/ℚ)) (t : ZMod r),
      galUnitsRep σ (g t) = (K σ + g) (cyclotomicCharMod Ω r σ * t) := by
  -- With `c σ` the cyclotomic character of `σ` modulo `p`, the factor is `K σ t = (χ t)⁻¹ (c σ)`.
  let c : Gal(Ω/ℚ) →* (ZMod p)ˣ := cyclotomicCharMod Ω p
  have hK_ne (σ : Gal(Ω/ℚ)) (t : ZMod r) : (((χ t)⁻¹ (c σ) : 𝓞 Ω) : Ω) ≠ 0 := by
    simp [apply_eq_zero_iff]
  let K (σ : Gal(Ω/ℚ)) (t : ZMod r) : DiscreteUnits Ω := .ofNeZero ((χ t)⁻¹ (c σ) : 𝓞 Ω) (hK_ne σ t)
  have K_add (σ : Gal(Ω/ℚ)) (a b : ZMod r) : K σ (a + b) = K σ a + K σ b := by
    simp [K, DiscreteUnits.ext_iff, field, map_add_eq_mul]
  refine ⟨fun σ ↦ mk' (K σ) (K_add σ), fun σ t ↦ ?_⟩
  -- The values of `χ t` on units are `r`-th, those of `ψ` are `p`-th roots of unity. So `σ` turns
  -- `gaussSum (χ t) ψ` into the Gauss sum of `χ (cyclotomicCharMod Ω r σ * t)` and
  -- `ψ.mulShift (c σ)`.
  have h_shift (s : ZMod r) : ((gaussSum (χ s) (ψ.mulShift (c σ)) : 𝓞 Ω) : Ω) =
      (((χ s)⁻¹ (c σ) * gaussSum (χ s) ψ : 𝓞 Ω) : Ω) := by
    rw [gaussSum_mulShift_eq]
  simpa [K, c, DiscreteUnits.ext_iff, smul_eq_pow_cyclotomicCharMod (N := p),
    smul_eq_pow_cyclotomicCharMod (N := r), hg, gaussSum, sum_eq_add_sum_units, smul_sum,
    NeZero.ne, ← RingHom.map_pow, ← pow_apply_coe, ← map_nsmul_eq_pow, natCast_self]
    using h_shift (cyclotomicCharMod Ω r σ * t)

/-- Let `B` be a place of `Ω` above the prime `p`. An algebraic integer `x` with `x ^ p = 1` is
congruent to `1` modulo the prime ideal `centrePrime Ω B` of `𝓞 Ω` that `B` defines. -/
lemma mk_centrePrime_eq_one_of_pow_eq_one (hB : B.valuation p < 1) {x : 𝓞 Ω} (hx : x ^ p = 1) :
    ↑x = (1 : 𝓞 Ω ⧸ centrePrime Ω B) := by
  -- Otherwise the residue of `x` is a primitive `p`-th root of unity in a domain where `p = 0`.
  by_contra h_ne
  have h_prim : IsPrimitiveRoot (x : 𝓞 Ω ⧸ centrePrime Ω B) p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (congrArg _ hx) h_ne)
  exact h_prim.neZero'.out (mk_ker.ge (mem_centrePrime.mpr hB))

/-- A weak form of Stickelberger's theorem for `𝔽_p`. Let `B` be a place of `Ω` above `p`, `ψ` a
primitive additive character of `ZMod p`, `r` prime to `p`, `t ↦ χ t` a primitive (so injective)
additive map from `ZMod r` to the multiplicative characters of `ZMod p`, and `g t` the Gauss sum of
`χ t` and `ψ`. Then some injective `S : ZMod r →+ ℚ/ℤ` has, for every `t`, representative
`(S t).fracRep` in `[0, 1)` equal to `ordRat ℚ B (g t)`, the order at `B` normalised so that `p` has
order `1`. Stickelberger's factorisation of Gauss sums computes these orders; here they are only
tied to `S`. -/
lemma stickelberger (hB : B.valuation p < 1) {ψ : AddChar (ZMod p) (𝓞 Ω)}
    {χ : AddChar (ZMod r) (MulChar (ZMod p) (𝓞 Ω))} (g : ZMod r → DiscreteUnits Ω)
    (hg : ∀ t : ZMod r, (g t).toMul.val = gaussSum (χ t) ψ) (hψ : ψ.IsPrimitive)
    (hχ : χ.IsPrimitive) (h_cop : p.Coprime r) :
    ∃ S : ZMod r →+ QZ, (⇑S).Injective ∧ ∀ t : ZMod r, (S t).fracRep = ordRat ℚ B (g t) := by
  -- `v` is the place of `ℚ` below `B`, and `p` has order one at `B`
  obtain ⟨v, hv, -, ord_p⟩ := exists_isPlaceOver_prime hB
  obtain ⟨K, hK⟩ := exists_galUnitsRep_gaussSum_eq g hg
  -- Inertia fixes the `r`-th roots of unity, so it multiplies `g t` by the character `K σ t` and
  -- fixes `g (a + b) / (g a * g b)`, whose order is therefore an integer.
  have ord_add (a b : ZMod r) : ∃ n : ℤ, ordRat ℚ B (g (a + b) - (g a + g b)) = n := by
    refine hv.exists_ordRat_eq_intCast (Γ := Gal(Ω/ℚ)) fun σ hσ ↦ ?_
    have hK_inert (s : ZMod r) : galUnitsRep σ (g s) = K σ s + g s := by
      simp [hK, cyclotomicCharMod_eq_one_of_mem_inertiaGroup hσ, h_cop.valuation_eq_one hB]
    simp only [map_sub, map_add, hK_inert]
    abel
  -- So the class of `ord (g t)` in `ℚ/ℤ` is additive in `t`.
  have S_add (a b : ZMod r) :
      QZ.mk (ordRat ℚ B (g (a + b))) = QZ.mk (ordRat ℚ B (g a)) + QZ.mk (ordRat ℚ B (g b)) := by
    obtain ⟨n, hn⟩ := ord_add a b
    rw [← map_add, ← map_add]
    exact eq_iff_sub_mem.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp [← hn]⟩)
  let S : ZMod r →+ QZ := mk' (fun t ↦ QZ.mk (ordRat ℚ B (g t))) S_add
  -- The Gauss sum of `χ' ≠ 1` has positive order: `ψ' ≡ 1` at `B`, so it is `≡ ∑ x, χ' x = 0`.
  have ord_pos (u : DiscreteUnits Ω) {χ' : MulChar (ZMod p) (𝓞 Ω)} {ψ' : AddChar (ZMod p) (𝓞 Ω)}
      (hu : u.toMul.val = gaussSum χ' ψ') (hχ' : χ' ≠ 1) : 0 < ordRat ℚ B u := by
    have h_cen : gaussSum χ' ψ' - gaussSum χ' 1 ∈ centrePrime Ω B := by
      simp [gaussSum, mk_centrePrime_eq_one_of_pow_eq_one hB, ← Submodule.Quotient.mk_eq_zero,
        ← map_nsmul_eq_pow, natCast_self]
    rw [gaussSum_one_right hχ', sub_zero, mem_centrePrime] at h_cen
    rw [lt_iff_le_and_ne, ne_comm, Ne, hv.ordRat_nonneg_iff, hv.ordRat_eq_zero_iff, hu]
    exact ⟨algebraMap_ringOfIntegers_mem B (gaussSum χ' ψ'), h_cen.ne⟩
  -- The order of `g t` lies in `[0, 1)`, so it is the representative of its class `S t`.
  have lift_S (t : ZMod r) : (S t).fracRep = ordRat ℚ B (g t) := by
    refine (toIcoMod_eq_self _).mpr ?_
    rw [zero_add]
    by_cases ht : χ t = 1
    · -- Here `g t = -1`.
      have hψ_ne : ψ ≠ 1 := by simpa using hψ one_ne_zero
      have ord_zero : ordRat ℚ B (g t) = 0 :=
        hv.ordRat_eq_zero_iff.mpr (by simp [hg, ht, gaussSum_one_left hψ_ne])
      simp [ord_zero]
    · -- `p / g t` is the Gauss sum of `(χ t)⁻¹` and `ψ⁻¹`, of positive order, and `ord p = 1`.
      have h_mul : ((gaussSum (χ t) ψ * gaussSum (χ t)⁻¹ ψ⁻¹ : 𝓞 Ω) : Ω) = p := by
        simp [gaussSum_mul_gaussSum_eq_card ht hψ]
      have h_quot : 0 < ordRat ℚ B (.ofNeZero p out - g t) :=
        ord_pos _ (ψ' := ψ⁻¹) (by simpa [field, ← hg] using h_mul.symm) (inv_ne_one.mpr ht)
      exact ⟨(ord_pos _ (hg t) ht).le, by simpa [ord_p] using h_quot⟩
  -- If `S t = 0` the order of `g t` is `0`, which forces `χ t = 1`, that is `t = 0`.
  refine ⟨S, (injective_iff_map_eq_zero S).mpr fun t ht ↦ ?_, lift_S⟩
  have ord_zero : ordRat ℚ B (g t) = 0 := by
    rw [← lift_S, ht, ← map_zero QZ.mk, fracRep_mk, fract_zero]
  by_contra ht_ne
  exact (ord_pos (g t) (hg t) (mt (hχ.zmod_char_eq_one_iff r t).mp ht_ne)).ne' ord_zero

/-- The distribution relation up to roots of unity. Let `Ω` be the algebraic closure of `ℚ`, let `B`
be a place of `Ω` above `p`, and let `J : ℚ/ℤ → Ωˣ` (written additively) satisfy the following on
the `M`-torsion: it is Galois equivariant (`σ (J x) = J (a • x)` when `σ` raises `M`-th roots of
unity to the power `a`), a unit at every place not above `p`, of order
`floorDiff c x = ⌊c⟨x⟩⌋ − ⌊c⟨−x⟩⌋` at `B` normalised on `ℚ` (where `⟨x⟩` is the representative of
`x` in `[0, 1)`), and of absolute value one in every complex embedding. Then for `M • x = 0`,
`r ∣ M` and `c` prime to `r`, the quotient `(∏ b mod r, J (x + b / r)) / J (r x)` is a root of
unity. -/
lemma isOfFinAddOrder_distribution (hB : B.valuation p < 1) {c M : ℕ} [NeZero M]
    {J : QZ → DiscreteUnits Ω}
    (h_gal : ∀ x : QZ, M • x = 0 → ∀ (σ : Gal(Ω/ℚ)) (a : ℕ),
      (cyclotomicCharMod Ω M σ).val = a → galUnitsRep σ (J x) = J (a • x))
    (h_unit : ∀ x : QZ, M • x = 0 → ∀ A : ClosurePlace, A.valuation p = 1 →
      A.valuation (J x).toMul.val = 1)
    (h_ord : ∀ x : QZ, M • x = 0 → ordRat ℚ B (J x) = floorDiff c x)
    (h_abs : ∀ x : QZ, M • x = 0 → ∀ τ : Ω →+* ℂ, ‖τ (J x).toMul.val‖ = 1) {x : QZ} (hx : M • x = 0)
    (hr : r ∣ M) (hc : c.Coprime r) :
    IsOfFinAddOrder (∑ b : ZMod r, J (x + ofZMod r b) - J (r • x)) := by
  obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = r * M' := hr
  -- `over_p`: all places of `Ω` above `p` lie over one place `v` of `ℚ`.
  obtain ⟨v, -, -, over_p⟩ := exists_rat_place_of_prime hp.out
  set Q : DiscreteUnits Ω := ∑ b : ZMod r, J (x + ofZMod r b) - J (r • x) with hQ
  -- By Kronecker's theorem it suffices to see integrality everywhere and absolute value one.
  refine Units.isOfFinOrder_val.mp (isOfFinOrder_of_norm_eq_one (fun A ↦ ?_) fun τ ↦ ?_)
  · obtain hA | hA : A.valuation p = 1 ∨ A.valuation p < 1 := (valuation_le_one A p).eq_or_lt
    · -- Off `p` every factor is a unit by `h_unit`, so the quotient has valuation one.
      have h_val_one : A.valuation (Q.toMul : Ω) = 1 := by
        simp [hQ, toMul_sub, toMul_sum, h_unit, hA, hx, smul_comm, ← map_nsmul, natCast_self]
      exact (valuation_le_one_iff A _).mp h_val_one.le
    · -- A place `A` above `p` is conjugate to `B`: `σ • A = B`. The conjugate quotient is the sum
      -- of `J (a x + a b / r)` minus `J (r a x)`; its order at `B` vanishes by `sum_floorDiff`.
      obtain ⟨σ, hσ⟩ := (over_p A hA).exists_smul Gal(Ω/ℚ) (over_p B hB)
      obtain ⟨a, ha⟩ : ∃ a : ℕ, (cyclotomicCharMod Ω (r * M') σ : ZMod (r * M')) = a :=
        ⟨_, (natCast_zmod_val _).symm⟩
      have ha_unit : IsUnit (a : ZMod r) := by
        rw [← ZMod.cast_natCast (dvd_mul_right r M'), ← ha]
        exact isUnit_cast_of_dvd (dvd_mul_right r M') _
      have h_ord_conj : ordRat ℚ B (galUnitsRep σ Q) =
          ↑(∑ b : ZMod r, floorDiff c (a • x + ofZMod r (a * b)) - floorDiff c (r • a • x)) := by
        simp [hQ, h_gal _ _ σ a ha, h_ord, hx, smul_comm (r * _), smul_comm r, ← map_nsmul,
          natCast_self, smul_add]
      refine ((over_p A hA).ordRat_nonneg_iff Q).mp (ge_of_eq ?_)
      rw [← (over_p A hA).ordRat_smul σ, hσ, h_ord_conj, sum_floorDiff hc _ ha_unit, sub_self,
        Int.cast_zero]
  · simp [hQ, toMul_sub, toMul_sum, h_abs, hx, smul_comm, ← map_nsmul, natCast_self]

/-- The properties of a family `J : ℚ/ℤ → Ωˣ` (written additively) of Jacobi-type quotients of
Gauss sums over `𝔽_p`, on the points `x` with `M • x = 0`. Here `B` is a place of `Ω` (above `p`
where the family is built), and `c` is the exponent in `g(χ) ^ c / g(χ ^ c)`. -/
structure IsJacobiFamily (p : ℕ) (B : ClosurePlace) (c M : ℕ) [NeZero M]
    (J : QZ → DiscreteUnits Ω) : Prop where
  /-- The distribution relation up to a root of unity: for `r ∣ M` prime to `c`, the quotient
  `(∏ b mod r, J (x + b / r)) / J (r • x)` has finite order. -/
  isOfFinAddOrder_sum_sub {x : QZ} (hx : M • x = 0) (r : ℕ) [NeZero r] (hr : r ∣ M)
    (hc : c.Coprime r) : IsOfFinAddOrder (∑ b : ZMod r, J (x + ofZMod r b) - J (r • x))
  /-- The Galois action: `σ (J x) = J (a • x)` if `σ` raises the `M`-th roots of unity to the
  power `a`. -/
  galUnitsRep_apply {x : QZ} (hx : M • x = 0) (σ : Gal(Ω/ℚ)) (a : ℕ)
    (ha : (cyclotomicCharMod Ω M σ).val = a) : galUnitsRep σ (J x) = J (a • x)
  /-- `J x` is a unit at every place not above `p`. -/
  valuation_eq_one {x : QZ} (hx : M • x = 0) (A : ClosurePlace) (hA : A.valuation p = 1) :
    A.valuation (J x).toMul.val = 1
  /-- The order of `J x` at `B` is `floorDiff c x`. -/
  ordRat_eq {x : QZ} (hx : M • x = 0) : ordRat ℚ B (J x) = floorDiff c x
  /-- `J x` has absolute value one in every complex embedding. -/
  norm_eq_one {x : QZ} (hx : M • x = 0) (τ : Ω →+* ℂ) : ‖τ (J x).toMul.val‖ = 1
  /-- For a prime `q ∣ p - 1` and `q • b = 0`, the quotient `J (x + b) / J x` is `≡ 1` at every
  place above `q`. -/
  sub_mem_principalUnits {x : QZ} (hx : M • x = 0) (q : ℕ) [Fact q.Prime] (A : ClosurePlace)
    (b : QZ) (hb : q • b = 0) (hq : q ∣ p - 1) (hA : A.valuation q < 1) :
    J (x + b) - J x ∈ principalUnits A

/-- A Gauss sum over `𝔽_p` of a multiplicative character `χ₀` and a primitive additive character
`ψ` divides `p` in `𝓞 Ω`. -/
lemma gaussSum_dvd_natCast_of_isPrimitive {ψ : AddChar (ZMod p) (𝓞 Ω)} (hψ : ψ.IsPrimitive)
    (χ₀ : MulChar (ZMod p) (𝓞 Ω)) :
    gaussSum χ₀ ψ ∣ p := by
  by_cases hχ₀ : χ₀ = 1
  · simp [hχ₀, gaussSum_one_left (show ψ ≠ 1 by simpa using hψ one_ne_zero)]
  · simpa using Dvd.intro _ (gaussSum_mul_gaussSum_eq_card hχ₀ hψ)

/-- Let `A` be a place of `Ω` not above `p`. A Gauss sum over `𝔽_p` of a multiplicative character
`χ₀` and a primitive additive character `ψ` has valuation one at `A`: it is integral and divides
`p`, which is a unit at `A`. -/
lemma valuation_gaussSum_eq_one_of_valuation_eq_one {A : ClosurePlace} (hA : A.valuation p = 1)
    {ψ : AddChar (ZMod p) (𝓞 Ω)} (hψ : ψ.IsPrimitive) (χ₀ : MulChar (ZMod p) (𝓞 Ω)) :
    A.valuation ((gaussSum χ₀ ψ : 𝓞 Ω) : Ω) = 1 := by
  have h_le : A.valuation ((gaussSum χ₀ ψ : 𝓞 Ω) : Ω) ≤ 1 :=
    A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (gaussSum χ₀ ψ)⟩
  refine h_le.eq_of_not_lt fun h_lt ↦ hA.not_lt ?_
  exact mem_centrePrime.mp (mem_of_dvd _ (gaussSum_dvd_natCast_of_isPrimitive hψ χ₀)
    (mem_centrePrime.mpr h_lt))

/-- An injective homomorphism `S : ℤ/r → ℚ/ℤ` maps the `m`-torsion onto the `m`-torsion, for
`m ∣ r`. -/
lemma exists_apply_eq_and_nsmul_eq_zero_of_injective {S : ZMod r →+ QZ} (hS : (⇑S).Injective)
    {x : QZ} (hx : m • x = 0) (h_dvd : m ∣ r) : ∃ t : ZMod r, S t = x ∧ m • t = 0 := by
  -- `S = ofZMod r ∘ f` with `f` injective, hence bijective; so `S` hits all the `r`-torsion.
  obtain ⟨f, rfl⟩ : ∃ f : ZMod r →+ ZMod r, (ofZMod r).comp f = S :=
    (bijective_ofZMod_comp (by simp [natCast_self])).surjective S
  obtain ⟨b, rfl⟩ : ∃ b : ZMod r, ofZMod r b = x :=
    exists_ofZMod (Submodule.torsionBy_le_torsionBy_of_dvd m r h_dvd hx)
  obtain ⟨t, rfl⟩ : ∃ t : ZMod r, f t = b :=
    (hS.of_comp (f := ofZMod r)).bijective_of_finite.surjective b
  exact ⟨t, rfl, hS (by rwa [map_nsmul, map_zero])⟩

/-- For a prime `p`, there are a primitive additive character `ψ` of `𝔽_p` and a primitive (so
injective) homomorphism `χ` from `ZMod (p - 1)` to the multiplicative characters of `𝔽_p`, both with
values in `𝓞 Ω`. -/
lemma exists_addChar_isPrimitive_and_mulChar_isPrimitive :
    ∃ (ψ : AddChar (ZMod p) (𝓞 Ω)) (χ : AddChar (ZMod p.pred) (MulChar (ZMod p) (𝓞 Ω))),
      ψ.IsPrimitive ∧ χ.IsPrimitive := by
  have hn_ne : NeZero p.pred := of_pos hp.out.pred_pos
  have root (m : ℕ) [NeZero m] : ∃ ζ : 𝓞 Ω, IsPrimitiveRoot ζ m :=
    ⟨_, (exists_isPrimitiveRoot Ω m).choose_spec.toInteger_isPrimitiveRoot⟩
  obtain ⟨ζp, hζp⟩ := root p
  obtain ⟨ζn, hζn⟩ := root p.pred
  -- `χ` sends `1` to a character `χ₀` of order `p - 1`, a generator of the dual of `𝔽_pˣ`.
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀ : MulChar (ZMod p) (𝓞 Ω), orderOf χ₀ = p.pred :=
    exists_mulChar_orderOf (ZMod p) (by simp) hζn
  exact ⟨_, _, zmodChar_primitive_of_primitive_root p hζp,
    zmodChar_primitive_of_primitive_root p.pred (IsPrimitiveRoot.iff_orderOf.mpr hχ₀)⟩

/-- Let `A` be a place of `Ω` above a prime `q`, let `ψ` be an additive character of `𝔽_p` and
`t ↦ χ t` a homomorphism from `ZMod n` to the multiplicative characters of `𝔽_p`. If `q • u = 0`,
the Gauss sums of `χ (w + u)` and of `χ w` with `ψ` are congruent modulo the prime ideal
`centrePrime Ω A`: the values of `χ u` on units are `q`-th roots of unity, so `≡ 1` at `A`. -/
lemma gaussSum_add_sub_gaussSum_mem_centrePrime_of_nsmul_eq_zero {n q : ℕ} [Fact q.Prime]
    {A : ClosurePlace} (hA : A.valuation q < 1) (ψ : AddChar (ZMod p) (𝓞 Ω))
    (χ : AddChar (ZMod n) (MulChar (ZMod p) (𝓞 Ω))) (w u : ZMod n) (hu : q • u = 0) :
    gaussSum (χ (w + u)) ψ - gaussSum (χ w) ψ ∈ centrePrime Ω A := by
  simp [gaussSum, mk_centrePrime_eq_one_of_pow_eq_one hA, hu, sum_eq_add_sum_units,
    map_add_eq_mul, ← Submodule.Quotient.mk_eq_zero, ← pow_apply_coe, ← map_nsmul_eq_pow]

/-- Let `B` be a place of `Ω` above the prime `p` and let `c : ℕ`. There is a family `J : ℚ/ℤ → Ωˣ`
(written additively) such that, for every `M` with `p ≡ 1` mod `M`, its values at the points `x`
with `M • x = 0` have the properties `New.OddPart.IsJacobiFamily`. It is built from the Jacobi-type
quotients `j t = g(χ) ^ c / g(χ ^ c)` of Gauss sums over `𝔽_p` (`χ` the character of index `t`): at
the point `x` of index `t` it is `j t / j (-t)`.

Such quotients of Gauss sums are used to prove Stickelberger's theorem on annihilators of class
groups of cyclotomic fields; no class group appears in the statement. -/
lemma exists_isJacobiFamily (hB : B.valuation p < 1) (c : ℕ) :
    ∃ J : QZ → DiscreteUnits Ω,
      ∀ (M : ℕ) [NeZero M], p ≡ 1 [MOD M] → IsJacobiFamily p B c M J := by
  -- Let `G t` be the Gauss sum of `χ t = χ₀ ^ t`, for a generator `χ₀` of the dual of `𝔽_pˣ`. By
  -- `stickelberger`, `S t = ord (G t)` identifies `ZMod (p - 1)` with the `(p - 1)`-torsion of
  -- `ℚ/ℤ`. Put `j t = G t ^ c / G (c t)` and `J (S t) = j t / j (-t)`.
  let n : ℕ := p.pred
  have hn_ne : NeZero n := of_pos hp.out.pred_pos
  have h_cop : p.Coprime n := by simp [n, hp.out.one_le]
  obtain ⟨ψ, χ, hψ, hχ⟩ := exists_addChar_isPrimitive_and_mulChar_isPrimitive (p := p)
  -- Gauss sums divide `p`, so they are non-zero.
  have gauss_ne (t : ZMod n) : ((gaussSum (χ t) ψ : 𝓞 Ω) : Ω) ≠ 0 :=
    RingOfIntegers.ext.mt (ne_zero_of_dvd_ne_zero out
      (gaussSum_dvd_natCast_of_isPrimitive hψ (χ t)))
  let G (t : ZMod n) : DiscreteUnits Ω := .ofNeZero (gaussSum (χ t) ψ : 𝓞 Ω) (gauss_ne t)
  have hG (t : ZMod n) : (G t).toMul.val = gaussSum (χ t) ψ := rfl
  obtain ⟨K, hK⟩ := exists_galUnitsRep_gaussSum_eq G hG
  obtain ⟨S, hS, lift_S⟩ := stickelberger hB G hG hψ hχ h_cop
  let j : ZMod n → DiscreteUnits Ω := c • G - G ∘ fun t : ZMod n ↦ c • t
  let J : QZ → DiscreteUnits Ω := (⇑S).extend (j - j ∘ fun t : ZMod n ↦ -t) 0
  have J_S (t : ZMod n) : J (S t) = j t - j (-t) := hS.extend_apply _ 0 t
  refine ⟨J, fun M _ hM ↦ ?_⟩
  have S_surj {x : QZ} (hx : M • x = 0) : ∃ t : ZMod n, S t = x ∧ M • t = 0 :=
    exists_apply_eq_and_nsmul_eq_zero_of_injective hS hx hM.symm.dvd'
  have h_gal (x : QZ) (hx : M • x = 0) (σ : Gal(Ω/ℚ)) (a : ℕ)
      (ha : (cyclotomicCharMod Ω M σ).val = a) : galUnitsRep σ (J x) = J (a • x) := by
    obtain ⟨t, rfl, ht⟩ := S_surj hx
    -- The factors `K σ` cancel in `j`, and `σ` acts on the index by `t ↦ a • t`. Test this on an
    -- injective `μ : ZMod n →+ DiscreteUnits Ω`, where `M • μ t = 0` as `M • t = 0`.
    let μ : ZMod n →+ DiscreteUnits Ω := (rootPowHom Ω n).val
    have hμ : Function.Injective μ := (rootPowHom Ω n).property.left
    have hμ_tors : M • μ t = 0 := by rw [← map_nsmul, ht, map_zero]
    have cyc_mul : (cyclotomicCharMod Ω n σ).val * t = a • t := hμ <| by
      rw [map_cyclotomicCharMod_mul, cyclotomicCharMod_eq_iff_unitsRep.mp ha hμ_tors, map_nsmul]
    -- Without `-nsmul_eq_mul`, `a • t` becomes `↑a * t` and `cyc_mul` no longer applies.
    simp [J_S, j, hK, cyc_mul, -nsmul_eq_mul, ← map_nsmul]
  have h_unit (x : QZ) (hx : M • x = 0) (A : ClosurePlace) (hA : A.valuation p = 1) :
      A.valuation (J x).toMul.val = 1 := by
    obtain ⟨t, rfl, -⟩ := S_surj hx
    simp [J_S, j, hG, valuation_gaussSum_eq_one_of_valuation_eq_one hA hψ]
  have h_ord (x : QZ) (hx : M • x = 0) : ordRat ℚ B (J x) = floorDiff c x := by
    obtain ⟨t, rfl, -⟩ := S_surj hx
    -- With `x = S t`, the order of `j t` is `c ⟨x⟩ - ⟨c x⟩ = ⌊c ⟨x⟩⌋`.
    simp [J_S, floorDiff, map_nsmul, ← nsmul_eq_mul, ← lift_S, j, ← self_sub_fract, ← fracRep_mk]
  have h_abs (x : QZ) (hx : M • x = 0) (τ : Ω →+* ℂ) : ‖τ (J x).toMul.val‖ = 1 := by
    obtain ⟨t, rfl, -⟩ := S_surj hx
    -- A complex conjugation `σ` for `τ` sends `j t` to `j (-t)`, so `τ (J x)` is `z / conj z`.
    obtain ⟨σ, hσ⟩ : ∃ σ : Gal(Ω/ℚ), ∀ z : Ω, τ (σ • z) = star τ z :=
      exists_apply_smul_eq_of_comp_algebraMap_eq Gal(Ω/ℚ) τ (star τ) (RingHom.ext_rat _ _)
    have j_neg : j (-t) = galUnitsRep σ (j t) := by
      simp [j, hK, IsComplexConj.cyclotomicCharMod_eq_neg_one ⟨τ, hσ⟩, ← map_nsmul]
    -- `AlgEquiv.smul_def` would hide the action `σ • z` that `hσ` rewrites.
    simp [J_S, j_neg, hσ, -AlgEquiv.smul_def]
  -- The distribution relation follows from these four properties; the congruence remains.
  refine
    { isOfFinAddOrder_sum_sub hx r := isOfFinAddOrder_distribution hB h_gal h_unit h_ord h_abs hx
      galUnitsRep_apply := h_gal _
      valuation_eq_one := h_unit _
      ordRat_eq := h_ord _
      norm_eq_one := h_abs _
      sub_mem_principalUnits := fun hx q _ A b hb hq hA ↦ ?_ }
  obtain ⟨t, rfl, -⟩ := S_surj hx
  obtain ⟨s, rfl, hs⟩ := exists_apply_eq_and_nsmul_eq_zero_of_injective hS hb hq
  -- If `q • u = 0` the values of `χ u` on units are `q`-th roots of unity, `≡ 1` at `A`.
  -- So `G (w + u) ≡ G w`, and both are units at `A` as `q ≠ p`.
  have hA_p : A.valuation p = 1 := (h_cop.symm.of_dvd_left hq).valuation_eq_one hA
  have G_congr (w u : ZMod n) (hu : q • u = 0) :
      (G (w + u) : DiscreteUnits Ω ⧸ principalUnits A) = G w := by
    have h_val : valuationVia Ω A (gaussSum (χ (w + u)) ψ - gaussSum (χ w) ψ) < 1 :=
      mem_centrePrime.mp (gaussSum_add_sub_gaussSum_mem_centrePrime_of_nsmul_eq_zero hA ψ χ w u hu)
    refine eq_iff_sub_mem.mpr (show A.valuation (((G (w + u) - G w).toMul : Ω) - 1) < 1 from ?_)
    simpa [toMul_sub, valuationVia, div_sub_one, gauss_ne, map_div₀, hG,
      valuation_gaussSum_eq_one_of_valuation_eq_one hA_p hψ] using h_val
  have j_congr (w u : ZMod n) (hu : q • u = 0) :
      (j (w + u) : DiscreteUnits Ω ⧸ principalUnits A) = j w := by
    have hcu : q • c • u = 0 := by rw [smul_comm, hu, smul_zero]
    simp [-nsmul_eq_mul, j, G_congr w u hu, G_congr _ _ hcu]
  rw [← map_add, J_S, J_S, ← eq_iff_sub_mem, neg_add, QuotientAddGroup.mk_sub,
    QuotientAddGroup.mk_sub, j_congr t s hs, j_congr (-t) (-s) (by rw [smul_neg, hs, neg_zero])]

end New.OddPart

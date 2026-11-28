import Lib.General.NumberTheory.GaussValuation

/-!
# Roots of unity `ζ` with polynomials hardly more divisible at `ζ - 1` than at given points

For `ρ > 0`, `ε > 0`, finitely many integral polynomials `P_i` in at most `s₀` variables and points
`x_i` whose coordinates have valuation at least `ρ`, with a bound on `∑ v(P_i(x_i))`, we find roots
of unity `ζ_j` of `ℓ`-power order with `v(ζ_j - 1) ≤ ρ` such that `v(P_i((ζ_j - 1)_j))` exceeds
`v(P_i(x_i))` by at most `ε`. The orders of the `ζ_j` are bounded before the polynomials are given.

* `New.Selmer.exists_rootOfUnity_eval_le_gaussVal_add`: the step in one variable, by counting roots.
* `New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`: several variables, by moving one coordinate
  of all points at a time.

Notions from other files:
* `New.ThePrime ℓ`: the class saying that `ℓ` is prime and is the prime in scope.
* `New.ellVal`: the valuation `v(x) = max (-log_ℓ |x|) 0` on `ℚ̄_ℓ`, with `v ℓ = 1` and `v 0 = ∞`;
  `New.intQpBar ℓ` is the ring `ℤ̄_ℓ` of integral elements.
* `New.Selmer.gaussVal`: the Gauss valuation `v_ρ(g) = min_i (v(y_i) + ρ i)` of `g = ∑ y_i Y ^ i`.

## Relation to the literature

Finitely many integral polynomials of any degree that are little divisible at given points of
positive valuation remain so at a single tuple of `ζ - 1`, with `ζ` roots of unity of `ℓ`-power
order. A degree-free bound at some `ℓ`-power root of unity for one element is known in the
literature. Related work: Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Serban, An
infinitesimal p-adic multiplicative Manin–Mumford conjecture, 2018; Kurihara, The structure of
Selmer groups of elliptic curves and modular symbols, 2014.
-/

noncomputable section

namespace New.Selmer

open Finset Polynomial Filter

open scoped NNReal ENNReal NNRat

variable {ℓ : ℕ} [ThePrime ℓ]

/-! ### The radii `ρ_h` and the harmonic sum -/

variable (ℓ) in
/-- The number `ρ_h = 1 / φ(ℓ ^ h)`, where `φ` is Euler's totient. For `h ≥ 1` it is the valuation
`v(ζ - 1)`, normalised by `v ℓ = 1`, for `ζ` of order `ℓ ^ h`. -/
def rootRadius (h : ℕ) : ℚ≥0 := (Nat.totient (ℓ ^ h) : ℚ≥0)⁻¹

lemma totient_pow_pos (h : ℕ) : 0 < Nat.totient (ℓ ^ h) :=
  Nat.totient_pos.2 (pow_pos (Fact.out : ℓ.Prime).pos h)

lemma coe_rootRadius (h : ℕ) :
    ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞) = (Nat.totient (ℓ ^ h) : ℝ≥0∞)⁻¹ := by
  rw [rootRadius, NNRat.cast_inv, NNRat.cast_natCast,
    ENNReal.coe_inv (Nat.cast_ne_zero.2 (totient_pow_pos h).ne'), ENNReal.coe_natCast]

/-- For `h ≥ 1` and a primitive `ℓ ^ h`-th root of unity `ζ` in `ℤ̄_ℓ = intQpBar ℓ`, the valuation
`v(ζ - 1)`, where `v = ellVal` is normalised by `v ℓ = 1`, is the radius `ρ_h = 1 / φ(ℓ ^ h)`. -/
lemma ellVal_sub_one_eq_rootRadius {h : ℕ} (hh : 1 ≤ h) {ζ : intQpBar ℓ}
    (hζ : IsPrimitiveRoot ζ (ℓ ^ h)) : ellVal (ζ - 1).val = (rootRadius ℓ h : ℝ≥0) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, h = k + 1 := Nat.exists_eq_add_of_le' hh
  rw [ellVal_sub_one_of_isPrimitiveRoot hζ, coe_rootRadius]

lemma strictMono_totient_pow_succ : StrictMono fun k : ℕ ↦ Nat.totient (ℓ ^ (k + 1)) := by
  have hℓ : ℓ.Prime := Fact.out
  simp only [Nat.totient_prime_pow_succ hℓ]
  exact (pow_right_strictMono₀ hℓ.one_lt).mul_const (Nat.sub_pos_of_lt hℓ.one_lt)

/-- The radii `rootRadius ℓ h` with `h ≥ 1` are distinct. -/
lemma rootRadius_injOn : Set.InjOn (rootRadius ℓ) (Set.Ici 1) := by
  intro h hh h' hh' h_eq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hh
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hh'
  exact congrArg (· + 1)
    (strictMono_totient_pow_succ.injective (by simpa [rootRadius] using h_eq))

/-- For `ρ > 0`, all large `h` have `rootRadius ℓ h = 1 / φ(ℓ ^ h) ≤ ρ`. -/
lemma eventually_rootRadius_le {ρ : ℚ≥0} (hρ : 0 < ρ) :
    ∀ᶠ h : ℕ in atTop, rootRadius ℓ h ≤ ρ := by
  filter_upwards [eventually_ge_atTop (⌈ρ⁻¹⌉₊ + 1)] with h hh
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right hh)
  have h_totient : ⌈ρ⁻¹⌉₊ ≤ Nat.totient (ℓ ^ (k + 1)) :=
    (Nat.le_of_succ_le_succ hh).trans strictMono_totient_pow_succ.le_apply
  exact inv_le_of_inv_le₀ hρ ((Nat.le_ceil _).trans (Nat.cast_le.2 h_totient))

variable (ℓ) in
/-- The exponents `h` with `1 ≤ h ≤ h₀` and `ρ_h ≤ ρ`, where `ρ_h = rootRadius ℓ h`. -/
def radiusExponents (ρ : ℚ≥0) (h₀ : ℕ) : Finset ℕ := {h ∈ Icc 1 h₀ | rootRadius ℓ h ≤ ρ}

omit [ThePrime ℓ] in
lemma mem_radiusExponents {ρ : ℚ≥0} {h h₀ : ℕ} :
    h ∈ radiusExponents ℓ ρ h₀ ↔ 1 ≤ h ∧ h ≤ h₀ ∧ rootRadius ℓ h ≤ ρ := by
  rw [radiusExponents, mem_filter, mem_Icc, and_assoc]

/-- Let `ρ > 0` and `δ > 0`. As the harmonic series diverges, there is an `h₀` such that `δ` times
the sum of `1 / (h + 1)` over `radiusExponents ℓ ρ h₀` (the `h` with `1 ≤ h ≤ h₀` and
`rootRadius ℓ h = 1 / φ(ℓ ^ h) ≤ ρ`) exceeds `B`. -/
lemma exists_lt_mul_sum_radiusExponents {ρ : ℚ≥0} {δ : ℝ≥0} (hρ : 0 < ρ) (B : ℝ≥0) (hδ : 0 < δ) :
    ∃ h₀ : ℕ, B < δ * ∑ h ∈ radiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹ := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ h ≥ N, 1 ≤ h ∧ rootRadius ℓ h ≤ ρ :=
    eventually_atTop.1 ((eventually_ge_atTop 1).and (eventually_rootRadius_le hρ))
  have h_diverges : ∀ᶠ n : ℕ in atTop,
      (B : ℝ) / δ + ∑ h ∈ range N, 1 / ((h : ℝ) + 1) < ∑ h ∈ range n, 1 / ((h : ℝ) + 1) :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop _
  obtain ⟨h₀, h_large, hNh₀⟩ := (h_diverges.and (eventually_ge_atTop N)).exists
  have h_tail : B / δ < ∑ h ∈ Ico N h₀, ((h : ℝ≥0) + 1)⁻¹ := by
    rw [← sum_range_add_sum_Ico _ hNh₀, add_comm, add_lt_add_iff_left] at h_large
    simpa [← NNReal.coe_lt_coe] using h_large
  have h_subset : Ico N h₀ ⊆ radiusExponents ℓ ρ h₀ := fun h hh ↦ by
    obtain ⟨hNh, hh₀⟩ := mem_Ico.1 hh
    exact mem_radiusExponents.2 ⟨(hN h hNh).1, hh₀.le, (hN h hNh).2⟩
  exact ⟨h₀, (div_lt_iff₀' hδ).1 (h_tail.trans_le (sum_le_sum_of_subset h_subset))⟩

/-! ### One variable -/

open Classical in
/-- The multiset of roots of `g` in `ℤ̄_ℓ = intQpBar ℓ` of valuation `r`, counted with multiplicity,
where the valuation `ellVal` is normalised by `v ℓ = 1`. For `r = ρ_h` it is written `R_h` in the
docstrings. -/
def rootsOfValuation (g : (intQpBar ℓ)[X]) (r : ℚ≥0) : Multiset (intQpBar ℓ) :=
  g.roots.filter fun α : intQpBar ℓ ↦ ellVal α.1 = (r : ℝ≥0)

/-- A member of `rootsOfValuation g r`, the roots of `g` in `ℤ̄_ℓ` of valuation `r`, has valuation
`r`. -/
lemma ellVal_of_mem_rootsOfValuation {g : (intQpBar ℓ)[X]} {r : ℚ≥0} {α : intQpBar ℓ}
    (hα : α ∈ rootsOfValuation g r) : ellVal α.val = (r : ℝ≥0) :=
  (Multiset.mem_filter.1 hα).2

open Classical in
/-- For the valuation `v = ellVal` on `ℚ̄_ℓ`, normalised by `v ℓ = 1`, the number of roots of `g` in
`ℤ̄_ℓ = intQpBar ℓ` with `v(α) = r`, counted with multiplicity, times `c` is the sum, over all roots
`α` in `ℤ̄_ℓ` with multiplicity, of `c` if `v(α) = r` and `0` otherwise. -/
lemma card_rootsOfValuation_mul (g : (intQpBar ℓ)[X]) (r : ℚ≥0) (c : ℝ≥0∞) :
    (rootsOfValuation g r).card * c =
      (g.roots.map fun α : intQpBar ℓ ↦ if ellVal α.val = (r : ℝ≥0) then c else 0).sum := by
  rw [rootsOfValuation]
  induction g.roots using Multiset.induction_on with
  | empty => simp
  | cons α s ih => by_cases hα : ellVal α.1 = (r : ℝ≥0) <;> simp [hα, ← ih, add_mul, add_comm]

/-- Let `v = ellVal` be the valuation on `ℚ̄_ℓ` with `v ℓ = 1`, let `g = ∑ y_i Y ^ i` be a
polynomial over the valuation ring `ℤ̄_ℓ = intQpBar ℓ`, and let `v_r(g) = gaussVal r g` be its Gauss
valuation `min_i (v(y_i) + r i)`. At a point `y` of valuation `r` only the roots `α` of `g` in
`ℤ̄_ℓ` of valuation `r` matter: `v(g(y)) - v_r(g) = ∑ (v(y - α) - r)` over the multiset
`rootsOfValuation g r` of these roots, counted with multiplicity, stated here without
subtraction. -/
lemma ellVal_eval_add_card_mul (g : (intQpBar ℓ)[X]) {r : ℚ≥0} {y : intQpBar ℓ}
    (hy : ellVal y.val = (r : ℝ≥0)) :
    ellVal (g.eval y).val + (rootsOfValuation g r).card * ((r : ℝ≥0) : ℝ≥0∞) =
      gaussVal r g +
        ((rootsOfValuation g r).map fun α : intQpBar ℓ ↦ ellVal (y - α).val).sum := by
  classical
  set R : Multiset (intQpBar ℓ) := rootsOfValuation g r
  set R' : Multiset (intQpBar ℓ) := g.roots.filter fun α ↦ ¬ellVal α.1 = (r : ℝ≥0)
  have h_split : g.roots = R + R' := (Multiset.filter_add_not _ g.roots).symm
  have h_other : ∀ α ∈ R', ellVal (y - α).1 = min (ellVal α.1) (r : ℝ≥0) := fun α hα ↦ by
    rw [ellVal_sub_eq_min_of_ne (hy.trans_ne (Ne.symm (Multiset.mem_filter.1 hα).2)), hy, min_comm]
  have h_same : ∀ α ∈ R, min (ellVal α.1) (r : ℝ≥0) = (r : ℝ≥0) :=
    fun α hα ↦ min_eq_right (ellVal_of_mem_rootsOfValuation hα).ge
  rw [ellVal_eval_eq_add_sum_roots, gaussVal_eq_add_sum_roots (ρ := r), h_split]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl h_other,
    Multiset.map_congr rfl h_same, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  ring

open Classical in
/-- Let `α` be in the valuation ring `ℤ̄_ℓ = intQpBar ℓ` of `ℚ̄_ℓ` and `v = ellVal` the valuation
with `v ℓ = 1`. At most one radius `ρ_h = rootRadius ℓ h = 1 / φ(ℓ ^ h)` with `h` in
`radiusExponents ℓ ρ h₀` equals `v(α)`, so the sum of these radii is at most `min (v(α)) ρ`. -/
lemma sum_rootRadius_filter_le_min {ρ : ℚ≥0} {h₀ : ℕ} (α : intQpBar ℓ) :
    ∑ h ∈ radiusExponents ℓ ρ h₀ with ellVal α.1 = (rootRadius ℓ h : ℝ≥0),
      ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞) ≤ min (ellVal α.1) (ρ : ℝ≥0) := by
  obtain h_empty | ⟨k, hk⟩ :=
    {h ∈ radiusExponents ℓ ρ h₀ | ellVal α.1 = (rootRadius ℓ h : ℝ≥0)}.eq_empty_or_nonempty
  · simp [h_empty]
  · obtain ⟨hk_mem, hk_val⟩ := mem_filter.1 hk
    obtain ⟨hk_one, -, hk_radius⟩ := mem_radiusExponents.1 hk_mem
    rw [sum_eq_single_of_mem k hk, hk_val]
    · exact le_min le_rfl (mod_cast hk_radius)
    · intro h hh h_ne
      obtain ⟨hh_mem, hh_val⟩ := mem_filter.1 hh
      have h_radii : rootRadius ℓ h = rootRadius ℓ k := mod_cast hh_val.symm.trans hk_val
      exact absurd (rootRadius_injOn (mem_radiusExponents.1 hh_mem).1 hk_one h_radii) h_ne

/-- Let `v = ellVal` be the valuation on `ℚ̄_ℓ` with `v ℓ = 1`, and let `g = ∑ y_i Y ^ i` be a
polynomial over `ℤ̄_ℓ = intQpBar ℓ`. Let `ρ_h = rootRadius ℓ h = 1 / φ(ℓ ^ h)`, and let
`R_h = rootsOfValuation g ρ_h` be the multiset of roots of `g` in `ℤ̄_ℓ` of valuation `ρ_h`, counted
with multiplicity. The sum of `#R_h ρ_h` over `radiusExponents ℓ ρ h₀` is at most the Gauss
valuation `gaussVal ρ g = min_i (v(y_i) + ρ i)`. -/
lemma sum_card_rootsOfValuation_mul_le {ρ : ℚ≥0} {h₀ : ℕ} (g : (intQpBar ℓ)[X]) :
    ∑ h ∈ radiusExponents ℓ ρ h₀, (rootsOfValuation g (rootRadius ℓ h)).card *
      ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞) ≤ gaussVal ρ g := by
  classical
  -- A root lies in at most one `R_h`, and its summand `min (v(α)) ρ` in `v_ρ(g)` is then `ρ_h`.
  calc _ = (g.roots.map fun α ↦
          ∑ h ∈ radiusExponents ℓ ρ h₀ with ellVal α.1 = (rootRadius ℓ h : ℝ≥0),
            ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞)).sum := by
        simp only [sum_filter, Multiset.sum_map_sum, card_rootsOfValuation_mul]
    _ ≤ (g.roots.map fun α ↦ min (ellVal α.1) (ρ : ℝ≥0)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun α _ ↦ sum_rootRadius_filter_le_min α
    _ ≤ gaussVal ρ g := le_add_self.trans_eq (gaussVal_eq_add_sum_roots g).symm

/-- Let `v = ellVal` be the valuation on `ℚ̄_ℓ` with `v ℓ = 1`, and let `g = ∑ y_i Y ^ i` be a
polynomial over `ℤ̄_ℓ = intQpBar ℓ`. Let `ρ_h = rootRadius ℓ h = 1 / φ(ℓ ^ h)`, and let
`R_h = rootsOfValuation g ρ_h` be the multiset of roots of `g` in `ℤ̄_ℓ` of valuation `ρ_h`, counted
with multiplicity. Suppose that the Gauss valuation `gaussVal ρ g = min_i (v(y_i) + ρ i)` is at most
`B`. Suppose also that `B` is less than `δ` times the sum of `1 / (h + 1)` over
`radiusExponents ℓ ρ h₀`. Then one of these `h` has `#R_h ρ_h ≤ δ / (h + 1)`. -/
lemma exists_card_rootsOfValuation_mul_le {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0}
    (h_harmonic : B < δ * ∑ h ∈ radiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    {g : (intQpBar ℓ)[X]} (hg : gaussVal ρ g ≤ B) :
    ∃ h ∈ radiusExponents ℓ ρ h₀,
      (rootsOfValuation g (rootRadius ℓ h)).card * (rootRadius ℓ h : ℝ≥0) ≤ δ / (h + 1) := by
  by_contra! h_many
  have h_count : ∑ h ∈ radiusExponents ℓ ρ h₀,
      (rootsOfValuation g (rootRadius ℓ h)).card * (rootRadius ℓ h : ℝ≥0) ≤ B :=
    mod_cast (sum_card_rootsOfValuation_mul_le g).trans hg
  refine h_harmonic.not_ge (le_trans ?_ h_count)
  simpa [mul_sum, div_eq_mul_inv] using sum_le_sum fun h hh ↦ (h_many h hh).le

/-- An integral `α` is close to few `ζ - 1`: if `1 + α` is a unit of `ℤ̄_ℓ`, then the sum of
`min (v(ζ - 1 - α)) 1` over the primitive `ℓ ^ h`-th roots of unity `ζ` is at most `h + 1`, where
`v = ellVal` is the valuation with `v ℓ = 1`. -/
lemma sum_min_ellVal_sub_le {α : intQpBar ℓ} (hα : IsUnit (1 + α)) (h : ℕ) :
    ∑ ζ ∈ primitiveRoots (ℓ ^ h) (intQpBar ℓ), min (ellVal (ζ - 1 - α).val) 1 ≤ h + 1 := by
  -- The numbers `ζ - 1 - α` are roots of `f = (1 + α + Y) ^ ℓ ^ h - 1`, whose coefficient of `Y` is
  -- `ℓ ^ h` times a unit. Both sides are compared with `v₁(f)`.
  set f : (intQpBar ℓ)[X] := (X + C (1 + α)) ^ ℓ ^ h - 1 with hf
  have h_coeff : f.coeff 1 = (1 + α) ^ (ℓ ^ h - 1) * ℓ ^ h := by
    rw [hf, coeff_sub, coeff_X_add_C_pow, coeff_one, ite_eq_right one_ne_zero, sub_zero,
      Nat.choose_one_right, Nat.cast_pow]
  have h_val : ellVal (f.coeff 1).1 = h := by
    rw [h_coeff, ellVal_val_mul, ellVal_eq_zero_iff_isUnit.2 (hα.pow _), zero_add]
    simp [ellVal_pow, ellVal_ell]
  have hf_ne : f ≠ 0 := fun h_zero ↦ ENNReal.natCast_ne_top h
    (h_val.symm.trans (ellVal_eq_top_iff.2 (by simp [h_zero])))
  have h_roots :
      (primitiveRoots (ℓ ^ h) (intQpBar ℓ)).val.map (fun ζ ↦ ζ - 1 - α) ≤ f.roots := by
    have h_inj : Function.Injective fun ζ : intQpBar ℓ ↦ ζ - 1 - α :=
      sub_left_injective.comp sub_left_injective
    refine (Multiset.le_iff_subset ((primitiveRoots _ _).nodup.map h_inj)).2 fun y hy ↦ ?_
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.1 hy
    have h_point : ζ - 1 - α + (1 + α) = ζ := by ring
    rw [mem_roots hf_ne, IsRoot.def, hf, eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_one,
      h_point, (isPrimitiveRoot_of_mem_primitiveRoots hζ).pow_eq_one, sub_self]
  calc _ ≤ (f.roots.map fun y ↦ min (ellVal y.1) 1).sum := by
        obtain ⟨rest, h_rest⟩ := Multiset.le_iff_exists_add.1 h_roots
        simp [h_rest]
    _ ≤ gaussVal 1 f := by simp [gaussVal_eq_add_sum_roots (ρ := 1)]
    _ ≤ h + 1 := by simpa [h_val] using gaussVal_le_coeff (ρ := 1) f 1

/-- The valuation ring `ℤ̄_ℓ = intQpBar ℓ` of `ℚ̄_ℓ` contains a primitive `ℓ ^ h`-th root of
unity. -/
lemma exists_isPrimitiveRoot_pow (h : ℕ) : ∃ ζ : intQpBar ℓ, IsPrimitiveRoot ζ (ℓ ^ h) := by
  have : NeZero (ℓ ^ h) := ⟨pow_ne_zero h (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl ℓ) (ℓ ^ h)
  -- Membership in the valuation ring is by definition the bound `‖ζ‖ ≤ 1`.
  have h_int : ζ ∈ intQpBar ℓ := (hζ.isOfFinOrder NeZero.out).norm_eq_one.le
  exact ⟨⟨ζ, h_int⟩, IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ⟩

/-- Averaging over the roots of unity of order `ℓ ^ h`. Let `v = ellVal` be the valuation on `ℚ̄_ℓ`
with `v ℓ = 1` and `ρ_h = rootRadius ℓ h = 1 / φ(ℓ ^ h)`, so that there are `1 / ρ_h` such roots in
`ℤ̄_ℓ = intQpBar ℓ`. Let `R` be a multiset in `ℤ̄_ℓ` with `1 + α` a unit for all `α ∈ R`. Then for
one such root of unity `ζ` the numbers `min (v(ζ - 1 - α)) 1`, `α ∈ R`, add up to at most
`#R ρ_h (h + 1)`. -/
lemma exists_sum_min_ellVal_sub_le (h : ℕ) {R : Multiset (intQpBar ℓ)}
    (hR : ∀ α ∈ R, IsUnit (1 + α)) :
    ∃ ζ : intQpBar ℓ, IsPrimitiveRoot ζ (ℓ ^ h) ∧
      (R.map fun α : intQpBar ℓ ↦ min (ellVal (ζ - 1 - α).val) 1).sum ≤
        R.card * ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞) * (h + 1) := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_isPrimitiveRoot_pow (ℓ := ℓ) h
  set μ : Finset (intQpBar ℓ) := primitiveRoots (ℓ ^ h) (intQpBar ℓ)
  set c : ℝ≥0∞ := ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞) with hc
  have h_card : #μ * c = 1 := by
    simp [μ, hζ₀.card_primitiveRoots, hc, coe_rootRadius, ENNReal.mul_inv_cancel,
      (totient_pow_pos h).ne']
  have h_total : ∑ ζ ∈ μ, (R.map fun α ↦ min (ellVal (ζ - 1 - α).val) 1).sum ≤
      ∑ _ζ ∈ μ, R.card * c * (h + 1) :=
    calc _ = (R.map fun α ↦ ∑ ζ ∈ μ, min (ellVal (ζ - 1 - α).val) 1).sum :=
          Multiset.sum_map_sum.symm
      _ ≤ (R.map fun _ ↦ (h + 1 : ℝ≥0∞)).sum :=
          Multiset.sum_map_le_sum_map _ _ fun α hα ↦ sum_min_ellVal_sub_le (hR α hα) h
      _ = R.card * (#μ * c) * (h + 1) := by simp [h_card, mul_add]
      _ = ∑ _ζ ∈ μ, R.card * c * (h + 1) := by rw [sum_const, nsmul_eq_mul]; ring
  obtain ⟨ζ, hζ, h_average⟩ := ENNReal.exists_le_of_sum_le
    ⟨ζ₀, (mem_primitiveRoots (pow_pos (Fact.out : ℓ.Prime).pos h)).2 hζ₀⟩ h_total
  exact ⟨ζ, isPrimitiveRoot_of_mem_primitiveRoots hζ, h_average⟩

/-- An element `1 + α` of `ℤ̄_ℓ = intQpBar ℓ` is a unit if the valuation `ellVal` of `α` is
positive. -/
lemma isUnit_one_add_of_ellVal_pos {α : intQpBar ℓ} (hα : 0 < ellVal α.val) : IsUnit (1 + α) := by
  have h_one : ellVal (1 : intQpBar ℓ).val = 0 := ellVal_eq_zero_iff_isUnit.2 isUnit_one
  rw [← ellVal_eq_zero_iff_isUnit, ellVal_add_eq_min_of_ne (h_one.trans_ne hα.ne), h_one,
    min_eq_left hα.le]

/-- Write `v = ellVal` for the valuation on `ℚ̄_ℓ` with `v ℓ = 1`, and
`v_r(g) = gaussVal r g = min_i (v(y_i) + r i)` for the Gauss valuation of a polynomial
`g = ∑ y_i Y ^ i` over the ring `ℤ̄_ℓ = intQpBar ℓ` of integral elements. Let `δ < 1`, and let `δ`
times the sum of `1 / (h + 1)` over the exponents `1 ≤ h ≤ h₀` with `ρ_h ≤ ρ` exceed `B`, where
`ρ_h = rootRadius ℓ h = 1 / φ(ℓ ^ h)`. If `v_ρ(g) ≤ B`, then for one of these exponents `h` and some
`ζ` of order `ℓ ^ h` we have `v(g(ζ - 1)) ≤ v_{ρ_h}(g) + δ`. -/
theorem exists_rootOfUnity_eval_le_gaussVal_add {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : B < δ * ∑ h ∈ radiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    {g : (intQpBar ℓ)[X]} (hg : gaussVal ρ g ≤ B) :
    ∃ h ∈ radiusExponents ℓ ρ h₀, ∃ ζ : intQpBar ℓ, IsPrimitiveRoot ζ (ℓ ^ h) ∧
      ellVal (g.eval (ζ - 1)).val ≤ gaussVal (rootRadius ℓ h) g + δ := by
  -- Choose `h` with few roots `α` of valuation `ρ_h`, then `ζ` with `ζ - 1` far from them.
  obtain ⟨h, hh, h_few⟩ := exists_card_rootsOfValuation_mul_le h_harmonic hg
  obtain ⟨h_one, -, -⟩ := mem_radiusExponents.1 hh
  set R : Multiset (intQpBar ℓ) := rootsOfValuation g (rootRadius ℓ h)
  have h_unit : ∀ α ∈ R, IsUnit (1 + α) := fun α hα ↦ isUnit_one_add_of_ellVal_pos <| by
    simp [ellVal_of_mem_rootsOfValuation hα, coe_rootRadius]
  obtain ⟨ζ, hζ, h_average⟩ := exists_sum_min_ellVal_sub_le h h_unit
  have h_min : (R.map fun α ↦ min (ellVal (ζ - 1 - α).val) 1).sum ≤ δ :=
    h_average.trans (mod_cast (le_div_iff₀ (by positivity)).1 h_few)
  -- As `δ < 1`, no minimum is `1`.
  have h_not_one : ∀ α ∈ R, ellVal (ζ - 1 - α).val = min (ellVal (ζ - 1 - α).val) 1 := by
    intro α hα
    have h_le : min (ellVal (ζ - 1 - α).val) 1 ≤ δ :=
      (Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hα)).trans h_min
    have h_lt : ellVal (ζ - 1 - α).val < 1 := by
      simpa using h_le.trans_lt (ENNReal.coe_lt_one_iff.2 hδ)
    exact (min_eq_left h_lt.le).symm
  refine ⟨h, hh, ζ, hζ, ?_⟩
  calc ellVal (g.eval (ζ - 1)).val
      ≤ ellVal (g.eval (ζ - 1)).val + R.card * ((rootRadius ℓ h : ℝ≥0) : ℝ≥0∞) := le_self_add
    _ = gaussVal (rootRadius ℓ h) g + (R.map fun α ↦ ellVal (ζ - 1 - α).val).sum :=
        ellVal_eval_add_card_mul g (ellVal_sub_one_eq_rootRadius h_one hζ)
    _ = gaussVal (rootRadius ℓ h) g + (R.map fun α ↦ min (ellVal (ζ - 1 - α).val) 1).sum := by
        rw [Multiset.map_congr rfl h_not_one]
    _ ≤ gaussVal (rootRadius ℓ h) g + δ := add_le_add_right h_min _

/-! ### Several variables -/

variable {σ ι : Type*}

/-- If `b i ≤ a i` for all `i`, the sum `∑ b i` is finite and `∑ a i ≤ ∑ b i + c`, then
`a i ≤ b i + c` for each `i`. -/
lemma le_add_of_sum_le_sum_add [Fintype ι] {a b : ι → ℝ≥0∞} {c : ℝ≥0∞}
    (hba : ∀ i : ι, b i ≤ a i) (hb : ∑ i : ι, b i ≠ ⊤) (h_sum : ∑ i : ι, a i ≤ ∑ i : ι, b i + c)
    (i : ι) : a i ≤ b i + c := by
  classical
  refine ENNReal.le_of_add_le_add_right
    (ne_top_of_le_ne_top hb (sum_le_sum_of_subset (subset_univ (univ.erase i)))) ?_
  calc a i + ∑ k ∈ univ.erase i, b k
      ≤ a i + ∑ k ∈ univ.erase i, a k := add_le_add_right (sum_le_sum fun k _ ↦ hba k) _
    _ = ∑ k : ι, a k := add_sum_erase univ a (mem_univ i)
    _ ≤ ∑ k : ι, b k + c := h_sum
    _ = b i + c + ∑ k ∈ univ.erase i, b k := by
        rw [← add_sum_erase univ b (mem_univ i), add_right_comm]

/-- For a point `x` with coordinates in `ℤ̄_ℓ = intQpBar ℓ` and a coordinate index `j`, the
polynomial `P` at `x` with one variable `Y` in place of `x j`. -/
def freeCoordinate [DecidableEq σ] (x : σ → intQpBar ℓ) (j : σ)
    (P : MvPolynomial σ (intQpBar ℓ)) : (intQpBar ℓ)[X] :=
  MvPolynomial.aeval (Function.update (fun k : σ ↦ C (x k)) j X) P

/-- The value of `freeCoordinate x j P` at `y` is the value of `P` at the point `x` with its
coordinate `x j` replaced by `y`. -/
lemma eval_freeCoordinate [DecidableEq σ] (x : σ → intQpBar ℓ) (j : σ)
    (P : MvPolynomial σ (intQpBar ℓ)) (y : intQpBar ℓ) :
    (freeCoordinate x j P).eval y = MvPolynomial.eval (Function.update x j y) P := by
  have h_point : (fun k : σ ↦ (Function.update (fun k : σ ↦ C (x k)) j X k).eval y) =
      Function.update x j y := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  have h_const : (evalRingHom y).comp (algebraMap (intQpBar ℓ) (intQpBar ℓ)[X]) =
      RingHom.id (intQpBar ℓ) := RingHom.ext fun _ ↦ by simp
  rw [freeCoordinate, MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂, h_point, h_const,
    MvPolynomial.eval₂_id]

/-- Moving one coordinate `j`. Let `δ < 1`, and let `δ` times the sum of `1 / (h + 1)` over the
exponents `1 ≤ h ≤ h₀` with `1 / φ(ℓ ^ h) ≤ ρ` exceed `B`. Let `P i` be polynomials and `x i` points
over the valuation ring `ℤ̄_ℓ = intQpBar ℓ` of `ℚ̄_ℓ` with `v(x i j) ≥ ρ` and
`∑ i, v(P i (x i)) ≤ B`. Then all `x i j` can be replaced by one number `ζ - 1`, with
`ζ ^ ℓ ^ h₀ = 1` and `v(ζ - 1) ≤ ρ`, so that each `v(P i (x i))`, and also their sum, grows by at
most `δ`. -/
lemma exists_ellVal_eval_update_le_add [DecidableEq σ] [Fintype ι] {ρ : ℚ≥0} {h₀ : ℕ} {B δ : ℝ≥0}
    (hδ : δ < 1) (h_harmonic : B < δ * ∑ h ∈ radiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (P : ι → MvPolynomial σ (intQpBar ℓ)) {x : ι → σ → intQpBar ℓ} {j : σ}
    (hx : ∀ i : ι, (ρ : ℝ≥0) ≤ ellVal (x i j).val)
    (hP : ∑ i : ι, ellVal (MvPolynomial.eval (x i) (P i)).val ≤ B) :
    ∃ ζ : intQpBar ℓ,
      ζ ^ ℓ ^ h₀ = 1 ∧
      ellVal (ζ - 1).val ≤ (ρ : ℝ≥0) ∧
      (∀ i : ι, ellVal (MvPolynomial.eval (Function.update (x i) j (ζ - 1)) (P i)).val ≤
        ellVal (MvPolynomial.eval (x i) (P i)).val + δ) ∧
      ∑ i : ι, ellVal (MvPolynomial.eval (Function.update (x i) j (ζ - 1)) (P i)).val ≤
        ∑ i : ι, ellVal (MvPolynomial.eval (x i) (P i)).val + δ := by
  -- Apply the case of one variable to the product of the `g i`.
  set g : ι → (intQpBar ℓ)[X] := fun i ↦ freeCoordinate (x i) j (P i)
  have h_eval (i : ι) (y : intQpBar ℓ) :
      (g i).eval y = MvPolynomial.eval (Function.update (x i) j y) (P i) := eval_freeCoordinate ..
  have h_old (i : ι) : gaussVal ρ (g i) ≤ ellVal (MvPolynomial.eval (x i) (P i)).val := by
    simpa [h_eval] using gaussVal_le_eval (g i) (hx i)
  have h_prod : gaussVal ρ (∏ i : ι, g i) ≤ B := by
    simpa [gaussVal_prod] using (sum_le_sum fun i _ ↦ h_old i).trans hP
  obtain ⟨h, hh, ζ, hζ, h_prod_eval⟩ :
      ∃ h ∈ radiusExponents ℓ ρ h₀, ∃ ζ : intQpBar ℓ, IsPrimitiveRoot ζ (ℓ ^ h) ∧
        ellVal ((∏ i : ι, g i).eval (ζ - 1)).val ≤ gaussVal (rootRadius ℓ h) (∏ i : ι, g i) + δ :=
    exists_rootOfUnity_eval_le_gaussVal_add hδ h_harmonic h_prod
  obtain ⟨h_one, hh₀, h_radius⟩ := mem_radiusExponents.1 hh
  have hζ_val : ellVal (ζ - 1).val = (rootRadius ℓ h : ℝ≥0) :=
    ellVal_sub_one_eq_rootRadius h_one hζ
  have h_compare (i : ι) :
      gaussVal (rootRadius ℓ h) (g i) ≤ ellVal (MvPolynomial.eval (x i) (P i)).val :=
    (gaussVal_mono h_radius (g i)).trans (h_old i)
  have h_compare_sum : ∑ i : ι, gaussVal (rootRadius ℓ h) (g i) ≤
      ∑ i : ι, ellVal (MvPolynomial.eval (x i) (P i)).val := sum_le_sum fun i _ ↦ h_compare i
  have h_sum :
      ∑ i : ι, ellVal ((g i).eval (ζ - 1)).val ≤ ∑ i : ι, gaussVal (rootRadius ℓ h) (g i) + δ := by
    rwa [gaussVal_prod, eval_prod, ellVal_prod] at h_prod_eval
  have h_each (i : ι) : ellVal ((g i).eval (ζ - 1)).val ≤ gaussVal (rootRadius ℓ h) (g i) + δ :=
    le_add_of_sum_le_sum_add (fun k ↦ gaussVal_le_eval (g k) hζ_val.ge)
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (h_compare_sum.trans hP)) h_sum i
  simp only [h_eval] at h_sum h_each
  refine ⟨ζ, (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow ℓ hh₀),
    hζ_val.trans_le (mod_cast h_radius), fun i ↦ ?_, ?_⟩
  · exact (h_each i).trans (add_le_add_left (h_compare i) _)
  · exact h_sum.trans (add_le_add_left h_compare_sum _)

/-- Moving the coordinates in a finite set `t` in turn. Let `δ < 1` and `#σ δ ≤ 1`, and let `δ`
times the sum of `1 / (h + 1)` over the exponents `1 ≤ h ≤ h₀` with `1 / φ(ℓ ^ h) ≤ ρ` exceed
`β + 1`. Let `P i` be polynomials and `x i` points over the valuation ring `ℤ̄_ℓ = intQpBar ℓ` of
`ℚ̄_ℓ` with `v(x i j) ≥ ρ` for all `j` and `∑ i, v(P i (x i)) ≤ β`. Then the coordinates `x i j`
with `j ∈ t` can be replaced by numbers `ζ j - 1`, the same for all `i`, with `ζ j ^ ℓ ^ h₀ = 1` and
`v(ζ j - 1) ≤ ρ`, so that each `v(P i (x i))` grows by at most `#t δ` and their sum stays at most
`β + #t δ`. -/
lemma exists_ellVal_eval_piecewise_le_add [DecidableEq σ] [Fintype σ] [Fintype ι] {ρ : ℚ≥0} {h₀ : ℕ}
    {δ β : ℝ≥0} (hδ : δ < 1)
    (h_harmonic : β + 1 < δ * ∑ h ∈ radiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹)
    (hσ_card : Fintype.card σ * δ ≤ 1) (P : ι → MvPolynomial σ (intQpBar ℓ))
    {x : ι → σ → intQpBar ℓ} (hx : ∀ (i : ι) (j : σ), (ρ : ℝ≥0) ≤ ellVal (x i j).val)
    (hP : ∑ i : ι, ellVal (MvPolynomial.eval (x i) (P i)).val ≤ β) (t : Finset σ) :
    ∃ ζ : σ → intQpBar ℓ,
      (∀ j ∈ t, ζ j ^ ℓ ^ h₀ = 1) ∧
      (∀ j ∈ t, ellVal (ζ j - 1).val ≤ (ρ : ℝ≥0)) ∧
      (∀ i : ι, ellVal (MvPolynomial.eval (t.piecewise (fun j : σ ↦ ζ j - 1) (x i)) (P i)).val ≤
        ellVal (MvPolynomial.eval (x i) (P i)).val + #t * δ) ∧
      ∑ i : ι, ellVal (MvPolynomial.eval (t.piecewise (fun j : σ ↦ ζ j - 1) (x i)) (P i)).val ≤
        β + #t * δ := by
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp, by simp, by simpa using hP⟩
  | insert j t hj ih =>
    obtain ⟨ζ, h_pow, h_val, h_each, h_sum⟩ := ih
    -- The points `y i` have the coordinates in `t` moved; now move the coordinate `j`.
    set y : ι → σ → intQpBar ℓ := fun i ↦ t.piecewise (fun k ↦ ζ k - 1) (x i)
    have h_loss : (#t * δ : ℝ≥0) ≤ 1 :=
      (mul_le_mul_left (Nat.cast_le.2 (card_le_univ t)) δ).trans hσ_card
    have h_below : ∑ i : ι, ellVal (MvPolynomial.eval (y i) (P i)).val ≤ (β + 1 : ℝ≥0) :=
      h_sum.trans (mod_cast add_le_add_right h_loss β)
    obtain ⟨ξ, hξ_pow, hξ_val, h_each_step, h_sum_step⟩ :=
      exists_ellVal_eval_update_le_add (j := j) hδ h_harmonic P
        (fun i ↦ by simpa [y, hj] using hx i j) h_below
    have h_old : ∀ k ∈ t, Function.update ζ j ξ k = ζ k :=
      fun k hk ↦ Function.update_of_ne (ne_of_mem_of_not_mem hk hj) ξ ζ
    have h_point (i : ι) : (insert j t).piecewise (fun k ↦ Function.update ζ j ξ k - 1) (x i) =
        Function.update (y i) j (ξ - 1) := by
      rw [piecewise_insert, Function.update_self,
        piecewise_congr t (fun k hk ↦ by rw [h_old k hk]) fun _ _ ↦ rfl]
    have h_card_insert : (#(insert j t) * δ : ℝ≥0∞) = #t * δ + δ := by simp [hj, add_one_mul]
    refine ⟨Function.update ζ j ξ, ?_, ?_, fun i ↦ ?_, ?_⟩
    · simp +contextual [h_old, hξ_pow, h_pow]
    · rw [forall_mem_insert, Function.update_self]
      exact ⟨hξ_val, fun k hk ↦ by simpa only [h_old k hk] using h_val k hk⟩
    · rw [h_point, h_card_insert, ← add_assoc]
      exact (h_each_step i).trans (add_le_add_left (h_each i) _)
    · simp only [h_point, h_card_insert, ← add_assoc]
      exact h_sum_step.trans (add_le_add_left h_sum _)

/-- Let a natural number `s₀`, a rational `ρ > 0`, `β ≥ 0` and `ε > 0` be given. There is an `h₀`
with the following property. Let `P i` be finitely many polynomials over `ℤ̄_ℓ = intQpBar ℓ` in one
set of at most `s₀` variables, and `x i` points whose coordinates have valuation at least `ρ`, with
`∑ i, v(P i (x i)) ≤ β`. Then there are roots of unity `ζ j` of orders dividing `ℓ ^ h₀` with
`v(ζ j - 1) ≤ ρ` for all `j` and `v(P i ((ζ j - 1)_j)) ≤ v(P i (x i)) + ε` for all `i`. -/
theorem exists_rootsOfUnity_ellVal_eval_le_add (s₀ : ℕ) {ρ : ℚ≥0} (hρ : 0 < ρ) (β : ℝ≥0) {ε : ℝ≥0}
    (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (P : ι → MvPolynomial σ (intQpBar ℓ))
      (x : ι → σ → intQpBar ℓ),
      Fintype.card σ ≤ s₀ →
      (∀ (i : ι) (j : σ), (ρ : ℝ≥0) ≤ ellVal (x i j).val) →
      ∑ i : ι, ellVal (MvPolynomial.eval (x i) (P i)).val ≤ β →
      ∃ ζ : σ → intQpBar ℓ,
        (∀ j : σ, ζ j ^ ℓ ^ h₀ = 1) ∧
        (∀ j : σ, ellVal (ζ j - 1).val ≤ (ρ : ℝ≥0)) ∧
        ∀ i : ι, ellVal (MvPolynomial.eval (fun j : σ ↦ ζ j - 1) (P i)).val ≤
          ellVal (MvPolynomial.eval (x i) (P i)).val + ε := by
  classical
  -- Take `h₀` from the harmonic sum and move all coordinates, each with the loss
  -- `δ = min ε 1 / (s₀ + 2)`, so that `δ < 1` and the total loss is at most `min ε 1`.
  set δ : ℝ≥0 := min ε 1 / (s₀ + 2)
  have h_pos : (0 : ℝ≥0) < s₀ + 2 := by positivity
  have hδ_lt : δ < 1 :=
    (div_lt_one h_pos).2 ((min_le_right ε 1).trans_lt (one_lt_two.trans_le le_add_self))
  obtain ⟨h₀, h_harmonic⟩ :
      ∃ h₀ : ℕ, β + 1 < δ * ∑ h ∈ radiusExponents ℓ ρ h₀, ((h : ℝ≥0) + 1)⁻¹ :=
    exists_lt_mul_sum_radiusExponents hρ (β + 1) (by positivity)
  refine ⟨h₀, fun σ ι _ _ P x hσ_card hx hP ↦ ?_⟩
  have h_loss : (Fintype.card σ * δ : ℝ≥0) ≤ min ε 1 :=
    calc (Fintype.card σ * δ : ℝ≥0) ≤ (s₀ + 2) * δ :=
          mul_le_mul_left (le_add_right (mod_cast hσ_card)) δ
      _ = min ε 1 := mul_div_cancel₀ (min ε 1) h_pos.ne'
  obtain ⟨h_loss_ε, h_loss_one⟩ := le_min_iff.1 h_loss
  obtain ⟨ζ, h_pow, h_val, h_each, -⟩ :=
    exists_ellVal_eval_piecewise_le_add hδ_lt h_harmonic h_loss_one P hx hP univ
  refine ⟨ζ, fun j ↦ h_pow j (mem_univ j), fun j ↦ h_val j (mem_univ j), fun i ↦ ?_⟩
  calc ellVal (MvPolynomial.eval (fun j : σ ↦ ζ j - 1) (P i)).val
      = ellVal (MvPolynomial.eval (univ.piecewise (fun j : σ ↦ ζ j - 1) (x i)) (P i)).val := by
        rw [piecewise_univ]
    _ ≤ ellVal (MvPolynomial.eval (x i) (P i)).val + Fintype.card σ * δ := h_each i
    _ ≤ ellVal (MvPolynomial.eval (x i) (P i)).val + ε := add_le_add_right (mod_cast h_loss_ε) _

end New.Selmer

end

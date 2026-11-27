import Lib.PadicHodge.Crystalline.HodgeTateJumps
import Lib.PadicHodge.Crystalline.Regularity

/-!
# Period matrices over a chart: lattice bases and existence for crystalline lattices

This file studies period matrices over a chart `c` (`New.Lift.Chart`). `A_inf ⊂ B⁺ = A_max[1/p]` are
the period rings `New.Period.Ainf`, `New.Period.BPlus`, and `amaxImage` is the image of `A_max` in
`B⁺`. A chart gives a subring `S` of `A_inf` with elements `z` and `E`. Here `E` is `ξ` times a
unit, and `ξ` generates the kernel of `θ`. `S_B` denotes `New.Lift.Chart.bicommutant`. Write
`μ = [ε] - 1` (`New.Period.mu`) and `τ = [ε^{1/p}] - 1` (`New.Period.tau`). Then `E τ` is `μ` times
a unit.

## Main definitions and results

* `New.Lift.Chart.IsPeriodMatrix`: period matrices `U` over `B⁺` of height `h`.
* `New.Lift.Chart.IsPeriodMatrix.exists_basis`: a basis `Q`, `Z` for `U`
  (`New.Lift.Chart.IsPeriodBasis`): the `x` over `A_inf` with `E ^ h x ∈ U S_B ^ d` are the `S`-span
  of the columns of a nonsingular matrix `Q`.
* `New.Lift.Chart.IsChartOf.exists_mem_bicommutant_of_fixed`: elements of `New.Period.Bmax` fixed by
  `Γ` come from `c.bicommutant`, an `S`-subalgebra of `New.Period.BPlus` in which `p` is invertible
  (defined as a commutant, `New.Lift.Chart.bicommutant`).
* `New.Lift.Chart.IsChartOf.exists_isPeriodMatrixOf`: if the Hodge–Tate jumps lie in `[-a, b]`, an
  invariant basis `M` gives the period matrix `(E τ) ^ a M` of height `a + b`
  (`New.Lift.Chart.IsPeriodMatrix`).

Notions from other files:
* `New.Period.mu`, `New.Period.tau`, `New.Period.xi`: The elements μ = [ε] − 1, τ = [ε^{1/p}] − 1
  and ξ = ∑_{i<p} [ε^{1/p}]^i of A_inf, with ξτ = μ; brackets denote Teichmüller lifts, and ε = (1,
  ζ_p, ζ_{p²}, …) is `New.Period.epsTilt`.
* `New.Lift.Chart.z`, `New.Lift.Chart.E`: For a chart, the images in S of X and of the series X^e
  A + p, A a unit of Λ[[X]]. Here Λ = `New.Lift.WittFq` = W(F_{p^f}).
* `New.Period.jump`: The multiplicity of an integer as a Hodge–Tate jump of ρ at an embedding.
* `New.Lift.Chart.IsChartOf`: The field of the chart contains the field fixed by the image of j:
  Γ → G_p: every g in G_p that fixes Λ pointwise and fixes θ(z) lies in the image of j.
* `New.Lift.Chart.extendToBPlus`: a chosen `S`-linear extension to `B⁺` of an `S`-linear map
  `A_inf → A_inf`; it maps `amaxImage` into itself.
* `New.Period.frobEnd`: the Frobenius endomorphism `φ` of the period rings.

## Relation to the literature

Known; see `Lib.PadicHodge.Kisin.PeriodMatrixFrame` for sources.
-/

/-!
## Lifting the exponent and bases for period matrices

Denominators are bounded uniformly: first in `A_max`, then in `A_inf` by
`New.Period.exists_Ainf_eq_of_contraction`.
-/

section PeriodMatrixBasis

namespace New.Lift

open Period Ainf BPlus Fintype RingHom Function Algebra Matrix Amax Fact Ideal

variable {p : ℕ} [ThePrime p] {d : Type}
  (c : Chart) [Fintype d] [DecidableEq d]
  (U : Matrix d d BPlus) (h : ℕ) (v : Ainfˣ)

@[simp]
lemma tau_ne_zero : tau ≠ 0 := ne_zero_of_map theta_tau_ne_zero

/-! ### Lifting the exponent -/

/-- If `x - 1` is not a unit of `A_inf` and `p ∤ m`, then `1 + x + ⋯ + x ^ (m - 1)` is a unit. -/
lemma isUnit_geom_sum {x : Ainf} {m : ℕ} (hx : ¬IsUnit (x - 1)) (hm : ¬p ∣ m) :
    IsUnit (∑ i ∈ Finset.range m, x ^ i) := by
  -- The sum is `m` modulo `x - 1`, and `A_inf` is `(x - 1)`-adically complete.
  have h_complete : IsAdicComplete (span {x - 1}) Ainf := isAdicComplete_span_singleton hx
  have hm_unit : IsUnit (m : Ainf) := by
    simp [Ainf.isUnit_iff_isUnit_constantCoeff, CharP.isUnit_natCast_iff (out : p.Prime), hm]
  have h_sum : x - 1 ∣ ∑ i ∈ .range m, x ^ i - m := by
    simpa using (Finset.range m).dvd_sum fun i _ ↦ sub_one_dvd_pow_sub_one x i
  exact isUnit_of_dvd_sub hm_unit h_sum

/-- Lifting the exponent. Let f: A_inf → R be a surjective ring map, v a non-unit dividing x − 1,
with p·f(x − 1)·f(v) dividing f(x − 1)^p. For n ≠ 0, f(x^n − 1) divides p^{v_p(n)} f(x − 1). -/
lemma lifting_the_exponent {R : Type*} [CommRing R] {f : Ainf →+* R} (hf : Surjective f)
    (x v : Ainf) {n : ℕ} (hv : ¬IsUnit v) (hvx : v ∣ x - 1)
    (h_dvd : p * f (x - 1) * f v ∣ f (x - 1) ^ p) (hn : n ≠ 0) :
    f (x ^ n - 1) ∣ p ^ padicValNat p n * f (x - 1) := by
  -- Write `n = n' * p ^ k` with `p ∤ n'` and `x ^ n' = 1 + (x - 1) * s`. Raising to the power
  -- `p ^ k` gives `f (x ^ n - 1) = p ^ k * f (x - 1) * f (s + v * y)`, and `s + v * y` is a unit.
  set s : Ainf := ∑ i ∈ .range (n.divMaxPow p), x ^ i with hs
  obtain ⟨y, hy⟩ : ∃ y : Ainf, (1 + f (x - 1) * f s) ^ p ^ padicValNat p n =
      1 + p ^ padicValNat p n * f (x - 1) * (f s + f v * f y) :=
    hf.exists.mp (ZMod.exists_one_add_mul_pow_prime_pow_eq out (map_dvd f hvx) h_dvd (f s) _)
  have hs_unit : IsUnit s := isUnit_geom_sum (fun h_unit ↦ hv (isUnit_of_dvd_unit hvx h_unit))
    (Nat.not_dvd_divMaxPow (out : p.Prime).one_lt hn)
  -- `A_inf` is `v`-adically complete, so an element congruent to a unit modulo `v` is a unit.
  have h_complete : IsAdicComplete (span {v}) Ainf := isAdicComplete_span_singleton hv
  have h_unit : IsUnit (s + v * y) := isUnit_of_dvd_sub hs_unit (by simp : v ∣ s + v * y - s)
  have h_geom : (x - 1) * s = x ^ n.divMaxPow p - 1 := by rw [hs, mul_geom_sum]
  have h_pow : x ^ n = (1 + (x - 1) * s) ^ p ^ padicValNat p n := by
    simp [h_geom, ← pow_mul, Nat.divMaxPow_mul_pow_padicValNat]
  have h_eq : f (x ^ n - 1) = p ^ padicValNat p n * f (x - 1) * f (s + v * y) := by
    calc f (x ^ n - 1) = (1 + f (x - 1) * f s) ^ p ^ padicValNat p n - 1 := by simp [h_pow]
      _ = p ^ padicValNat p n * f (x - 1) * f (s + v * y) := by
          rw [hy, add_sub_cancel_left, map_add f, map_mul f]
  rw [h_eq]
  exact (h_unit.map f).mul_right_dvd.mpr dvd_rfl

namespace Chart

/-- Let `b` be in `B⁺` and let `φ` be `frobEnd`. If `φ(τ) ^ n` divides `φ(b)`, then `τ ^ n` divides
`b`. The case `n = 1`: if `φ(τ)` divides `φ(a)`, then `θ(φ^j a) = 0` for all `j ≥ 1`, which gives
`τ ∣ a`. -/
lemma tau_pow_dvd_of_frobEnd_tau_pow_dvd {b : BPlus} {n : ℕ}
    (h_dvd : frobEnd (ainfToBPlus tau) ^ n ∣ frobEnd b) : ainfToBPlus tau ^ n ∣ b := by
  have h_mu : (mu : Ainf) ≠ 0 := ne_zero_of_map constantCoeff_mu_ne_zero
  have h_nzd : frobEnd (ainfToBPlus tau) ∈ nonZeroDivisors BPlus := by simp [h_mu]
  have h_one (a : BPlus) (h_dvd_one : frobEnd (ainfToBPlus tau) ∣ frobEnd a) :
      ainfToBPlus tau ∣ a := by
    obtain ⟨q, hq⟩ := h_dvd_one
    have h_theta : ∀ j : ℕ, thetaBPlus (frobEnd^[j + 1] a) = 0 := by simp [hq]
    exact a.dvd_of_thetaBPlus_frobEnd_eq_zero tau_dvd_of_theta_frobEnd h_theta
  exact pow_dvd_of_map (map_mul frobEnd _) h_nzd h_one h_dvd

/-- `E τ` and `μ` are associated in `A_inf`, as `E` is `ξ` up to a unit and `ξ τ = μ`. -/
lemma associated_E_mul_tau_mu : Associated (c.E * tau) mu := by
  rw [← xi_mul_tau]
  exact c.associated_E_xi.mul_right tau

/-- `E` is associated in `A_inf` to its translate `g E` by any `g` in `Gal(ℚ̄_p/ℚ_p)`. -/
lemma associated_smul_E (g : Gp p) : Associated c.E.val (g • c.E.val) := by
  -- `E` generates the kernel of `θ`, which every `g` preserves, so `E` divides each translate.
  have h_dvd (g : Gp p) : c.E.val ∣ g • c.E.val := by
    simp [c.associated_E_xi.dvd_iff_dvd_left, ← theta_eq_zero_iff_xi_dvd, theta_E]
  exact (associated_smul_of_dvd g h_dvd).symm

/-- For every `a`, the element `[ε] ^ p ^ a - 1 = φ^a μ` of `A_inf` is associated to the product
of `τ = [ε^{1/p}] - 1` and the `φ^b E = c.frobE b` for `b ≤ a`. Here `[ε]` is the Teichmüller lift
of `epsTilt`. -/
lemma associated_teichmuller_pow_p_pow_sub_one (a : ℕ) :
    Associated (WittVector.teichmuller p epsTilt ^ p ^ a - 1)
      (tau * ∏ b ∈ Finset.range (a + 1), (c.frobE b).val) := by
  -- `φ^b μ` is `φ^b τ · φ^b E` up to a unit, since `E τ` and `μ` are associated, and
  -- `φ^(b + 1) τ = φ^b μ`.
  have h_step (b : ℕ) : Associated (frobEnd^[b] mu) (frobEnd^[b] tau * (c.frobE b).val) := by
    have h_map := c.associated_E_mul_tau_mu.map (frobEnd ^ b : Ainf →+* Ainf)
    rw [map_mul, RingHom.coe_pow] at h_map
    rw [frobE, c.coe_phi_pow, mul_comm]
    exact h_map.symm
  rw [← map_pow, ← iterate_frobEnd_mu]
  induction a with
  | zero => simpa using h_step 0
  | succ a ih =>
    refine (h_step (a + 1)).trans ?_
    rw [Finset.prod_range_succ, ← mul_assoc, Function.iterate_succ_apply, frobEnd_tau]
    exact ih.mul_right _

/-- For a chart `c`, take `S` to be its ring inside `A_inf` and `φ` the Frobenius of `S`. The chart
is a Λ-algebra map Λ[[X]] → A_inf sending a series X^e A + p to `E`, which is ξ times a unit. Then
for `n ≠ 0`, the element `[ε] ^ n - 1` of `A_inf` is associated to the product of
`τ = [ε^{1/p}] - 1` with the `φ^a(E) = c.frobE a` for `a ≤ v_p(n)`, where `[ε]` is the Teichmüller
lift of `epsTilt`, ε = (1, ζ_p, ζ_{p²}, …) ∈ O^♭. -/
lemma associated_teichmuller_pow_sub_one {n : ℕ} (hn : n ≠ 0) :
    Associated (WittVector.teichmuller p epsTilt ^ n - 1)
      (tau * ∏ a ∈ Finset.range (padicValNat p n + 1), (c.frobE a).val) := by
  -- Write `n = m p ^ v` with `p ∤ m` and `x = [ε] ^ p ^ v`. Then `x ^ m - 1` is `x - 1` times the
  -- unit `1 + x + ⋯ + x ^ (m - 1)`.
  refine Associated.trans ?_ (c.associated_teichmuller_pow_p_pow_sub_one (padicValNat p n))
  set x : Ainf := WittVector.teichmuller p epsTilt ^ p ^ padicValNat p n with hx
  have h_theta : theta (x - 1) = 0 := by simp [hx, theta_teichmuller, untilt_epsTilt]
  have h_unit : IsUnit (∑ i ∈ .range (n.divMaxPow p), x ^ i) :=
    isUnit_geom_sum (fun h_unit ↦ (h_unit.map theta).ne_zero h_theta)
      (Nat.not_dvd_divMaxPow (out : p.Prime).one_lt hn)
  have h_pow : WittVector.teichmuller p epsTilt ^ n = x ^ n.divMaxPow p := by
    rw [hx, ← pow_mul, mul_comm, Nat.divMaxPow_mul_pow_padicValNat]
  rw [h_pow, ← mul_geom_sum]
  exact associated_mul_unit_left _ _ h_unit

/-- For `n ≠ 0`, the element `[ε] ^ n - 1` divides `τ E (p ^ v_p(n) + β z)` in `A_inf` for some
`β`. -/
lemma exists_tau_mul_E_eq_mul_epsTilt_pow_sub_one {n : ℕ} (hn : n ≠ 0) :
    ∃ α β : Ainf,
      tau * c.E * (p ^ padicValNat p n + β * c.z) = α * (.teichmuller p epsTilt ^ n - 1) := by
  -- `[ε] ^ n - 1` is `τ E` times the product of the `φ^a E`, `1 ≤ a ≤ v_p(n)`, up to a unit, and
  -- each `φ^a E` is `p` modulo `z`.
  obtain ⟨α, hα⟩ : WittVector.teichmuller p epsTilt ^ n - 1 ∣
      tau * ∏ a ∈ Finset.range (padicValNat p n + 1), (c.frobE a).val :=
    (c.associated_teichmuller_pow_sub_one hn).dvd
  have h_factor (a : ℕ) :
      Ideal.Quotient.mk (span {c.z.val}) (c.frobE a).val = Ideal.Quotient.mk (span {c.z.val}) p :=
    mk_span_eq_iff_dvd_sub.mpr (c.dvd_iff_coe_dvd.mp (c.z_dvd_frobE_sub_p a))
  obtain ⟨β, hβ⟩ : c.z.val ∣
      ∏ a ∈ Finset.range (padicValNat p n), (c.frobE (a + 1)).val - p ^ padicValNat p n := by
    rw [← mk_span_eq_iff_dvd_sub, map_prod, map_pow]
    simp only [h_factor, Finset.prod_const, Finset.card_range]
  rw [Finset.prod_range_succ', show (c.frobE 0).val = c.E by simp [frobE]] at hα
  exact ⟨α, β, by linear_combination hα - tau * c.E * hβ⟩

/-- `U` over `B⁺` is a period matrix of height `h`, with the unit `v` of `A_inf` as Frobenius
factor: `U` divides `(E τ) ^ h`; `φ(U) = v U F` with `F` over `S_B` and invertible over `B⁺`; every
`g` satisfying `c.FixesThetaZ` (`g` fixes Λ pointwise and fixes θ(z)) acts on `U` through matrices
over `A_inf`; and divisibility of `U y` by `E ^ h` is kept when `c.extendToBPlus f` is applied to
`y`. -/
structure IsPeriodMatrix where
  /-- `U` divides the scalar matrix `(E τ) ^ h` over `B⁺`; here `E τ` is `μ` up to a unit. -/
  exists_mul_eq_smul_one : ∃ W : Matrix d d BPlus, U * W = (c.E * tau) ^ h • 1
  /-- `φ(U) = v U F` for a matrix `F` with entries in `S_B` that has a left inverse over `B⁺`. -/
  exists_frob : ∃ F F' : Matrix d d BPlus,
    (∀ i j : d, F i j ∈ c.bicommutant) ∧ F' * F = 1 ∧ U.map frobEnd = v • (U * F)
  /-- If `g` satisfies `c.FixesThetaZ`, then `U = ρ g(U)` for a matrix `ρ` over `A_inf`. -/
  exists_gal (g : Gp p) :
    c.FixesThetaZ g → ∃ ρ : Matrix d d Ainf, Matrix.map ρ ainfToBPlus * g • U = U
  /-- If `E ^ h` divides `U y`, it divides `U y'`, where `y'` is `y` with the extension
  `c.extendToBPlus f` of an `S`-linear map `f` applied to each coordinate. -/
  extendToBPlus_stable (f : Ainf →ₗ[c.S] Ainf) (y : d → BPlus) :
      (∃ w : d → BPlus, U *ᵥ y = c.E.val ^ h • w) →
      ∃ w : d → BPlus, U *ᵥ c.extendToBPlus f ∘ y = c.E.val ^ h • w

/-- `E` is nonzero, being associated to the prime `ξ`. -/
lemma E_ne_zero : c.E.val ≠ 0 := (c.associated_E_xi.symm.prime prime_xi).ne_zero

/-- `E` is nonzero as an element of the subring `S`. -/
lemma E_ne_zero' : c.E ≠ 0 := fun h_E_zero ↦ c.E_ne_zero (congrArg Subtype.val h_E_zero)

/-- Let `f`, `f'` be `S`-linear maps `A_inf → A_inf` with `φ ∘ f' = f ∘ φ`, where `φ` is `frobEnd`.
Then the same holds for their extensions `c.extendToBPlus` to `B⁺`: the difference of the two
sides is additive, keeps `amaxImage` and vanishes on the image of `A_inf`. -/
lemma frobEnd_extendToBPlus_eq_extendToBPlus_frobEnd_of_comm {f f' : Ainf →ₗ[c.S] Ainf}
    (h_comm : ∀ a : Ainf, frobEnd (f' a) = f (frobEnd a)) (b : BPlus) :
    frobEnd (c.extendToBPlus f' b) = c.extendToBPlus f (frobEnd b) := by
  let G : BPlus →+ BPlus :=
    .mk' (fun a ↦ frobEnd (c.extendToBPlus f' a) - c.extendToBPlus f (frobEnd a))
      fun _ _ ↦ by simp [sub_add_sub_comm]
  have hG_int (a : BPlus) (ha : a ∈ amaxImage) : G a ∈ amaxImage := by
    apply_rules [sub_mem, extendToBPlus_mem_amaxImage, smul_mem_amaxImage]
  have hG_zero (a : Ainf) : G (ainfToBPlus a) = 0 := by simp [G, h_comm, extendToBPlus_ainfToBPlus]
  exact sub_eq_zero.mp (eq_zero_of_map_ainfToBPlus_eq_zero G hG_int hG_zero)

/-- Let `ψ` be a right inverse of `φ = frobEnd` on `A_inf`, and let `φ` be injective. For an
`S`-linear map `f` on `A_inf`, the map `ψ ∘ f ∘ φ` is again `S`-linear, since `φ` maps `S` into
itself. -/
private noncomputable def frobeniusConj (f : Ainf →ₗ[c.S] Ainf) {ψ : Ainf → Ainf}
    (φ_inj : Injective (frobEnd : Ainf → Ainf)) (hψ : ∀ a : Ainf, frobEnd (ψ a) = a) :
    Ainf →ₗ[c.S] Ainf where
  toFun := ψ ∘ f ∘ frobEnd
  map_add' a₁ a₂ := φ_inj (by simp [hψ])
  map_smul' s a := by
    have h_φ_coe : ((c.φ s : c.S) : Ainf) = frobEnd (s : Ainf) := rfl
    apply φ_inj
    simpa [smul_def, hψ, h_φ_coe] using f.map_smul' (c.φ s) (frobEnd a)

omit [DecidableEq d] in
/-- Let `e` divide `μ`. There is `k`, depending only on `U`, `h` and `e`, such that
`U y = e ^ h w` with `y` over the image of `A_max` puts `p ^ k w` over the image of `A_max`. -/
lemma exists_p_pow_mul_mem_amaxImage {e : Ainf} (he : e ∣ mu) :
    ∃ k : ℕ, ∀ {y w : d → BPlus}, U *ᵥ y = e ^ h • w →
      (∀ i : d, y i ∈ amaxImage) → ∀ i : d, p ^ k * w i ∈ amaxImage := by
  -- `p ^ k` clears the denominators of `U`; `amaxImage.p_pow_mul_mem_of_dvd_mu` then removes
  -- `e ^ h` at the cost of a further factor `p ^ (2 * h)`.
  obtain ⟨⟨_, k, rfl⟩, hk⟩ : ∃ b : Submonoid.powers (p : Amax), ∀ ij : d × d,
      IsLocalization.IsInteger Amax ((b : Amax) • U.uncurry ij) :=
    IsLocalization.exist_integer_multiples_of_finite (.powers (p : Amax)) U.uncurry
  refine ⟨2 * h + k, fun {y w} h_Uy hy i ↦ ?_⟩
  have h_U_int (j : d) : (p : BPlus) ^ k * U i j ∈ amaxImage :=
    (hk (i, j)).imp fun a ha ↦ by simpa [Algebra.smul_def, uncurry] using ha
  have h_int : e ^ h • (p ^ k * w i) ∈ amaxImage := by
    rw [← mul_smul_comm, ← Pi.smul_apply, ← h_Uy, mulVec, dotProduct, Finset.mul_sum]
    exact sum_mem fun j _ ↦ by simpa [mul_assoc] using mul_mem (h_U_int j) (hy j)
  simpa [pow_add, mul_assoc] using amaxImage.p_pow_mul_mem_of_dvd_mu he h_int

variable {c U h v}

/-- Let `W` invert `U` up to `(E τ) ^ h`, let `F'` be a left inverse of `F`, and suppose that
`U a = r x'` implies `F φ(a) = φ(r) y` for every `r` in `A_inf` and `a` over `B⁺`, where `φ` is
`frobEnd`. Then `U y' = E ^ h x'` has a solution `y'` over `B⁺`: `φ (W x')` is divisible by
`φ(τ) ^ h`, hence `W x'` by `τ ^ h` (`tau_pow_dvd_of_frobEnd_tau_pow_dvd`), and
`y' = τ ^ (-h) W x'`. -/
lemma exists_mulVec_eq_smul_of_frobEnd {W F F' : Matrix d d BPlus} {x' : d → Ainf}
    {y : d → BPlus} (hW : ∀ x : d → BPlus, U *ᵥ W *ᵥ x = (c.E * tau) ^ h • x) (hF' : F' * F = 1)
    (h_frob : ∀ {r : Ainf} {a : d → BPlus}, U *ᵥ a = r • ainfToBPlus ∘ x' →
      F *ᵥ frobEnd ∘ a = frobEnd (ainfToBPlus r) • y) :
    ∃ y' : d → BPlus, U *ᵥ y' = c.E.val ^ h • ainfToBPlus ∘ x' := by
  have h_dvd (i : d) : ∃ q : BPlus, (W *ᵥ ainfToBPlus ∘ x') i = ainfToBPlus tau ^ h * q := by
    -- apply `F'` to `F φ(W x') = φ(E τ) ^ h y`
    have h_phi : frobEnd ((W *ᵥ ainfToBPlus ∘ x') i) =
        frobEnd (ainfToBPlus tau) ^ h * (frobEnd (ainfToBPlus c.E.val) ^ h * (F' *ᵥ y) i) := by
      simpa [hF', mul_left_comm, mulVec_smul, mul_pow, mul_assoc] using
        congrArg (fun a : d → BPlus ↦ (F' *ᵥ a) i) (h_frob (hW _))
    exact tau_pow_dvd_of_frobEnd_tau_pow_dvd ⟨_, h_phi⟩
  choose y' hy' using h_dvd
  have h_U_vec : ainfToBPlus tau ^ h • U *ᵥ y' = U *ᵥ W *ᵥ ainfToBPlus ∘ x' := by
    rw [← mulVec_smul, funext hy']
    rfl
  refine ⟨y', ?_⟩
  simpa [hW, smul_def, mul_left_comm, funext_iff, mulVec_smul, mul_pow, mul_assoc] using h_U_vec

omit [DecidableEq d] in
/-- Let `P` be an `S`-submodule of `A_inf ^ d` whose members `j` have vectors `y j` over `S_B`
with the same `A_inf`-linear relations as the `j`. Then the rank of `P` over `S` is at most `d`:
the coordinates `c.extendedCoord i` turn an `A_inf`-relation among members of `P` into
`S`-relations. -/
lemma rank_le_card_of_sum_smul_eq_zero_iff {P : Submodule c.S (d → Ainf)}
    (y : P → d → c.bicommutant)
    (h_rel : ∀ {b : Finset P} {a : b → Ainf},
      ∑ j : b, a j • Subtype.val ∘ y j = 0 ↔ ∑ j : b, a j • ((j : P) : d → Ainf) = 0) :
    Module.rank c.S P ≤ card d := by
  refine rank_le fun b hb ↦ ?_
  have hb' : LinearIndependent Ainf fun j : b ↦ ((j : P) : d → Ainf) := by
    refine linearIndependent_iff.mpr fun a ha j ↦ c.adicBasis.eq_zero_of_coord fun i ↦ ?_
    refine linearIndependent_iff.mp hb (fun j ↦ c.adicBasis.coord i (a j)) ?_ j
    ext1
    have h_rel_coord :
        ∑ j : b, (c.adicBasis.coord i (a j) : Ainf) • Subtype.val ∘ y j = 0 := by
      simpa [smul_def, mul_comm, funext_iff, extendToBPlus_mul, extendToBPlus_ainfToBPlus] using
        congrArg (c.extendedCoord i ∘ ·) (h_rel.mpr ha)
    simpa [Subalgebra.smul_def] using h_rel.mp h_rel_coord
  rw [← card_coe, ← Module.finrank_fintype_fun_eq_card Ainf (η := d)]
  exact hb'.fintype_card_le_finrank

/-- `Q` over `A_inf` and `Z` over `B⁺` form a basis for the period matrix `U` of height `h`: `Q` is
nonsingular, `Z` lies over `c.bicommutant` with `U Z = E ^ h Q`, the columns of `Q` span the `x`
that have solutions over `c.bicommutant`, and `Q` controls divisibility for solutions over `B⁺`. -/
structure IsPeriodBasis (c : Chart) (U : Matrix d d BPlus) (h : ℕ) (Q : Matrix d d Ainf)
    (Z : Matrix d d BPlus) : Prop where
  /-- `Q` is nonsingular. -/
  det_ne_zero : Q.det ≠ 0
  /-- The entries of `Z` lie in `c.bicommutant`. -/
  mem_bicommutant : ∀ i j : d, Z i j ∈ c.bicommutant
  /-- `U Z = E ^ h Q` over `B⁺`. -/
  mul_eq : U * Z = c.E.val ^ h • Q.map ainfToBPlus
  /-- Every `x` over `A_inf` with `U y = E ^ h x` for some `y` over `c.bicommutant` is `Q s` with
  `s` over `c.S`. -/
  exists_mulVec_eq : ∀ (x : d → Ainf) (y : d → BPlus), (∀ i : d, y i ∈ c.bicommutant) →
    U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x → ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x
  /-- If `U y = E ^ h x` with `y` over `B⁺`, `p ∤ δ` and `l Q = δ g`, then `δ` divides `l · x`. -/
  dvd_dotProduct : ∀ (x : d → Ainf) (y : d → BPlus), U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
    ∀ (δ : Ainf) (l g : d → Ainf), ¬↑p ∣ δ → l ᵥ* Q = δ • g → δ ∣ l ⬝ᵥ x

namespace IsPeriodMatrix

/-- A period matrix acts injectively on vectors over `B⁺`, since `U W` is a nonzero scalar
matrix. -/
lemma mulVec_injective (hU : c.IsPeriodMatrix U h v) : Injective U.mulVec := by
  obtain ⟨W, hW⟩ := hU.exists_mul_eq_smul_one
  refine mulVec_injective_of_det_ne_zero fun h_det ↦ ?_
  have h_det_eq : ((c.E * tau) ^ h • (1 : Matrix d d BPlus)).det = 0 := by
    rw [← hW, det_mul, h_det, zero_mul]
  simp [smul_def (A := BPlus), c.E_ne_zero'] at h_det_eq

/-- The field `exists_mul_eq_smul_one` read on vectors: there is a matrix `W` over `B⁺` with
`U (W x) = (E τ) ^ h x` for every vector `x`. -/
lemma exists_mulVec_mulVec_eq_smul (hU : c.IsPeriodMatrix U h v) :
    ∃ W : Matrix d d BPlus, ∀ x : d → BPlus, U *ᵥ W *ᵥ x = (c.E * tau) ^ h • x := by
  obtain ⟨W, hW⟩ := hU.exists_mul_eq_smul_one
  exact ⟨W, fun x ↦ by rw [mulVec_mulVec, hW, smul_mulVec, one_mulVec]⟩

/-- A single power `p ^ m` puts every vector `w` with `U (c.extendToBPlus f ∘ y) = E ^ h w` into
`amaxImage`, where `y` over `B⁺` runs through the solutions of `U y = E ^ h x` with `x` over
`A_inf`, and `f` through the `S`-linear maps `A_inf → A_inf`. -/
lemma exists_pow_mul_mem_amaxImage (hU : c.IsPeriodMatrix U h v) :
    ∃ m : ℕ, ∀ {x : d → Ainf} {y w : d → BPlus} {f : Ainf →ₗ[c.S] Ainf},
      U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
      U *ᵥ c.extendToBPlus f ∘ y = c.E.val ^ h • w →
      ∀ i : d, p ^ m * w i ∈ amaxImage := by
  obtain ⟨W, hW⟩ : ∃ W : Matrix d d BPlus, ∀ x : d → BPlus, U *ᵥ W *ᵥ x = (c.E * tau) ^ h • x :=
    hU.exists_mulVec_mulVec_eq_smul
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ {y w : d → BPlus}, W *ᵥ y = (c.E * tau) ^ h • w →
      (∀ i : d, y i ∈ amaxImage) → ∀ i : d, p ^ n * w i ∈ amaxImage :=
    exists_p_pow_mul_mem_amaxImage W h c.associated_E_mul_tau_mu.dvd
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ {y w : d → BPlus}, U *ᵥ y = c.E.val ^ h • w →
      (∀ i : d, y i ∈ amaxImage) → ∀ i : d, p ^ k * w i ∈ amaxImage :=
    exists_p_pow_mul_mem_amaxImage U h (dvd_of_mul_right_dvd c.associated_E_mul_tau_mu.dvd)
  refine ⟨k + n, fun {x y w f} hy hw i ↦ ?_⟩
  -- `W` inverts `U` up to `(E τ) ^ h`, so `p ^ n y` is integral; `c.extendToBPlus f` preserves
  -- `amaxImage`
  have hWU : W *ᵥ U *ᵥ y = (c.E * tau) ^ h • y := hU.mulVec_injective (by rw [hW, mulVec_smul])
  -- the entries of `U y = E ^ h x` lie in `amaxImage`
  have hUy_int : ∀ j : d, (U *ᵥ y) j ∈ amaxImage := by aesop
  have h_eq : U *ᵥ (p ^ n • c.extendToBPlus f ∘ y) = c.E.val ^ h • p ^ n • w := by
    rw [smul_comm, ← hw, ← mulVec_smul]
  have h_hat_int (j : d) : (p ^ n • c.extendToBPlus f ∘ y) j ∈ amaxImage := by
    simpa [map_p_pow_mul] using c.extendToBPlus_mem_amaxImage f _ (hn hWU hUy_int j)
  simpa [pow_add, mul_assoc] using hk h_eq h_hat_int i

/-- Descent along Frobenius. Let `U` be a period matrix of height `h` with Frobenius factor `v` for
the chart `c` (`IsPeriodMatrix`), and let `f` be a `c.S`-linear map of `A_inf`. Suppose
`U y = E ^ h x` with `x` over `A_inf`, and `U (c.extendToBPlus f ∘ y) = E ^ h w`. Then there are
`x'`, `y'`, `w'`, `f'` satisfying the same two equations with `φ w' = v E ^ h w`, where `φ` is
`frobEnd`. The proof takes `x' = φ⁻¹ (v E ^ h x)` and `f' = φ⁻¹ f φ`. -/
lemma exists_frobenius_preimage (hU : c.IsPeriodMatrix U h v) {x : d → Ainf} {y w : d → BPlus}
    {f : Ainf →ₗ[c.S] Ainf} (hy : U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x)
    (hw : U *ᵥ c.extendToBPlus f ∘ y = c.E.val ^ h • w) :
    ∃ (x' : d → Ainf) (y' w' : d → BPlus) (f' : Ainf →ₗ[c.S] Ainf),
      U *ᵥ y' = c.E.val ^ h • ainfToBPlus ∘ x' ∧
      U *ᵥ c.extendToBPlus f' ∘ y' = c.E.val ^ h • w' ∧
      ∀ i : d, frobEnd (w' i) = (v * c.E.val ^ h) • w i := by
  -- Solve `U y' = E ^ h x'` by `y' = τ ^ (-h) W x'`, which lies over `B⁺` because `φ (W x')` is
  -- divisible by `φ(τ) ^ h`; then apply `φ` to the equation of `w'` and cancel `φ(E) ^ h`.
  obtain ⟨W, hW⟩ := hU.exists_mulVec_mulVec_eq_smul
  obtain ⟨F, F', hF, hF', hUF⟩ := hU.exists_frob
  have φ_inj : Injective (frobEnd : Ainf → Ainf) := frobEnd_bijective.injective
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ainf → Ainf, ∀ a : Ainf, frobEnd (ψ a) = a :=
    frobEnd_bijective.surjective.hasRightInverse
  let x' : d → Ainf := ψ ∘ (v • c.E.val ^ h • x)
  -- apply `φ` to `U a = r x'` and use `φ U = v U F`
  have h_frob {r : Ainf} {a : d → BPlus} (ha : U *ᵥ a = r • ainfToBPlus ∘ x') :
      F *ᵥ frobEnd ∘ a = frobEnd (ainfToBPlus r) • y := by
    have h_map : U.map frobEnd *ᵥ frobEnd ∘ a =
        frobEnd (ainfToBPlus r) • frobEnd ∘ ainfToBPlus ∘ x' := by
      simpa [map_mulVec, funext_iff, smul_def (A := BPlus)] using congrArg (frobEnd ∘ ·) ha
    have h_x' : frobEnd ∘ ainfToBPlus ∘ x' = ((v : Ainf) * c.E.val ^ h) • ainfToBPlus ∘ x :=
      funext fun i ↦ by simp [x', hψ, smul_def (A := BPlus), Units.smul_def, mul_assoc]
    -- cancel `v` in `v U F φ(a) = φ(r) v E ^ h x = φ(r) v U y`
    apply hU.mulVec_injective
    simpa [hUF, h_x', hy, smul_mulVec, ← mulVec_mulVec, mulVec_smul, Units.smul_def,
      smul_def (A := BPlus), mul_assoc, mul_left_comm, funext_iff] using h_map
  obtain ⟨y', hUy'⟩ : ∃ y' : d → BPlus, U *ᵥ y' = c.E.val ^ h • ainfToBPlus ∘ x' :=
    exists_mulVec_eq_smul_of_frobEnd hW hF' h_frob
  let f' : Ainf →ₗ[c.S] Ainf := frobeniusConj c f φ_inj hψ
  obtain ⟨w', hw'⟩ := hU.extendToBPlus_stable f' y' ⟨_, hUy'⟩
  refine ⟨x', y', w', f', hUy', hw', fun i ↦ ?_⟩
  -- `φ f' = f φ` on `A_inf`, hence on `B⁺` for the extensions
  have h_comm : frobEnd ∘ c.extendToBPlus f' ∘ y' = c.extendToBPlus f ∘ frobEnd ∘ y' :=
    funext fun j ↦ c.frobEnd_extendToBPlus_eq_extendToBPlus_frobEnd_of_comm (fun _ ↦ hψ _) (y' j)
  -- `c.extendToBPlus f` is linear over `c.bicommutant`, which contains the entries of `F` and `φ E`
  have h_hat : F *ᵥ c.extendToBPlus f ∘ frobEnd ∘ y' =
      frobEnd (ainfToBPlus (c.E.val ^ h)) • c.extendToBPlus f ∘ y := by
    have h_φE_mem : ainfToBPlus (frobEnd c.E.val) ^ h ∈ c.bicommutant := by
      simpa using pow_mem (c.frobEnd_mem_bicommutant (c.ainfToBPlus_mem_bicommutant c.E)) h
    simpa [mulVec, dotProduct, hF, h_φE_mem, funext_iff, extendToBPlus_mul] using
      congrArg (c.extendToBPlus f ∘ ·) (h_frob hUy')
  -- apply `φ` to the equation of `w'` and cancel `φ(E) ^ h`, which is nonzero
  have h_φE_ne : frobEnd (ainfToBPlus c.E.val) ^ h ≠ 0 := by
    simp [map_eq_zero_iff _ φ_inj, c.E_ne_zero']
  refine mul_left_cancel₀ h_φE_ne ?_
  calc frobEnd (ainfToBPlus c.E.val) ^ h * frobEnd (w' i)
      = frobEnd ((c.E.val ^ h • w') i) := by simp [smul_def (A := BPlus)]
    _ = (v • U *ᵥ frobEnd (ainfToBPlus (c.E.val ^ h)) • c.extendToBPlus f ∘ y) i := by
      rw [← hw', map_mulVec, h_comm, hUF, smul_mulVec, ← mulVec_mulVec, h_hat]
    _ = frobEnd (ainfToBPlus c.E.val) ^ h * (v * c.E.val ^ h) • w i := by
      simp [hw, mulVec_smul, Units.smul_def, smul_def (A := BPlus), mul_left_comm, mul_assoc]

/-- Let `U` be a period matrix of height `h` with Frobenius factor `v` for the chart `c`
(`IsPeriodMatrix`). A single power `p ^ N` puts into the image of `A_inf` every vector `w` with
`U (c.extendToBPlus f ∘ y) = E ^ h w`, for every `c.S`-linear map `f` of `A_inf` and every `y` over
`BPlus` with `U y = E ^ h x`, `x` over `A_inf`. These vectors lie in `amaxImage` after one power of
`p` and are closed under descent along Frobenius, so `exists_Ainf_eq_of_contraction` applies. -/
lemma exists_ainfToBPlus_eq_pow_mul (hU : c.IsPeriodMatrix U h v) :
    ∃ N : ℕ, ∀ {x : d → Ainf} {y w : d → BPlus} {f : Ainf →ₗ[c.S] Ainf},
      U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
      U *ᵥ c.extendToBPlus f ∘ y = c.E.val ^ h • w →
      ∃ a : d → Ainf, ∀ i : d, ainfToBPlus (a i) = p ^ N * w i := by
  obtain ⟨m, hm⟩ := hU.exists_pow_mul_mem_amaxImage
  obtain ⟨η, hη⟩ : c.E.val ∣ xi := c.associated_E_xi.dvd
  -- `exists_Ainf_eq_of_contraction`: if `V` lies in `amaxImage` and each `a ∈ V` has
  -- `ξ ^ h a = u φ a'` with `a' ∈ V` and a fixed `u`, then `p ^ (h + 1) V` lies over `Ainf`
  let V : Set BPlus := {a | ∃ (x : d → Ainf) (y w : d → BPlus) (f : Ainf →ₗ[c.S] Ainf) (i : d),
    U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x ∧ U *ᵥ c.extendToBPlus f ∘ y = c.E.val ^ h • w ∧
      p ^ m * w i = a}
  have hV_int : ∀ a ∈ V, a ∈ amaxImage := by
    rintro _ ⟨x, y, w, f, i, hy, hw, rfl⟩
    exact hm hy hw i
  have hV_desc : ∀ a ∈ V, ∃ a' ∈ V, xi ^ h • a = (η ^ h * ↑v⁻¹ : Ainf) • frobEnd a' := by
    rintro _ ⟨x, y, w, f, i, hy, hw, rfl⟩
    obtain ⟨x', y', w', f', hy', hw', hφ⟩ := hU.exists_frobenius_preimage hy hw
    refine ⟨p ^ m * w' i, ⟨x', y', w', f', i, hy', hw', rfl⟩, ?_⟩
    -- `φ w' = v E ^ h w` and `ξ = E η`
    simp [hφ, hη, smul_smul, mul_comm _ η, mul_pow, mul_assoc]
  refine ⟨h + 1 + m, fun {x y w f} hy hw ↦ ?_⟩
  have h_lift (i : d) : ∃ a : Ainf, ainfToBPlus a = p ^ (h + 1) * (p ^ m * w i) :=
    exists_Ainf_eq_of_contraction V h _ hV_int hV_desc _ ⟨x, y, w, f, i, hy, hw, rfl⟩
  choose a ha using h_lift
  exact ⟨a, fun i ↦ by rw [ha, pow_add _ _ m, mul_assoc]⟩

/-- Let `U` over `B⁺` be a period matrix of height `h` with Frobenius factor `v`. The `x` over
`A_inf` for which `U y = E ^ h x` has a solution `y` with entries in `S_B` (`c.bicommutant`, the
closure of `S[E/p]` in `B⁺` with `p` inverted) form an `S`-module spanned by the columns of a square
matrix `Q` over `A_inf`; moreover `U Z = E ^ h Q` for a matrix `Z` with entries in `S_B`. -/
lemma exists_spanning_matrix (hU : c.IsPeriodMatrix U h v) :
    ∃ (Q : Matrix d d Ainf) (Z : Matrix d d BPlus),
      (∀ i j : d, Z i j ∈ c.bicommutant) ∧
      U * Z = c.E.val ^ h • Q.map ainfToBPlus ∧
      ∀ (x : d → Ainf) (y : d → BPlus),
        (∀ i : d, y i ∈ c.bicommutant) →
        U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
        ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x := by
  obtain ⟨u, hu, hup⟩ : ∃ u ∈ c.bicommutant, u * p = 1 := c.exists_bicommutant_mul_p_eq_one
  let g : (d → Ainf) →ₗ[Ainf] d → BPlus := c.E.val ^ h • (Algebra.linearMap Ainf BPlus).compLeft d
  let P : Submodule c.S (d → Ainf) :=
    (mulVecBilin ℕ _ U ∘ₗ c.bicommutant.val.toLinearMap.compLeft d).range.comap
      (g.restrictScalars _)
  -- each member `j` of `P` has a solution `y j` over `S_B` of `U (y j) = E ^ h j`
  have h_sol : ∀ j : P, ∃ y : d → c.bicommutant, U *ᵥ Subtype.val ∘ y = g j := P.coe_mem
  choose y hy using h_sol
  -- members of `P` and their solutions `y` have the same `Ainf`-relations
  have h_rel {b : Finset P} {a : b → Ainf} :
      ∑ j : b, a j • Subtype.val ∘ y j = 0 ↔ ∑ j : b, a j • ((j : P) : d → Ainf) = 0 := by
    have hg : Injective g := fun a₁ a₂ ↦ by simp [g, smul_def, funext_iff, c.E_ne_zero']
    rw [← hU.mulVec_injective.eq_iff, ← g.map_eq_zero_iff hg]
    simp [hy, mulVec_sum, mulVec_smul]
  -- the coordinates `c.extendedCoord i` bound the rank of `P` by `card d`
  have h_rank : Module.rank c.S P ≤ card d := rank_le_card_of_sum_smul_eq_zero_iff y h_rel
  -- `z` is injective on `P / p P`: in `Ainf` the prime `p` does not divide `z`, and `P` is
  -- `p`-saturated because `p` is a unit of `c.bicommutant`
  have h_sat (a b : P) (hab : c.z • a.val = (p : c.S) • b.val) :
      ∃ w : P, a.val = (p : c.S) • w.val := by
    obtain ⟨x, hx_mem⟩ := a
    obtain ⟨y₀, hx⟩ : ∃ y₀ : d → c.bicommutant, U *ᵥ Subtype.val ∘ y₀ = g x := hx_mem
    have h_entry (i : d) : (c.z : Ainf) * x i = p * (b : d → Ainf) i := congrFun hab i
    obtain ⟨w, rfl⟩ : (p : d → Ainf) ∣ x :=
      pi_dvd_iff.mpr fun i ↦ (prime_p.dvd_or_dvd ⟨_, h_entry i⟩).resolve_left c.not_p_dvd_z
    refine ⟨⟨w, fun i ↦ ⟨u, hu⟩ * y₀ i, ?_⟩, rfl⟩
    -- `u` inverts `p` in `S_B`, so `u y₀` solves the equation for `w`
    show U *ᵥ (u • Subtype.val ∘ y₀) = g w
    rw [mulVec_smul, hx, ← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul BPlus, smul_smul, hup,
      one_smul]
  -- `P` is also `(p, z)`-adically separated, `p`-torsion free and of bounded rank, hence free
  -- over the complete ring `c.S`
  have h_sat_P (a b : P) (hab : c.z • a = (p : c.S) • b) : ∃ w : P, a = (p : c.S) • w :=
    (h_sat a b (congrArg Subtype.val hab)).imp fun _ hw ↦ Subtype.ext hw
  have h_torsion : ∀ a : P, (p : c.S) • a = 0 → (p : c.S) = 0 ∨ a = 0 := by simp
  obtain ⟨⟨κ, b⟩, -⟩ : Module.Free c.S P ∧ Module.Finite c.S P :=
    free_finite_of_rank_le rfl
      (isHausdorff_of_injective_pi c.maxIdeal P.subtype P.injective_subtype)
      h_sat_P (card d) h_rank h_torsion
  -- pad the basis `b` of `P` to a family `q` indexed by `d`
  obtain ⟨e⟩ : Nonempty (κ ↪ d) := by
    rwa [← Cardinal.le_def, b.mk_eq_rank'', Cardinal.mk_fintype]
  obtain ⟨q, hq⟩ : ∃ q : d → P, q ∘ e = b := e.injective.surjective_comp_right b
  have hZ_mem : ∀ i j : d, (of fun j i ↦ (y (q j) i).val)ᵀ i j ∈ c.bicommutant := by simp
  refine ⟨(of fun j ↦ (q j).val)ᵀ, (of fun j i ↦ (y (q j) i).val)ᵀ, hZ_mem,
    ext_col fun j ↦ hy (q j), fun x y₀ hy₀ hx ↦ ?_⟩
  -- the basis `b = q ∘ e` spans `P`, so the columns `q` do
  have h_span_b : ⟨x, fun i : d ↦ ⟨y₀ i, hy₀ i⟩, hx⟩ ∈ Submodule.span c.S (Set.range (q ∘ e)) := by
    simp [hq]
  have h_span : ⟨x, fun i : d ↦ ⟨y₀ i, hy₀ i⟩, hx⟩ ∈ Submodule.span c.S (Set.range q) :=
    Submodule.span_mono (Set.range_comp_subset_range e q) h_span_b
  obtain ⟨s, hs⟩ : ∃ s : d → c.S, ∑ i : d, s i • q i = ⟨x, fun i : d ↦ ⟨y₀ i, hy₀ i⟩, hx⟩ :=
  (Submodule.mem_span_range_iff_exists_fun _).mp h_span
  have h_vals : ∑ i : d, s i • ((q i : P) : d → Ainf) = x := by
    simpa using congrArg Subtype.val hs
  refine ⟨s, funext fun k ↦ ?_⟩
  simpa [mulVec, dotProduct, Finset.sum_apply, Subalgebra.smul_def, mul_comm] using
    congrFun h_vals k

omit [DecidableEq d] in
/-- If `p` does not divide `δ`, then `δ ∣ l · (p ^ n x)` gives `δ ∣ l · x`. -/
private lemma dvd_dotProduct_of_dvd_dotProduct_pow_smul {δ : Ainf} (hδ : ¬(p : Ainf) ∣ δ)
    (l x : d → Ainf) (n : ℕ) (h_dvd : δ ∣ l ⬝ᵥ p ^ n • x) : δ ∣ l ⬝ᵥ x := by
  rw [dotProduct_smul, nsmul_eq_mul, Nat.cast_pow] at h_dvd
  exact dvd_of_dvd_prime_pow_mul prime_p hδ h_dvd

/-- The approximation step of `dvd_dotProduct_of_spanning`. Let `U` be a period matrix of height `h`
with Frobenius factor `v` for `c` (`IsPeriodMatrix`). Let `Q` over `A_inf` be such that every `x`
with `U y = E ^ h x` for some `y` over `S_B = c.bicommutant` equals `Q s` with `s` over `c.S`. Let
`U y = E ^ h x` with `x` over `A_inf` and `y` over `BPlus`, and let `l Q = δ g` over `A_inf`. Then
for some `N` and every `m`, some `z` has `l · (p ^ N x) - δ z` in the ideal `(p, ξ) ^ m` of
`A_inf`. -/
lemma exists_dotProduct_pow_smul_sub_mul_mem_span_pow (hU : c.IsPeriodMatrix U h v)
    {Q : Matrix d d Ainf}
    (hQ : ∀ (x : d → Ainf) (y : d → BPlus),
      (∀ i : d, y i ∈ c.bicommutant) →
      U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
      ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x)
    (x : d → Ainf) (y : d → BPlus) (hy : U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x) (δ : Ainf)
    (l g : d → Ainf) (hl : l ᵥ* Q = δ • g) :
    ∃ N : ℕ, ∀ m : ℕ, ∃ z : Ainf, l ⬝ᵥ p ^ N • x - δ * z ∈ span {(p : Ainf), xi} ^ m := by
  classical
  obtain ⟨u, -, hup⟩ := c.exists_bicommutant_mul_p_eq_one
  obtain ⟨N, hN⟩ := hU.exists_ainfToBPlus_eq_pow_mul
  obtain ⟨k, hk⟩ :=
    exists_p_pow_mul_mem_amaxImage U h (dvd_of_mul_right_dvd c.associated_E_mul_tau_mu.dvd)
  refine ⟨N, fun m ↦ ?_⟩
  -- the vectors `x' i = p ^ N E ^ (-h) U (c.extendedCoord i ∘ y)` lie over `Ainf`, and in `Q S ^ d`
  have h_stable : ∀ i : c.adicBasis.Index,
      ∃ w : d → BPlus, U *ᵥ c.extendedCoord i ∘ y = c.E.val ^ h • w :=
    fun i ↦ hU.extendToBPlus_stable _ y ⟨ainfToBPlus ∘ x, hy⟩
  choose w hw using h_stable
  have h_int : ∀ i : c.adicBasis.Index,
      ∃ a : d → Ainf, ∀ j : d, ainfToBPlus (a j) = p ^ N * w i j :=
    fun i ↦ hN hy (hw i)
  choose x' hx' using h_int
  have hx'_eq (i : c.adicBasis.Index) :
      U *ᵥ (p ^ N • c.extendedCoord i ∘ y) = c.E.val ^ h • ainfToBPlus ∘ x' i := by
    have h_vec : p ^ N • w i = ainfToBPlus ∘ x' i := funext fun j ↦ by simp [hx']
    rw [mulVec_smul, hw, smul_comm, h_vec]
  have h_span : ∀ i : c.adicBasis.Index, ∃ s : d → c.S, Q *ᵥ Subtype.val ∘ s = x' i :=
    fun i ↦ hQ (x' i) _ (fun _ ↦ nsmul_mem (c.extendedCoord_mem_bicommutant i _) _) (hx'_eq i)
  choose s hs using h_span
  -- expand `y` in the topological basis up to `p ^ (m + k)`
  obtain ⟨G, hG⟩ : ∃ G : Finset c.adicBasis.Index, ∀ i : d, ∃ r ∈ amaxImage,
      y i - ∑ j ∈ G, c.adicBasis.b j • c.extendedCoord j (y i) = p ^ (m + k) * r :=
    (Filter.eventually_all.mpr fun j ↦ c.eventually_approx_sum_extendedCoord (y j) (m + k)).exists
  choose r hr hyr using hG
  refine ⟨g ⬝ᵥ ∑ j ∈ G, c.adicBasis.b j • Subtype.val ∘ s j, ?_⟩
  -- as `δ g = l Q`, the difference is `l · t` for the error vector `t`
  rw [← smul_eq_mul, ← smul_dotProduct, ← hl, ← dotProduct_mulVec, ← dotProduct_sub]
  set t : d → Ainf := p ^ N • x - Q *ᵥ ∑ j ∈ G, c.adicBasis.b j • Subtype.val ∘ s j with ht
  show l ⬝ᵥ t ∈ span {(p : Ainf), xi} ^ m
  -- the error `t`, divided by `p ^ (m + k)`, has an integral solution; `hk` loses `p ^ k`, so
  -- `p ^ m` divides `t` in `Amax`, which puts `t` in `(p, ξ) ^ m` (`mem_span_pow_of_p_pow_dvd`)
  have h_error :
      U *ᵥ (p ^ N • u ^ (m + k) • (y - ∑ j ∈ G, c.adicBasis.b j • c.extendedCoord j ∘ y)) =
        c.E.val ^ h • u ^ (m + k) • ainfToBPlus ∘ t := by
    rw [mulVec_smul, mulVec_smul, mulVec_sub]
    simp [ht, hy, hw, hx', hs, G.mul_sum, G.smul_sum, smul_comm (c.E.val ^ h), ← smul_def,
      mulVec_smul, mulVec_sum, smul_sub, funext_iff]
  -- entry by entry, it suffices that `p ^ m` divides `t i` in `Amax`
  refine sum_mem fun i _ ↦ mul_mem_left _ _ (mem_span_pow_of_p_pow_dvd ?_)
  have h_mem (j : d) :
      (u ^ (m + k) • (y - ∑ i ∈ G, c.adicBasis.b i • c.extendedCoord i ∘ y)) j ∈ amaxImage := by
    simp [hyr, hr, hup, ← mul_assoc, ← mul_pow]
  obtain ⟨a, ha⟩ : p ^ k * (u ^ (m + k) • ainfToBPlus ∘ t) i ∈ amaxImage :=
    hk h_error (fun j ↦ nsmul_mem (h_mem j) _) i
  -- multiply `ha` by `p ^ m`: as `u p = 1`, the image of `p ^ m a` in `B⁺` is that of `t i`
  have h_t : ainfToBPlus (t i) =
      (p : BPlus) ^ m * (IsScalarTower.toAlgHom Ainf Amax BPlus).toRingHom a := by
    rw [ha]
    simp [← pow_add, ← mul_assoc, ← mul_pow, hup, mul_comm _ u]
  refine ⟨a, injective_Amax_BPlus ?_⟩
  show ainfToBPlus (t i) = (IsScalarTower.toAlgHom Ainf Amax BPlus).toRingHom ((p : Amax) ^ m * a)
  rwa [map_mul, map_pow, map_natCast]

/-- Let `U` be a period matrix of height `h` (`hU`), and let `Q` span the solutions over
`c.bicommutant` (`hQ`): every `x` over `A_inf` with `U y = E ^ h x` for some `y` over
`c.bicommutant` is `Q s` with `s` over `c.S`. Let `U y = E ^ h x` with `y` over `B⁺` only. If `δ`,
not divisible by `p`, divides the row `l Q` (`l Q = δ g`), then `δ` divides `l · x`. -/
lemma dvd_dotProduct_of_spanning (hU : c.IsPeriodMatrix U h v) {Q : Matrix d d Ainf}
    (hQ : ∀ (x : d → Ainf) (y : d → BPlus),
      (∀ i : d, y i ∈ c.bicommutant) →
      U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x →
      ∃ s : d → c.S, Q *ᵥ (↑) ∘ s = x)
    (x : d → Ainf) (y : d → BPlus) (hy : U *ᵥ y = c.E.val ^ h • ainfToBPlus ∘ x) (δ : Ainf)
    (l g : d → Ainf) (hδ : ¬↑p ∣ δ) (hl : l ᵥ* Q = δ • g) :
    δ ∣ l ⬝ᵥ x := by
  -- `δ` divides `l · (p ^ N x)` as the ideal of `δ` is closed for the `(p, ξ)`-adic topology
  -- (`dvd_of_forall_exists_sub_mem_span_pow`); `p ∤ δ` then removes `p ^ N`.
  obtain ⟨N, h_approx⟩ := hU.exists_dotProduct_pow_smul_sub_mul_mem_span_pow hQ x y hy δ l g hl
  exact dvd_dotProduct_of_dvd_dotProduct_pow_smul hδ l x N
    (dvd_of_forall_exists_sub_mem_span_pow prime_p.not_isUnit prime_xi.not_isUnit hδ h_approx)

/-- Every period matrix `U` has a basis `Q`, `Z` in the sense of `New.Lift.Chart.IsPeriodBasis`:
the nonsingular `Q` over `A_inf` spans the `x` with `U y = E ^ h x` solvable over `c.bicommutant`,
and `U Z = E ^ h Q`. -/
lemma exists_basis (hU : c.IsPeriodMatrix U h v) :
    ∃ (Q : Matrix d d Ainf) (Z : Matrix d d BPlus), c.IsPeriodBasis U h Q Z := by
  obtain ⟨Q, Z, hZ, hUZ, hQ⟩ := hU.exists_spanning_matrix
  have h_dvd := hU.dvd_dotProduct_of_spanning hQ
  refine ⟨Q, Z, ⟨?_, hZ, hUZ, hQ, h_dvd⟩⟩
  -- if `l Q = 0`, every power of `z` divides `τ ^ h l x`, for all `x`; only `0` is divisible by
  -- all powers of `z`, so `l = 0`
  obtain ⟨W, hW⟩ := hU.exists_mulVec_mulVec_eq_smul
  rw [Ne, ← exists_vecMul_eq_zero_iff]
  rintro ⟨l, hl_ne, hl⟩
  refine hl_ne (dotProduct_eq_zero _ fun x ↦ ?_)
  -- `W x` solves `U y = E ^ h (τ ^ h x)`, and `z ^ n` divides the row `l Q = 0`
  have hW_sol : U *ᵥ (W *ᵥ ainfToBPlus ∘ x) = c.E.val ^ h • ainfToBPlus ∘ (tau ^ h • x) := by
    simp [hW, smul_def, mul_pow, mul_assoc, funext_iff]
  have h_pow (n : ℕ) : c.z.val ^ n ∣ l ⬝ᵥ tau ^ h • x :=
    h_dvd _ _ hW_sol _ l 0 (c.not_p_dvd_z ∘ prime_p.dvd_of_dvd_pow) (by simp [hl])
  have h_zero : ainfToBPlus (l ⬝ᵥ tau ^ h • x) = 0 :=
    c.eq_zero_of_z_pow_dvd fun n ↦ by
      rw [← map_pow]
      exact map_dvd ainfToBPlus (h_pow n)
  -- `ainfToBPlus` is injective and `τ ≠ 0`
  have h_smul : l ⬝ᵥ tau ^ h • x = tau ^ h * l ⬝ᵥ x := by rw [dotProduct_smul, smul_eq_mul]
  simpa [h_smul, tau_ne_zero] using h_zero

end IsPeriodMatrix

end Chart

end New.Lift

end PeriodMatrixBasis

/-!
## Period matrices of crystalline lattices with bounded jumps

`ρ` is a representation of `Γ` on a free `ℤ_p`-module with basis `e` (matrices
`New.Period.repMatrix ρ e g`), `𝒥.toGp` maps `Γ` onto an open subgroup of `Gal(ℚ̄_p/ℚ_p)`, and `c`
is a chart for it (`hc : IsChartOf c 𝒥.toGp`). Here `Bmax = BPlus [1/μ]`, `BdRPlus ⊂ BdR` with
`t = tUnit`, `hodgeMatrix P k = P diag (t ^ k i)`, `hodgeFil s` is the filtration `t ^ s BdRPlus`,
and the prime `p` is fixed by the instance `[ThePrime p]`.
-/

namespace New.Lift.Chart

open Period Module Function Algebra Matrix RingHom BdRPlus algebraMap Basis

variable {p : ℕ} [ThePrime p] {T Γ ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Group Γ] [Fintype ι]
  [DecidableEq ι] [𝒥 : OverGp Γ p] {ρ : Representation ℤ_[p] Γ T} (a b : ℕ) {c : Chart}

/-- The columns of `M` are the coordinates, in the basis `e`, of vectors of `B ⊗ T` fixed by `Γ`:
`ρ(g) * g M = M`, where `ρ(g)` is the matrix of `ρ g` in `e` and `g` acts on entries through
`toGp`. -/
def _root_.New.Period.HasInvariantColumns (ρ : Representation ℤ_[p] Γ T) (e : Basis ι ℤ_[p] T)
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] [SMul (Gp p) B] (M : Matrix ι ι B) : Prop :=
  ∀ g : Γ, (repMatrix ρ e g).map (algebraMap ℤ_[p] B) * M.map (toGp g • ·) = M

/-- `U` over `BPlus` is the period matrix of `ρ` in the basis `e` made from the matrix `M` over
`Bmax` with invariant columns by the factor `(E τ) ^ a`. Here `v` is the unit `μ / (E τ)`. Its
height is `a + b` and its Frobenius factor is `v ^ a`. -/
structure IsPeriodMatrixOf (ρ : Representation ℤ_[p] Γ T) (a b : ℕ) (c : Chart)
    (e : Basis ι ℤ_[p] T) (M : Matrix ι ι Bmax) (U : Matrix ι ι BPlus) (v : Ainfˣ) : Prop where
  /-- The columns of `M` are invariant vectors. -/
  hasInvariantColumns : HasInvariantColumns ρ e M
  /-- The unit `v` is `μ / (E τ)`. -/
  E_mul_tau_mul : c.E * tau * v.val = mu
  /-- `U` is a period matrix of height `a + b` with Frobenius factor `v ^ a`. -/
  isPeriodMatrix : c.IsPeriodMatrix U (a + b) (v ^ a)
  /-- `U = (E τ) ^ a M` over `Bmax`. -/
  map_eq_smul : U.map (algebraMap BPlus Bmax) = (c.E * tau) ^ a • M

/-- The action of an element of `FrobGal` on matrices over `Bmax`, entry by entry; `(.ofAdd n, 1)`
acts as `φ ^ n` and `(1, g)` as `g` in `Gal(ℚ̄_p/ℚ_p)`. -/
noncomputable abbrev _root_.New.Period.matrixAction (m : FrobGal) :
    Matrix ι ι Bmax →+* Matrix ι ι Bmax :=
  (MulSemiringAction.toRingHom FrobGal Bmax m).mapMatrix

/-- The twist `φ ^ n M` of an invertible matrix over `Bmax` by a power of Frobenius. -/
noncomputable abbrev _root_.New.Period.frobTwist (n : ℕ) (M : GL ι Bmax) : GL ι Bmax :=
  Units.map (matrixAction (.ofAdd n, 1)).toMonoidHom M

/-- A crystalline `ρ` (`Bmax ⊗ T` has a `Bmax`-basis of `Γ`-invariant vectors) has an invertible
matrix over `Bmax` with invariant columns. -/
lemma _root_.New.Period.IsCrystalline.exists_hasInvariantColumns (h : IsCrystalline ρ)
    (e : Basis ι ℤ_[p] T) : ∃ M : GL ι Bmax, HasInvariantColumns ρ e M.val := by
  -- `M` holds the coordinates, in the basis `e`, of a basis of invariant vectors.
  obtain ⟨s, u, hu⟩ := h.exists_basis le_top
  let u' : Basis ι Bmax (TensorProduct ℤ_[p] Bmax T) := u.reindex (u.indexEquiv (e.baseChange Bmax))
  have hu' (g : Γ) (i : ι) : tensorAction Bmax (toGp g) (ρ g) (u' i) = u' i := by
    simpa [u'] using hu _ g
  let : Invertible ((e.baseChange Bmax).toMatrix u') := (e.baseChange Bmax).invertibleToMatrix u'
  exact ⟨unitOfInvertible ((e.baseChange Bmax).toMatrix u'), fun g ↦ ext_col fun i ↦
    (equivFun_tensorAction ρ e g (u' i)).symm.trans
      (congrArg (e.baseChange Bmax).equivFun (hu' g i))⟩

section InvariantColumns

variable {e : Basis ι ℤ_[p] T}

/-- Frobenius commutes with the Galois action, so `φ ^ n M` has invariant columns if `M` has. -/
lemma _root_.New.Period.HasInvariantColumns.frobTwist {M : GL ι Bmax}
    (hM : HasInvariantColumns ρ e M.val) (n : ℕ) :
    HasInvariantColumns ρ e (frobTwist n M).val := by
  intro g
  have h_inv : (repMatrix ρ e g).map (↑) * matrixAction (1, toGp g) M.val = M.val := hM g
  show (repMatrix ρ e g).map (↑) * matrixAction (1, toGp g) (Period.frobTwist n M).val =
    (Period.frobTwist n M).val
  refine .trans ?_ (congrArg (matrixAction (.ofAdd n, 1)) h_inv)
  simp [comp_def, smul_smul]

/-- An invertible matrix `M` over `Bmax` with invariant columns has a Hodge frame
`M Y = W diag (t ^ k i)` with `Y` fixed by `Γ`, and this product has invariant columns. -/
lemma _root_.New.Period.HasInvariantColumns.exists_hodge_frame {M : GL ι Bmax}
    (hM : HasInvariantColumns ρ e M.val) :
    ∃ (Y : SpecialLinearGroup ι (PadicAlgCl p)) (W : GL ι BdRPlus) (k : ι → ℤ),
      (∀ g : Γ, Y.val.map (toGp g) = Y.val) ∧
      M.val.map (algebraMap Bmax BdR) * Y.val.map (algebraMap (PadicAlgCl p) BdR) =
        hodgeMatrix W.val k ∧
      HasInvariantColumns ρ e (hodgeMatrix W.val k) := by
  have hM_dR : HasInvariantColumns ρ e (M.val.map (algebraMap Bmax BdR)) := fun g ↦ by
    refine .trans ?_ (congrArg (fun X : Matrix ι ι Bmax ↦ X.map (ofId Bmax BdR)) (hM g))
    simp [comp_def]
  obtain ⟨Y, W', k, h_frame⟩ :=
    Period.exists_isHodgeFrame Γ le_top (M.isUnit.map (mapMatrix _)) hM_dR
  obtain ⟨W, rfl⟩ := h_frame.isUnit
  exact ⟨Y, W, k, Filter.eventually_top.mp h_frame.eventually_map_eq, h_frame.mul_map_eq,
    Filter.eventually_top.mp h_frame.eventually_mul_smul_eq⟩

/-- If `W diag (t ^ k i)` has invariant columns, then each `k i` is a Hodge–Tate jump of `ρ`. -/
lemma _root_.New.Period.HasInvariantColumns.jump_ne_zero {W : GL ι BdRPlus} {k : ι → ℤ}
    (hW : HasInvariantColumns ρ e (hodgeMatrix W.val k)) (i : ι) :
    jump ρ (ofId ℤ_[p] ℂ_[p]) (k i) ≠ 0 := by
  -- The rows of `θ(W)⁻¹` are Hodge–Tate forms of weights `k`.
  have h_jumps : HasJumps ρ (ofId ℤ_[p] ℂ_[p]) (Finset.univ.val.map k) := by
    refine (hasJumps_of_rows e (.map (thetaBdR : BdRPlus →+* ℂ_[p]) W)⁻¹ k
      (.of_forall fun g ↦ ?_)).1
    exact inv_mul_apply_of_isHodgeTateFrame (isHodgeTateFrame_of_hodgeMatrix (hW g))
  exact (h_jumps (k i)).trans_ne (by simp)

/-- A matrix `B` with `B Q = P diag (t ^ k i)`, `Q` invertible over `BdRPlus` and `s ≤ k i` for all
`i`, has entries in `hodgeFil s`. -/
lemma _root_.New.Period.mem_hodgeFil_of_mul_eq_hodgeMatrix {B : Matrix ι ι BdR} {k : ι → ℤ}
    {s : ℤ} {P : Matrix ι ι BdRPlus} (Q : GL ι BdRPlus) (hk : ∀ i : ι, s ≤ k i)
    (hB : B * Q.val.map (algebraMap BdRPlus BdR) = hodgeMatrix P k) (i l : ι) :
    B i l ∈ hodgeFil s := by
  rw [(Q.map _).eq_mul_inv_iff_mul_eq.mpr hB]
  refine sum_mem fun m _ ↦ hodgeFil_anti (hk m) ?_
  simp [mem_hodgeFil, ← map_inv, field, ← map_mul, hodgeMatrix]

omit [Fintype ι] [DecidableEq ι] in
/-- If all Frobenius twists of `B` have entries in `hodgeFil (-m)`, then `(E τ) ^ m B` lies over
`BPlus`. -/
lemma exists_map_eq_pow_smul (c : Chart) (B : Matrix ι ι Bmax) (m : ℕ)
    (hB : ∀ (n : ℕ) (i l : ι),
      algebraMap Bmax BdR (((.ofAdd n, 1) : FrobGal) • B i l) ∈ hodgeFil (-m)) :
    ∃ C : Matrix ι ι BPlus, C.map (algebraMap BPlus Bmax) = (c.E * tau) ^ m • B := by
  choose C hC using
    fun i l ↦ pow_smul_mem_range_BPlus (B i l) m c.associated_E_mul_tau_mu.dvd' fun n ↦ hB n i l
  exact ⟨of C, ext hC⟩

/-- Let the jumps of `ρ` lie in `[-a, b]` and let `M` be invertible over `Bmax` with invariant
columns. Then `(E τ) ^ a M` and `(E τ) ^ b M⁻¹` lie over `BPlus`. -/
lemma exists_map_eq_pow_smul_of_hasInvariantColumns (c : Chart) {e : Basis ι ℤ_[p] T}
    {M : GL ι Bmax} (hM : HasInvariantColumns ρ e M.val)
    (hab : ∀ k : ℤ, jump ρ (ofId ℤ_[p] ℂ_[p]) k ≠ 0 → -(a : ℤ) ≤ k ∧ k ≤ (b : ℤ)) :
    (∃ U : Matrix ι ι BPlus, U.map (algebraMap BPlus Bmax) = (c.E * tau) ^ a • M.val) ∧
      ∃ U' : Matrix ι ι BPlus, U'.map (algebraMap BPlus Bmax) = (c.E * tau) ^ b • M.inv := by
  -- Hodge frames `φ ^ n M * Y n = W n * t ^ k n` for every Frobenius twist; the `k n i` are jumps.
  choose Y W k h_fix h_hodge h_inv using fun n ↦ (hM.frobTwist n).exists_hodge_frame
  have hk (n : ℕ) (i : ι) : -(a : ℤ) ≤ k n i ∧ k n i ≤ b := hab _ ((h_inv n).jump_ne_zero i)
  refine ⟨c.exists_map_eq_pow_smul _ a fun n ↦ ?_, c.exists_map_eq_pow_smul _ b fun n ↦ ?_⟩
  · exact mem_hodgeFil_of_mul_eq_hodgeMatrix (.map _ (Y n).toGL) (fun i ↦ (hk n i).left) (h_hodge n)
  · -- Invert the frame: `(φ ^ n M)⁻¹ * W n = Y n * t ^ (-k n)`.
    let N : GL ι BdR := .map (algebraMap Bmax BdR) (frobTwist n M)
    refine mem_hodgeFil_of_mul_eq_hodgeMatrix (P := (Y n).val.map (↑)) (W n)
      (fun i ↦ neg_le_neg (hk n i).right) (N.inv_mul_eq_iff_eq_mul.mpr ?_)
    -- `Y n` reaches `BdR` through `BdRPlus`; `h_hodge` writes the two casts as one map
    have h_cast : (((Y n).val.map (↑) : Matrix ι ι BdRPlus).map (↑) : Matrix ι ι BdR) =
        (Y n).val.map (algebraMap (PadicAlgCl p) BdR) := by
      simp [Matrix.map_map, comp_def, ← IsScalarTower.algebraMap_apply]
    rw [hodgeMatrix, ← mul_assoc, h_cast,
      show (N : Matrix ι ι BdR) * _ = hodgeMatrix (W n).val (k n) from h_hodge n]
    simp [zpow_ne_zero, hodgeMatrix, mul_assoc]

/-- Let `c` be a chart for `toGp` (`hc`). An element of `Bmax` fixed by `Γ` comes from
`c.bicommutant`. -/
lemma IsChartOf.exists_mem_bicommutant_of_fixed (hc : IsChartOf c 𝒥.toGp) {b : Bmax}
    (hb : ∀ g : Γ, toGp g • b = b) :
    ∃ s ∈ c.bicommutant, algebraMap BPlus Bmax s = b := by
  -- `p ^ m * b` is a constant `w` in `WittFq c.f`, and `p` has an inverse `u` in `c.bicommutant`;
  -- so `b` is the image of `u ^ m * w`.
  have h_comm : ∀ g : Γ, (1 : Bmax) * toGp g • b = toGp g • (1 : Bmax) * b := by simpa using hb
  obtain ⟨m, w, hw⟩ := exists_pow_mul_eq_wittFq_mul_of_isChartOf hc (b := b) one_ne_zero h_comm
  obtain ⟨u, hu, hup⟩ := c.exists_bicommutant_mul_p_eq_one
  -- the witness is `u ^ m * w`
  refine ⟨_, mul_mem (pow_mem hu m) (ainfToBPlus_mem_bicommutant w), ?_⟩
  have h_pow : (u * p) ^ m • b = b := by rw [hup, one_pow, one_smul]
  simpa [smul_def, mul_pow, hw, ← IsScalarTower.algebraMap_apply, mul_assoc] using h_pow

/-- Let `c` be a chart for `toGp` (`hc`). The transition matrix of two invertible matrices with
invariant columns has entries in `c.bicommutant`. -/
lemma IsChartOf.exists_transition_matrix (hc : IsChartOf c 𝒥.toGp) {e : Basis ι ℤ_[p] T}
    {M N : GL ι Bmax} (hM : HasInvariantColumns ρ e M.val) (hN : HasInvariantColumns ρ e N.val) :
    ∃ X : Matrix ι ι BPlus, (∀ i l : ι, X i l ∈ c.bicommutant) ∧
      X.map (algebraMap BPlus Bmax) = M.val⁻¹ * N.val := by
  have h_fix (g : Γ) : matrixAction (1, toGp g) (M.val⁻¹ * N.val) = M.val⁻¹ * N.val := by
    set σ : Matrix ι ι Bmax →+* Matrix ι ι Bmax := matrixAction (1, toGp g)
    set R : Matrix ι ι Bmax := (repMatrix ρ e g).map (algebraMap ℤ_[p] Bmax)
    have hMg : R * σ M.val = M.val := hM g
    have hNg : R * σ N.val = N.val := hN g
    have h_det : IsUnit M.val.det := isUnits_det_units M
    calc σ (M.val⁻¹ * N.val)
        = M.val⁻¹ * (R * σ M.val) * σ (M.val⁻¹ * N.val) := by
          rw [hMg, nonsing_inv_mul _ h_det, one_mul]
      _ = M.val⁻¹ * (R * σ (M.val * (M.val⁻¹ * N.val))) := by
          rw [map_mul σ M.val, mul_assoc, mul_assoc]
      _ = M.val⁻¹ * N.val := by rw [mul_nonsing_inv_cancel_left _ _ h_det, hNg]
  choose X hX_mem hX using
    fun i l ↦ hc.exists_mem_bicommutant_of_fixed fun g ↦ congrFun₂ (h_fix g) i l
  exact ⟨of X, hX_mem, ext hX⟩

/-- Let `c` be a chart of `𝒥.toGp : Γ →* G_p` (`hc`), let `M` be invertible over `Bmax` with columns
`Γ`-invariant for `ρ` in the basis `e`, and let `U` over `BPlus` have image `(c.E * tau) ^ a • M` in
`Bmax`. If `U y = E ^ n w` for some `w` over `BPlus`, then `U (c.extendToBPlus f ∘ y) = E ^ n w'`
for some `w'`. Here `c.extendToBPlus f` is the chosen extension to `BPlus` of the `c.S`-linear map
`f` of `A_inf`. -/
lemma IsChartOf.exists_mulVec_extendToBPlus_eq_smul (hc : IsChartOf c 𝒥.toGp) {e : Basis ι ℤ_[p] T}
    {M : GL ι Bmax} {U : Matrix ι ι BPlus}
    (hM : HasInvariantColumns ρ e M.val)
    (hU : U.map (algebraMap BPlus Bmax) = (c.E * tau) ^ a • M.val) {n : ℕ}
    (f : Ainf →ₗ[c.S] Ainf) {y : ι → BPlus}
    (hy : ∃ w : ι → BPlus, U *ᵥ y = c.E.val ^ n • w) :
    ∃ w : ι → BPlus, U *ᵥ c.extendToBPlus f ∘ y = c.E.val ^ n • w := by
  obtain ⟨Y, W, k, hY, h_hodge, -⟩ := hM.exists_hodge_frame
  -- The rows of `Y⁻¹` lie over the fixed field, so `c.extendToBPlus f` multiplies the `l`-th
  -- coordinate of `Y⁻¹ y` by some `s l` in `BdRPlus`.
  have hY_mem (l i : ι) : Y⁻¹.val l i ∈ localFieldOf Γ := by
    rintro ⟨_, g, rfl⟩
    -- `g` fixes the entries of `Y`, hence those of its adjugate `Y⁻¹`
    have h_adj : Y.val.adjugate.map (toGp g) = Y.val.adjugate :=
      ((toGp g).toAlgHom.map_adjugate Y.val).trans (congrArg adjugate (hY g))
    exact congrFun₂ h_adj l i
  have h_dvd_row (l : ι) :
      ∑ i : ι, Y⁻¹.val l i * algebraMap BPlus BdRPlus (y i) ∣
        ∑ i : ι, (Y⁻¹.val l i : BdRPlus) * c.extendToBPlus f (y i) :=
    hc.dvd_extendToBPlus (Y⁻¹.val l) (hY_mem l) f y
  choose s hs using h_dvd_row
  -- Divisibility by `E ^ n` in `BPlus` is divisibility by `ξ ^ n` in `BdRPlus`.
  have h_dvd_iff (x : ι → BPlus) : (∃ w : ι → BPlus, x = c.E.val ^ n • w) ↔
      ∀ i : ι, algebraMap Ainf BdRPlus xi ^ n ∣ algebraMap BPlus BdRPlus (x i) := by
    simp [smul_def, ← dvd_def, pi_dvd_iff, ← xi_pow_dvd_iff,
      (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left]
  rw [h_dvd_iff] at hy ⊢
  intro i
  have hU_dR : U.map (fun x ↦ algebraMap BPlus BdR x) =
      (c.E * tau) ^ a • M.val.map (algebraMap Bmax BdR) := by
    simpa [ofId, comp_def, ← IsScalarTower.algebraMap_apply, AlgHom.map_smul_of_tower] using
      congrArg (ofId Bmax BdR).mapMatrix hU
  have hM_dR : M.val.map (algebraMap Bmax BdR) =
      hodgeMatrix W.val k * Y.val.adjugate.map (algebraMap (PadicAlgCl p) BdR) := by
    simpa [← map_inv] using (Y.toGL.map _).eq_mul_inv_iff_mul_eq.mpr h_hodge
  have hs_dR (l : ι) :
      ∑ j, algebraMap (PadicAlgCl p) BdR (Y.val.adjugate l j) *
          algebraMap BPlus BdR (c.extendToBPlus f (y j)) =
        (∑ j, algebraMap (PadicAlgCl p) BdR (Y.val.adjugate l j) * algebraMap BPlus BdR (y j)) *
          algebraMap BdRPlus BdR (s l) := by
    simpa [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap BdRPlus BdR) (hs l)
  -- As `U = (E τ) ^ a W t ^ k Y⁻¹` over `BdR`, `U (c.extendToBPlus f ∘ y) = W diag(s) W⁻¹ (U y)`.
  have h_mulVec_extend : ((W.val * diagonal s * W.inv) *ᵥ algebraMap BPlus BdRPlus ∘ (U *ᵥ y)) i =
      algebraMap BPlus BdRPlus ((U *ᵥ c.extendToBPlus f ∘ y) i) := by
    simp [RingHom.map_mulVec, ← coe_inj _ BdR, mul_assoc, comp_def,
      ← IsScalarTower.algebraMap_apply]
    simp [hU_dR, hM_dR, ← mul_assoc, hodgeMatrix, smul_mulVec]
    -- As `U = (E τ) ^ a W t ^ k adj(Y)` over `BdR`, both sides are `(E τ) ^ a W` times a vector.
    show (c.E.val * tau) ^ a •
        (((W.val.map (algebraMap BdRPlus BdR) *
            diagonal fun j ↦ algebraMap BdRPlus BdR (s j) * (tUnit : BdR) ^ k j) *
          Y.val.adjugate.map (algebraMap (PadicAlgCl p) BdR)) *ᵥ
          fun j ↦ algebraMap BPlus BdR (y j)) i =
      (c.E.val * tau) ^ a •
        (((W.val.map (algebraMap BdRPlus BdR) * diagonal fun j ↦ (tUnit : BdR) ^ k j) *
          Y.val.adjugate.map (algebraMap (PadicAlgCl p) BdR)) *ᵥ
          fun j ↦ algebraMap BPlus BdR (c.extendToBPlus f (y j))) i
    -- Row by row (`hs_dR`), `adj(Y)` times the extended vector is `diag(s)` times `adj(Y) y`.
    have h_rows : Y.val.adjugate.map (algebraMap (PadicAlgCl p) BdR) *ᵥ
          (fun j ↦ algebraMap BPlus BdR (c.extendToBPlus f (y j))) =
        (diagonal fun l ↦ algebraMap BdRPlus BdR (s l)) *ᵥ
          (Y.val.adjugate.map (algebraMap (PadicAlgCl p) BdR) *ᵥ
            fun j ↦ algebraMap BPlus BdR (y j)) := by
      ext l
      rw [mulVec_diagonal]
      simpa [mulVec, dotProduct, mul_comm] using hs_dR l
    have h_diag : (diagonal fun j ↦ algebraMap BdRPlus BdR (s j) * (tUnit : BdR) ^ k j) =
        (diagonal fun j ↦ (tUnit : BdR) ^ k j) * diagonal fun j ↦ algebraMap BdRPlus BdR (s j) := by
      rw [diagonal_mul_diagonal]
      exact congrArg diagonal (funext fun j ↦ mul_comm _ _)
    rw [h_diag]
    simp only [← mulVec_mulVec, h_rows]
  -- the left side of `h_mulVec_extend` combines the entries of `U y`, each divisible by `ξ ^ n`
  rw [← h_mulVec_extend]
  exact Finset.dvd_sum fun l _ ↦ (hy l).mul_left _

end InvariantColumns

/-- Let `c` be a chart of `𝒥.toGp : Γ → G_p` (`hc`), let `ρ` be crystalline with Hodge–Tate jumps at
the identity embedding in `[-a, b]`, and let `e` be a `ℤ_p`-basis of `T`. Then there are an
invertible matrix `M` over `Bmax`, whose columns (in the basis `e`) are invariant under
`toGp g ⊗ ρ g` for all `g`, and a unit `v = μ / (E τ)` of `Ainf`. With these, `U = (E τ) ^ a M` is a
period matrix of `ρ` over `BPlus` of height `a + b` with Frobenius factor `v ^ a`
(`IsPeriodMatrixOf`).

This does part of the work usually done by Kisin's theorem on the module attached to a crystalline
lattice: it supplies only a period matrix over `B⁺` for jumps in `[-a, b]`, not the Frobenius-stable
submodule itself. -/
lemma IsChartOf.exists_isPeriodMatrixOf (hc : IsChartOf c 𝒥.toGp) (h : IsCrystalline ρ)
    (e : Basis ι ℤ_[p] T)
    (hab : ∀ k : ℤ, jump ρ (ofId ℤ_[p] ℂ_[p]) k ≠ 0 → -(a : ℤ) ≤ k ∧ k ≤ (b : ℤ)) :
    ∃ (M : GL ι Bmax) (U : Matrix ι ι BPlus) (v : Ainfˣ),
      c.IsPeriodMatrixOf ρ a b e M.val U v := by
  -- Take `M` with invariant columns. Then `U = (E τ) ^ a M` and `U' = (E τ) ^ b M⁻¹` lie over
  -- `BPlus`, and it remains to check the four fields of `IsPeriodMatrix`.
  let incl : Matrix ι ι BPlus →ₐ[BPlus] Matrix ι ι Bmax := (ofId BPlus Bmax).mapMatrix
  have incl_inj : Injective incl := map_injective injective_BPlus_Bmax
  obtain ⟨v, hv⟩ : ∃ v : Ainfˣ, c.E * tau * v = mu := c.associated_E_mul_tau_mu
  obtain ⟨w, hw_mem, hw⟩ : ∃ w ∈ c.bicommutant, w * Chart.ainfToBPlus (c.φ c.E) = 1 :=
    c.exists_bicommutant_mul_phi_E_eq_one
  obtain ⟨M, hM⟩ := h.exists_hasInvariantColumns e
  obtain ⟨⟨U, hU⟩, U', hU'⟩ :
      (∃ U : Matrix ι ι BPlus, incl U = (c.E * tau) ^ a • M.val) ∧
        ∃ U' : Matrix ι ι BPlus, incl U' = (c.E * tau) ^ b • M.inv :=
    c.exists_map_eq_pow_smul_of_hasInvariantColumns a b hM hab
  have hU_smul (m : FrobGal) :
      incl (m • U) = (m • c.E.val * m • tau) ^ a • matrixAction m M.val := by
    ext i l
    simpa [incl, smul_def] using congrArg (fun A : Matrix ι ι Bmax ↦ m • A i l) hU
  -- The Frobenius matrix of `U` is `φ E ^ a • X`, with `X = M⁻¹ φ M` and left inverse
  -- `w ^ a • X'`.
  obtain ⟨X, hX_mem, hX⟩ :
      ∃ X : Matrix ι ι BPlus, (∀ i l : ι, X i l ∈ c.bicommutant) ∧
        incl X = M.val⁻¹ * (frobTwist 1 M).val :=
    hc.exists_transition_matrix hM (hM.frobTwist 1)
  obtain ⟨X', -, hX'⟩ :
      ∃ X' : Matrix ι ι BPlus, (∀ i l : ι, X' i l ∈ c.bicommutant) ∧
        incl X' = (frobTwist 1 M).val⁻¹ * M.val :=
    hc.exists_transition_matrix (hM.frobTwist 1) hM
  have hX'X : X' * X = 1 := incl_inj <| by
    rw [map_mul, map_one, hX, hX', mul_assoc, mul_nonsing_inv_cancel_left _ _ (isUnits_det_units M),
      nonsing_inv_mul _ (isUnits_det_units _)]
  -- The four fields of `IsPeriodMatrix`, then those of `IsPeriodMatrixOf`.
  have h_exists_inv : ∃ W : Matrix ι ι BPlus, U * W = (c.E * tau) ^ (a + b) • 1 :=
    ⟨U', incl_inj <| by simp [hU, hU', pow_add, mul_comm, smul_smul, AlgHom.map_smul_of_tower]⟩
  have h_exists_frob : ∃ F F' : Matrix ι ι BPlus, (∀ i j : ι, F i j ∈ c.bicommutant) ∧
      F' * F = 1 ∧ U.map frobEnd = v ^ a • (U * F) := by
    refine ⟨Chart.ainfToBPlus (c.φ c.E) ^ a • X, w ^ a • X', ?_, ?_, incl_inj ?_⟩
    · simp [hX_mem, mul_mem, pow_mem]
    · rw [smul_mul_smul, ← mul_pow, hw, hX'X, one_pow, one_smul]
    · -- `φ (E τ) = φ E * μ = φ E * v * E τ`
      refine (hU_smul _).trans ?_
      simp [Units.smul_def, hU, hX, ← hv, φ, FrobGal.smul_def, mul_assoc, AlgHom.map_smul_of_tower]
      -- both sides are `(φ E · E τ v) ^ a` times `φ M`
      show (frobEnd c.E.val * (c.E.val * (tau * v.val))) ^ a • matrixAction (.ofAdd 1, 1) M.val =
        v.val ^ a • Chart.ainfToBPlus (frobEnd c.E.val) ^ a • (c.E.val * tau) ^ a •
          matrixAction (.ofAdd 1, 1) M.val
      module
  have h_exists_gal (g : Gp p) (hg : c.FixesThetaZ g) :
      ∃ R : Matrix ι ι Ainf, R.map Chart.ainfToBPlus * g • U = U := by
    -- An element fixing the chart comes from `Γ`; the factor `r` is `E τ / g (E τ)`.
    obtain ⟨g, rfl⟩ : ∃ g' : Γ, toGp g' = g := hc g hg
    obtain ⟨r, hr⟩ : ∃ r : Ainfˣ, toGp g • c.E.val * toGp g • tau * r = c.E.val * tau :=
      (c.associated_smul_E (toGp g)).symm.mul_mul associated_smul_tau
    have h_act : incl (toGp g • U) =
        (toGp g • c.E.val * toGp g • tau) ^ a • matrixAction (1, toGp g) M.val :=
      hU_smul (1, toGp g)
    have h_incl :
        incl ((r.val ^ a • (repMatrix ρ e g).map (↑) : Matrix ι ι Ainf).map Chart.ainfToBPlus) =
          r.val ^ a • (repMatrix ρ e g).map (algebraMap ℤ_[p] Bmax) := by
      ext i j
      simp [incl, Matrix.smul_apply, smul_def (A := Bmax), ← IsScalarTower.algebraMap_apply]
    refine ⟨r.val ^ a • (repMatrix ρ e g).map (↑), incl_inj ?_⟩
    rw [map_mul, h_act, hU, h_incl, smul_mul_smul, ← mul_pow, mul_comm, hr,
      show (repMatrix ρ e g).map (↑) * matrixAction (1, toGp g) M.val = M.val from hM g]
    -- the two sides agree up to unfolding instances
    rfl
  exact ⟨M, U, v,
    { hasInvariantColumns := hM
      E_mul_tau_mul := hv
      isPeriodMatrix :=
        { exists_mul_eq_smul_one := h_exists_inv
          exists_frob := h_exists_frob
          exists_gal := h_exists_gal
          extendToBPlus_stable := fun f y ↦ hc.exists_mulVec_extendToBPlus_eq_smul a hM hU f }
      map_eq_smul := hU }⟩

end New.Lift.Chart

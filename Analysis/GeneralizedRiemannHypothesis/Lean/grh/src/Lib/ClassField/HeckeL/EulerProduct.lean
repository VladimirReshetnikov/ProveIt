import Lib.ClassField.Places.Ideles

/-!
# Euler products over primes of a number field and densities at primes of degree one

This file treats Hecke characters of a number field `K`, given by their finite part `ψ`, a
character of the finite ideles `(𝔸f K)ˣ`, and Euler products with coefficients `a v`, `‖a v‖ ≤ 1`,
over the primes `v` of `K`, as functions of a real variable `s > 1`.

* `New.IsHeckeOfType`: `ψ` has open kernel and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` on `Kˣ`;
  `New.heckeCoeff ψ S` is the value of `ψ` at the local idele of the chosen uniformiser for `v ∉ S`,
  and `0` for `v ∈ S`.
* `New.eulerProd`: the product `∏ (1 - a v * q ^ (-s))⁻¹`, defined as `exp` of a sum of logarithms;
  `New.hasProd_eulerProd` says that it is the limit of the partial products.
* `New.hasSum_eulerProd`: for a completely multiplicative function on ideals, of modulus at most
  `1`, the product equals the Dirichlet series.
* `New.HasPrimeDensity`: the Dirichlet mean of `a` over the primes of degree one. Densities are
  linear and monotone (`New.HasPrimeDensity.sum`, `New.HasPrimeDensity.re_le_re`).
* `New.hasPrimeDensity_of_tendsto`: the density is read off from the order of the pole or zero of
  the product at `1`.

Up to a bounded error, the logarithm of the product is the sum of `a v * q ^ (-s)` over the primes
of degree one (`New.norm_log_one_add_neg_mul_cpow_sub_ite_le_of_norm_le_one`,
`New.sum_inv_minFac_sq_le_finrank`). Here `New.FinPlace K` is the type of nonzero primes of `𝓞 K`,
`q = v.q` is the absolute norm of `v`, and degree one means that `q` is prime.

Notions from other files:
* `New.locIdele v`: sends `x ∈ K_vˣ` to the finite idele with component `x` at `v` and `1`
  elsewhere; `New.uniformizer v` is a chosen uniformiser of the completion `K_v`.
* `Φ w` (class `New.PlaceEmbedding`): a chosen complex embedding of `K` inducing the infinite
  place `w`.

## Relation to the literature

Known; see `Lib.ClassField.HeckeL.ContinuationAtOne` for sources.
-/

noncomputable section

open NumberField IsDedekindDomain.HeightOneSpectrum Filter Topology Complex Finset Ideal Module
  ContinuousAt Set

namespace New

variable {K : Type*} [Field K] [NumberField K]
  (ψ : (𝔸f K)ˣ →* ℂˣ) (n : InfinitePlace K → ℤ) (a b : FinPlace K → ℂ) {s : ℝ}

/-- The character `ψ` of the finite ideles is the finite part of a Hecke character of type `n`,
where `n` gives an integer exponent `n w` to each infinite place `w`: the kernel of `ψ` is open,
and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` for `x ∈ Kˣ`, with `Φ w` the chosen complex embedding
inducing `w` and `x` read as a finite idele by the diagonal embedding. -/
def IsHeckeOfType [PlaceEmbedding K] : Prop :=
  ψ.ker.IsOpen ∧
  ∀ x : Kˣ, ψ (principalIdele x) * ∏ w : InfinitePlace K, (Φ w x.val / ‖Φ w x‖) ^ n w = 1

/-- `ψ` is unramified at the finite place `v`: it is `1` on the units of the completion `K_v` of
valuation `1`, read as finite ideles by `New.locIdele v`. -/
def CharUnramifiedAt (v : FinPlace K) : Prop :=
  ∀ u : (LocField v)ˣ, Valued.v u.val = 1 → ψ (locIdele v u) = 1

/-- The function on finite places sending `v ∉ S` to the value of `ψ` at the local idele of the
chosen uniformiser `uniformizer v` of `K_v`, and `v ∈ S` to `0`. -/
def heckeCoeff (S : Set (FinPlace K)) : FinPlace K → ℂ :=
  indicator Sᶜ fun v : FinPlace K ↦ (ψ (locIdele v (uniformizer v))).val

/-- The Euler product `∏ (1 - a v * q ^ (-s))⁻¹` over the primes `v` of `K`, with `q = v.q` the norm
of `v`, as a function of real `s`. It is written `exp (-∑' v, log (1 + -(a v * q ^ (-s))))`, in the
form `log (1 + w)` of Mathlib's bounds for the logarithm. The value at `s` is the limit of this
expression at `s` within `(1, ∞)`: for `‖a v‖ ≤ 1` and `s > 1` it is the expression itself
(`New.eulerProd_eq_exp`, `New.hasProd_eulerProd`), at `s = 1` it is the limit from the right if that
exists, and for `s < 1` it has no meaning. With `a = heckeCoeff ψ S` and `ψ` unramified at every
`v ∉ S` it is the Euler product of the Hecke `L`-function of `ψ` without the factors at `S`. -/
def eulerProd : ℝ → ℂ :=
  extendFrom (Set.Ioi 1) fun s : ℝ ↦
    exp (-∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ))))

/-- The Dirichlet mean of `a` over the primes of degree one (those of prime norm `q`) is `l`, with
a bounded error: for `s > 1` near `1` the series `∑ a v * q ^ (-s)` over these primes converges,
and its sum is `l * log (1 / (s - 1)) + x s` with `x` bounded as `s → 1⁺`. -/
def HasPrimeDensity (l : ℂ) : Prop :=
  ∃ x : ℝ → ℂ,
    -- `∑ a v * q ^ (-s) = -l * log (s - 1) + O(1)` as `s → 1⁺`, over the `v` whose norm `q` is
    -- prime
    x =O[𝓝[>] 1] (1 : ℝ → ℝ) ∧
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      HasSum (fun v : FinPlace K ↦ ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ))
        (x s - l * Real.log (s - 1))

/-- At most `[K : ℚ]` primes of `K` lie over a maximal ideal of `ℤ`. -/
lemma ncard_primesOver_le_finrank (p : Ideal ℤ) [p.IsMaximal] :
    (p.primesOver (𝓞 K)).ncard ≤ finrank ℚ K := by
  -- Each term of the fundamental identity `∑ e f = [K : ℚ]` is at least `1`.
  rw [← RingOfIntegers.rank, ← sum_ramification_inertia_eq_finrank p (𝓞 K),
    ← Set.fintypeCard_eq_ncard, Fintype.card_eq_sum_ones]
  exact sum_le_sum fun P _ ↦ mul_pos (P.1.ramificationIdx_pos ℤ) (P.1.inertiaDeg_pos ℤ)

/-- For a finite set `u` of primes of `K`, the sum over `v ∈ u` of `1 / p ^ 2`, with `p` the least
prime factor of the norm `v.q`, is at most the degree `[K : ℚ]`. -/
lemma sum_inv_minFac_sq_le_finrank (u : Finset (FinPlace K)) :
    ∑ v ∈ u, (v.q.minFac ^ 2 : ℝ)⁻¹ ≤ finrank ℚ K := by
  -- Group the primes by the least factor `p` of their norm. The primes of one group lie over the
  -- same rational prime, so there are at most `[K : ℚ]` of them, and `∑ 1 / p ^ 2 ≤ 1`.
  have h_minFac (v : FinPlace K) : v.q.minFac = absNorm (v.asIdeal.under ℤ) := by
    -- The norm of `v` is a positive power of the rational prime below `v`.
    simp [← (v.asIdeal.under ℤ).absNorm_pow_inertiaDeg v.asIdeal,
      (Nat.absNorm_under_prime _).pow_minFac (inertiaDeg_pos ..).ne']
  have h_group (v : FinPlace K) : #{w ∈ u | w.q.minFac = v.q.minFac} ≤ finrank ℚ K := by
    grw [← ncard_primesOver_le_finrank (v.asIdeal.under ℤ), ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn _ (fun w hw ↦ ⟨w.isPrime, ⟨ext ?_⟩⟩) asIdeal_injective.injOn
      (IsDedekindDomain.primesOver_finite ..)
    -- `w` lies over the prime below `v`: two ideals of `ℤ` with the same norm are equal.
    simp_all [Int.cast_mem_ideal_iff]
  -- The least prime factors lie in `(1, N)` for `N` one more than their maximum.
  set N : ℕ := u.sup fun v : FinPlace K ↦ v.q.minFac + 1
  have h_range : u.image (fun v : FinPlace K ↦ v.q.minFac) ⊆ Ioo 1 N :=
    image_subset_iff.mpr fun v hv ↦ mem_Ioo.mpr ⟨(Nat.minFac_prime v.one_lt_q.ne').one_lt,
      le_sup (f := fun w : FinPlace K ↦ w.q.minFac + 1) hv⟩
  calc
    _ = ∑ p ∈ u.image (fun v : FinPlace K ↦ v.q.minFac),
          #{w ∈ u | w.q.minFac = p} • (p ^ 2 : ℝ)⁻¹ :=
      sum_comp (fun p : ℕ ↦ (p ^ 2 : ℝ)⁻¹) _
    _ ≤ ∑ p ∈ u.image (fun v : FinPlace K ↦ v.q.minFac), finrank ℚ K • (p ^ 2 : ℝ)⁻¹ :=
      sum_le_sum (forall_mem_image.mpr fun v _ ↦ nsmul_le_nsmul_left (by positivity) (h_group v))
    _ ≤ finrank ℚ K • (2 / ((1 : ℕ) + 1) : ℝ) := by
      -- `∑ 1 / p ^ 2 ≤ 2 / (1 + 1)` over `1 < p < N`.
      grw [← smul_sum, h_range, sum_Ioo_inv_sq_le]
    _ = finrank ℚ K := by norm_num

variable {a b} {l l' : ℂ}

/-- For real `s > 1` the series of `N(I) ^ (-s)` over all ideals `I` of `𝓞 K` converges, with
`N(I) = absNorm I` (the zero ideal has norm `0` and term `0`). -/
lemma summable_absNorm_rpow (hs : 1 < s) :
    Summable fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s) := by
  -- The Dedekind zeta function has a pole at `1`, so it is nonzero at some `t` in `(1, s]`.
  obtain ⟨t, ht_ne, -, ht_le⟩ : ∃ t : ℝ, (t - 1 : ℂ) * dedekindZeta K t ≠ 0 ∧ t ∈ Ioc 1 s :=
    (((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).eventually_ne
      (mod_cast dedekindZeta_residue_ne_zero K)).and (Ioc_mem_nhdsGT hs)).exists
  -- A divergent series has sum `0` by convention, so the series converges at `t`, hence at `s`.
  have h_s : LSeriesSummable (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s := by
    refine LSeriesSummable.of_re_le_re (s := (t : ℂ)) (by simpa using ht_le) ?_
    by_contra h_not
    exact right_ne_zero_of_mul ht_ne (LSeries.eq_zero_of_not_LSeriesSummable _ _ h_not)
  -- Group the ideals by their norm: each group is finite and gives one term of that series.
  have h_part (I : Ideal (𝓞 K)) : ∃! n : ℕ, I ∈ {J : Ideal (𝓞 K) | absNorm J = n} := by simp
  rw [summable_partition (fun I ↦ by positivity) h_part]
  refine ⟨fun n ↦ (finite_setOfPred_absNorm_eq n).summable (fun I ↦ (absNorm I : ℝ) ^ (-s)),
    h_s.norm.congr fun n ↦ ?_⟩
  have h_fiber (I : {J : Ideal (𝓞 K) | absNorm J = n}) :
      (absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s) = (n : ℝ) ^ (-s) :=
    congrArg (fun m : ℕ ↦ (m : ℝ) ^ (-s)) I.property
  -- The `Nat.card` ideals of norm `n` each give `n ^ (-s)`; for `n = 0` both sides are `0`.
  rw [tsum_congr h_fiber, tsum_const, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (neg_neg_of_pos (zero_lt_one.trans hs)).ne]
  · simp [LSeries.term_of_ne_zero hn, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Real.rpow_neg, div_eq_mul_inv, Set.coe_ofPred]

/-- For `‖a v‖ ≤ 1` and real `t ≤ s`, the term `-(a v * q ^ (-s))` of the Euler factor has norm at
most `q ^ (-t)`, with `q = v.q` the norm of the prime `v`. -/
private lemma norm_neg_mul_cpow_le_rpow_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {t : ℝ}
    (ht : t ≤ s) (v : FinPlace K) : ‖-(a v * v.q ^ (-s : ℂ))‖ ≤ (v.q : ℝ) ^ (-t) := by
  grw [norm_neg, norm_mul_le, ha, one_mul, norm_cpow_le, ht]
  · -- `‖q ^ (-s)‖ = q ^ (-s)` for the positive real `q`.
    simp
  · exact mod_cast v.one_lt_q.le

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the term `-(a v * q ^ (-s))` has norm at most `1 / q`. -/
private lemma norm_neg_mul_cpow_le_inv_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) : ‖-(a v * v.q ^ (-s : ℂ))‖ ≤ (v.q : ℝ)⁻¹ := by
  simpa [Real.rpow_neg] using norm_neg_mul_cpow_le_rpow_of_norm_le_one ha hs v

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the logarithm of the Euler factor `1 - a v * q ^ (-s)`
differs from `-(a v * q ^ (-s))` (if `q` is prime) or from `0` (if not) by at most `2 / p ^ 2`, with
`p` the least prime factor of `q`. -/
lemma norm_log_one_add_neg_mul_cpow_sub_ite_le_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) :
    ‖Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) -
        (if v.q.Prime then -(a v * v.q ^ (-s : ℂ)) else 0)‖ ≤ 2 / v.q.minFac ^ 2 := by
  set w : ℂ := -(a v * v.q ^ (-s : ℂ))
  have h_inv : ‖w‖ ≤ (v.q : ℝ)⁻¹ := norm_neg_mul_cpow_le_inv_of_norm_le_one ha hs v
  have h_half : ‖w‖ ≤ 2⁻¹ := h_inv.trans (inv_anti₀ two_pos (mod_cast v.one_lt_q))
  have h_log : ‖log (1 + w)‖ ≤ 2 * ‖w‖ := by grind [norm_log_one_add_half_le_self, norm_nonneg]
  split_ifs with hq
  · -- `q` is its own least factor, and `‖log (1 + w) - w‖ ≤ ‖w‖ ^ 2 / (1 - ‖w‖) / 2 ≤ 1 / q ^ 2`.
    calc ‖log (1 + w) - w‖ ≤ ((v.q : ℝ)⁻¹) ^ 2 * (1 - 2⁻¹)⁻¹ / 2 := by
          grw [norm_log_one_add_sub_self_le (h_half.trans_lt (by norm_num)),
            ← sub_le_sub_left h_half, h_inv]
      _ = 1 / (v.q : ℝ) ^ 2 := by ring
      _ ≤ 2 / v.q.minFac ^ 2 := by
          rw [hq.minFac_eq]
          gcongr
          norm_num
  · -- Nothing is subtracted, `‖log (1 + w)‖ ≤ 2 / q` and `minFac q ^ 2 ≤ q`.
    have h_sq_le : ((v.q.minFac : ℝ) ^ 2) ≤ v.q :=
      mod_cast Nat.minFac_sq_le_self (zero_lt_one.trans v.one_lt_q) hq
    have h_sq_pos : (0 : ℝ) < (v.q.minFac : ℝ) ^ 2 := pow_pos (mod_cast v.q.minFac_pos) 2
    rw [sub_zero]
    calc ‖log (1 + w)‖ ≤ 2 * (v.q : ℝ)⁻¹ := by grw [h_log, h_inv]
      _ ≤ 2 * ((v.q.minFac : ℝ) ^ 2)⁻¹ := by grw [inv_anti₀ h_sq_pos h_sq_le]
      _ = 2 / v.q.minFac ^ 2 := by rw [div_eq_mul_inv]

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the Euler factor `1 - a v * q ^ (-s)` lies in the slit plane,
where the logarithm is continuous. -/
lemma one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) : 1 + -(a v * v.q ^ (-s : ℂ)) ∈ slitPlane :=
  mem_slitPlane_of_norm_lt_one ((norm_neg_mul_cpow_le_inv_of_norm_le_one ha hs v).trans_lt
    (inv_lt_one_of_one_lt₀ (mod_cast v.one_lt_q)))

/-- For `‖a v‖ ≤ 1` and real `1 ≤ σ ≤ s`, the logarithm of the Euler factor `1 - a v * q ^ (-s)` has
norm at most `2 * q ^ (-σ)`. -/
lemma norm_log_one_add_neg_mul_cpow_le_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (hσs : σ ≤ s) (v : FinPlace K) :
    ‖Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * v.q ^ (-σ) := by
  set w : ℂ := -(a v * v.q ^ (-s : ℂ))
  have h_inv : ‖w‖ ≤ (v.q : ℝ)⁻¹ := norm_neg_mul_cpow_le_inv_of_norm_le_one ha (hσ.trans hσs) v
  have h_half : ‖w‖ ≤ 2⁻¹ := h_inv.trans (inv_anti₀ two_pos (mod_cast v.one_lt_q))
  have h_log : ‖log (1 + w)‖ ≤ 2 * ‖w‖ := by grind [norm_log_one_add_half_le_self, norm_nonneg]
  grw [h_log, norm_neg_mul_cpow_le_rpow_of_norm_le_one ha hσs v]

/-- If `‖a v‖ ≤ 1` and `s > 1`, the series `∑ v, log (1 - a v * q ^ (-s))` converges, its sum is
continuous at `s`, and `New.eulerProd a s` is the exponential of minus this sum. -/
@[local simp]
lemma eulerProd_eq_exp (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    let logFactor (s : ℝ) (v : FinPlace K) : ℂ := Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))
    eulerProd a s = exp (-∑' v : FinPlace K, logFactor s v) ∧
    Summable (logFactor s) ∧
    ContinuousAt (fun t : ℝ ↦ -∑' v : FinPlace K, logFactor t v) s := by
  -- Fix `σ` between `1` and `s`. For `t ≥ σ` the logarithms are dominated by the convergent series
  -- `∑ 2 * q ^ (-σ)`, which gives summability and, by dominated convergence, continuity.
  intro logFactor
  obtain ⟨σ, hσ, hσs⟩ : ∃ σ : ℝ, 1 < σ ∧ σ < s := exists_between hs
  have h_sum : Summable fun v : FinPlace K ↦ 2 * (v.q : ℝ) ^ (-σ) :=
    ((summable_absNorm_rpow hσ).comp_injective asIdeal_injective).mul_left _
  have h_bound (t : ℝ) (ht : σ ≤ t) (v : FinPlace K) : ‖logFactor t v‖ ≤ 2 * (v.q : ℝ) ^ (-σ) :=
    norm_log_one_add_neg_mul_cpow_le_of_norm_le_one ha hσ.le ht v
  have h_term (v : FinPlace K) : ContinuousAt (fun t : ℝ ↦ logFactor t v) s :=
    ContinuousAt.clog (by fun_prop (disch := simp))
      (one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one ha hs.le v)
  have h_cont : ContinuousAt (fun t : ℝ ↦ -∑' v : FinPlace K, logFactor t v) s :=
    (tendsto_tsum_of_dominated_convergence h_sum h_term (.mono (Ici_mem_nhds hσs) h_bound)).neg
  -- The extension by continuity keeps the value at a point of continuity.
  exact ⟨extendFrom_eq (subset_closure hs) h_cont.cexp.continuousWithinAt.tendsto,
    h_sum.of_norm_bounded (h_bound s hσs.le), h_cont⟩

/-- For `‖a v‖ ≤ 1` and real `s > 1`, `New.eulerProd a s` is the exponential of minus the sum of
the logarithms of the Euler factors `1 - a v * q ^ (-s)`. -/
lemma eulerProd_eq_exp_neg_tsum_log_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    eulerProd a s = exp (-∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))) := by
  obtain ⟨h_eq, -, -⟩ := eulerProd_eq_exp ha hs
  exact h_eq

/-- For `‖a v‖ ≤ 1` and real `s > 1`, the logarithms of the Euler factors `1 - a v * q ^ (-s)` are
summable over the primes `v`. -/
lemma summable_log_one_add_neg_mul_cpow_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 < s) : Summable fun v : FinPlace K ↦ Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) := by
  obtain ⟨-, h_sum, -⟩ := eulerProd_eq_exp ha hs
  exact h_sum

/-- If `‖a v‖ ≤ 1` for all primes `v` of `K` and `s > 1` is real, the Euler product
`∏ v, (1 - a v * q ^ (-s))⁻¹` converges unconditionally to `New.eulerProd a s`. -/
lemma hasProd_eulerProd (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    HasProd (fun v : FinPlace K ↦ (1 - a v * v.q ^ (-s : ℂ))⁻¹) (eulerProd a s) := by
  have h_sum := (summable_log_one_add_neg_mul_cpow_of_norm_le_one ha hs).hasSum
  rw [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one ha hs, exp_neg]
  -- The factor `1 - x` is written `1 + -x`, the form whose logarithms are summed.
  simp only [sub_eq_add_neg]
  exact (hasProd_of_hasSum_log (fun v ↦ slitPlane_ne_zero
    (one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one ha hs.le v)) h_sum).inv₀ (exp_ne_zero _)

/-- For `‖a v‖ ≤ 1`, a finite set `Q` of primes and `P s = ∏ w ∈ Q, (1 - a w * q_w ^ (-s))`: `P` is
analytic at the real point `1`, `P 1 ≠ 0`, and for real `s > 1` setting the coefficients at `Q` to
zero multiplies the Euler product by `P s`. -/
lemma eulerProd_erase (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (Q : Finset (FinPlace K)) :
    let P (s : ℂ) : ℂ := ∏ w ∈ Q, (1 - a w * w.q ^ (-s))
    AnalyticAt ℝ (P ∘ ofReal) 1 ∧
    P 1 ≠ 0 ∧
    ∀ s > (1 : ℝ), eulerProd (indicator Qᶜ a) s = eulerProd a s * P s := by
  intro P
  have h_factor_ne {t : ℝ} (ht : 1 ≤ t) (w : FinPlace K) : 1 - a w * w.q ^ (-t : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using
      slitPlane_ne_zero (one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one ha ht w)
  have hP_analytic : AnalyticAt ℂ P 1 := by fun_prop (disch := simp)
  have hP_one : P 1 ≠ 0 := prod_ne_zero_iff.mpr fun w _ ↦ by simpa using h_factor_ne le_rfl w
  refine ⟨(hP_analytic.restrictScalars (𝕜' := ℂ)).comp_of_eq (ofRealCLM.analyticAt 1) (by simp),
    hP_one, fun s hs ↦ ?_⟩
  -- The two convergent products have the same factors outside `Q`, so their values differ by
  -- the quotient of the finite products over `Q`.
  let g (v : FinPlace K) : ℂ := (1 - Set.indicator Qᶜ a v * v.q ^ (-s : ℂ))⁻¹
  have h_erased : HasProd g (eulerProd (Set.indicator Qᶜ a) s) :=
    hasProd_eulerProd (fun v ↦ (norm_indicator_le_norm_self a v).trans (ha v)) hs
  have h_congr : HasProd g (eulerProd a s *
      ((∏ w ∈ Q, g w) / ∏ w ∈ Q, (1 - a w * w.q ^ (-s : ℂ))⁻¹)) :=
    (hasProd_eulerProd ha hs).congr_cofinite₀ (fun w _ ↦ inv_ne_zero (h_factor_ne hs.le w))
      fun w hw ↦ by simp [g, hw]
  -- At `Q` the new factors are `1` and the old ones have product `(P s)⁻¹`.
  have h_g_one : ∀ w ∈ Q, g w = 1 := fun w hw ↦ by simp [g, hw]
  rw [h_erased.unique h_congr, prod_eq_one h_g_one, prod_inv_distrib, one_div, inv_inv]

/-- If `‖a v‖ ≤ 1` for all `v` and `(s - 1) ^ l * eulerProd a s` tends to some `c ≠ 0` as real
`s ↓ 1`, with `l` a complex number, then `a` has density `l` over the primes of degree one. This
means `HasPrimeDensity a l`: the sum of `a v * q_v ^ (-s)` over the primes `v` of prime norm `q_v`
equals `l * log (1 / (s - 1))` plus a term bounded as `s ↓ 1`. (A pole of order `m` is the case
`l = m`, a zero of order `m` the case `l = -m`.) -/
lemma hasPrimeDensity_of_tendsto (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {l : ℂ} {c : ℂ} (hc : c ≠ 0)
    (h_lim : Tendsto (fun s : ℝ ↦ (s - 1) ^ l * eulerProd a s) (𝓝[>] 1) (𝓝 c)) :
    HasPrimeDensity a l := by
  -- `logProd` is a continuous logarithm of `(s - 1) ^ l * eulerProd a s` for `s > 1`. As
  -- `exp logProd` tends to `c ≠ 0`, `logProd` stays bounded near `1`; and the logarithm of the
  -- Euler product differs from the sum over the primes of degree one by a bounded error.
  let L (s : ℝ) (v : FinPlace K) : ℂ := log (1 + -(a v * v.q ^ (-s : ℂ)))
  let logProd (s : ℝ) : ℂ := (s - 1).log * l + -∑' v, L s v
  have h_exp_logProd (s : ℝ) (hs_gt : 1 < s) : (s - 1) ^ l * eulerProd a s = exp (logProd s) := by
    have h_ne : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (mod_cast hs_gt.ne')
    rw [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one ha hs_gt, cpow_def_of_ne_zero h_ne, ← exp_add]
    simp [logProd, L, ofReal_log (sub_nonneg.mpr hs_gt.le)]
  have h_exp : Tendsto (fun s : ℝ ↦ exp (logProd s) / c) (𝓝[>] 1) (𝓝 (c / c)) :=
    (tendsto_nhdsWithin_congr h_exp_logProd h_lim).div_const c
  have h_one : c / c ∈ slitPlane := by simp [div_self hc]
  obtain ⟨s₁, hs₁, h_slit⟩ :
      ∃ s₁ ∈ Set.Ioi (1 : ℝ), ∀ s ∈ Set.Ioc 1 s₁, exp (logProd s) / c ∈ slitPlane :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp (h_exp (isOpen_slitPlane.mem_nhds h_one))
  have hlog_cont : ContinuousOn logProd (Ioc 1 s₁) := by
    refine .add (by fun_prop (disch := grind)) fun s ⟨hs_gt, _⟩ ↦ ?_
    obtain ⟨-, -, h_cont⟩ := eulerProd_eq_exp ha hs_gt
    exact h_cont.continuousWithinAt
  -- On `(1, s₁]` the function `logProd - log (exp logProd / c)` is a continuous logarithm of the
  -- constant `c`, so it is constant.
  have h_exp_eq (t : ℝ) (ht : t ∈ Ioc 1 s₁) : exp (logProd t - log (exp (logProd t) / c)) = c := by
    rw [exp_sub, exp_log (slitPlane_ne_zero (h_slit t ht)), div_div_cancel₀ (exp_ne_zero _)]
  have hlog_const (s : ℝ) (hs : s ∈ Set.Ioc 1 s₁) :
      logProd s - log (exp (logProd s) / c) = logProd s₁ - log (exp (logProd s₁) / c) :=
    isCoveringMap_exp.constOn_of_comp isPreconnected_Ioc
      (hlog_cont.fun_sub ((hlog_cont.cexp.div_const c).clog h_slit))
      (fun t ht t' ht' ↦ Subtype.ext ((h_exp_eq t ht).trans (h_exp_eq t' ht').symm)) hs
      ⟨hs₁, le_rfl⟩
  let C : ℂ := logProd s₁ - log (exp (logProd s₁) / c)
  have hlog_bdd : (fun s ↦ C + log (exp (logProd s) / c)) =O[𝓝[>] 1] (1 : ℝ → ℝ) :=
    ((h_exp.clog h_one).const_add C).isBigO_one ℝ
  -- The error terms `E s v` are bounded, uniformly in `s > 1`, by a convergent series.
  let E (s : ℝ) (v : FinPlace K) : ℂ := L s v - ite v.q.Prime (-(a v * v.q ^ (-s : ℂ))) 0
  have hE_le (s : ℝ) (hs : 1 < s) (v : FinPlace K) : ‖E s v‖ ≤ 2 * (v.q.minFac ^ 2 : ℝ)⁻¹ :=
    (norm_log_one_add_neg_mul_cpow_sub_ite_le_of_norm_le_one ha hs.le v).trans_eq
      (div_eq_mul_inv _ _)
  have h_sum : Summable fun v : FinPlace K ↦ 2 * (v.q.minFac ^ 2 : ℝ)⁻¹ :=
    (summable_of_sum_le (fun v ↦ by positivity) sum_inv_minFac_sq_le_finrank).mul_left 2
  have hE_bdd : (fun s ↦ ∑' v, E s v) =O[𝓝[>] 1] (1 : ℝ → ℝ) :=
    (isBoundedUnder_of_eventually_le <| eventually_mem_nhdsWithin.mono fun s hs ↦
      tsum_of_norm_bounded h_sum.hasSum (hE_le s hs)).isBigO_one ℝ
  -- The bounded error term: the sum of the `E s v` plus `logProd s`, written as the constant
  -- logarithm `C` of `c` plus `log (exp (logProd s) / c)`.
  let err (s : ℝ) : ℂ := ∑' v, E s v + (C + log (exp (logProd s) / c))
  refine ⟨err, hE_bdd.add hlog_bdd, .mono (Ioc_mem_nhdsGT hs₁) fun s ⟨hs_gt, hs_le⟩ ↦ ?_⟩
  -- The terms are `E s v - L s v`, and `-∑' v, L s v = logProd s - log (s - 1) * l`.
  have h_terms : (fun v : FinPlace K ↦ ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ)) =
      fun v ↦ E s v - L s v := by grind
  have h_value : err s - l * Real.log (s - 1) = ∑' v, E s v - ∑' v, L s v := by
    linear_combination -hlog_const s ⟨hs_gt, hs_le⟩
  rw [h_terms, h_value]
  exact (h_sum.of_norm_bounded (hE_le s hs_gt)).hasSum.sub
    (summable_log_one_add_neg_mul_cpow_of_norm_le_one ha hs_gt).hasSum

open Real

/-- If `‖a v‖ ≤ 1` for all `v` and `s ≥ σ ≥ 2` are real, the Euler product with coefficients `a` is
nonzero at `s`, and the logarithm of its modulus has absolute value at most
`2 * [K : ℚ] * 2 ^ (2 - σ)`. -/
lemma eulerProd_ne_zero_and_abs_log_norm_le (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {σ : ℝ} (hσ : 2 ≤ σ)
    (hs : σ ≤ s) :
    eulerProd a s ≠ 0 ∧ |Real.log ‖eulerProd a s‖| ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
  have hs_one : 1 < s := by linarith
  have h_summable := summable_log_one_add_neg_mul_cpow_of_norm_le_one ha hs_one
  -- Each logarithm is at most `2 * q ^ (-σ) ≤ 2 * 2 ^ (2 - σ) / p ^ 2`, as `q ≥ 2` and `p ≤ q` for
  -- the least prime factor `p` of `q`.
  have h_term (v : FinPlace K) :
      ‖log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * 2 ^ (2 - σ) * (v.q.minFac ^ 2 : ℝ)⁻¹ := by
    have hq : (2 : ℝ) ≤ v.q := mod_cast v.one_lt_q
    have hp : 0 < v.q.minFac := v.q.minFac_pos
    calc _ ≤ 2 * (v.q : ℝ) ^ (-σ) :=
          norm_log_one_add_neg_mul_cpow_le_of_norm_le_one ha (by linarith) hs v
      _ = 2 * v.q ^ (2 - σ) * (v.q ^ 2 : ℝ)⁻¹ := by simp [rpow_sub, v.q_bounds, field, rpow_neg]
      _ ≤ _ := by
        grw [rpow_le_rpow_of_nonpos two_pos hq (sub_nonpos.mpr hσ), Nat.minFac_le v.one_lt_q.le]
  -- Sum over the primes, using `∑ p⁻² ≤ [K : ℚ]`.
  have h_sum : ‖∑' v, log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
    refine le_of_tendsto' h_summable.hasSum.norm fun u ↦ ?_
    grw [norm_sum_le, h_term, ← Finset.mul_sum, sum_inv_minFac_sq_le_finrank u, mul_right_comm]
  -- The product is `exp (-z)` for the sum `z` of the logarithms: it is nonzero, and
  -- `|log ‖exp (-z)‖| = |re z| ≤ ‖z‖`.
  rw [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one ha hs_one]
  refine ⟨exp_ne_zero _, ?_⟩
  set z : ℂ := ∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))
  calc |Real.log ‖exp (-z)‖| = |z.re| := by rw [norm_exp, Real.log_exp, neg_re, abs_neg]
    _ ≤ ‖z‖ := abs_re_le_norm z
    _ ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := h_sum

/-- Euler product: for `χ` multiplicative on the ideals of `𝓞 K` with `‖χ I‖ ≤ 1` and real `s > 1`,
the series `∑ I, χ I * N(I) ^ (-s)` converges to the Euler product with coefficients `χ v`. -/
lemma hasSum_eulerProd (χ : Ideal (𝓞 K) →* ℂ) (hχ : ∀ I : Ideal (𝓞 K), ‖χ I‖ ≤ 1) (hs : 1 < s) :
    HasSum (fun I : Ideal (𝓞 K) ↦ χ I * I.absNorm ^ (-s : ℂ))
      (eulerProd (fun v : FinPlace K ↦ χ v.asIdeal) s) := by
  classical
  -- Sieve: multiplying the series by the factors `1 - χ v * N v ^ (-s)`, `v ∈ T`, removes the
  -- ideals divisible by a prime of `T`. As `T` grows only the term `1` of the unit ideal survives,
  -- so the sum of the series times the inverse of the Euler product is `1`.
  let t (I : Ideal (𝓞 K)) : ℂ := χ I * I.absNorm ^ (-s : ℂ)
  let sieved (T : Finset (FinPlace K)) (I : Ideal (𝓞 K)) : ℂ :=
    if ∀ v ∈ T, ¬v.asIdeal ∣ I then t I else 0
  have h_norm_le (I : Ideal (𝓞 K)) : ‖t I‖ ≤ (absNorm I : ℝ) ^ (-s) := by
    grw [norm_mul_le, hχ, norm_cpow_le]
    simp
  have h_summable : Summable t := (summable_absNorm_rpow hs).of_norm_bounded h_norm_le
  have h_sieve (T : Finset (FinPlace K)) :
      HasSum (sieved T) ((∑' I, t I) * ∏ v ∈ T, (1 - t v.asIdeal)) := by
    induction T using Finset.cons_induction with
    | empty => simpa [sieved] using h_summable.hasSum
    | cons v T hv ih =>
      -- The terms removed at `v` are those of the ideals `v * I`: they are `t v` times the old
      -- terms at `I`.
      let removed (I : Ideal (𝓞 K)) : ℂ := sieved T I - sieved (cons v T hv) I
      have h_mul (I : Ideal (𝓞 K)) : removed (v.asIdeal * I) = t v.asIdeal * sieved T I := by
        -- `t` is multiplicative; `v ∣ v * I`, and a prime `w ∈ T` (so `w ≠ v`) divides `v * I`
        -- if and only if it divides `I`.
        have h_t_mul : t (v.asIdeal * I) = t v.asIdeal * t I := by
          simp only [t, map_mul, Nat.cast_mul, natCast_mul_natCast_cpow]
          ring
        have h_cons_zero : sieved (cons v T hv) (v.asIdeal * I) = 0 :=
          ite_eq_right fun h ↦ h v (mem_cons_self v T) (dvd_mul_right v.asIdeal I)
        have h_iff : (∀ w ∈ T, ¬w.asIdeal ∣ v.asIdeal * I) ↔ ∀ w ∈ T, ¬w.asIdeal ∣ I := by
          refine forall₂_congr fun w hw ↦ ?_
          simp [(prime w).dvd_mul, prime_dvd_prime_iff_eq (prime w) (prime v),
            asIdeal_injective.ne (ne_of_mem_of_not_mem hw hv)]
        simp only [removed, h_cons_zero, sub_zero]
        simp only [sieved, h_iff, h_t_mul, mul_ite, mul_zero]
      have h_off : ∀ I ∉ Set.range fun J : Ideal (𝓞 K) ↦ v.asIdeal * J, removed I = 0 := by
        grind [dvd_def]
      have h_removed :
          HasSum removed (t v.asIdeal * ((∑' I, t I) * ∏ w ∈ T, (1 - t w.asIdeal))) :=
        ((mul_right_injective₀ v.ne_bot).hasSum_iff h_off).mp
          ((ih.mul_left (t v.asIdeal)).congr_fun h_mul)
      rw [prod_cons, mul_left_comm, one_sub_mul]
      exact (ih.sub h_removed).congr_fun fun I ↦ (sub_sub_self _ _).symm
  -- Termwise limit: a proper ideal lies in some prime, and is removed once `T` contains it.
  have h_term (I : Ideal (𝓞 K)) :
      Tendsto (fun T ↦ sieved T I) atTop (𝓝 (if I = ⊤ then 1 else 0)) := by
    split_ifs with hI
    · simp [sieved, t, hI, ← one_eq_top, (prime _).not_dvd_one]
    · obtain ⟨v, hI_le⟩ : ∃ v : FinPlace K, I ≤ v.asIdeal :=
        (ideal_ne_top_iff_exists (RingOfIntegers.not_isField K) I).mp hI
      have h_zero : ∀ T ≥ ({v} : Finset (FinPlace K)), sieved T I = 0 := by grind [dvd_iff_le]
      exact tendsto_atTop_of_eventually_const h_zero
  -- Dominated convergence: each sieved term is `t I` or `0`.
  have h_bound (T : Finset (FinPlace K)) (I : Ideal (𝓞 K)) : ‖sieved T I‖ ≤ ‖t I‖ := by
    grind [norm_zero]
  have h_lim_one : Tendsto (fun T : Finset (FinPlace K) ↦ (∑' I, t I) * ∏ v ∈ T, (1 - t v.asIdeal))
      atTop (𝓝 1) := by
    have h_dom := tendsto_tsum_of_dominated_convergence h_summable.norm h_term (.of_forall h_bound)
    rw [tsum_ite_eq] at h_dom
    exact h_dom.congr fun T ↦ (h_sieve T).tsum_eq
  -- The partial products of the factors `1 - t v` tend to the inverse of the Euler product.
  have h_lim_prod : HasProd (fun v : FinPlace K ↦ 1 - t v.asIdeal)
      (eulerProd (fun v : FinPlace K ↦ χ v.asIdeal) s)⁻¹ := by
    have h_ne : eulerProd (fun v : FinPlace K ↦ χ v.asIdeal) s ≠ 0 := by
      simp [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one (fun v ↦ hχ v.asIdeal) hs]
    simpa only [inv_inv] using (hasProd_eulerProd (fun v ↦ hχ v.asIdeal) hs).inv₀ h_ne
  exact h_summable.hasSum_iff.mpr
    (eq_of_mul_inv_eq_one (tendsto_nhds_unique (h_lim_prod.const_mul _) h_lim_one))

/-- Densities are linear: if each `a i` has density `l i` over the primes of degree one, then
`∑ i, w i * a i` has density `∑ i, w i * l i`. -/
lemma HasPrimeDensity.sum {ι : Type*} [Fintype ι] {a : ι → FinPlace K → ℂ} (w : ι → ℂ) {l : ι → ℂ}
    (h : ∀ i : ι, HasPrimeDensity (a i) (l i)) :
    HasPrimeDensity (fun v : FinPlace K ↦ ∑ i : ι, w i * a i v) (∑ i : ι, w i * l i) := by
  -- Take the same combination of the bounded error terms.
  choose x h_bdd h_sum using show ∀ i, ∃ x : ℝ → ℂ, x =O[𝓝[>] 1] (1 : ℝ → ℝ) ∧
      ∀ᶠ s : ℝ in 𝓝[>] 1, HasSum (fun v : FinPlace K ↦ ite v.q.Prime (a i v) 0 * v.q ^ (-s : ℂ))
        (x s - l i * Real.log (s - 1)) from h
  refine ⟨∑ i, fun s ↦ w i * x i s, .sum fun i _ ↦ (h_bdd i).const_mul_left (w i), ?_⟩
  filter_upwards [eventually_all.mpr h_sum] with s hs
  have h_each : HasSum (fun v : FinPlace K ↦ ∑ i, w i * (ite v.q.Prime (a i v) 0 * v.q ^ (-s : ℂ)))
      (∑ i, w i * (x i s - l i * Real.log (s - 1))) :=
    hasSum_sum fun i _ ↦ (hs i).mul_left (w i)
  have h_terms (v : FinPlace K) : ite v.q.Prime (∑ i, w i * a i v) 0 * v.q ^ (-s : ℂ) =
      ∑ i, w i * (ite v.q.Prime (a i v) 0 * v.q ^ (-s : ℂ)) := by
    by_cases hq : v.q.Prime <;> simp [hq, Finset.sum_mul, mul_assoc]
  have h_value : ∑ i, w i * (x i s - l i * Real.log (s - 1)) =
      (∑ i, fun s ↦ w i * x i s) s - (∑ i, w i * l i) * Real.log (s - 1) := by
    simp [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
  rw [h_value] at h_each
  exact h_each.congr_fun h_terms

/-- Suppose `a` has density `l` and `b` has density `l'` in the Dirichlet sense of
`HasPrimeDensity`: over the primes `v` of degree one (prime norm `q_v`),
`∑ a v * q_v ^ (-s) = l * log (1 / (s - 1)) + O(1)` as `s ↓ 1`, and likewise for `b` and `l'`.
Suppose also that `Re (a v) ≤ Re (b v)` for all but finitely many primes `v` of degree one. Then
`Re l ≤ Re l'`. -/
lemma HasPrimeDensity.re_le_re (ha : HasPrimeDensity a l) (hb : HasPrimeDensity b l')
    (h_le : ∀ᶠ v : FinPlace K in cofinite, v.q.Prime → (a v).re ≤ (b v).re) :
    l.re ≤ l'.re := by
  -- Subtract the two series. Outside a finite set `S` the terms `d s v` have real part `≥ 0`, so
  -- `∑ v ∈ S, re (d s v) + re (l' - l) log (s - 1) ≤ ‖y s - x s‖`, which is bounded as `s ↓ 1`.
  -- If `re l' < re l` the left side tends to `+∞`.
  obtain ⟨x, hx_bdd, hx_sum⟩ : ∃ x : ℝ → ℂ, x =O[𝓝[>] 1] (1 : ℝ → ℝ) ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      HasSum (fun v : FinPlace K ↦ ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ))
        (x s - l * Real.log (s - 1)) := ha
  obtain ⟨y, hy_bdd, hy_sum⟩ : ∃ y : ℝ → ℂ, y =O[𝓝[>] 1] (1 : ℝ → ℝ) ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      HasSum (fun v : FinPlace K ↦ ite v.q.Prime (b v) 0 * v.q ^ (-s : ℂ))
        (y s - l' * Real.log (s - 1)) := hb
  by_contra! h_lt : l'.re < l.re
  -- `S`: the finitely many primes where the hypothesis `h_le` fails.
  let S : Finset (FinPlace K) := (eventually_cofinite.mp h_le).toFinset
  let d (s : ℝ) (v : FinPlace K) : ℂ :=
    ite v.q.Prime (b v) 0 * v.q ^ (-s : ℂ) - ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ)
  have h_nonneg (s : ℝ) (v : FinPlace K) (hv : v ∉ S) : 0 ≤ (d s v).re := by
    have h_real : (v.q : ℂ) ^ (-s : ℂ) = ((v.q : ℝ) ^ (-s) : ℝ) := by simp [ofReal_cpow]
    have h_coeff_nonneg : 0 ≤ (ite v.q.Prime (b v) 0).re - (ite v.q.Prime (a v) 0).re := by
      by_cases hq : v.q.Prime <;> simp_all [S]
    simp only [d, h_real, ← sub_mul, re_mul_ofReal, sub_re]
    exact mul_nonneg h_coeff_nonneg (by positivity)
  have h_bound : ∀ᶠ s : ℝ in 𝓝[>] 1,
      ∑ v ∈ S, (d s v).re + (l'.re - l.re) * (s - 1).log ≤ ‖y s - x s‖ := by
    filter_upwards [hx_sum, hy_sum] with s has hbs
    calc
      _ ≤ (y s - l' * (s - 1).log - (x s - l * (s - 1).log)).re + (l'.re - l.re) * (s - 1).log := by
        grw [sum_le_hasSum S (h_nonneg s) (hasSum_re (hbs.sub has))]
      _ = (y s - x s).re := by grind [sub_re, re_mul_ofReal]
      _ ≤ ‖y s - x s‖ := re_le_norm _
  have h_cont : ContinuousAt (fun s ↦ ∑ v ∈ S, (d s v).re) 1 := by fun_prop (disch := simp)
  have h_log : Tendsto (fun s : ℝ ↦ (s - 1).log) (𝓝[>] 1) atBot :=
    tendsto_log_nhdsGT_zero.comp (by simp [Tendsto, map_subRight_nhdsGT])
  -- As `re l' < re l`, the left side of `h_bound` tends to `+∞`, but the right side is bounded.
  have h_lhs_top : Tendsto (fun s : ℝ ↦ ∑ v ∈ S, (d s v).re + (l'.re - l.re) * (s - 1).log)
      (𝓝[>] 1) atTop :=
    h_cont.continuousWithinAt.tendsto.add_atTop (h_log.const_mul_atBot_of_neg (sub_neg.mpr h_lt))
  have h_rhs_bdd : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s : ℝ ↦ ‖y s - x s‖ :=
    (hy_bdd.sub hx_bdd).isBoundedUnder_le
  exact not_isBoundedUnder_of_tendsto_atTop h_lhs_top (h_rhs_bdd.mono_le h_bound)

/-- For `c ∈ ℂ` the constant family `v ↦ c` has density `c` over the primes of degree one of `K`, in
the sense of `New.HasPrimeDensity`. -/
lemma hasPrimeDensity_const (c : ℂ) : HasPrimeDensity (fun _ : FinPlace K ↦ c) c := by
  -- For `s > 1` the Euler product with coefficients `1` is `ζ_K(s)`: group the ideals by norm.
  have h_zeta (s : ℝ) (hs : 1 < s) : dedekindZeta K s = eulerProd (fun _ : FinPlace K ↦ 1) s := by
    have h_sum := (hasSum_eulerProd (K := K) 1 (fun I ↦ by simp) hs).tsum_fiberwise absNorm
    -- For each `n`: the term of `ζ_K` at `n` is the sum over the ideals of norm `n`.
    refine (h_sum.congr_fun fun n ↦ ?_).tsum_eq
    have h_fiber (I : absNorm ⁻¹' {n}) :
        (1 : Ideal (𝓞 K) →* ℂ) I.val * ((absNorm I.val : ℕ) : ℂ) ^ (-s : ℂ) =
          (n : ℂ) ^ (-s : ℂ) := by
      rw [I.property, MonoidHom.one_apply, one_mul]
    -- The `Nat.card` ideals of norm `n` each give `n ^ (-s)`; for `n = 0` both sides are `0`.
    rw [tsum_congr h_fiber, tsum_const, nsmul_eq_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [zero_cpow (neg_ne_zero.mpr (ofReal_ne_zero.mpr (zero_lt_one.trans hs).ne'))]
    · simp [LSeries.term_of_ne_zero hn, cpow_neg, div_eq_mul_inv,
        Set.preimage, Set.coe_ofPred]
  -- The simple pole of `ζ_K` at `s = 1` gives the constant family `1` mean `1`; scale by `c`.
  have h_one : HasPrimeDensity (fun _ : FinPlace K ↦ 1) 1 := by
    refine hasPrimeDensity_of_tendsto (fun _ ↦ by simp)
      (ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K))
      (tendsto_nhdsWithin_congr (fun s hs ↦ ?_) (tendsto_sub_one_mul_dedekindZeta_nhdsGT K))
    rw [cpow_one, h_zeta s hs]
  simpa using HasPrimeDensity.sum (ι := Unit) (fun _ ↦ c) fun _ ↦ h_one

/-- A number field `K` has infinitely many primes of degree one, that is, finite places `w` whose
absolute norm `w.q` is a prime number. -/
lemma frequently_prime_q : ∃ᶠ w : FinPlace K in cofinite, w.q.Prime := by
  -- Otherwise the hypothesis of `HasPrimeDensity.re_le_re` for the constants `1` and `0` holds
  -- vacuously outside a finite set, and it gives `1 ≤ 0`.
  by_contra h_few
  have h_le := (hasPrimeDensity_const (K := K) 1).re_le_re (hasPrimeDensity_const 0)
    ((not_frequently.mp h_few).mono fun _ h_not h_prime ↦ (h_not h_prime).elim)
  norm_num at h_le

/-- Let `L/K` be an extension of number fields and `c ∈ ℂ`. Consider the family that sends `v` to
`c` times the number of places `w` of `L` above `v` whose residue field has the same cardinality
`q_w = q_v`, that is, those of relative residue degree one. This family has density `c` over the
primes of degree one of `K`: the sum of its values times `q_v ^ (-s)` over the `v` of prime norm is
`c * log (1 / (s - 1))` plus a term bounded as `s ↓ 1`. -/
lemma hasPrimeDensity_card_degree_one (L : Type*) [Field L] [NumberField L] [Algebra K L] (c : ℂ) :
    HasPrimeDensity (fun v : FinPlace K ↦ c * {w : FinPlace L | w.below K = v ∧ w.q = v.q}.ncard)
      c := by
  -- The constant family `c` on the primes of `L` has mean `c`; group its series by the prime of
  -- `K` below.
  obtain ⟨x, hx, h_sum⟩ : HasPrimeDensity (fun _ : FinPlace L ↦ c) c := hasPrimeDensity_const c
  refine ⟨x, hx, h_sum.mono fun s hs ↦ ?_⟩
  -- It remains to compare, for each `v`, the term of `v` with the sum over the primes above `v`.
  have h_fiber (v : FinPlace K) :
      ite v.q.Prime (c * {w : FinPlace L | w.below K = v ∧ w.q = v.q}.ncard) 0 * v.q ^ (-s : ℂ) =
        ∑' w : (fun w : FinPlace L ↦ w.below K) ⁻¹' {v},
          ite (w : FinPlace L).q.Prime c 0 * (w : FinPlace L).q ^ (-s : ℂ) := by
    set S : Set (FinPlace L) := {w : FinPlace L | w.below K = v ∧ w.q = v.q}
    have hS : S ⊆ (fun w : FinPlace L ↦ w.below K) ⁻¹' {v} := fun _ ⟨h_below, _⟩ ↦ h_below
    -- A prime `w` above `v` of prime norm lies in `S`, because `w.q` is a power of `v.q`.
    have h_prime (w : FinPlace L) (hw : w.below K = v) (hq : w.q.Prime) : w ∈ S := by
      subst hw
      obtain ⟨h_q_eq, -⟩ :=
        hq.pow_eq_iff.mp ((Ideal.under (𝓞 K) w.asIdeal).absNorm_pow_inertiaDeg w.asIdeal)
      exact ⟨rfl, h_q_eq.symm⟩
    -- On `S` every term is the same, since `w.q = v.q` there.
    have h_term (w : S) : ite (w : FinPlace L).q.Prime c 0 * ((w : FinPlace L).q : ℂ) ^ (-s : ℂ) =
        ite v.q.Prime c 0 * (v.q : ℂ) ^ (-s : ℂ) := by
      obtain ⟨w, -, hw_q⟩ := w
      rw [hw_q]
    -- Only the `w ∈ S` contribute to the sum over the primes above `v`.
    have h_support : Function.support (fun w : (fun w : FinPlace L ↦ w.below K) ⁻¹' {v} ↦
        ite (w : FinPlace L).q.Prime c 0 * ((w : FinPlace L).q : ℂ) ^ (-s : ℂ)) ⊆
          Set.range (Set.inclusion hS) := fun w hw ↦
      have hq : (w : FinPlace L).q.Prime := of_not_not fun hq ↦ by simp [hq] at hw
      ⟨⟨w, h_prime w w.property hq⟩, rfl⟩
    calc ite v.q.Prime (c * S.ncard) 0 * (v.q : ℂ) ^ (-s : ℂ)
        = S.ncard • (ite v.q.Prime c 0 * (v.q : ℂ) ^ (-s : ℂ)) := by
          by_cases hq : v.q.Prime <;> simp [hq, mul_left_comm, mul_assoc]
      _ = ∑' w : S, ite (w : FinPlace L).q.Prime c 0 * ((w : FinPlace L).q : ℂ) ^ (-s : ℂ) := by
          rw [tsum_congr h_term, tsum_const, Nat.card_coe_set_eq]
      _ = _ := (Set.inclusion_injective hS).tsum_eq h_support
  exact (hs.tsum_fiberwise fun w : FinPlace L ↦ w.below K).congr_fun h_fiber

end New

end

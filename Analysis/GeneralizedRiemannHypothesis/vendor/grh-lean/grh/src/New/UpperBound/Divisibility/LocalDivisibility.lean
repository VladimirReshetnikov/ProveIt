import New.UpperBound.Divisibility.ColengthAtLevel
import New.UpperBound.Divisibility.MarkOperator
import New.UpperBound.Divisibility.ValuationAtLevel
import New.UpperBound.Divisibility.ValuationAtNonSplitPrimes
import New.UpperBound.Size.Estimates

/-!
# The divisibility of the composite lift at each prime

This file bounds the gauge of the composite lift `New.Data.compositeLift` at a prime p, for a fixed
embedding ι : ℂ → ℂ_p; for p ≠ N it does so through the expansion `New.Data.restrictedChain` into
chains of `m` lifts. At the exceptional primes it uses the bound of
`New.Data.IsMarked.isOntoUpToColength_scaledHeckeOperator` for the elementary divisors of the
normalised Hecke operators `New.Data.IsMarked.scaledHeckeOperator`.

A form *has valuation at least* `v` if its gauge at the base point `1` is at most `p ^ (-v)`. The
*a-places* (`New.Data.aPlaces`) are the infinite places ≡ 1 modulo q₀. At a non-split prime `p < x₁`
that is not *exceptional* (`New.Data.IsExceptional`), the loss pays for all collisions between
a-places. For an exceptional prime `p < x₁`, a *full mark* is a choice `Λ` of one prime from each
conjugate pair induced by the a-places; the places *inducing* `Λ` are those that induce a prime of
`Λ`, the *odd* places those that induce the conjugate of one.

With `m` the number of lifts, `f` the number of infinite places of `E` and `a` the length of a long
row, the exponents below are built from the following numbers.

* `D.heckeScalingExponent l` is `a` times the number of a-places that induce the prime `l`.
* `D.collisionExponent p`, written `j_p`, is the ceiling of `2 m f a / p`.
* `D.collisionSum p ev` is the sum of `a / p ^ e` over the collisions `(τ, e)` outside the set of
  places `ev` (`New.Data.IsCollision`).

## Main definitions and results

* `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_one`: for p different from N and d, the chain
  of lifts keeps integrality.
* `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_collisionSum`: at a non-split prime `p < x₁`
  the bounds for single lifts add up to the gain, less the loss and `m` times the collision sum.
* `New.Data.IsWeakChainDatum.gaugeLe_restrictedChain_of_isFullMark`: for a full mark Λ, the bound
  for `New.Data.restrictedChain` on the image of the m-th power of the product of the operators
  `New.Data.IsMarked.scaledHeckeOperator`.
* `New.Data.IsMarked.isOntoUpToColength_prod_scaledHeckeOperator_pow`: this power keeps the integral
  source forms and is onto modulo `p ^ j_p` up to a small colength.
* `New.Data.exists_colengthDvd_gaugeLe_compositeLift`: there is a module of source forms whose
  integral members have colength at most l in the integral source forms, with
  l ≤ allowedLoss(p) · dim (source forms), and on whose ramified members the composite lift of a
  chain datum has valuation at least gain(p) − allowedLoss(p).
* `New.Data.exists_err_gaugeLe_compositeLift`: the same bound for all primes p, on a submodule of
  the integral ramified source forms, with losses err(p) such that every finite sum ∑ err(p) log p
  is at most `New.Data.errorUnit`.

Notions from other files:
* `New.GaugeLe d c φ`: for every `g`, the p-adic gauge of the value `φ g` at `g * d` is at most `c`.
* `New.ColengthDvd M N z`: the index of `N` in `M` divides `z`, that is, each finite family in `M`
  has combinations in `N` by a matrix whose determinant divides `z`.
* `New.IsOntoUpToColength p M n y c`: the endomorphism `y` keeps `M`, and `y (M) + p ^ n • M` has
  index dividing `p ^ l` in `M` for some natural number `l ≤ c`.
* `New.Data.allowedLoss`: 2·loss(p) for a non-split prime p < x₁ (`New.Data.loss`); otherwise 2mfb
  if p = N, and 0 if not.
* `New.Data.gain`: the divisibility asked of the chain of lifts at p.

## Relation to the literature

For each prime p and twist of conductor prime to p, the chain of theta lifts is divisible by the
predicted power of p, less an error, on a submodule of the ramified source forms whose colength per
dimension is at most that error. The errors times log p have a small sum, which gives the
divisibility side of the bound. p-integrality of single theta lifts is known in the literature.
Related work: X. Zhang, Non-vanishing mod p of theta lifts for (O(2n+1),Mp(4n)), 2022; Berger,
Arithmetic properties of similitude theta lifts, 2009; Prasanna, Integrality of a ratio of Petersson
norms, 2006.

At an inert prime p pairing two a-places, each lift may lose divisibility. Outside a sparse set of
such p, the chain regains the predicted power of p, up to about one lift's loss, on the image of
scaled Hecke operators above p applied once per lift. Once enlarged by a p-power multiple of all
source forms, this image has small colength. Hecke operators passing through theta lifts, p-power
scaling by weight and p-adapted lifts at ordinary p are known in the literature. Related work:
Rallis, Langlands' functoriality and the Weil representation, 1982; V. Lafforgue, Estimées pour les
valuations p-adiques des valeurs propres des opérateurs de Hecke, 2011; Z. Liu, Test Schwartz
functions at p for theta lifts of Hida families, arXiv 2510.21644, 2025.
-/

open Module Finset Submodule Real

namespace New.GaugeLe

/-! ## Gauge bounds under sums, scalars and larger exponents -/

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  {κ : NumberField.InfinitePlace E → ℕ → ℕ} {e : NumberField.InfinitePlace E → ℤ}
  {p : ℕ} [hp : Fact p.Prime] [PadicPlace p] {d : Gf E n}

/-- Gauge bounds can be weakened. If the `p`-adic gauge of every value `φ g` of a form, taken at
`g * d` for a fixed adelic point `d` (`New.GaugeLe`), is at most `p ^ r`, then it is at most
`p ^ r'` for every `r' ≥ r`. -/
lemma rpow_mono {r r' : ℝ} {φ : AlgForm (E := E) n κ e} (hφ : GaugeLe d (p ^ r) φ) (hr : r ≤ r') :
    GaugeLe d (p ^ r') φ :=
  fun g ↦ (hφ g).trans (rpow_le_rpow_of_exponent_le (mod_cast hp.1.pos) hr)

/-- The `p`-adic gauge is ultrametric. If, for a fixed adelic point `d` and every `g`, the gauges of
the values of two forms at `g`, taken at `g * d` (`New.GaugeLe`), are at most `c`, then the same
holds for the sum of the two forms. -/
lemma add {c : ℝ} {φ ψ : AlgForm (E := E) n κ e} (hφ : GaugeLe d c φ) (hψ : GaugeLe d c ψ) :
    GaugeLe d c (φ + ψ) := fun g ↦ by
  simpa [weylGauge, Matrix.mulVec_add] using
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hφ g) (hψ g))

/-- Let `c` bound, for a fixed adelic point `d` and every `g`, the `p`-adic gauge of the value `φ g`
at `g * d` (`New.GaugeLe`). Then the values of `a • φ` are bounded in the same sense by `c` times
the `p`-adic absolute value of the complex number `a`. -/
lemma smul {c : ℝ} {φ : AlgForm (E := E) n κ e} (hφ : GaugeLe d c φ) (a : ℂ) :
    GaugeLe d (‖ιₚ a‖ * c) (a • φ) := fun g ↦ by
  rw [Submodule.coe_smul, Pi.smul_apply, weylGauge_smul]
  exact mul_le_mul_of_nonneg_left (hφ g) (norm_nonneg _)

/-- Let `p ^ r` bound, for a fixed adelic point `d` and every `g`, the `p`-adic gauge of the value
`φ g` at `g * d` (`New.GaugeLe`), and let `β` be an integer with `β ≤ -r`. Then `p ^ (-β) • φ` has
these gauges at most `1`. -/
lemma zpow_neg_smul {r : ℝ} {β : ℤ} {φ : AlgForm (E := E) n κ e} (hφ : GaugeLe d (p ^ r) φ)
    (hβ : β ≤ -r) : GaugeLe d 1 ((p : ℂ) ^ (-β) • φ) := by
  have hp_pos : (0 : ℝ) < p := mod_cast hp.1.pos
  have h_norm : ‖ιₚ ((p : ℂ) ^ (-β))‖ = p ^ (β : ℝ) := by simp [norm_p_eq_inv]
  have h_smul : GaugeLe d (p ^ (β + r)) ((p : ℂ) ^ (-β) • φ) := by
    rw [rpow_add hp_pos, ← h_norm]
    exact hφ.smul _
  simpa using h_smul.rpow_mono (r' := 0) (by linarith)

end New.GaugeLe

namespace New.Data

section FixedPrime

variable {P : Parameters} {D : Data P} {p : ℕ} [hp : Fact p.Prime] [PadicPlace p]
  {Λ : Finset (FinPlace D.E)}

/-! ## The valuation of the chains of lifts of a weak chain datum -/

variable {ϑ : D.Twist} {Ψ : D.Translations →₀ ℂ}

/-- Let `Ψ` be a weak chain datum for the twist `ϑ`: coefficients, subject to integrality and
invariance conditions, of tuples `x` of translations. The datum `translateDatum x j` of the `j`-th
theta lift is the normalised vacuum vector translated by `x j`. That it lies in
`raises 1 1 (p ^ r j)` says that this lift, with both gauges based at the identity, multiplies
`p`-adic gauges by at most `p ^ r j`. Suppose this holds for every `x` in the support of `Ψ`, that
`p ≠ D.N`, and that `p` is prime to `ϑ.normQ`, the product of the norms of the places in the set Q
of `ϑ`. Then `restrictedChain ϑ Ψ`, the combination with coefficients `Ψ` of chains of `D.m` lifts,
sends an integral source form to a form of gauge at most `p ^ ∑ j < D.m, r j`. -/
lemma IsWeakChainDatum.gaugeLe_restrictedChain_of_mem_raises (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) (hN : p ≠ D.N) {r : ℕ → ℝ}
    (h_raises : ∀ x ∈ Ψ.support, ∀ j : ℕ,
      D.translateDatum x j ∈ (D.liftKernel ϑ j).raises 1 1 (p ^ r j))
    {v : D.SourceForm} (hv : v ∈ D.integralSourceForms) :
    GaugeLe 1 (p ^ ∑ j ∈ range D.m, r j) (restrictedChain ϑ Ψ v) := by
  exact GaugeLe.restrictToY D hN (hΨ.gaugeLe_chain hQ (t := 1) (by simp) (d := 1)
    (fun x hx j _ ↦ h_raises x hx j) hv.2)

/-- Let `Ψ` be a weak chain datum for the twist `ϑ`: coefficients, subject to integrality and
invariance conditions, of tuples of translations. Let `p` be a prime prime to the norm of the level
of `ϑ` and different from the level `N` and from `d`, the prime parameter that defines the quadratic
character `χ_K`. Then `restrictedChain ϑ Ψ`, the combination with coefficients `Ψ` of chains of `m`
theta lifts, sends an integral source form `v` to an integral form: in `GaugeLe 1 1`, the first `1`
is the base point, the second the bound on the `p`-adic gauge. -/
lemma IsWeakChainDatum.gaugeLe_restrictedChain_one (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) {v : D.SourceForm}
    (hv : v ∈ D.integralSourceForms) (hN : p ≠ D.N) (hd : p ≠ P.d) :
    GaugeLe 1 1 (restrictedChain ϑ Ψ v) := by
  -- The data are standard for `δ = piMBar` and the scale is `star δ`, so each lift multiplies
  -- gauges by at most a power of `‖ιₚ d‖⁻¹ = 1`.
  have h_norm_d : ‖(P.d : PadicComplex p)‖ = 1 :=
    ((p.coprime_primes hp.1 P.d_prime).2 hd).norm_natCast_eq_one _
  have h_ratio : ‖ιₚ (star (D.piMBar : ℂ))‖ / ‖ιₚ (star (D.piMBar : ℂ) * P.d)‖ = 1 := by
    simp [h_norm_d]
  have h_raises (x : D.Translations) (hx : x ∈ Ψ.support) (j : ℕ) :
      D.translateDatum x j ∈ (D.liftKernel ϑ j).raises 1 1 (p ^ (0 : ℝ)) := by
    have h_standard : D.translateDatum x j ∈ (D.liftKernel ϑ j).raises 1 1
        ((‖ιₚ (star (D.piMBar : ℂ))‖ / ‖ιₚ (star (D.piMBar : ℂ) * P.d)‖) ^
          boxes D.columnCount (Fintype.card (D.X (j + 1)))) :=
      P.mem_raises_of_standardData (c := star D.piMBar) D.piMBar_ne_zero
        (hΨ.translateDatum_mem_standardData hQ hN hx j (.inl rfl))
    rwa [h_ratio, one_pow, ← rpow_zero p] at h_standard
  have h_chain : GaugeLe 1 (p ^ ∑ _j ∈ range D.m, (0 : ℝ)) (restrictedChain ϑ Ψ v) :=
    hΨ.gaugeLe_restrictedChain_of_mem_raises hQ hN h_raises hv
  simpa using h_chain

/-- Let `Ψ` be a weak chain datum for the twist `ϑ`, and `p < x₁` a non-split prime
(`IsSmallNonsplit`) prime to the norm of the level of `ϑ`. For an integral source form `v`, the
image under the combination `restrictedChain ϑ Ψ` of chains of `m` theta lifts has valuation at
least `gain p - loss p - m * collisionSum p ∅`.

Here `gain p` is the divisibility asked of the chain at `p` and `loss p = f a (log b)² / p`, times
`m` if `p ≡ ±1` modulo `m`. -/
lemma IsWeakChainDatum.gaugeLe_restrictedChain_collisionSum (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ)
    {v : D.SourceForm} (hv : v ∈ D.integralSourceForms) (hp_small : D.IsSmallNonsplit p) :
    GaugeLe 1 (p ^ (D.m * D.collisionSum p ∅ + D.loss p - D.gain p)) (restrictedChain ϑ Ψ v) := by
  obtain ⟨hp_M, hp_N, -⟩ := hp_small.not_dvd_M_mul_N
  have hm_pos : (0 : ℝ) < D.m := HasLogBound.pos D
  -- As `p` does not divide `D.M`, the product of the two level primes, the data are standard for
  -- every `δ`, so lift `j` raises valuations by `divisibilityBound p j ∅`.
  have h_raises (x : D.Translations) (hx : x ∈ Ψ.support) (j : ℕ) :
      D.translateDatum x j ∈ (D.liftKernel ϑ j).raises 1 1 (p ^ (-D.divisibilityBound p j ∅)) :=
    D.mem_raises_neg_divisibilityBound hp_small.2 ϑ
      (hΨ.translateDatum_mem_standardData hQ hp_N hx j (.inr hp_M))
  have h_lift (j : ℕ) (hj : j ∈ range D.m) :
      -D.divisibilityBound p j ∅ ≤ D.collisionSum p ∅ + (D.loss p - D.gain p) / D.m := by
    have h_bound : D.gain p / D.m - D.collisionSum p ∅ - D.f * D.logB ^ 2 * (D.a / p) / D.m ≤
        D.divisibilityBound p j ∅ := by
      simpa using le_divisibilityBound (mem_range.1 hj) hp_small ∅
    have h_loss : D.f * D.logB ^ 2 * (D.a / p) / D.m ≤ D.loss p / D.m :=
      div_le_div_of_nonneg_right (D.le_loss p) hm_pos.le
    rw [sub_div]
    linarith
  refine (hΨ.gaugeLe_restrictedChain_of_mem_raises hQ hp_N h_raises hv).rpow_mono ?_
  calc ∑ j ∈ range D.m, -D.divisibilityBound p j ∅
      ≤ ∑ _j ∈ range D.m, (D.collisionSum p ∅ + (D.loss p - D.gain p) / D.m) := sum_le_sum h_lift
    _ = D.m * D.collisionSum p ∅ + D.loss p - D.gain p := by
        rw [sum_const, card_range, nsmul_eq_mul]
        field

/-- The crude bound. Let `Ψ` be a weak chain datum for the twist `ϑ`, and `p < x₁` a non-split prime
(`IsSmallNonsplit`) prime to the norm of the level of `ϑ`. For an integral source form `v` and
`j_p = D.collisionExponent p = ⌈2 m f a / p⌉`, the image of `p ^ j_p • v` under the combination
`restrictedChain ϑ Ψ` of chains of `m` theta lifts has valuation at least `gain p - loss p`. -/
lemma IsWeakChainDatum.gaugeLe_pow_collisionExponent_smul (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) {v : D.SourceForm} (hv : v ∈ D.integralSourceForms)
    (hp_small : D.IsSmallNonsplit p) :
    GaugeLe 1 (p ^ (D.loss p - D.gain p))
      (restrictedChain ϑ Ψ ((p : ℂ) ^ D.collisionExponent p • v)) := by
  have hp_pos : (0 : ℝ) < p := mod_cast hp.1.pos
  -- Every collision `(τ, e)` has `e ≥ 1`, so `j_p` pays for the collisions of all `m` lifts.
  have h_paid : D.m * D.collisionSum p ∅ ≤ D.collisionExponent p := by
    have h_sum : D.collisionSum p ∅ ≤ 2 * D.f * D.a / p ^ 1 :=
      collisionSum_le fun h_coll ↦ (mem_positivePartnerExponents.1 h_coll.1).1
    rw [collisionExponent]
    grw [h_sum, pow_one, ← Nat.le_ceil]
  have h_norm : ‖ιₚ ((p : ℂ) ^ D.collisionExponent p)‖ = p ^ (-D.collisionExponent p : ℝ) := by
    simp [norm_p_eq_inv, rpow_neg]
  have h_gauge :
      GaugeLe 1 (p ^ (-D.collisionExponent p + (D.m * D.collisionSum p ∅ + D.loss p - D.gain p)))
        ((p : ℂ) ^ D.collisionExponent p • restrictedChain ϑ Ψ v) := by
    rw [rpow_add hp_pos, ← h_norm]
    exact (hΨ.gaugeLe_restrictedChain_collisionSum hQ hv hp_small).smul _
  rw [map_smul]
  exact h_gauge.rpow_mono (by linarith)

/-- **Valuation.** Let `Ψ` be a weak chain datum for the twist `ϑ` (`New.Data.IsWeakChainDatum`) and
let `p` be prime to the norm of the level of `ϑ`. Let `Λ` be a full mark: a set of primes above `p`,
disjoint from its conjugate and induced by a-places, that contains the prime of each a-place or its
conjugate, where `p < x₁` is exceptional and non-split. Let `Y` be the product over `l ∈ Λ` of
`scaledHeckeOperator l`, the Hecke operator at `l` of index `D.ceilLogLifts p` scaled by
`p ^ heckeScalingExponent l`.

For an integral source form `v`, the image of `(Y ^ m) v` under the combination
`restrictedChain ϑ Ψ` of chains of `m` theta lifts has valuation at least `gain p - 2 * loss p`,
that is, `p`-adic gauge at most `p ^ (2 * loss p - gain p)`. Here `gain p` is the divisibility asked
of the chain and `loss p = f a (log b)² / p`, times `m` if `p ≡ ±1` modulo `m`. -/
theorem IsWeakChainDatum.gaugeLe_restrictedChain_of_isFullMark (hΨ : IsWeakChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ)
    {v : D.SourceForm} (hv : v ∈ D.integralSourceForms) (hΛ : D.IsFullMark Λ) :
    GaugeLe 1 (p ^ (2 * D.loss p - D.gain p))
      (restrictedChain ϑ Ψ (((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m) v)) := by
  have hm_pos : (0 : ℝ) < D.m := HasLogBound.pos D
  -- No collision is left. The surplus `a / x₁` at each a-place inducing a prime of `Λ`, with
  -- `loss p / m`, pays for the low columns (`lowColumns`) and for the powers
  -- `p ^ transferExponent p`.
  have h_lift (j : ℕ) (hj : j ∈ range D.m) :
      #Λ * D.transferExponent p + liftLoss Λ j ≤ (2 * D.loss p - D.gain p) / D.m := by
    have h_bound : D.gain p / D.m + #(D.aPlaces ∩ placesInducing Λ) * (D.a / D.x₁) -
        D.f * D.logB ^ 2 * (D.a / p) / D.m ≤ D.divisibilityBound p j (placesInducing Λ) := by
      have h_ne : p ≠ P.d := ne_of_chiK_ne_zero (by simp [hΛ.isExceptional.chiK_eq_neg_one])
      simpa [hΛ.collisionSum_placesInducing_eq_zero, piPrimeValuation_of_ne h_ne] using
        le_divisibilityBound (mem_range.1 hj) hΛ.isSmallNonsplit (placesInducing Λ)
    have h_low : #Λ * D.transferExponent p + D.ceilLogLifts p * ∑ σ ∈ placesInducing Λ,
          D.lowColumns j σ ≤
        D.loss p / D.m + #(D.aPlaces ∩ placesInducing Λ) * (D.a / D.x₁) :=
      hΛ.card_mul_transferExponent_add_sum_lowColumns_le (mem_range.1 hj)
    have h_loss : D.f * D.logB ^ 2 * (D.a / p) / D.m ≤ D.loss p / D.m :=
      div_le_div_of_nonneg_right (D.le_loss p) hm_pos.le
    rw [liftLoss, sub_div, mul_div_assoc]
    linarith
  refine (hΨ.gaugeLe_scaledHeckeOperator_pow hQ hΛ.toIsMarked hv).rpow_mono ?_
  calc ∑ j ∈ range D.m, (#Λ * D.transferExponent p + liftLoss Λ j)
      ≤ ∑ _j ∈ range D.m, (2 * D.loss p - D.gain p) / D.m := sum_le_sum h_lift
    _ = 2 * D.loss p - D.gain p := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hm_pos.ne']

/-! ## The index of the image of the scaled Hecke operators -/

/-- Let `Λ` be a marked set of primes of `E` above the exceptional non-split prime `p < x₁`: it is
disjoint from its conjugate and each of its primes is induced by an a-place. Let
`A_l = heckeScalingExponent l`, which is `a` times the number of a-places that induce `l`,
`j_p = collisionExponent p = ⌈2 m f a / p⌉`, `m` the number of lifts and `f` the number of infinite
places of `E`. Then `m` times the sum over `l ∈ Λ` of `12 A_l / (m p) + j_p / (m ^ 2 f)`, the
colength exponent per dimension of the scaled Hecke operator at `l`, is at most `loss p`, which is
`f a (log b)² / p`, times `m` if `p ≡ ±1` modulo `m`. -/
lemma IsMarked.mul_sum_heckeScalingExponent_le_loss (hΛ : D.IsMarked Λ) :
    D.m * ∑ l ∈ Λ, (12 * D.heckeScalingExponent l / (D.m * p) +
      1 / (D.m ^ 2 * D.f) * D.collisionExponent p : ℝ) ≤ D.loss p := by
  have hp_pos : (0 : ℝ) < p := mod_cast hp.1.pos
  have hm_pos : (0 : ℝ) < D.m := HasLogBound.pos D
  have hf_pos : (0 : ℝ) < D.f := HasLogBound.pos D
  -- Each a-place induces one prime, so the `A_l` add up to at most `a f`.
  have h_sum : ∑ l ∈ Λ, heckeScalingExponent l ≤ D.a * D.f :=
    (sum_heckeScalingExponent Λ).trans_le (Nat.mul_le_mul_left _ (card_le_univ _))
  have h_exponent : (D.collisionExponent p : ℝ) ≤ 2 * D.m * D.f * D.a / p + 1 := by
    rw [collisionExponent]
    exact (Nat.ceil_lt_add_one (by positivity)).le.trans_eq (by ring)
  have h_size : (14 * D.f * D.a + p / D.m : ℝ) ≤ D.f * D.logB ^ 2 * D.a := by
    -- The size of `p < x₁`, as an instance for `D.le_of_hasLogBound`.
    have hp_size : D.HasLogUpper p D.logX₁ :=
      D.hasLogUpper_of_le_of_nonneg hΛ.isSmallNonsplit.1.le p.cast_nonneg
    exact D.le_of_hasLogBound
  calc D.m * ∑ l ∈ Λ, (12 * D.heckeScalingExponent l / (D.m * p) +
          1 / (D.m ^ 2 * D.f) * D.collisionExponent p : ℝ)
      = D.m * (12 * (∑ l ∈ Λ, heckeScalingExponent l : ℕ) / (D.m * p) +
          #Λ * (1 / (D.m ^ 2 * D.f) * D.collisionExponent p)) := by
        rw [sum_add_distrib, ← sum_div, ← mul_sum, sum_const, nsmul_eq_mul, Nat.cast_sum]
    _ ≤ D.m * (12 * (D.a * D.f : ℕ) / (D.m * p) +
          D.f * (1 / (D.m ^ 2 * D.f) * (2 * D.m * D.f * D.a / p + 1))) := by
        gcongr
        exact hΛ.card_le
    _ = (14 * D.f * D.a + p / D.m) / p := by
        push_cast
        field
    _ ≤ D.f * D.logB ^ 2 * D.a / p := div_le_div_of_nonneg_right h_size hp_pos.le
    _ ≤ D.loss p := (mul_div_assoc _ _ _).trans_le (D.le_loss p)

/-- **Colength.** Let `Λ` be a marked set of primes above the exceptional non-split prime `p < x₁`,
`Y` the product over `l ∈ Λ` of the Hecke operators at `l` scaled by `p ^ heckeScalingExponent l`,
and `M` the module of integral source forms. Then `Y ^ m`, with `m` the number of lifts, keeps `M`,
and the index of `Y ^ m M + p ^ j_p M` in `M` divides `p ^ c` for some natural number
`c ≤ loss p * dim (source forms)`. -/
theorem IsMarked.isOntoUpToColength_prod_scaledHeckeOperator_pow (hΛ : D.IsMarked Λ) :
    IsOntoUpToColength ↑p D.integralSourceForms (D.collisionExponent p)
      ((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m)
        (D.loss p * finrank ℂ D.SourceForm) := by
  -- Exponents add under products, and `Y ^ m` is the product over `m` copies of `Λ`.
  let L : List Λ := (List.replicate D.m Λ.attach.toList).flatten
  let cost (l : FinPlace D.E) : ℝ :=
    12 * D.heckeScalingExponent l / (D.m * p) + 1 / (D.m ^ 2 * D.f) * D.collisionExponent p
  have h_onto : IsOntoUpToColength ↑p D.integralSourceForms (D.collisionExponent p)
      (L.map hΛ.scaledHeckeOperator).prod (L.map fun l : Λ ↦ cost l * finrank ℂ D.SourceForm).sum :=
    IsOntoUpToColength.prod L fun l _ ↦ hΛ.isOntoUpToColength_scaledHeckeOperator
      (D.collisionExponent p) l.2
  have h_prod :
      (L.map hΛ.scaledHeckeOperator).prod = (Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^
        D.m := by
    simp [L]
  have h_cost : (L.map fun l : Λ ↦ cost l * finrank ℂ D.SourceForm).sum =
      (D.m * ∑ l ∈ Λ, cost l) * finrank ℂ D.SourceForm := by
    rw [← Λ.sum_attach, mul_assoc, sum_mul, ← sum_map_toList]
    simp [L, List.sum_flatten]
  rw [h_prod, h_cost] at h_onto
  obtain ⟨h_stable, c, hc, h_index⟩ := h_onto
  exact ⟨h_stable, c, hc.trans
    (mul_le_mul_of_nonneg_right hΛ.mul_sum_heckeScalingExponent_le_loss (Nat.cast_nonneg _)),
      h_index⟩

omit [PadicPlace p] in
/-- A prime `p` lies in `D.smallNonsplitPrimes` if and only if `p < x₁` and `χ_K(p) ≠ 1`. -/
lemma mem_smallNonsplitPrimes_iff_isSmallNonsplit :
    p ∈ D.smallNonsplitPrimes ↔ D.IsSmallNonsplit p := by
  simp [Nat.lt_ceil, hp.1]

omit [PadicPlace p] in
/-- A prime `p` outside `D.smallNonsplitPrimes` splits in `K`, that is `χ_K(p) = 1`, or is at least
`x₁`. -/
lemma chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes (h_notMem : p ∉ D.smallNonsplitPrimes) :
    chiK P.d p = 1 ∨ D.x₁ ≤ p := by
  rwa [mem_smallNonsplitPrimes_iff_isSmallNonsplit, not_and_or, not_lt, not_ne_iff, or_comm]
    at h_notMem

open scoped Pointwise in
/-- Let `Ψ` be a chain datum for the twist `ϑ`, with `p` prime to the norm of the level of `ϑ`. Let
`Λ` be a full mark: a set of primes above the exceptional non-split prime `p < x₁`, disjoint from
its conjugate and induced by a-places, that contains the prime of each a-place or its conjugate. Let
`Y` be the product over `l ∈ Λ` of the Hecke operators at `l` scaled by
`p ^ heckeScalingExponent l`, `M` the module of integral source forms over the ring `embValRing` of
complex numbers that are `p`-integral under `ιₚ`, and `j_p = collisionExponent p = ⌈2 m f a / p⌉`.

The composite lift passes a source form through `m` theta lifts with the glued tensor of `Ψ` as data
and restricts the result from `X_m` to `Y_m`. For a source form in `Y ^ m M + p ^ j_p M` it has
valuation at least `gain p - 2 * loss p`. -/
lemma IsChainDatum.gaugeLe_compositeLift_of_isFullMark (hΨ : IsChainDatum ϑ Ψ)
    (hQ : p.Coprime ϑ.normQ) (hΛ : D.IsFullMark Λ) {φ : D.SourceForm}
    (hφ : φ ∈ D.integralSourceForms.map ((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m) ⊔
      (p : embValRing) ^ D.collisionExponent p • D.integralSourceForms) :
    GaugeLe 1 (p ^ (2 * D.loss p - D.gain p)) (compositeLift ϑ Ψ φ) := by
  have h_loss : 0 ≤ D.loss p := le_trans (by positivity) (D.le_loss p)
  obtain ⟨Ψ', hΨ', h_eq⟩ : ∃ Ψ' : D.Translations →₀ ℂ, IsWeakChainDatum ϑ Ψ' ∧
      ∀ φ : D.SourceForm, compositeLift ϑ Ψ φ = restrictedChain ϑ Ψ' φ :=
    hΨ.exists_isWeakChainDatum_compositeLift_eq
  obtain ⟨u, hu, v, hv, rfl⟩ : ∃ u ∈ D.integralSourceForms, ∃ v ∈ D.integralSourceForms,
      ((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m) u +
        (p : ℂ) ^ D.collisionExponent p • v = φ := by
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, h_sum⟩ := mem_sup.1 hφ
    exact ⟨u, hu, v, hv, h_sum⟩
  rw [h_eq, map_add]
  exact (hΨ'.gaugeLe_restrictedChain_of_isFullMark hQ hu hΛ).add
    ((hΨ'.gaugeLe_pow_collisionExponent_smul hQ hv hΛ.isSmallNonsplit).rpow_mono (by linarith))

end FixedPrime

/-- The divisibility at one prime. There are a natural number `l ≤ allowedLoss p * dim`, where `dim`
is the dimension of the space of source forms, and a module `S` of source forms whose integral
members have index dividing `p ^ l` in the integral source forms (`New.ColengthDvd`), such that for
every twist `ϑ` of level prime to `p` and every chain datum `Ψ` (`New.Data.IsChainDatum`) the
composite lift of a ramified source form in `S` has valuation at least `gain p - allowedLoss p`. -/
theorem exists_colengthDvd_gaugeLe_compositeLift {P : Parameters} {D : Data P} {p : ℕ}
    [hp : Fact p.Prime] [PadicPlace p] :
    ∃ (l : ℕ) (S : Submodule embValRing D.SourceForm),
      l ≤ D.allowedLoss p * finrank ℂ D.SourceForm ∧
      ColengthDvd D.integralSourceForms S (p ^ l) ∧
      ∀ (ϑ : D.Twist) (Ψ : D.Translations →₀ ℂ), IsChainDatum ϑ Ψ → p.Coprime ϑ.normQ →
        ∀ φ ∈ S, φ ∈ D.ramifiedSourceForms →
          GaugeLe 1 (p ^ (D.allowedLoss p - D.gain p)) (compositeLift ϑ Ψ φ) := by
  -- There are four cases: `p ≠ N` split or at least `x₁`; `p < x₁` non-split and not exceptional;
  -- `p < x₁` exceptional; and `p = N`. Away from `N`, a chain datum expands into a weak chain
  -- datum.
  have h_loss : 0 ≤ D.loss p := le_trans (by positivity) (D.le_loss p)
  have h_cases : (p ∉ D.smallNonsplitPrimes ∧ p ≠ D.N) ∨
    (p ∈ D.smallNonsplitPrimes ∧ ¬D.IsExceptional p) ∨
      (p ∈ D.smallNonsplitPrimes ∧ D.IsExceptional p) ∨ (p ∉ D.smallNonsplitPrimes ∧ p = D.N) := by
    tauto
  obtain ⟨h_mem, hN⟩ | ⟨h_mem, h_exc⟩ | ⟨h_mem, h_exc⟩ | ⟨h_mem, hN⟩ := h_cases
  · -- `p ≠ N` is split or at least `x₁`, so it differs from `d` and has no gain.
    rw [allowedLoss, ite_eq_right h_mem, ite_eq_right hN]
    have hd : p ≠ P.d := by
      rintro rfl
      exact h_mem (mem_smallNonsplitPrimes_iff_isSmallNonsplit.2
        ⟨D.lt_of_hasLogBound, by simp [chiK, ZMod.natCast_self]⟩)
    refine ⟨0, D.integralSourceForms, by simp, .of_le le_rfl, fun ϑ Ψ hΨ hQ φ hφ _ ↦ ?_⟩
    obtain ⟨Ψ', hΨ', h_eq⟩ : ∃ Ψ' : D.Translations →₀ ℂ, IsWeakChainDatum ϑ Ψ' ∧
        ∀ φ : D.SourceForm, compositeLift ϑ Ψ φ = restrictedChain ϑ Ψ' φ :=
      hΨ.exists_isWeakChainDatum_compositeLift_eq
    rw [h_eq, D.gain_eq_zero (chiK_eq_one_or_le_of_notMem_smallNonsplitPrimes h_mem), sub_zero,
      rpow_zero]
    exact hΨ'.gaugeLe_restrictedChain_one hQ hφ hN hd
  · -- `p < x₁` is not exceptional: the loss pays for the collisions on all integral source forms.
    rw [allowedLoss, ite_eq_left h_mem]
    have h_nonsplit : D.IsSmallNonsplit p := mem_smallNonsplitPrimes_iff_isSmallNonsplit.1 h_mem
    have h_paid : D.m * D.collisionSum p ∅ ≤ D.loss p :=
      mul_collisionSum_le_loss h_nonsplit h_exc
    refine ⟨0, D.integralSourceForms, mod_cast by positivity, .of_le le_rfl,
      fun ϑ Ψ hΨ hQ φ hφ _ ↦ ?_⟩
    obtain ⟨Ψ', hΨ', h_eq⟩ : ∃ Ψ' : D.Translations →₀ ℂ, IsWeakChainDatum ϑ Ψ' ∧
        ∀ φ : D.SourceForm, compositeLift ϑ Ψ φ = restrictedChain ϑ Ψ' φ :=
      hΨ.exists_isWeakChainDatum_compositeLift_eq
    rw [h_eq]
    exact (hΨ'.gaugeLe_restrictedChain_collisionSum hQ hφ h_nonsplit).rpow_mono (by linarith)
  · -- `p < x₁` is exceptional: for a full mark `Λ` with operator `Y`, the module is
    -- `Y ^ m M + p ^ j_p M`, where `M` is the module of integral source forms.
    rw [allowedLoss, ite_eq_left h_mem]
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : Finset (FinPlace D.E), D.IsFullMark Λ :=
      D.exists_isFullMark (mem_smallNonsplitPrimes_iff_isSmallNonsplit.1 h_mem).1 h_exc
    obtain ⟨-, l, hl, h_index⟩ : IsOntoUpToColength ↑p D.integralSourceForms (D.collisionExponent p)
        ((Λ.attach.toList.map hΛ.scaledHeckeOperator).prod ^ D.m)
          (D.loss p * finrank ℂ D.SourceForm) :=
      hΛ.isOntoUpToColength_prod_scaledHeckeOperator_pow
    have h_le : D.loss p * finrank ℂ D.SourceForm ≤ 2 * D.loss p * finrank ℂ D.SourceForm := by
      gcongr
      linarith
    exact ⟨l, _, hl.trans h_le, h_index, fun ϑ Ψ hΨ hQ φ hφ _ ↦
      hΨ.gaugeLe_compositeLift_of_isFullMark hQ hΛ hφ⟩
  · -- `p = N`: the module consists of the source forms in `upIntegralForms`, and `x₁ ≤ N` makes the
    -- gain zero.
    rw [allowedLoss, ite_eq_right h_mem, ite_eq_left hN]
    subst hN
    have h_size : 0 ≤ D.m * D.f * D.b := (HasLogBound.pos D).le
    obtain ⟨l, hl, h_index⟩ : ∃ l : ℕ, l ≤ D.m * D.f * D.b * finrank ℂ D.SourceForm ∧
        ColengthDvd (integralFormsAt D.SourceForm 1) D.upIntegralForms (D.N ^ l) :=
      D.exists_colengthDvd_upIntegralForms_pow
    have h_le :
        D.m * D.f * D.b * finrank ℂ D.SourceForm ≤ 2 * D.m * D.f * D.b * finrank ℂ
          D.SourceForm := by
      gcongr
      linarith
    refine ⟨l, D.upIntegralForms.comap (D.SourceForm.subtype.restrictScalars embValRing),
      hl.trans h_le, h_index.comap _ le_rfl fun _ _ ↦ mem_comap.2,
      fun ϑ Ψ hΨ _ φ hφ h_ram ↦ ?_⟩
    rw [D.gain_eq_zero (.inr D.le_of_hasLogBound), sub_zero]
    exact D.gaugeLe_compositeLift_at_N hΨ h_ram hφ

/-- **Divisibility of the composite lift.** There are real numbers `err p` with these properties.
* (a) Each `err p` is non-negative.
* (b) If `p ≠ N`, and `chiK d p = 1` (split primes) or `x₁ ≤ p`, then `err p = 0`.
* (c) Every finite sum `∑ err p * log p` is at most `errorUnit`.
* (d) For every prime `p` and every embedding `ιₚ` of `ℂ` in `ℂ_p`, the module of integral ramified
  source forms has a submodule `S`, over the ring `embValRing` of numbers that `ιₚ` sends to
  `p`-adic integers, of index dividing `p ^ l` for a natural number `l ≤ err p * dim`, such that the
  composite lift of every source form in `S` has valuation at least `gain p - err p`, for all twists
  `ϑ` of level prime to `p` and all chain data `Ψ`.

Here `dim` is the dimension of the space of source forms, `N` the level, `x₁` the second cut-off and
`chiK d` the quadratic character `χ_K` of the prime parameter `d`. -/
theorem exists_err_gaugeLe_compositeLift {P : Parameters} (D : Data P) :
    ∃ err : ℕ → ℝ,
      -- (a)
      (∀ p : ℕ, 0 ≤ err p) ∧
      -- (b)
      (∀ p : ℕ, p ≠ D.N → chiK P.d p = 1 ∨ D.x₁ ≤ p → err p = 0) ∧
      -- (c)
      (∀ U : Finset ℕ, ∑ p ∈ U, err p * log p ≤ D.errorUnit) ∧
      -- (d)
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], ∃ (l : ℕ) (S : Submodule embValRing D.SourceForm),
        l ≤ err p * finrank ℂ D.SourceForm ∧
        S ≤ D.integralSourceForms ⊓ D.ramifiedSourceForms.restrictScalars embValRing ∧
        ColengthDvd (D.integralSourceForms ⊓ D.ramifiedSourceForms.restrictScalars embValRing) S
          (p ^ l) ∧
        ∀ (ϑ : D.Twist) (Ψ : D.Translations →₀ ℂ), IsChainDatum ϑ Ψ → p.Coprime ϑ.normQ →
          ∀ φ ∈ S, GaugeLe 1 (p ^ (err p - D.gain p)) (compositeLift ϑ Ψ φ) := by
  -- The errors are the allowed losses.
  refine ⟨D.allowedLoss, D.allowedLoss_nonneg, fun p hN h_cases ↦ ?_, D.sum_allowedLoss_mul_log_le,
    fun p _ _ ↦ ?_⟩
  · have h_notMem : p ∉ D.smallNonsplitPrimes := by
      simp only [mem_filter, mem_range, Nat.lt_ceil]
      exact fun ⟨hp_lt, _, hp_nonsplit⟩ ↦ h_cases.elim hp_nonsplit hp_lt.not_ge
    rw [allowedLoss, ite_eq_right h_notMem, ite_eq_right hN]
  · -- Intersect the module `S` found at `p` with the integral ramified source forms.
    obtain ⟨l, S, hl, h_index, h_gauge⟩ :=
      exists_colengthDvd_gaugeLe_compositeLift (D := D) (p := p)
    set M : Submodule embValRing D.SourceForm :=
      D.integralSourceForms ⊓ D.ramifiedSourceForms.restrictScalars embValRing
    have h_index_inf : ColengthDvd M (M ⊓ S) (p ^ l) :=
      h_index.comap .id inf_le_left fun φ hφ_M hφ_S ↦ ⟨hφ_M, hφ_S⟩
    refine ⟨l, M ⊓ S, hl, inf_le_left, h_index_inf, ?_⟩
    rintro ϑ Ψ hΨ hQ φ ⟨⟨-, h_ram⟩, hφ_S⟩
    exact h_gauge ϑ Ψ hΨ hQ φ hφ_S h_ram

end New.Data

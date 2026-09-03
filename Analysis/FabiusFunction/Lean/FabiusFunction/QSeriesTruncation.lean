import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Coefficientwise limits and the exact truncation principle

This module formalises the two foundational propositions of the section
*Coefficientwise and `q`-adic limits* of the `q`-Pochhammer / `q`-binomial monograph:
`qg:prop-coefficientwise-limit` (coefficientwise passage to an analytic limit) and
`qg:prop-truncation-principle` (the exact truncation principle, in both its product and
its `q`-adic-sum half).  Together they are the licence, used silently throughout the
`q`-series literature, to compute with an infinite product or an infinite series of
formal power series by truncating it.

## Dictionary between the printed statements and the Lean ones

* the printed `ord_{q=0} G`, with `ord_{q=0} 0 = ∞`, is Mathlib's
  `PowerSeries.order : R⟦X⟧ → ℕ∞`, whose value at `0` is `⊤`;
* the printed congruence `G ≡ H (mod q^{N+1})` ("their coefficients agree through degree
  `N`") is `∀ d ≤ N, coeff d G = coeff d H`, equivalently `(X : R⟦X⟧)^(N+1) ∣ G - H` by
  `PowerSeries.X_pow_dvd_iff`.  Every congruence below is stated in the coefficient form;
* "coefficientwise limit" is a genuine limit here, in Mathlib's coefficientwise (product)
  topology `PowerSeries.WithPiTopology`, and not merely a shorthand for stabilisation.

## What is covered

**(A) `qg:prop-coefficientwise-limit`, the formal half** — verbatim and strictly stronger.
`existsUnique_coefficientwise_limit` proves existence and uniqueness of the coefficientwise
limit, and `tendsto_of_eventually_coeff_eq` upgrades it to a genuine `Tendsto` once `R`
carries a topology.  The generalisations over the printed statement are all free, and one
of them is *required* for the paper's own use of the proposition:

* the approximants are arbitrary **power series** `P : ι → R⟦X⟧`, not polynomials
  `P_N ∈ R[q]`.  The printed proposition is stated for polynomials, but the printed proof
  of `qg:prop-truncation-principle` applies it to the truncated products
  `∏_{j≤M}(1-q^j)^{e_j}`, which lie in `ℤ[[q]] ∖ ℤ[q]` as soon as one `e_j` is negative.
  Nothing in the printed argument uses polynomiality, and nothing here does either;
* `R` is an arbitrary `Semiring`, not a commutative ring;
* the index set is an arbitrary type `ι` and the limit is along an arbitrary filter `l`
  with `[l.NeBot]`; the printed `N → ∞` over `ℕ` is the case `l = atTop`.  It is this
  generality that lets the same lemma serve products indexed by finsets.

**(B) `qg:prop-truncation-principle`, the product half** — verbatim and strictly stronger.
`coeff_qInfProduct` is `eq:qg-truncation-product`, `tendsto_qTruncProduct` is the
"well-defined coefficientwise limit", and `existsUnique_qInfProduct` is its uniqueness.
The engine `coeff_prod_zpow_stabilises` is proved for:

* an arbitrary `CommRing R`, not `ℤ`;
* factors `1 - X^(m j)` for an arbitrary exponent family `m : ℕ → ℕ` subject only to
  `∀ j, j < m j`.  The paper's product is `m j = j + 1`; the corpus's Thue–Morse product
  (`Fabius.hasProd_one_sub_X_two_pow`) is `m j = 2 ^ j`; Mathlib's
  `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow` is the case `e ≡ 1`.  One engine
  covers all three;
* in fact for arbitrary units `v : ℕ → (R⟦X⟧)ˣ` with `X^(m j) ∣ ↑(v j) - 1`.

**(C) `qg:prop-truncation-principle`, the `q`-adic-sum half** — verbatim and strictly
stronger.  `hasSum_qAdicSum` proves that the sum is well defined (a theorem, not a
convention), `coeff_qAdicSum_eq_coeff_sum` is `eq:qg-truncation-series` in topology-free
form, and `coeff_tsum_eq_coeff_sum` restates it for `∑' m, S m`.  Generalisations:

* arbitrary index type `ι`, not `ℕ`; arbitrary `Semiring R`;
* the truncation index set is generalised from the paper's exact
  `{m : ord S_m ≤ N}` to **any** finset containing it — which is what callers have.

**(D) `qg:prop-coefficientwise-limit`, the analytic half** — proved in the derivative form.
`iteratedDeriv_eq_of_eventually_coeff` is the second equality of
`eq:qg-coefficientwise-cauchy`, namely `c_d = P^{(d)}(0)/d!`, over an arbitrary open
`U ∋ 0` and an arbitrary `[NeBot]` filter;
`differentiableOn_of_tendstoLocallyUniformlyOn_polynomial` is the holomorphy of the limit.
`iteratedDeriv_eq_of_eventually_coeff_ball` is the printed statement (unit disk, `N → ∞`).

## What is NOT covered

* **The first equality of `eq:qg-coefficientwise-cauchy`**, the circle-integral expression
  `c_d = (1/2πi) ∮_{|z|=r} P(z) z^{-(d+1)} dz`.  Once `P` is known holomorphic this is
  Mathlib's Cauchy integral formula for derivatives applied to the derivative form proved
  here; it is mathematically equivalent to it and adds only `circleIntegral` plumbing.
  It is a deliberate follow-up, not a gap in a proof: nothing below depends on it.
* **The binomial expansion of negative powers.**  The paper defines `(1-q^j)^{-r}` by fiat
  as `∑_k C(k+r-1, r-1) q^{jk}` and splits its proof into the cases `e ≥ 0` (finite
  binomial theorem) and `e < 0` (binomial series).  The Lean route makes the split moot:
  `1 - X^n` is a unit of `R⟦X⟧` for `n ≠ 0` (`isUnit_one_sub_X_pow`), `(1-X^n)^e` is the
  integer power in the unit group `(R⟦X⟧)ˣ`, and the entire case split collapses to one
  application of `zpow_mem` on the subgroup `unitsCongrOne` of units congruent to `1`.
  The displayed binomial identity is therefore *not* a declaration of this module.  The
  element produced is the same one; only the definition is different.
* `qg:thm-qpochhammer-modular-asymptotic`, the modular acceleration of the same section.

## Worked instances (none of the statements below is vacuous)

* (A)/(B): `R = ℤ`, `ι = ℕ`, `l = atTop`, `e` arbitrary, `m j = j + 1` — this is the
  paper's own setting, and `hm : ∀ j, j < j + 1` holds.
* (C): `ι = ℕ`, `S m = X ^ m`, so `{m | order (S m) ≤ N} = {m | m ≤ N}` is finite, and
  `t = (hfin N).toFinset` satisfies the hypothesis `ht` of `coeff_qAdicSum_eq_coeff_sum`.
* (D): `P N = ∑_{k < N} z^k`, `f z = (1-z)⁻¹`, `U = Metric.ball 0 1`, `c d = 1`.

## Main declarations

* `eq_of_eventually_coeff_eq`, `existsUnique_coefficientwise_limit`,
  `tendsto_of_eventually_coeff_eq` — (A);
* `unitsCongrOne`, `dvd_val_zpow_sub_one`, `dvd_val_prod_sub_one` — the group-theoretic
  core of the congruence `(1-q^j)^e ≡ 1 (mod q^j)`, `e ∈ ℤ`;
* `isUnit_one_sub_X_pow`, `oneSubXPowUnit`, `coeff_prod_zpow_stabilises`,
  `qTruncProduct`, `qInfProduct`, `coeff_qInfProduct`, `tendsto_qTruncProduct` — (B);
* `qAdicSum`, `hasSum_qAdicSum`, `summable_of_finite_low_order`,
  `coeff_qAdicSum_eq_coeff_sum`, `coeff_tsum_eq_coeff_sum` — (C);
* `iterate_deriv_polynomial_eval_zero`, `tendstoLocallyUniformlyOn_iterate_deriv`,
  `differentiableOn_of_tendstoLocallyUniformlyOn_polynomial`,
  `iteratedDeriv_eq_of_eventually_coeff`, `iteratedDeriv_eq_of_eventually_coeff_ball` — (D).
-/

set_option autoImplicit false

open PowerSeries Filter

open scoped PowerSeries.WithPiTopology

namespace Fabius

/-! ### Coefficientwise limits of formal power series

This is `qg:prop-coefficientwise-limit`, formal half.  Everything is stated for arbitrary
power-series approximants along an arbitrary filter; see the module docstring for why the
extra generality is not optional. -/

/-- **Uniqueness of a coefficientwise limit.**  Along a nontrivial filter, a family of
power series has at most one coefficientwise limit.  This is the "only possible
coefficientwise limit" of the printed proof. -/
theorem eq_of_eventually_coeff_eq {R : Type*} [Semiring R] {ι : Type*} {l : Filter ι}
    [l.NeBot] {P : ι → R⟦X⟧} {F G : R⟦X⟧}
    (hF : ∀ d, ∀ᶠ i in l, PowerSeries.coeff d (P i) = PowerSeries.coeff d F)
    (hG : ∀ d, ∀ᶠ i in l, PowerSeries.coeff d (P i) = PowerSeries.coeff d G) :
    F = G := by
  refine PowerSeries.ext fun d => ?_
  obtain ⟨i, hi1, hi2⟩ := ((hF d).and (hG d)).exists
  exact hi1.symm.trans hi2

/-- If every coefficient of `P i` is eventually equal to `c d`, then the series
`∑ c_d X^d` is a coefficientwise limit of the family. -/
theorem eventually_coeff_mk {R : Type*} [Semiring R] {ι : Type*} {l : Filter ι}
    {P : ι → R⟦X⟧} {c : ℕ → R}
    (h : ∀ d, ∀ᶠ i in l, PowerSeries.coeff d (P i) = c d) (d : ℕ) :
    ∀ᶠ i in l, PowerSeries.coeff d (P i) = PowerSeries.coeff d (PowerSeries.mk c) := by
  filter_upwards [h d] with i hi
  rw [PowerSeries.coeff_mk]
  exact hi

/-- **`qg:prop-coefficientwise-limit`, first assertion.**  If for every `d` the `d`-th
coefficient of `P i` is eventually equal to `c d`, then there is a *unique* power series
`F` of which the family `P` is a coefficientwise limit, namely `F = ∑_{d≥0} c_d X^d`. -/
theorem existsUnique_coefficientwise_limit {R : Type*} [Semiring R] {ι : Type*}
    {l : Filter ι} [l.NeBot] {P : ι → R⟦X⟧} {c : ℕ → R}
    (h : ∀ d, ∀ᶠ i in l, PowerSeries.coeff d (P i) = c d) :
    ∃! F : R⟦X⟧, ∀ d, ∀ᶠ i in l, PowerSeries.coeff d (P i) = PowerSeries.coeff d F := by
  refine ⟨PowerSeries.mk c, eventually_coeff_mk h, fun G hG => ?_⟩
  exact eq_of_eventually_coeff_eq hG (eventually_coeff_mk h)

/-- **The coefficientwise limit is a genuine limit.**  Once `R` carries a topology,
eventual agreement of every coefficient is exactly convergence in Mathlib's
coefficientwise topology on `R⟦X⟧`. -/
theorem tendsto_of_eventually_coeff_eq {R : Type*} [Semiring R] [TopologicalSpace R]
    {ι : Type*} {l : Filter ι} {P : ι → R⟦X⟧} {F : R⟦X⟧}
    (h : ∀ d, ∀ᶠ i in l, PowerSeries.coeff d (P i) = PowerSeries.coeff d F) :
    Tendsto P l (nhds F) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h d] with i hi
  exact hi.symm

/-! ### Units congruent to one

The printed proof of `qg:prop-truncation-principle` proves `(1-q^j)^e ≡ 1 (mod q^j)` for
every integer `e` by splitting into `e ≥ 0` (finite binomial theorem) and `e = -r < 0`
(binomial series).  Both cases say only that the elements of a commutative ring congruent
to `1` modulo a fixed `a` form a *subgroup* of the unit group; that is proved once here,
and the case split disappears. -/

/-- The units of a commutative ring `A` congruent to `1` modulo a fixed element `a`, as a
subgroup of `Aˣ`.  Being a subgroup, it is closed under arbitrary integer powers and under
finite products — which is the entire content of the printed congruence
`(1-q^j)^e ≡ 1 (mod q^j)`, `e ∈ ℤ`. -/
def unitsCongrOne {A : Type*} [CommRing A] (a : A) : Subgroup Aˣ where
  carrier := {v : Aˣ | a ∣ (v : A) - 1}
  mul_mem' {u v} hu hv := by
    have hu' : a ∣ ((u : Aˣ) : A) - 1 := hu
    have hv' : a ∣ ((v : Aˣ) : A) - 1 := hv
    show a ∣ ((u * v : Aˣ) : A) - 1
    have key : ((u * v : Aˣ) : A) - 1
        = ((u : Aˣ) : A) * (((v : Aˣ) : A) - 1) + (((u : Aˣ) : A) - 1) := by
      rw [Units.val_mul]; ring
    rw [key]
    exact dvd_add (hv'.mul_left _) hu'
  one_mem' := by
    show a ∣ ((1 : Aˣ) : A) - 1
    rw [Units.val_one, sub_self]
    exact dvd_zero a
  inv_mem' {v} hv := by
    have hv' : a ∣ ((v : Aˣ) : A) - 1 := hv
    show a ∣ ((v⁻¹ : Aˣ) : A) - 1
    have hvv : ((v⁻¹ : Aˣ) : A) * ((v : Aˣ) : A) = 1 := Units.inv_mul v
    have key : ((v⁻¹ : Aˣ) : A) - 1 = -(((v⁻¹ : Aˣ) : A) * (((v : Aˣ) : A) - 1)) := by
      have hexp : ((v⁻¹ : Aˣ) : A) * (((v : Aˣ) : A) - 1)
          = ((v⁻¹ : Aˣ) : A) * ((v : Aˣ) : A) - ((v⁻¹ : Aˣ) : A) := by ring
      rw [hexp, hvv]
      ring
    rw [key]
    exact dvd_neg.mpr (hv'.mul_left _)

/-- Membership in `unitsCongrOne a` is literally the congruence `v ≡ 1 (mod a)`. -/
theorem mem_unitsCongrOne {A : Type*} [CommRing A] {a : A} {v : Aˣ} :
    v ∈ unitsCongrOne a ↔ a ∣ (v : A) - 1 := Iff.rfl

/-- **Integer powers preserve the congruence.**  If `v ≡ 1 (mod a)` then `v^e ≡ 1 (mod a)`
for *every* integer `e`, positive or negative.  This one line replaces the printed case
split between the finite binomial theorem and the binomial series. -/
theorem dvd_val_zpow_sub_one {A : Type*} [CommRing A] {a : A} {v : Aˣ}
    (h : a ∣ (v : A) - 1) (e : ℤ) : a ∣ ((v ^ e : Aˣ) : A) - 1 :=
  mem_unitsCongrOne.mp (zpow_mem (mem_unitsCongrOne.mpr h) e)

/-- **Finite products preserve the congruence.** -/
theorem dvd_val_prod_sub_one {A : Type*} [CommRing A] {ι : Type*} {a : A} {s : Finset ι}
    {v : ι → Aˣ} (h : ∀ j ∈ s, a ∣ (v j : A) - 1) :
    a ∣ ((∏ j ∈ s, v j : Aˣ) : A) - 1 :=
  mem_unitsCongrOne.mp
    (Subgroup.prod_mem (unitsCongrOne a) fun j hj => mem_unitsCongrOne.mpr (h j hj))

/-! ### The exact truncation principle for products

This is `qg:prop-truncation-principle`, product half, together with its engine. -/

/-- For `n ≠ 0` the power series `1 - X^n` is a unit of `R⟦X⟧`: its constant coefficient is
`1`.  This is what makes `(1 - X^n)^e` meaningful for negative integers `e` without any
binomial series. -/
theorem isUnit_one_sub_X_pow (R : Type*) [CommRing R] {n : ℕ} (hn : n ≠ 0) :
    IsUnit (1 - (X : R⟦X⟧) ^ n) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr ?_
  have h : PowerSeries.constantCoeff (1 - (X : R⟦X⟧) ^ n) = 1 := by
    rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow hn, sub_zero]
  rw [h]
  exact isUnit_one

/-- The unit `1 - X^n` of `R⟦X⟧`, as an element of `(R⟦X⟧)ˣ`.  The value at `n = 0` is the
junk value `1`, forced because `1 - X^0 = 0` is not a unit; every lemma below carries the
hypothesis `n ≠ 0`. -/
noncomputable def oneSubXPowUnit (R : Type*) [CommRing R] (n : ℕ) : (R⟦X⟧)ˣ :=
  if h : n = 0 then 1 else (isUnit_one_sub_X_pow R h).unit

/-- The underlying power series of `oneSubXPowUnit R n` is `1 - X^n`, for `n ≠ 0`. -/
theorem val_oneSubXPowUnit (R : Type*) [CommRing R] {n : ℕ} (hn : n ≠ 0) :
    ((oneSubXPowUnit R n : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 - X ^ n := by
  have hdef : oneSubXPowUnit R n = (isUnit_one_sub_X_pow R hn).unit := by
    unfold oneSubXPowUnit
    exact dif_neg hn
  rw [hdef]
  exact IsUnit.unit_spec _

/-- `1 - X^n ≡ 1 (mod X^n)`: the base congruence of the truncation principle. -/
theorem X_pow_dvd_val_oneSubXPowUnit_sub_one (R : Type*) [CommRing R] {n : ℕ} (hn : n ≠ 0) :
    (X : R⟦X⟧) ^ n ∣ ((oneSubXPowUnit R n : (R⟦X⟧)ˣ) : R⟦X⟧) - 1 := by
  rw [val_oneSubXPowUnit R hn]
  exact ⟨-1, by ring⟩

/-- **The stabilisation engine of the truncation principle**, in full generality.
Let `v : ℕ → (R⟦X⟧)ˣ` be units with `v j ≡ 1 (mod X^{m j})` and `j < m j`, and let
`e : ℕ → ℤ` be arbitrary integer exponents.  Then for `d ≤ N ≤ M` the `d`-th coefficient
of `∏_{j < M} (v j)^{e j}` has already stabilised at its value for `M = N`.

This is the printed step "every factor with `j > N` is congruent to `1` modulo `q^{N+1}`,
hence `P_M ≡ P_N (mod q^{N+1})`", generalised from `ℤ` to any commutative ring, from
`1 - q^j` to any congruent-to-one units, and from the exponents `m j = j + 1` to any
family with `j < m j` — which also covers the Thue–Morse family `m j = 2 ^ j`. -/
theorem coeff_prod_zpow_stabilises {R : Type*} [CommRing R] {v : ℕ → (R⟦X⟧)ˣ} {m : ℕ → ℕ}
    (hv : ∀ j, (X : R⟦X⟧) ^ (m j) ∣ ((v j : (R⟦X⟧)ˣ) : R⟦X⟧) - 1) (hm : ∀ j, j < m j)
    (e : ℕ → ℤ) {N M d : ℕ} (hNM : N ≤ M) (hd : d ≤ N) :
    PowerSeries.coeff d ((∏ j ∈ Finset.range M, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧)
      = PowerSeries.coeff d ((∏ j ∈ Finset.range N, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧) := by
  have hsplit : (∏ j ∈ Finset.range M, v j ^ e j)
      = (∏ j ∈ Finset.range N, v j ^ e j) * (∏ j ∈ Finset.Ico N M, v j ^ e j) :=
    (Finset.prod_range_mul_prod_Ico (fun j => v j ^ e j) hNM).symm
  have hfac : ∀ j ∈ Finset.Ico N M,
      (X : R⟦X⟧) ^ (N + 1) ∣ ((v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧) - 1 := by
    intro j hj
    have hNj : N ≤ j := (Finset.mem_Ico.mp hj).1
    have hmj : j < m j := hm j
    have hle : N + 1 ≤ m j := by omega
    exact dvd_val_zpow_sub_one (dvd_trans (pow_dvd_pow (X : R⟦X⟧) hle) (hv j)) (e j)
  have hQ : (X : R⟦X⟧) ^ (N + 1) ∣
      ((∏ j ∈ Finset.Ico N M, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧) - 1 :=
    dvd_val_prod_sub_one (v := fun j => v j ^ e j) hfac
  have hdvd : (X : R⟦X⟧) ^ (N + 1) ∣
      ((∏ j ∈ Finset.range M, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧)
        - ((∏ j ∈ Finset.range N, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧) := by
    rw [hsplit, Units.val_mul]
    have hre : ((∏ j ∈ Finset.range N, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧)
          * ((∏ j ∈ Finset.Ico N M, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧)
        - ((∏ j ∈ Finset.range N, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧)
        = ((∏ j ∈ Finset.range N, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧)
          * (((∏ j ∈ Finset.Ico N M, v j ^ e j : (R⟦X⟧)ˣ) : R⟦X⟧) - 1) := by
      ring
    rw [hre]
    exact hQ.mul_left _
  have hz := PowerSeries.X_pow_dvd_iff.mp hdvd d (by omega)
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- The truncated product `∏_{j=1}^{M} (1 - X^j)^{e_j}` of `qg:prop-truncation-principle`,
as a unit of `R⟦X⟧`.  The paper's exponent `e_j` (`j ≥ 1`) is our `e (j - 1)`. -/
noncomputable def qTruncProduct (R : Type*) [CommRing R] (e : ℕ → ℤ) (M : ℕ) : (R⟦X⟧)ˣ :=
  ∏ j ∈ Finset.range M, (oneSubXPowUnit R (j + 1)) ^ e j

/-- The coefficientwise limit `F` of the truncated products, defined by its (stabilised)
coefficients.  `coeff_qInfProduct` identifies it with every sufficiently long truncation. -/
noncomputable def qInfProduct (R : Type*) [CommRing R] (e : ℕ → ℤ) : R⟦X⟧ :=
  PowerSeries.mk fun d => PowerSeries.coeff d ((qTruncProduct R e d : (R⟦X⟧)ˣ) : R⟦X⟧)

/-- **Coefficient stabilisation for the paper's product.**  For `d ≤ N ≤ M`,
`[q^d] ∏_{j=1}^{M}(1-q^j)^{e_j} = [q^d] ∏_{j=1}^{N}(1-q^j)^{e_j}`. -/
theorem coeff_qTruncProduct_stabilises (R : Type*) [CommRing R] (e : ℕ → ℤ) {N M d : ℕ}
    (hNM : N ≤ M) (hd : d ≤ N) :
    PowerSeries.coeff d ((qTruncProduct R e M : (R⟦X⟧)ˣ) : R⟦X⟧)
      = PowerSeries.coeff d ((qTruncProduct R e N : (R⟦X⟧)ˣ) : R⟦X⟧) := by
  unfold qTruncProduct
  exact coeff_prod_zpow_stabilises (R := R) (v := fun j => oneSubXPowUnit R (j + 1))
    (m := fun j => j + 1)
    (fun j => X_pow_dvd_val_oneSubXPowUnit_sub_one R (n := j + 1) (Nat.succ_ne_zero j))
    (fun j => Nat.lt_succ_self j) e hNM hd

/-- **`eq:qg-truncation-product`.**  `F(q) ≡ ∏_{j=1}^{N}(1-q^j)^{e_j} (mod q^{N+1})`,
written out as the agreement of all coefficients in degrees `d ≤ N`. -/
theorem coeff_qInfProduct (R : Type*) [CommRing R] (e : ℕ → ℤ) {N d : ℕ} (hd : d ≤ N) :
    PowerSeries.coeff d (qInfProduct R e)
      = PowerSeries.coeff d ((qTruncProduct R e N : (R⟦X⟧)ˣ) : R⟦X⟧) := by
  have h1 : PowerSeries.coeff d (qInfProduct R e)
      = PowerSeries.coeff d ((qTruncProduct R e d : (R⟦X⟧)ˣ) : R⟦X⟧) := by
    unfold qInfProduct
    exact PowerSeries.coeff_mk d _
  rw [h1]
  exact (coeff_qTruncProduct_stabilises R e hd le_rfl).symm

/-- Every coefficient of the truncated products is eventually the corresponding coefficient
of `qInfProduct R e`. -/
theorem eventually_coeff_qTruncProduct (R : Type*) [CommRing R] (e : ℕ → ℤ) (d : ℕ) :
    ∀ᶠ M in atTop, PowerSeries.coeff d ((qTruncProduct R e M : (R⟦X⟧)ˣ) : R⟦X⟧)
      = PowerSeries.coeff d (qInfProduct R e) := by
  filter_upwards [eventually_ge_atTop d] with M hM
  exact (coeff_qInfProduct R e hM).symm

/-- **`qg:prop-truncation-principle`: the truncated products have a well-defined
coefficientwise limit**, and it is a genuine limit in the coefficientwise topology. -/
theorem tendsto_qTruncProduct (R : Type*) [CommRing R] [TopologicalSpace R] (e : ℕ → ℤ) :
    Tendsto (fun M => ((qTruncProduct R e M : (R⟦X⟧)ˣ) : R⟦X⟧)) atTop
      (nhds (qInfProduct R e)) :=
  tendsto_of_eventually_coeff_eq (eventually_coeff_qTruncProduct R e)

/-- The coefficientwise limit of the truncated products is *unique*; combined with
`coeff_qInfProduct` this is the full first sentence of `qg:prop-truncation-principle`. -/
theorem existsUnique_qInfProduct (R : Type*) [CommRing R] (e : ℕ → ℤ) :
    ∃! F : R⟦X⟧, ∀ d, ∀ᶠ M in atTop,
      PowerSeries.coeff d ((qTruncProduct R e M : (R⟦X⟧)ˣ) : R⟦X⟧) = PowerSeries.coeff d F := by
  refine ⟨qInfProduct R e, eventually_coeff_qTruncProduct R e, fun G hG => ?_⟩
  exact eq_of_eventually_coeff_eq hG (eventually_coeff_qTruncProduct R e)

/-! ### The exact truncation principle for `q`-adic sums

This is `qg:prop-truncation-principle`, second half.  The hypothesis
`ord_{q=0} S_m → ∞` is taken in the paper's own "precise sense": for each `N`, only
finitely many `m` have `ord_{q=0} S_m ≤ N`. -/

/-- If `d ≤ N` and the order of `S` exceeds `N`, then the `d`-th coefficient of `S`
vanishes. -/
theorem coeff_eq_zero_of_lt_order_of_le {R : Type*} [Semiring R] {S : R⟦X⟧} {d N : ℕ}
    (hd : d ≤ N) (h : (N : ℕ∞) < S.order) : PowerSeries.coeff d S = 0 := by
  refine PowerSeries.coeff_of_lt_order d ?_
  have h2 : (d : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hd
  exact lt_of_le_of_lt h2 h

/-- The contrapositive form of `coeff_eq_zero_of_lt_order_of_le`, which is how the
finiteness hypothesis produces vanishing coefficients. -/
theorem coeff_eq_zero_of_not_order_le {R : Type*} [Semiring R] {S : R⟦X⟧} {d N : ℕ}
    (hd : d ≤ N) (h : ¬ S.order ≤ (N : ℕ∞)) : PowerSeries.coeff d S = 0 :=
  coeff_eq_zero_of_lt_order_of_le hd (not_le.mp h)

/-- The `q`-adic sum `S = ∑_m S_m` of a family whose orders tend to infinity: its `d`-th
coefficient is the (finite) sum of the `d`-th coefficients of those `S_m` of order at most
`d`.  `hasSum_qAdicSum` shows this really is the sum of the family. -/
noncomputable def qAdicSum {R : Type*} [Semiring R] {ι : Type*} (S : ι → R⟦X⟧)
    (hfin : ∀ N : ℕ, {m : ι | (S m).order ≤ (N : ℕ∞)}.Finite) : R⟦X⟧ :=
  PowerSeries.mk fun d => ∑ m ∈ (hfin d).toFinset, PowerSeries.coeff d (S m)

/-- The defining coefficients of `qAdicSum`. -/
theorem coeff_qAdicSum {R : Type*} [Semiring R] {ι : Type*} (S : ι → R⟦X⟧)
    (hfin : ∀ N : ℕ, {m : ι | (S m).order ≤ (N : ℕ∞)}.Finite) (d : ℕ) :
    PowerSeries.coeff d (qAdicSum S hfin)
      = ∑ m ∈ (hfin d).toFinset, PowerSeries.coeff d (S m) := by
  unfold qAdicSum
  exact PowerSeries.coeff_mk d _

/-- **The `q`-adic sum is well defined**, and not merely by convention: if for each `N`
only finitely many `S_m` have order at most `N`, then the family `S` is summable in the
coefficientwise topology and its sum is `qAdicSum S hfin`. -/
theorem hasSum_qAdicSum {R : Type*} [Semiring R] [TopologicalSpace R] {ι : Type*}
    (S : ι → R⟦X⟧) (hfin : ∀ N : ℕ, {m : ι | (S m).order ≤ (N : ℕ∞)}.Finite) :
    HasSum S (qAdicSum S hfin) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [coeff_qAdicSum S hfin d]
  have hz : ∀ m ∉ (hfin d).toFinset, PowerSeries.coeff d (S m) = 0 := by
    intro m hm
    have hm' : ¬ ((S m).order ≤ (d : ℕ∞)) := fun hle => hm ((hfin d).mem_toFinset.mpr hle)
    exact coeff_eq_zero_of_not_order_le le_rfl hm'
  exact hasSum_sum_of_ne_finset_zero hz

/-- Summability of a family of power series whose orders tend to infinity. -/
theorem summable_of_finite_low_order {R : Type*} [Semiring R] [TopologicalSpace R]
    {ι : Type*} (S : ι → R⟦X⟧)
    (hfin : ∀ N : ℕ, {m : ι | (S m).order ≤ (N : ℕ∞)}.Finite) : Summable S :=
  ⟨qAdicSum S hfin, hasSum_qAdicSum S hfin⟩

/-- **`eq:qg-truncation-series`, topology-free form.**
`S(q) ≡ ∑_{m ∈ t} S_m(q) (mod q^{N+1})` for *any* finset `t` containing every index of
order at most `N` — the paper's `{m : ord S_m ≤ N}` being the smallest such `t`. -/
theorem coeff_qAdicSum_eq_coeff_sum {R : Type*} [Semiring R] {ι : Type*} (S : ι → R⟦X⟧)
    (hfin : ∀ N : ℕ, {m : ι | (S m).order ≤ (N : ℕ∞)}.Finite) {N : ℕ} {t : Finset ι}
    (ht : ∀ m : ι, (S m).order ≤ (N : ℕ∞) → m ∈ t) {d : ℕ} (hd : d ≤ N) :
    PowerSeries.coeff d (qAdicSum S hfin) = PowerSeries.coeff d (∑ m ∈ t, S m) := by
  rw [coeff_qAdicSum S hfin d, map_sum]
  have hsub : (hfin d).toFinset ⊆ t := by
    intro m hm
    have h1 : (S m).order ≤ (d : ℕ∞) := (hfin d).mem_toFinset.mp hm
    have h2 : (d : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hd
    exact ht m (le_trans h1 h2)
  have hzero : ∀ m ∈ t, m ∉ (hfin d).toFinset → PowerSeries.coeff d (S m) = 0 := by
    intro m _ hm
    have hm' : ¬ ((S m).order ≤ (d : ℕ∞)) := fun hle => hm ((hfin d).mem_toFinset.mpr hle)
    exact coeff_eq_zero_of_not_order_le le_rfl hm'
  exact Finset.sum_subset hsub hzero

/-- **`eq:qg-truncation-series`** for the unconditional sum `∑' m, S m`. -/
theorem coeff_tsum_eq_coeff_sum {R : Type*} [Semiring R] [TopologicalSpace R] [T2Space R]
    {ι : Type*} (S : ι → R⟦X⟧)
    (hfin : ∀ N : ℕ, {m : ι | (S m).order ≤ (N : ℕ∞)}.Finite) {N : ℕ} {t : Finset ι}
    (ht : ∀ m : ι, (S m).order ≤ (N : ℕ∞) → m ∈ t) {d : ℕ} (hd : d ≤ N) :
    PowerSeries.coeff d (∑' m, S m) = PowerSeries.coeff d (∑ m ∈ t, S m) := by
  have htsum : (∑' m, S m) = qAdicSum S hfin := (hasSum_qAdicSum S hfin).tsum_eq
  rw [htsum]
  exact coeff_qAdicSum_eq_coeff_sum S hfin ht hd

/-! ### The analytic limit over `ℂ`

This is `qg:prop-coefficientwise-limit`, analytic half.  We prove the second equality of
`eq:qg-coefficientwise-cauchy`, `c_d = P^{(d)}(0)/d!`, together with the holomorphy of the
limit.  The circle-integral expression is deliberately not formalised; see the module
docstring. -/

/-- Iterated complex differentiation of a polynomial evaluation is polynomial evaluation of
the iterated formal derivative. -/
theorem iterate_deriv_polynomial_eval (p : Polynomial ℂ) (k : ℕ) :
    deriv^[k] (fun z : ℂ => p.eval z) = fun z : ℂ => (Polynomial.derivative^[k] p).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : deriv^[k + 1] (fun z : ℂ => p.eval z)
          = deriv (deriv^[k] (fun z : ℂ => p.eval z)) :=
        Function.iterate_succ_apply' deriv k _
      have h2 : Polynomial.derivative^[k + 1] p
          = Polynomial.derivative (Polynomial.derivative^[k] p) :=
        Function.iterate_succ_apply' (⇑Polynomial.derivative) k p
      rw [h1, h2, ih]
      funext z
      exact Polynomial.deriv _

/-- **Taylor coefficients of a polynomial.**  `(d/dz)^k (p(z))|_{z=0} = k! · [z^k] p`. -/
theorem iterate_deriv_polynomial_eval_zero (p : Polynomial ℂ) (k : ℕ) :
    deriv^[k] (fun z : ℂ => p.eval z) 0 = (Nat.factorial k : ℂ) * p.coeff k := by
  have h0 : deriv^[k] (fun z : ℂ => p.eval z) 0
      = Polynomial.eval (0 : ℂ) (Polynomial.derivative^[k] p) :=
    congrFun (iterate_deriv_polynomial_eval p k) 0
  rw [h0, ← Polynomial.coeff_zero_eq_eval_zero]
  simp only [Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

/-- **Weierstrass, iterated.**  If polynomials converge locally uniformly on an open set to
`f`, then all their iterated derivatives converge locally uniformly to the corresponding
iterated derivative of `f`.  No `[NeBot]` hypothesis is needed: `TendstoLocallyUniformlyOn.deriv`
handles the trivial filter itself. -/
theorem tendstoLocallyUniformlyOn_iterate_deriv {ι : Type*} {l : Filter ι} {U : Set ℂ}
    {P : ι → Polynomial ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hP : TendstoLocallyUniformlyOn (fun i z => (P i).eval z) f l U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => deriv^[k] (fun z : ℂ => (P i).eval z))
      (deriv^[k] f) l U := by
  induction k with
  | zero =>
      simpa only [Function.iterate_zero, Function.iterate_zero_apply, id_eq] using hP
  | succ k ih =>
      have hdiff : ∀ᶠ i in l,
          DifferentiableOn ℂ (deriv^[k] (fun z : ℂ => (P i).eval z)) U := by
        refine Eventually.of_forall fun i => ?_
        rw [iterate_deriv_polynomial_eval (P i) k]
        exact Polynomial.differentiableOn _
      have hd := ih.deriv hdiff hU
      have hfam : (fun i => deriv^[k + 1] (fun z : ℂ => (P i).eval z))
          = (deriv ∘ fun i => deriv^[k] (fun z : ℂ => (P i).eval z)) := by
        funext i
        exact Function.iterate_succ_apply' deriv k _
      have hlim : deriv^[k + 1] f = deriv (deriv^[k] f) :=
        Function.iterate_succ_apply' deriv k f
      rw [hfam, hlim]
      exact hd

/-- **The analytic limit is holomorphic.**  A locally uniform limit of polynomials on an
open subset of `ℂ` is holomorphic there. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn_polynomial {ι : Type*} {l : Filter ι}
    [l.NeBot] {U : Set ℂ} {P : ι → Polynomial ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hP : TendstoLocallyUniformlyOn (fun i z => (P i).eval z) f l U) :
    DifferentiableOn ℂ f U := by
  have hdiff : ∀ᶠ i in l, DifferentiableOn ℂ (fun z : ℂ => (P i).eval z) U :=
    Eventually.of_forall fun i => Polynomial.differentiableOn _
  exact hP.differentiableOn hdiff hU

/-- **`eq:qg-coefficientwise-cauchy`, derivative form.**  If polynomials `P i` converge
locally uniformly on an open `U ∋ 0` to `f`, and the `d`-th coefficient of `P i` is
eventually `c d`, then `f^{(d)}(0) = d! · c_d`; equivalently `c_d = f^{(d)}(0)/d!`.

This is the printed statement with the unit disk replaced by an arbitrary open `U ∋ 0` and
`N → ∞` by an arbitrary nontrivial filter. -/
theorem iteratedDeriv_eq_of_eventually_coeff {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} {P : ι → Polynomial ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hP : TendstoLocallyUniformlyOn (fun i z => (P i).eval z) f l U)
    {c : ℕ → ℂ} {d : ℕ} (hc : ∀ᶠ i in l, (P i).coeff d = c d) :
    iteratedDeriv d f 0 = (Nat.factorial d : ℂ) * c d := by
  have hconv : Tendsto (fun i => deriv^[d] (fun z : ℂ => (P i).eval z) 0) l
      (nhds (deriv^[d] f 0)) :=
    (tendstoLocallyUniformlyOn_iterate_deriv hU hP d).tendsto_at h0
  have heq : ∀ᶠ i in l, (Nat.factorial d : ℂ) * c d
      = deriv^[d] (fun z : ℂ => (P i).eval z) 0 := by
    filter_upwards [hc] with i hi
    rw [iterate_deriv_polynomial_eval_zero (P i) d, hi]
  have hconst : Tendsto (fun i => deriv^[d] (fun z : ℂ => (P i).eval z) 0) l
      (nhds ((Nat.factorial d : ℂ) * c d)) :=
    Tendsto.congr' heq tendsto_const_nhds
  have hval : deriv^[d] f 0 = (Nat.factorial d : ℂ) * c d := tendsto_nhds_unique hconv hconst
  rw [iteratedDeriv_eq_iterate]
  exact hval

/-- **`qg:prop-coefficientwise-limit`, analytic half, at the printed hypotheses**: the
polynomials `P_N` converge locally uniformly on the open unit disk to `f`, and their `d`-th
coefficients are eventually `c_d`.  Then `f` is holomorphic on the disk and
`c_d = f^{(d)}(0)/d!`.

The remaining clause of `eq:qg-coefficientwise-cauchy`, the circle integral over `|z| = r`
for `0 < r < 1`, is not formalised; see the module docstring. -/
theorem iteratedDeriv_eq_of_eventually_coeff_ball {P : ℕ → Polynomial ℂ} {f : ℂ → ℂ}
    (hP : TendstoLocallyUniformlyOn (fun N z => (P N).eval z) f atTop
      (Metric.ball (0 : ℂ) 1))
    {c : ℕ → ℂ} {d : ℕ} (hc : ∀ᶠ N in atTop, (P N).coeff d = c d) :
    DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
      iteratedDeriv d f 0 = (Nat.factorial d : ℂ) * c d := by
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨differentiableOn_of_tendstoLocallyUniformlyOn_polynomial Metric.isOpen_ball hP, ?_⟩
  exact iteratedDeriv_eq_of_eventually_coeff Metric.isOpen_ball h0 hP hc

end Fabius

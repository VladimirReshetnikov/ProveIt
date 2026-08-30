import FabiusFunction.GeneralizedRvachevProduct
import FabiusFunction.SincCanonicalProduct
import FabiusFunction.WeightedScaleMultiplicity

/-!
# The canonical product of a generalized Rvachev transform

For an exponent sequence `a : ℕ → ℕ` the exponents volume writes the
generalized Rvachev transform

`Φ_a(z) = ∏_{h ≥ 0} sinc (z / 2 ^ h) ^ (a h)`

as a product over the positive integers,

`Φ_a(z) = ∏_{n ≥ 1} (1 - z² / n²) ^ (m_a n)`,
`m_a n = ∑_{h ≤ v₂ n} a h`.

This module proves that identity for every `z : ℂ` and every `a` with
`∑_h a h / 2 ^ h < ∞`, indexing `n ≥ 1` by `n = m + 1` and writing the
exponent as the corpus's `weightedScaleMultiplicity 2 a (m + 1)`,
which is `inclusivePrefixSum a (padicValNat 2 (m + 1))` by definition.

The route is the one taken for the constant exponent sequence in
`FabiusFunction.SincCanonicalProduct`, with every factor raised to
`a h`:

* each scale-`h` factor is expanded by the Euler product
  `tprod_one_add_sineTerm`, so `Φ_a` becomes a product over pairs
  `(h, r)` of `(1 - z² / ((r+1)² · 4 ^ h)) ^ (a h)`;
* the pair index is regrouped along `dyadicFactorEquiv`, whose fibre
  over `m` is `{h : h ≤ v₂ (m+1)}`;
* that fibre is finite and all of its factors share the base
  `1 - z² / (m+1)²`, so the fibre product is the base raised to
  `∑_{h ≤ v₂ (m+1)} a h`.

The new analytic ingredient is norm-summability of the double family
*with* exponents, obtained from the power deviation bound
`norm_one_add_pow_sub_one_le` of
`FabiusFunction.GeneralizedRvachevProduct`.  Its comparison test
`summable_norm_of_norm_le_exp_sub_one` was stated there only for the
index type `ℕ`; it is generalized in place to an arbitrary index
type, which is what the double family over `ℕ × ℕ` needs.

## What is not proved here

No statement about an order of vanishing is made: nothing here mentions
`multiplicity` or `analyticOrderAt`, and
`weightedScaleMultiplicity 2 a (m + 1)` occurs only as the exponent of
a factor of an infinite product.  Nothing is claimed about convergence
that is uniform on compact sets, about analyticity of `Φ_a`, or about
any probabilistic model.

The exponents volume states the same display with two further clauses,
"with locally uniform convergence" and
"In particular, `\ord_{z=\pm n}\Phi_a=m_a(n)`"; neither of those two
clauses is formalized here.

## Main declarations

* `Fabius.norm_sineTerm_div_two_pow` — the modulus of the scaled Euler
  factor deviation, `‖sineTerm (z / 2 ^ h) r‖`, as
  `‖z‖² / 4 ^ h · (1 / (r+1)²)`.
* `Fabius.summable_norm_of_norm_le_exp_sub_one` — the comparison test
  of `GeneralizedRvachevProduct` restated for an arbitrary index type.
* `Fabius.summable_natCast_mul_norm_sineTerm_pair` — the weighted
  double series `∑_{(h,r)} a h · ‖sineTerm (z / 2 ^ h) r‖` converges.
* `Fabius.summable_norm_generalizedSineTerm_pair` — **the double family
  with exponents is norm-summable**: the deviations
  `(1 + sineTerm (z / 2 ^ h) r) ^ (a h) - 1` are absolutely summable
  over `ℕ × ℕ`.
* `Fabius.generalizedSineTermPair_multipliable` — consequently the
  raised pair factors are `Multipliable`.
* `Fabius.generalizedRvachevProduct_eq_tprod_pair` — **the pair form**
  `Φ_a(z) = ∏'_{(h,r)} (1 + sineTerm (z / 2 ^ h) r) ^ (a h)`.
* `Fabius.one_add_sineTerm_dyadic` — the fibre computation: for
  `j ≤ v₂ (m+1)` the factor at `(j, (m+1)/2^j - 1)` is
  `1 - z² / (m+1)²`.
* `Fabius.weightedScaleMultiplicity_one_nat` — the `ℕ`-valued unit
  weights give `padicValNat b n + 1`.
* `Fabius.generalizedRvachevProduct_eq_canonical` — **the canonical
  product** `Φ_a(z) = ∏'_m (1 - z²/(m+1)²) ^ (m_a (m+1))`.
* `Fabius.generalizedRvachevProduct_one_of_canonical` — the regression
  test: routing the constant exponent sequence through the canonical
  product returns `rvachevFourierProduct`.
* `Fabius.canonicalFactor_eq_zero_iff` — the factor indexed by `m`
  vanishes if and only if `z = ±(m+1)`.
-/

set_option autoImplicit false

namespace Fabius

/-- The modulus of the scaled Euler factor deviation:
`‖sineTerm (z / 2 ^ h) r‖ = ‖z‖² / 4 ^ h · (1 / (r+1)²)`.

The shape on the right is chosen so that the double family splits as a
product of a geometric factor in `h` and a `p`-series factor in `r`. -/
theorem norm_sineTerm_div_two_pow (z : ℂ) (h r : ℕ) :
    ‖sineTerm (z / (2 : ℂ) ^ h) r‖ =
      ‖z‖ ^ 2 / (4 : ℝ) ^ h * (1 / ((r : ℝ) + 1) ^ 2) := by
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hnr : ‖(r : ℂ) + 1‖ = (r : ℝ) + 1 := by
    have hc := Complex.norm_natCast (r + 1)
    push_cast at hc
    exact hc
  have hpow4 : (((2 : ℝ)) ^ h) ^ 2 = (4 : ℝ) ^ h := by
    rw [← pow_mul, mul_comm h 2, pow_mul]
    norm_num
  simp only [sineTerm, norm_div, norm_neg, norm_pow]
  rw [hn2, hnr, div_pow, hpow4, mul_one_div]

/-- **The weighted double series converges.**  Under admissibility,

`∑_{(h,r)} a h · ‖sineTerm (z / 2 ^ h) r‖ < ∞`.

The summand factors as `(a h · ‖z‖² / 4 ^ h) · (1 / (r+1)²)`; the
first factor is dominated by `‖z‖² · (a h / 2 ^ h)` because
`2 ^ h ≤ 4 ^ h`, and the second is a convergent `p`-series. -/
theorem summable_natCast_mul_norm_sineTerm_pair
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Summable fun p : ℕ × ℕ =>
      (a p.1 : ℝ) * ‖sineTerm (z / (2 : ℂ) ^ p.1) p.2‖ := by
  have hA : Summable fun h : ℕ =>
      (a h : ℝ) * (‖z‖ ^ 2 / (4 : ℝ) ^ h) := by
    refine Summable.of_nonneg_of_le (fun h => by positivity) ?_
      (ha.mul_left (‖z‖ ^ 2))
    intro h
    have h24 : (2 : ℝ) ^ h ≤ (4 : ℝ) ^ h :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) h
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
    have hstep : ‖z‖ ^ 2 / (4 : ℝ) ^ h ≤ ‖z‖ ^ 2 / (2 : ℝ) ^ h :=
      div_le_div_of_nonneg_left (by positivity) h2pos h24
    calc (a h : ℝ) * (‖z‖ ^ 2 / (4 : ℝ) ^ h)
        ≤ (a h : ℝ) * (‖z‖ ^ 2 / (2 : ℝ) ^ h) :=
          mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
      _ = ‖z‖ ^ 2 * ((a h : ℝ) / 2 ^ h) := by ring
  have hp2 : Summable fun r : ℕ => ((1 : ℝ) / ((r + 1) ^ 2)) := by
    have hs := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact_mod_cast (summable_nat_add_iff 1).mpr hs
  have hprod := hA.mul_of_nonneg hp2
    (fun h => by positivity) (fun r => by positivity)
  have hcongr : ∀ p : ℕ × ℕ,
      (a p.1 : ℝ) * (‖z‖ ^ 2 / (4 : ℝ) ^ p.1) *
          (1 / ((p.2 : ℝ) + 1) ^ 2) =
        (a p.1 : ℝ) * ‖sineTerm (z / (2 : ℂ) ^ p.1) p.2‖ := by
    intro p
    rw [norm_sineTerm_div_two_pow z p.1 p.2, mul_assoc]
  exact hprod.congr hcongr

/-- **Norm-summability of the double family with exponents** — the
generalization of `Fabius.summable_norm_sineTerm_pair` to a raised
factor.  Under admissibility,

`∑_{(h,r)} ‖(1 + sineTerm (z / 2 ^ h) r) ^ (a h) - 1‖ < ∞`.

The power deviation bound `norm_one_add_pow_sub_one_le` turns the
`(h,r)`-th summand into `exp (a h · ‖sineTerm (z / 2 ^ h) r‖) - 1`,
and the weighted double series in the exponent converges. -/
theorem summable_norm_generalizedSineTerm_pair
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Summable fun p : ℕ × ℕ =>
      ‖(1 + sineTerm (z / (2 : ℂ) ^ p.1) p.2) ^ a p.1 - 1‖ := by
  refine summable_norm_of_norm_le_exp_sub_one
    (summable_natCast_mul_norm_sineTerm_pair a ha z)
    (fun p => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) ?_
  intro p
  exact norm_one_add_pow_sub_one_le
    (sineTerm (z / (2 : ℂ) ^ p.1) p.2) (a p.1)

/-- The raised pair factors are `Multipliable`.  As everywhere in this
development, Mathlib's `Multipliable` is unconditional convergence of
the net of finite subproducts and admits the limit `0`, so this holds
at every `z : ℂ`, the zeros included. -/
theorem generalizedSineTermPair_multipliable
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Multipliable fun p : ℕ × ℕ =>
      (1 + sineTerm (z / (2 : ℂ) ^ p.1) p.2) ^ a p.1 := by
  have hp := multipliable_one_add_of_summable
    (summable_norm_generalizedSineTerm_pair a ha z)
  convert hp using 1
  funext p
  ring

/-- **The pair form of the generalized transform**:

`Φ_a(z) = ∏'_{(h,r)} (1 + sineTerm (z / 2 ^ h) r) ^ (a h)`,

the flattened double Euler product.  Each scale factor is expanded by
`tprod_one_add_sineTerm`, the exponent is moved inside the fibre
product by `Multipliable.tprod_pow`, and the two indices are merged by
`Multipliable.tprod_prod'`. -/
theorem generalizedRvachevProduct_eq_tprod_pair
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    generalizedRvachevProduct a z =
      ∏' p : ℕ × ℕ,
        (1 + sineTerm (z / (2 : ℂ) ^ p.1) p.2) ^ a p.1 := by
  have hGmult := generalizedSineTermPair_multipliable a ha z
  have hfib : ∀ h : ℕ, Multipliable fun r : ℕ =>
      (1 + sineTerm (z / (2 : ℂ) ^ h) r) ^ a h :=
    fun h => (multipliable_sineTerm (z / (2 : ℂ) ^ h)).pow (a h)
  calc generalizedRvachevProduct a z
      = ∏' h : ℕ,
          complexSinc ((Real.pi : ℂ) * (z / (2 : ℂ) ^ h)) ^ a h := by
        unfold generalizedRvachevProduct
        simp only [mul_div_assoc]
    _ = ∏' h : ℕ, ∏' r : ℕ,
          (1 + sineTerm (z / (2 : ℂ) ^ h) r) ^ a h := by
        refine tprod_congr fun h => ?_
        have hpow : (∏' r : ℕ,
            (1 + sineTerm (z / (2 : ℂ) ^ h) r) ^ a h)
            = (∏' r : ℕ, (1 + sineTerm (z / (2 : ℂ) ^ h) r)) ^ a h :=
          Multipliable.tprod_pow
            (multipliable_sineTerm (z / (2 : ℂ) ^ h)) (a h)
        rw [hpow, tprod_one_add_sineTerm (z / (2 : ℂ) ^ h)]
    _ = ∏' p : ℕ × ℕ,
          (1 + sineTerm (z / (2 : ℂ) ^ p.1) p.2) ^ a p.1 :=
        (hGmult.tprod_prod' hfib).symm

/-- **The fibre computation.**  If `j ≤ v₂ (m+1)` then `2 ^ j` divides
`m + 1`, and the Euler factor of index `r = (m+1)/2^j - 1` at scale
`j` is

`1 + sineTerm (z / 2 ^ j) ((m+1)/2^j - 1) = 1 - z² / (m+1)²`,

because `2 ^ j · ((m+1)/2^j) = m + 1`.  This is the reason the whole
fibre of `dyadicFactorEquiv` over `m` contributes the *same* base. -/
theorem one_add_sineTerm_dyadic (z : ℂ) (m j : ℕ)
    (hj : j ≤ padicValNat 2 (m + 1)) :
    1 + sineTerm (z / (2 : ℂ) ^ j) ((m + 1) / 2 ^ j - 1) =
      1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by
  have hdvd : 2 ^ j ∣ m + 1 :=
    dvd_trans (pow_dvd_pow 2 hj) pow_padicValNat_dvd
  have hquot : 0 < (m + 1) / 2 ^ j :=
    Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos m) hdvd) (by positivity)
  have h1 : ((m + 1) / 2 ^ j - 1) + 1 = (m + 1) / 2 ^ j := by omega
  have h2 : 2 ^ j * ((m + 1) / 2 ^ j) = m + 1 :=
    Nat.mul_div_cancel' hdvd
  rw [sineTerm]
  have hcast : (((m + 1) / 2 ^ j - 1 : ℕ) : ℂ) + 1 =
      (((m + 1) / 2 ^ j : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) h1
  rw [hcast]
  have hkey : ((2 : ℂ) ^ j) * (((m + 1) / 2 ^ j : ℕ) : ℂ) =
      ((m + 1 : ℕ) : ℂ) := by
    have hc := congrArg (fun k : ℕ => (k : ℂ)) h2
    push_cast at hc ⊢
    exact_mod_cast hc
  have hexpand : (z / (2 : ℂ) ^ j) ^ 2 /
      (((m + 1) / 2 ^ j : ℕ) : ℂ) ^ 2 =
      z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 := by
    rw [div_pow, div_div, ← mul_pow, hkey]
  rw [neg_div, hexpand]
  ring

/-- **The canonical product of a generalized Rvachev transform** — the
boxed display `p1:eq:canonical-a` of the exponents volume, inside its
theorem "Zero divisor and spectral zeta" in the subsection "The
universal zero-divisor formula": for every admissible exponent
sequence `a` and every `z : ℂ`,

`Φ_a(z) = ∏'_m (1 - z²/(m+1)²) ^ (weightedScaleMultiplicity 2 a (m+1))`,

that is, indexing the positive integers by `n = m + 1`, the factor at
`n` carries the exponent `∑_{h ≤ v₂ n} a h`.

The proof regroups the pair form along `dyadicFactorEquiv`: the fibre
over `m` is `Fin (v₂ (m+1) + 1)`, on it every factor has the same base
`1 - z²/(m+1)²` by `one_add_sineTerm_dyadic`, and the finite fibre
product collapses by `Finset.prod_pow_eq_pow_sum`, whose exponent sum
`∑_{j : Fin (v₂ (m+1) + 1)} a j` is the inclusive prefix sum defining
`weightedScaleMultiplicity`.

No order of vanishing is asserted: the exponent appears here only as
the exponent of a factor. -/
theorem generalizedRvachevProduct_eq_canonical
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    generalizedRvachevProduct a z =
      ∏' m : ℕ, (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^
        weightedScaleMultiplicity 2 a (m + 1) := by
  classical
  set G : ℕ × ℕ → ℂ := fun p =>
    (1 + sineTerm (z / (2 : ℂ) ^ p.1) p.2) ^ a p.1
  have hGmult : Multipliable G :=
    generalizedSineTermPair_multipliable a ha z
  have hfactor : ∀ (m : ℕ) (j : Fin (padicValNat 2 (m + 1) + 1)),
      G (dyadicFactorEquiv.symm ⟨m, j⟩) =
        (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^ a (j : ℕ) := by
    intro m j
    show (1 + sineTerm (z / (2 : ℂ) ^ (j : ℕ))
        ((m + 1) / 2 ^ (j : ℕ) - 1)) ^ a (j : ℕ) = _
    rw [one_add_sineTerm_dyadic z m (j : ℕ)
      (Nat.lt_succ_iff.mp j.isLt)]
  calc generalizedRvachevProduct a z
      = ∏' p : ℕ × ℕ, G p :=
        generalizedRvachevProduct_eq_tprod_pair a ha z
    _ = ∏' σ : Σ m : ℕ, Fin (padicValNat 2 (m + 1) + 1),
          G (dyadicFactorEquiv.symm σ) :=
        (dyadicFactorEquiv.symm.tprod_eq G).symm
    _ = ∏' m : ℕ, ∏' j : Fin (padicValNat 2 (m + 1) + 1),
          G (dyadicFactorEquiv.symm ⟨m, j⟩) := by
        refine Multipliable.tprod_sigma'
          (fun m => ⟨_, hasProd_fintype _⟩) ?_
        exact (dyadicFactorEquiv.symm.multipliable_iff).mpr hGmult
    _ = ∏' m : ℕ, (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^
          weightedScaleMultiplicity 2 a (m + 1) := by
        refine tprod_congr fun m => ?_
        have hfib : ∏' j : Fin (padicValNat 2 (m + 1) + 1),
            G (dyadicFactorEquiv.symm ⟨m, j⟩) =
            ∏' j : Fin (padicValNat 2 (m + 1) + 1),
              (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^ a (j : ℕ) :=
          tprod_congr (hfactor m)
        have hexp : ∑ j : Fin (padicValNat 2 (m + 1) + 1),
            a (j : ℕ) = weightedScaleMultiplicity 2 a (m + 1) := by
          rw [weightedScaleMultiplicity, inclusivePrefixSum]
          exact Fin.sum_univ_eq_sum_range a
            (padicValNat 2 (m + 1) + 1)
        rw [hfib, tprod_fintype, Finset.prod_pow_eq_pow_sum, hexp]

/-- **The classical recovery, as a regression test on the exponent
convention.**  Feeding the constant exponent sequence `a h = 1` to the
canonical product above and comparing with
`rvachevFourierProduct_eq_canonical` gives

`generalizedRvachevProduct (fun _ => 1) z = rvachevFourierProduct z`,

which is the identity already recorded as
`generalizedRvachevProduct_one`.  So the two canonical routes agree
at `a ≡ 1`, via
`weightedScaleMultiplicity 2 (fun _ => 1) (m + 1) = v₂ (m+1) + 1`.

This is a consistency check between the two routes, not the guard on
the prefix convention: an exclusive prefix `h < v₂ (m+1)` would
already fail one step earlier, inside `hexp` in the headline, where
`Fin.sum_univ_eq_sum_range` pins the number of summands.  The guards
on the convention are `weightedScaleMultiplicity_one_nat` and that
`hexp` step. -/
theorem generalizedRvachevProduct_one_of_canonical (z : ℂ) :
    generalizedRvachevProduct (fun _ => 1) z =
      rvachevFourierProduct z := by
  have hone : Summable fun h : ℕ => ((1 : ℕ) : ℝ) / 2 ^ h := by
    have hg : Summable fun h : ℕ => ((1 : ℝ) / 2) ^ h :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hpt : ∀ h : ℕ,
        ((1 : ℝ) / 2) ^ h = ((1 : ℕ) : ℝ) / 2 ^ h := by
      intro h
      rw [Nat.cast_one, div_pow, one_pow]
    exact hg.congr hpt
  rw [generalizedRvachevProduct_eq_canonical (fun _ => 1) hone z,
    rvachevFourierProduct_eq_canonical]
  refine tprod_congr fun m => ?_
  rw [weightedScaleMultiplicity_one_nat]

/-- **The zero set of one canonical factor.**  The factor indexed by
`m` vanishes if and only if `z = m + 1` or `z = -(m + 1)`.

This is the factor-level statement only.  Nothing here computes an
order of vanishing of `Φ_a` at `± (m+1)`, and nothing here rules out
contributions of other factors at those points. -/
theorem canonicalFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 = 0 ↔
      z = ((m + 1 : ℕ) : ℂ) ∨ z = -((m + 1 : ℕ) : ℂ) := by
  have hc : ((m + 1 : ℕ) : ℂ) ≠ 0 := by
    have hn : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
    exact_mod_cast hn
  have hc2 : ((m + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hc
  constructor
  · intro hz
    have hX : z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2 = 1 := by
      linear_combination -hz
    rw [div_eq_one_iff_eq hc2] at hX
    have hfac :
        (z - ((m + 1 : ℕ) : ℂ)) * (z + ((m + 1 : ℕ) : ℂ)) = 0 := by
      linear_combination hX
    rcases mul_eq_zero.mp hfac with h4 | h4
    · exact Or.inl (by linear_combination h4)
    · exact Or.inr (by linear_combination h4)
  · rintro (rfl | rfl)
    · rw [div_self hc2, sub_self]
    · rw [neg_sq, div_self hc2, sub_self]

end Fabius

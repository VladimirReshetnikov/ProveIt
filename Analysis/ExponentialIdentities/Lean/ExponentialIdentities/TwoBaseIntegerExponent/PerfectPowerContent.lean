import ExponentialIdentities.TwoBaseIntegerExponent.PrimitiveGenerator
import Mathlib.Order.Interval.Finset.Nat

/-!
# Perfect-power content, affine descent, and primitive-output statistics

`ArithmeticRigidity` records the *implications* that a common perfect-power degree, or a
matched base depth together with a common outer degree, produce a new solution.
`LeastSolution` turns those implications into *exclusions* at the least noninteger solution.
This module supplies the missing converses and the resulting classification at every point of
the solution monoid.

The core is unconditional and needs no hypothesis at all:

* `isCommonOutputPower_iff_twoBaseIntegralSolution_div`: both outputs at `x` are perfect
  `e`-th powers of natural numbers **iff** `x / e` is again a two-base solution;
* `isMatchedAffineDecomposition_iff_twoBaseIntegralSolution`: the two outputs at `x` have
  the matched shapes `2 ^ r * U ^ d` and `3 ^ r * V ^ d` **iff** `(x - r) / d` is a solution.

Along the free monoid `ℕ + ℕ β` of the exact primitive-generator theorem, both criteria become
divisibility conditions on the coordinates; the maximal common perfect-power degree at
`n + k β` is exactly `Nat.gcd n k` (`isGreatest_commonOutputPowerDegree_coordinates`), and the
output pair is simultaneously power-primitive exactly when `n` and `k` are coprime.  The
coordinates `(n, k) = (0, 1)` recover the kernel-verified exclusions at the least pair.

The last part converts the classification into exact finite counts.  The nonzero monoid points
below a real bound `T` split into the fibres of the coordinate gcd, and the fibre of degree
`g` is in bijection with the primitive points below `T / g`.  This gives the exact identity

`N(T) = ∑ g ∈ Finset.Icc 1 G, P (T / g)`,   `G = ⌈T⌉₊ + ⌈T / β⌉₊`,

the finite form of the report's `N_β(T) = ∑_{d ≥ 1} P_β(T / d)`.  The asymptotic evaluation
`P_β(T) ~ 3 T ^ 2 / (π ^ 2 β)` is *not* formalized here: it needs Möbius inversion together
with `∑ μ d / d ^ 2 = 1 / ζ 2`, which this corpus does not carry.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- A positive real which is a rational integer is the cast of a natural number. -/
private theorem exists_natCast_eq_of_pos_of_mem_range {t : ℝ} (ht : 0 < t)
    (h : t ∈ Set.range ((↑) : ℤ → ℝ)) : ∃ P : ℕ, (P : ℝ) = t := by
  obtain ⟨z, hz⟩ := h
  have hzpos : (0 : ℝ) < (z : ℝ) := by rw [hz]; exact ht
  have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast hzpos.le
  refine ⟨z.toNat, ?_⟩
  rw [← hz]
  exact_mod_cast Int.toNat_of_nonneg hz0

/-- An integral value of a real power with positive base is a natural number. -/
private theorem exists_natCast_eq_rpow {b : ℝ} (hb : 0 < b) {y : ℝ}
    (h : b ^ y ∈ Set.range ((↑) : ℤ → ℝ)) : ∃ P : ℕ, (P : ℝ) = b ^ y :=
  exists_natCast_eq_of_pos_of_mem_range (Real.rpow_pos_of_pos hb y) h

/-- Uniqueness of positive real `e`-th roots, in the form used throughout this module. -/
private theorem rpow_div_eq_of_pow_eq {b : ℝ} (hb : 0 ≤ b) {x : ℝ} {P e : ℕ} (he : 0 < e)
    (hP : ((P ^ e : ℕ) : ℝ) = b ^ x) : b ^ (x / (e : ℝ)) = (P : ℝ) := by
  have heR : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hpow : (b ^ (x / (e : ℝ))) ^ e = (P : ℝ) ^ e := by
    rw [← Real.rpow_mul_natCast hb, div_mul_cancel₀ x heR]
    simpa using hP.symm
  exact (pow_left_inj₀ (Real.rpow_nonneg hb _) (Nat.cast_nonneg P) he.ne').mp hpow

/-! ## Simultaneous perfect powers -/

/-- Both integral outputs at `x` are perfect `e`-th powers of natural numbers. -/
def IsCommonOutputPower (x : ℝ) (e : ℕ) : Prop :=
  ∃ P Q : ℕ, ((P ^ e : ℕ) : ℝ) = (2 : ℝ) ^ x ∧ ((Q ^ e : ℕ) : ℝ) = (3 : ℝ) ^ x

/-- **Exact roots.**  A simultaneous `e`-th power decomposition of the two outputs at `x`
identifies the two bases raised to `x / e` with the two roots. -/
theorem two_three_rpow_div_of_isCommonOutputPower {x : ℝ} {P Q e : ℕ} (he : 0 < e)
    (hP : ((P ^ e : ℕ) : ℝ) = (2 : ℝ) ^ x)
    (hQ : ((Q ^ e : ℕ) : ℝ) = (3 : ℝ) ^ x) :
    (2 : ℝ) ^ (x / (e : ℝ)) = (P : ℝ) ∧ (3 : ℝ) ^ (x / (e : ℝ)) = (Q : ℝ) :=
  ⟨rpow_div_eq_of_pow_eq (by norm_num) he hP,
    rpow_div_eq_of_pow_eq (by norm_num) he hQ⟩

/-- A point carrying a common output power degree is itself a two-base solution. -/
theorem twoBaseIntegralSolution_of_isCommonOutputPower {x : ℝ} {e : ℕ}
    (h : IsCommonOutputPower x e) : TwoBaseIntegralSolution x := by
  obtain ⟨P, Q, hP, hQ⟩ := h
  exact ⟨⟨((P ^ e : ℕ) : ℤ), by exact_mod_cast hP⟩,
    ⟨((Q ^ e : ℕ) : ℤ), by exact_mod_cast hQ⟩⟩

/-- **Simultaneous perfect powers descend.**  If both outputs at `x` are perfect `e`-th
powers with `e ≥ 1`, then `x / e` is itself a two-base solution. -/
theorem twoBaseIntegralSolution_div_of_isCommonOutputPower {x : ℝ} {e : ℕ} (he : 0 < e)
    (h : IsCommonOutputPower x e) : TwoBaseIntegralSolution (x / (e : ℝ)) := by
  obtain ⟨P, Q, hP, hQ⟩ := h
  obtain ⟨h₂, h₃⟩ := two_three_rpow_div_of_isCommonOutputPower he hP hQ
  exact ⟨⟨(P : ℤ), by exact_mod_cast h₂.symm⟩, ⟨(Q : ℤ), by exact_mod_cast h₃.symm⟩⟩

/-- **Converse descent.**  If `x / e` is a two-base solution then both outputs at `x` are
perfect `e`-th powers of natural numbers. -/
theorem isCommonOutputPower_of_twoBaseIntegralSolution_div {x : ℝ} {e : ℕ} (he : 0 < e)
    (h : TwoBaseIntegralSolution (x / (e : ℝ))) : IsCommonOutputPower x e := by
  have heR : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  obtain ⟨P, hP⟩ := exists_natCast_eq_rpow (by norm_num) h.1
  obtain ⟨Q, hQ⟩ := exists_natCast_eq_rpow (by norm_num) h.2
  refine ⟨P, Q, ?_, ?_⟩
  · rw [Nat.cast_pow, hP, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      div_mul_cancel₀ x heR]
  · rw [Nat.cast_pow, hQ, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
      div_mul_cancel₀ x heR]

/-- **Exact common-power criterion, analytic form.**  For `e ≥ 1` the two outputs at `x` are
simultaneously perfect `e`-th powers exactly when `x / e` is a two-base solution.  This is the
equivalence of clauses (i) and (ii) of the report's exact common-power criterion, and it is
unconditional. -/
theorem isCommonOutputPower_iff_twoBaseIntegralSolution_div {x : ℝ} {e : ℕ} (he : 0 < e) :
    IsCommonOutputPower x e ↔ TwoBaseIntegralSolution (x / (e : ℝ)) :=
  ⟨twoBaseIntegralSolution_div_of_isCommonOutputPower he,
    isCommonOutputPower_of_twoBaseIntegralSolution_div he⟩

/-- Degree one is always a common output power degree of a solution. -/
theorem isCommonOutputPower_one_of_twoBaseIntegralSolution {x : ℝ}
    (h : TwoBaseIntegralSolution x) : IsCommonOutputPower x 1 :=
  isCommonOutputPower_of_twoBaseIntegralSolution_div Nat.one_pos (by simpa using h)

/-- **Power primitivity of the least output pair.**  At a least noninteger solution the only
common perfect-power degree of the two outputs is `1`. -/
theorem IsLeastTwoBaseNonintegerSolution.isCommonOutputPower_iff
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β) {e : ℕ} (he : 0 < e) :
    IsCommonOutputPower β e ↔ e = 1 := by
  constructor
  · rintro ⟨P, Q, hP, hQ⟩
    by_contra hne
    exact hβ.no_common_perfect_power (by omega : 2 ≤ e) hP hQ
  · rintro rfl
    exact isCommonOutputPower_one_of_twoBaseIntegralSolution hβ.1.1

/-- The greatest common perfect-power degree of the least output pair is `1`.  This is the
report's value `g β = gcd 0 1 = 1`. -/
theorem IsLeastTwoBaseNonintegerSolution.isGreatest_commonOutputPowerDegree
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β) :
    IsGreatest {e : ℕ | 0 < e ∧ IsCommonOutputPower β e} 1 := by
  constructor
  · exact ⟨Nat.one_pos, isCommonOutputPower_one_of_twoBaseIntegralSolution hβ.1.1⟩
  · intro e he
    obtain ⟨hepos, hpow⟩ := he
    exact le_of_eq ((hβ.isCommonOutputPower_iff hepos).mp hpow)

/-! ## The coordinate criterion for simultaneous perfect powers -/

/-- **Coordinate criterion.**  Along the free additive monoid `ℕ + ℕ β` generated by an
irrational `β`, the two outputs at `n + k β` are simultaneously perfect `e`-th powers exactly
when `e` divides both coordinates.  This is clause (iii) of the report's exact common-power
criterion. -/
theorem isCommonOutputPower_coordinates_iff
    {β : ℝ} (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    {n k e : ℕ} (he : 0 < e) :
    IsCommonOutputPower ((n : ℝ) + (k : ℝ) * β) e ↔ e ∣ n ∧ e ∣ k := by
  have heR : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [isCommonOutputPower_iff_twoBaseIntegralSolution_div he, hchar]
  constructor
  · rintro ⟨p, q, hpq⟩
    have h : (n : ℝ) + (k : ℝ) * β = ((p : ℝ) + (q : ℝ) * β) * (e : ℝ) := by
      rw [← hpq, div_mul_cancel₀ _ heR]
    have hpair : ((n, k) : ℕ × ℕ) = (e * p, e * q) := by
      apply IntegerExponent.Irrational.injective_nat_add_mul hβirr
      show (n : ℝ) + (k : ℝ) * β = ((e * p : ℕ) : ℝ) + ((e * q : ℕ) : ℝ) * β
      rw [h]
      push_cast
      ring
    rw [Prod.mk.injEq] at hpair
    exact ⟨⟨p, hpair.1⟩, ⟨q, hpair.2⟩⟩
  · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
    refine ⟨p, q, ?_⟩
    rw [div_eq_iff heR]
    push_cast
    ring

/-- **Coordinate gcd.**  The maximal common perfect-power degree of the output pair at a
nonzero monoid point `n + k β` is `Nat.gcd n k`. -/
theorem isGreatest_commonOutputPowerDegree_coordinates
    {β : ℝ} (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    {n k : ℕ} (hnk : ¬ (n = 0 ∧ k = 0)) :
    IsGreatest {e : ℕ | 0 < e ∧ IsCommonOutputPower ((n : ℝ) + (k : ℝ) * β) e}
      (Nat.gcd n k) := by
  have hgpos : 0 < Nat.gcd n k := by
    rcases Nat.eq_zero_or_pos (Nat.gcd n k) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h
      exact absurd h hnk
    · exact h
  constructor
  · exact ⟨hgpos, (isCommonOutputPower_coordinates_iff hβirr hchar hgpos).mpr
      ⟨Nat.gcd_dvd_left n k, Nat.gcd_dvd_right n k⟩⟩
  · intro e he
    obtain ⟨hepos, hpow⟩ := he
    obtain ⟨hn, hk⟩ := (isCommonOutputPower_coordinates_iff hβirr hchar hepos).mp hpow
    exact Nat.le_of_dvd hgpos (Nat.dvd_gcd hn hk)

/-- **Power primitivity in coordinates.**  The output pair at a nonzero monoid point is
simultaneously power-primitive exactly when the two coordinates are coprime. -/
theorem coprime_coordinates_iff_no_nontrivial_commonOutputPower
    {β : ℝ} (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    {n k : ℕ} (hnk : ¬ (n = 0 ∧ k = 0)) :
    Nat.gcd n k = 1 ↔
      ∀ e : ℕ, 2 ≤ e → ¬ IsCommonOutputPower ((n : ℝ) + (k : ℝ) * β) e := by
  have hgpos : 0 < Nat.gcd n k := by
    rcases Nat.eq_zero_or_pos (Nat.gcd n k) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h
      exact absurd h hnk
    · exact h
  constructor
  · intro hcop e he hpow
    obtain ⟨hn, hk⟩ :=
      (isCommonOutputPower_coordinates_iff hβirr hchar (by omega : 0 < e)).mp hpow
    have hdvd : e ∣ Nat.gcd n k := Nat.dvd_gcd hn hk
    rw [hcop] at hdvd
    have hle := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  · intro hprim
    by_contra hne
    exact hprim (Nat.gcd n k) (by omega)
      ((isCommonOutputPower_coordinates_iff hβirr hchar hgpos).mpr
        ⟨Nat.gcd_dvd_left n k, Nat.gcd_dvd_right n k⟩)

/-! ## Matched affine decompositions -/

/-- A matched affine decomposition of the two outputs at `x`: a common distinguished-base
depth `r` and a common outer power degree `d`. -/
def IsMatchedAffineDecomposition (x : ℝ) (r d : ℕ) : Prop :=
  ∃ U V : ℕ, ((2 ^ r * U ^ d : ℕ) : ℝ) = (2 : ℝ) ^ x ∧
    ((3 ^ r * V ^ d : ℕ) : ℝ) = (3 : ℝ) ^ x

/-- **Matched affine decomposition criterion, analytic form.**  For `d ≥ 1` the outputs at
`x` admit a matched decomposition of depth `r` and degree `d` exactly when `(x - r) / d` is a
two-base solution.  The forward implication is the kernel-verified affine descent theorem; the
converse is the new content. -/
theorem isMatchedAffineDecomposition_iff_twoBaseIntegralSolution
    {x : ℝ} {r d : ℕ} (hd : 0 < d) :
    IsMatchedAffineDecomposition x r d ↔
      TwoBaseIntegralSolution ((x - (r : ℝ)) / (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  constructor
  · rintro ⟨U, V, hU, hV⟩
    exact affine_descent_integral_powers hd hU hV
  · intro h
    obtain ⟨U, hU⟩ := exists_natCast_eq_rpow (by norm_num) h.1
    obtain ⟨V, hV⟩ := exists_natCast_eq_rpow (by norm_num) h.2
    have hexp : (r : ℝ) + (x - (r : ℝ)) = x := by ring
    refine ⟨U, V, ?_, ?_⟩
    · push_cast
      rw [hU, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        div_mul_cancel₀ _ hdR, ← Real.rpow_natCast (2 : ℝ) r,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hexp]
    · push_cast
      rw [hV, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
        div_mul_cancel₀ _ hdR, ← Real.rpow_natCast (3 : ℝ) r,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hexp]

/-- **Exact affine primitivity of the least output pair, as an equivalence.**  At a least
noninteger solution the only matched affine decomposition is the trivial one. -/
theorem IsLeastTwoBaseNonintegerSolution.isMatchedAffineDecomposition_iff
    {β : ℝ} (hβ : IsLeastTwoBaseNonintegerSolution β) {r d : ℕ} (hd : 0 < d) :
    IsMatchedAffineDecomposition β r d ↔ (r = 0 ∧ d = 1) := by
  constructor
  · rintro ⟨U, V, hU, hV⟩
    exact hβ.affine_primitive hd hU hV
  · rintro ⟨rfl, rfl⟩
    obtain ⟨U, hU⟩ := exists_natCast_eq_rpow (by norm_num) hβ.1.1.1
    obtain ⟨V, hV⟩ := exists_natCast_eq_rpow (by norm_num) hβ.1.1.2
    exact ⟨U, V, by simpa using hU, by simpa using hV⟩

/-- **Matched affine decompositions in coordinates.**  At the monoid point `n + k β` the
matched decompositions of depth `r` and degree `d ≥ 1` are exactly those with `r ≤ n`,
`d ∣ n - r` and `d ∣ k`. -/
theorem isMatchedAffineDecomposition_coordinates_iff
    {β : ℝ} (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    {n k r d : ℕ} (hd : 0 < d) :
    IsMatchedAffineDecomposition ((n : ℝ) + (k : ℝ) * β) r d ↔
      r ≤ n ∧ d ∣ (n - r) ∧ d ∣ k := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [isMatchedAffineDecomposition_iff_twoBaseIntegralSolution hd, hchar]
  constructor
  · rintro ⟨p, q, hpq⟩
    have h : (n : ℝ) + (k : ℝ) * β
        = (r : ℝ) + ((p : ℝ) + (q : ℝ) * β) * (d : ℝ) := by
      rw [← hpq, div_mul_cancel₀ _ hdR]
      ring
    have hpair : ((n, k) : ℕ × ℕ) = (r + d * p, d * q) := by
      apply IntegerExponent.Irrational.injective_nat_add_mul hβirr
      show (n : ℝ) + (k : ℝ) * β
        = ((r + d * p : ℕ) : ℝ) + ((d * q : ℕ) : ℝ) * β
      rw [h]
      push_cast
      ring
    rw [Prod.mk.injEq] at hpair
    obtain ⟨hn, hk⟩ := hpair
    subst hn
    refine ⟨Nat.le_add_right r (d * p), ?_, ⟨q, hk⟩⟩
    rw [Nat.add_sub_cancel_left]
    exact dvd_mul_right d p
  · rintro ⟨hrn, ⟨p, hp⟩, ⟨q, rfl⟩⟩
    refine ⟨p, q, ?_⟩
    have h1 : n = r + d * p := by
      rw [← hp]
      omega
    have hn : (n : ℝ) = (r : ℝ) + (d : ℝ) * (p : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h1
    rw [div_eq_iff hdR, hn]
    push_cast
    ring

/-- The canonical reduced affine presentation `x = r + k (q + β)` with `n = q k + r`.  The
normalization `0 ≤ r < k` is `Nat.mod_lt`, and the outer degree `k` is the `β`-coordinate. -/
theorem euclidean_affine_presentation (β : ℝ) (n k : ℕ) :
    (n : ℝ) + (k : ℝ) * β
      = ((n % k : ℕ) : ℝ) + (k : ℝ) * (((n / k : ℕ) : ℝ) + β) := by
  have h : (k : ℝ) * ((n / k : ℕ) : ℝ) + ((n % k : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.div_add_mod n k
  rw [mul_add]
  linarith

/-- The reduced presentation really is a matched affine decomposition: at `n + k β` with
`k ≥ 1`, the depth `n % k` and the degree `k` are admissible. -/
theorem isMatchedAffineDecomposition_euclidean
    {β : ℝ} (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    {n k : ℕ} (hk : 0 < k) :
    IsMatchedAffineDecomposition ((n : ℝ) + (k : ℝ) * β) (n % k) k := by
  refine (isMatchedAffineDecomposition_coordinates_iff hβirr hchar hk).mpr
    ⟨Nat.mod_le n k, ?_, dvd_rfl⟩
  have h : n - n % k = k * (n / k) := Nat.sub_eq_of_eq_add (Nat.div_add_mod n k).symm
  rw [h]
  exact dvd_mul_right k (n / k)

/-! ## Total and primitive counts -/

/-- Coordinate pairs of nonzero monoid points below the bound `T`. -/
def coordinatePairsBelow (β T : ℝ) : Set (ℕ × ℕ) :=
  {nk | nk ≠ (0, 0) ∧ (nk.1 : ℝ) + (nk.2 : ℝ) * β < T}

/-- Coordinate pairs of monoid points below `T` whose coordinate gcd is exactly `g`. -/
def coordinatePairsBelowOfDegree (β T : ℝ) (g : ℕ) : Set (ℕ × ℕ) :=
  {nk | Nat.gcd nk.1 nk.2 = g ∧ (nk.1 : ℝ) + (nk.2 : ℝ) * β < T}

/-- Coordinate pairs of monoid points below `T` with coprime coordinates. -/
def primitiveCoordinatePairsBelow (β T : ℝ) : Set (ℕ × ℕ) :=
  coordinatePairsBelowOfDegree β T 1

theorem mem_coordinatePairsBelow {β T : ℝ} {nk : ℕ × ℕ} :
    nk ∈ coordinatePairsBelow β T ↔
      nk ≠ (0, 0) ∧ (nk.1 : ℝ) + (nk.2 : ℝ) * β < T := Iff.rfl

theorem mem_coordinatePairsBelowOfDegree {β T : ℝ} {g : ℕ} {nk : ℕ × ℕ} :
    nk ∈ coordinatePairsBelowOfDegree β T g ↔
      Nat.gcd nk.1 nk.2 = g ∧ (nk.1 : ℝ) + (nk.2 : ℝ) * β < T := Iff.rfl

theorem mem_primitiveCoordinatePairsBelow {β T : ℝ} {nk : ℕ × ℕ} :
    nk ∈ primitiveCoordinatePairsBelow β T ↔
      Nat.gcd nk.1 nk.2 = 1 ∧ (nk.1 : ℝ) + (nk.2 : ℝ) * β < T := Iff.rfl

/-- The monoid points below a bound occupy a finite coordinate box. -/
theorem finite_coordinateBoxBelow {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    {nk : ℕ × ℕ | (nk.1 : ℝ) + (nk.2 : ℝ) * β < T}.Finite := by
  apply Set.Finite.subset
    (Finset.finite_toSet (Finset.range ⌈T⌉₊ ×ˢ Finset.range ⌈T / β⌉₊))
  rintro ⟨n, k⟩ hmem
  have hlt : (n : ℝ) + (k : ℝ) * β < T := hmem
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * β := by positivity
  have hn : (n : ℝ) < T := by linarith
  have hk : (k : ℝ) < T / β := (lt_div_iff₀ hβ).mpr (by linarith)
  exact Finset.mem_coe.mpr (Finset.mk_mem_product
    (Finset.mem_range.mpr (Nat.lt_ceil.mpr hn))
    (Finset.mem_range.mpr (Nat.lt_ceil.mpr hk)))

/-- There are finitely many nonzero monoid points below any bound. -/
theorem finite_coordinatePairsBelow {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    (coordinatePairsBelow β T).Finite :=
  (finite_coordinateBoxBelow hβ T).subset fun _ h => h.2

/-- There are finitely many monoid points of a given coordinate gcd below any bound. -/
theorem finite_coordinatePairsBelowOfDegree {β : ℝ} (hβ : 0 < β) (T : ℝ) (g : ℕ) :
    (coordinatePairsBelowOfDegree β T g).Finite :=
  (finite_coordinateBoxBelow hβ T).subset fun _ h => h.2

/-- **Degree rescaling.**  Multiplication by `g` is a bijection from the primitive coordinate
pairs below `T / g` onto the coordinate pairs of gcd exactly `g` below `T`. -/
theorem coordinatePairsBelowOfDegree_eq_image {β T : ℝ} {g : ℕ} (hg : 0 < g) :
    coordinatePairsBelowOfDegree β T g =
      (fun nk : ℕ × ℕ => (g * nk.1, g * nk.2)) ''
        primitiveCoordinatePairsBelow β (T / (g : ℝ)) := by
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  refine Set.Subset.antisymm ?_ ?_
  · rintro ⟨n, k⟩ hmem
    obtain ⟨hgcd0, hlt0⟩ := hmem
    have hgcd : Nat.gcd n k = g := hgcd0
    have hlt : (n : ℝ) + (k : ℝ) * β < T := hlt0
    obtain ⟨n₀, k₀, hcop, hn, hk⟩ := Nat.exists_coprime n k
    rw [hgcd] at hn hk
    have hcop' : Nat.gcd n₀ k₀ = 1 := hcop
    have hval : ((n₀ : ℝ) + (k₀ : ℝ) * β) * (g : ℝ) = (n : ℝ) + (k : ℝ) * β := by
      rw [hn, hk]
      push_cast
      ring
    have hbound : (n₀ : ℝ) + (k₀ : ℝ) * β < T / (g : ℝ) := by
      rw [lt_div_iff₀ hgR, hval]
      exact hlt
    refine ⟨(n₀, k₀), ⟨hcop', hbound⟩, ?_⟩
    show ((g * n₀, g * k₀) : ℕ × ℕ) = (n, k)
    rw [hn, hk, Nat.mul_comm n₀ g, Nat.mul_comm k₀ g]
  · rw [Set.image_subset_iff]
    rintro ⟨n₀, k₀⟩ hmem
    obtain ⟨hcop0, hlt0⟩ := hmem
    have hcop : Nat.gcd n₀ k₀ = 1 := hcop0
    have hlt : (n₀ : ℝ) + (k₀ : ℝ) * β < T / (g : ℝ) := hlt0
    show ((g * n₀, g * k₀) : ℕ × ℕ) ∈ coordinatePairsBelowOfDegree β T g
    have hgcd : Nat.gcd (g * n₀) (g * k₀) = g := by
      rw [Nat.gcd_mul_left, hcop, Nat.mul_one]
    have hval : ((g * n₀ : ℕ) : ℝ) + ((g * k₀ : ℕ) : ℝ) * β
        = ((n₀ : ℝ) + (k₀ : ℝ) * β) * (g : ℝ) := by
      push_cast
      ring
    have hbound : ((g * n₀ : ℕ) : ℝ) + ((g * k₀ : ℕ) : ℝ) * β < T := by
      rw [hval]
      exact (lt_div_iff₀ hgR).mp hlt
    exact ⟨hgcd, hbound⟩

/-- **Exact-degree count.**  The number of monoid points of coordinate gcd exactly `g` below
`T` equals the number of primitive points below `T / g`. -/
theorem ncard_coordinatePairsBelowOfDegree {β T : ℝ} {g : ℕ} (hg : 0 < g) :
    (coordinatePairsBelowOfDegree β T g).ncard
      = (primitiveCoordinatePairsBelow β (T / (g : ℝ))).ncard := by
  rw [coordinatePairsBelowOfDegree_eq_image hg]
  refine Set.ncard_image_of_injective _ ?_
  rintro ⟨n₁, k₁⟩ ⟨n₂, k₂⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Nat.eq_of_mul_eq_mul_left hg h.1)
    (Nat.eq_of_mul_eq_mul_left hg h.2)

/-- An explicit bound for the coordinate gcd of a monoid point below `T`. -/
theorem gcd_le_ceil_add_ceil {β : ℝ} (hβ : 0 < β) {T : ℝ} {n k : ℕ}
    (hlt : (n : ℝ) + (k : ℝ) * β < T) :
    Nat.gcd n k ≤ ⌈T⌉₊ + ⌈T / β⌉₊ := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * β := by positivity
  have hn : n < ⌈T⌉₊ := Nat.lt_ceil.mpr (by linarith)
  have hk : k < ⌈T / β⌉₊ := Nat.lt_ceil.mpr ((lt_div_iff₀ hβ).mpr (by linarith))
  have hgcd : Nat.gcd n k ≤ n + k := by
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp
    · exact le_trans (Nat.gcd_le_left k hnpos) (Nat.le_add_right n k)
  omega

/-- **Splitting by common power degree.**  The nonzero monoid points below `T` form the
disjoint union of the fibres of the coordinate gcd, and only finitely many fibres occur. -/
theorem ncard_coordinatePairsBelow_eq_sum_ofDegree {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    (coordinatePairsBelow β T).ncard =
      ∑ g ∈ Finset.Icc 1 (⌈T⌉₊ + ⌈T / β⌉₊),
        (coordinatePairsBelowOfDegree β T g).ncard := by
  have hfin : (coordinatePairsBelow β T).Finite := finite_coordinatePairsBelow hβ T
  have hfing : ∀ g : ℕ, (coordinatePairsBelowOfDegree β T g).Finite :=
    fun g => finite_coordinatePairsBelowOfDegree hβ T g
  have hdisj : ((Finset.Icc 1 (⌈T⌉₊ + ⌈T / β⌉₊) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun g => (hfing g).toFinset) := by
    intro g₁ _ g₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro nk h1 h2
    rw [Set.Finite.mem_toFinset, mem_coordinatePairsBelowOfDegree] at h1 h2
    exact hne (h1.1.symm.trans h2.1)
  have hbi : hfin.toFinset
      = (Finset.Icc 1 (⌈T⌉₊ + ⌈T / β⌉₊)).biUnion fun g => (hfing g).toFinset := by
    ext nk
    rw [Set.Finite.mem_toFinset, Finset.mem_biUnion, mem_coordinatePairsBelow]
    constructor
    · intro hmem
      refine ⟨Nat.gcd nk.1 nk.2, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨?_, gcd_le_ceil_add_ceil hβ hmem.2⟩
        rcases Nat.eq_zero_or_pos (Nat.gcd nk.1 nk.2) with h0 | hpos
        · rw [Nat.gcd_eq_zero_iff] at h0
          exact absurd (show nk = ((0, 0) : ℕ × ℕ) from Prod.ext h0.1 h0.2) hmem.1
        · exact hpos
      · rw [Set.Finite.mem_toFinset, mem_coordinatePairsBelowOfDegree]
        exact ⟨rfl, hmem.2⟩
    · rintro ⟨g, hg, hmem⟩
      rw [Finset.mem_Icc] at hg
      rw [Set.Finite.mem_toFinset, mem_coordinatePairsBelowOfDegree] at hmem
      refine ⟨?_, hmem.2⟩
      intro hzero
      have hg0 : Nat.gcd nk.1 nk.2 = 0 := by
        rw [hzero]
        simp
      rw [hmem.1] at hg0
      omega
  rw [Set.ncard_eq_toFinset_card _ hfin, hbi, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl ?_
  intro g _
  exact (Set.ncard_eq_toFinset_card _ (hfing g)).symm

/-- **Total and primitive counts.**  The exact finite form of the report's identity
`N_β(T) = ∑_{d ≥ 1} P_β(T / d)`: the nonzero monoid points below `T` are counted by the
primitive counts at the rescaled bounds `T / g`. -/
theorem ncard_coordinatePairsBelow_eq_sum_primitive {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    (coordinatePairsBelow β T).ncard =
      ∑ g ∈ Finset.Icc 1 (⌈T⌉₊ + ⌈T / β⌉₊),
        (primitiveCoordinatePairsBelow β (T / (g : ℝ))).ncard := by
  rw [ncard_coordinatePairsBelow_eq_sum_ofDegree hβ T]
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [Finset.mem_Icc] at hg
  exact ncard_coordinatePairsBelowOfDegree (by omega)

/-! ## Counting solutions rather than coordinates -/

/-- Positive two-base solutions below the bound `T`. -/
def twoBaseIntegralSolutionsBelow (T : ℝ) : Set ℝ :=
  {x | TwoBaseIntegralSolution x ∧ 0 < x ∧ x < T}

/-- Positive two-base solutions below `T` whose output pair is simultaneously
power-primitive. -/
def powerPrimitiveTwoBaseIntegralSolutionsBelow (T : ℝ) : Set ℝ :=
  {x | TwoBaseIntegralSolution x ∧ 0 < x ∧ x < T ∧
    ∀ e : ℕ, 2 ≤ e → ¬ IsCommonOutputPower x e}

/-- Positive two-base solutions below `T` whose two outputs are both perfect `r`-th
powers. -/
def commonOutputPowerSolutionsBelow (T : ℝ) (r : ℕ) : Set ℝ :=
  {x | TwoBaseIntegralSolution x ∧ 0 < x ∧ x < T ∧ IsCommonOutputPower x r}

theorem mem_twoBaseIntegralSolutionsBelow {T x : ℝ} :
    x ∈ twoBaseIntegralSolutionsBelow T ↔
      TwoBaseIntegralSolution x ∧ 0 < x ∧ x < T := Iff.rfl

theorem mem_powerPrimitiveTwoBaseIntegralSolutionsBelow {T x : ℝ} :
    x ∈ powerPrimitiveTwoBaseIntegralSolutionsBelow T ↔
      TwoBaseIntegralSolution x ∧ 0 < x ∧ x < T ∧
        ∀ e : ℕ, 2 ≤ e → ¬ IsCommonOutputPower x e := Iff.rfl

theorem mem_commonOutputPowerSolutionsBelow {T x : ℝ} {r : ℕ} :
    x ∈ commonOutputPowerSolutionsBelow T r ↔
      TwoBaseIntegralSolution x ∧ 0 < x ∧ x < T ∧ IsCommonOutputPower x r := Iff.rfl

/-- A monoid point with a nonzero coordinate pair is positive. -/
private theorem pos_of_coordinates_ne_zero {β : ℝ} (hβ : 0 < β) {n k : ℕ}
    (h : ¬ (n = 0 ∧ k = 0)) : 0 < (n : ℝ) + (k : ℝ) * β := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk : k ≠ 0 := fun hk0 => h ⟨rfl, hk0⟩
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hmul : (0 : ℝ) < (k : ℝ) * β := mul_pos hkpos hβ
    simpa using hmul
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hk0 : (0 : ℝ) ≤ (k : ℝ) * β := by positivity
    linarith

/-- **Solutions versus coordinates.**  Below any bound, the positive solutions are the image
of the nonzero coordinate pairs. -/
theorem twoBaseIntegralSolutionsBelow_eq_image {β : ℝ} (hβ : 0 < β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    (T : ℝ) :
    twoBaseIntegralSolutionsBelow T =
      (fun nk : ℕ × ℕ => (nk.1 : ℝ) + (nk.2 : ℝ) * β) '' coordinatePairsBelow β T := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨hsol, hpos, hlt⟩ := hx
    obtain ⟨n, k, rfl⟩ := (hchar x).mp hsol
    have hne : ((n, k) : ℕ × ℕ) ≠ (0, 0) := by
      intro hzero
      rw [Prod.mk.injEq] at hzero
      obtain ⟨hn0, hk0⟩ := hzero
      subst hn0
      subst hk0
      simp at hpos
    exact ⟨(n, k), ⟨hne, hlt⟩, rfl⟩
  · rw [Set.image_subset_iff]
    rintro ⟨n, k⟩ hmem
    obtain ⟨hne0, hlt0⟩ := hmem
    have hlt : (n : ℝ) + (k : ℝ) * β < T := hlt0
    have hne : ¬ (n = 0 ∧ k = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hne0 rfl
    show ((n : ℝ) + (k : ℝ) * β) ∈ twoBaseIntegralSolutionsBelow T
    exact ⟨(hchar _).mpr ⟨n, k, rfl⟩, pos_of_coordinates_ne_zero hβ hne, hlt⟩

/-- The exact count of positive solutions below `T`. -/
theorem ncard_twoBaseIntegralSolutionsBelow {β : ℝ} (hβ : 0 < β) (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    (T : ℝ) :
    (twoBaseIntegralSolutionsBelow T).ncard = (coordinatePairsBelow β T).ncard := by
  rw [twoBaseIntegralSolutionsBelow_eq_image hβ hchar T]
  exact Set.ncard_image_of_injective _
    (IntegerExponent.Irrational.injective_nat_add_mul hβirr)

/-- **Power-primitive solutions versus primitive coordinates.** -/
theorem powerPrimitiveTwoBaseIntegralSolutionsBelow_eq_image {β : ℝ} (hβ : 0 < β)
    (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    (T : ℝ) :
    powerPrimitiveTwoBaseIntegralSolutionsBelow T =
      (fun nk : ℕ × ℕ => (nk.1 : ℝ) + (nk.2 : ℝ) * β) ''
        primitiveCoordinatePairsBelow β T := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨hsol, hpos, hlt, hprim⟩ := hx
    obtain ⟨n, k, rfl⟩ := (hchar x).mp hsol
    have hne : ¬ (n = 0 ∧ k = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at hpos
    have hcop : Nat.gcd n k = 1 :=
      (coprime_coordinates_iff_no_nontrivial_commonOutputPower hβirr hchar hne).mpr hprim
    exact ⟨(n, k), ⟨hcop, hlt⟩, rfl⟩
  · rw [Set.image_subset_iff]
    rintro ⟨n, k⟩ hmem
    obtain ⟨hcop0, hlt0⟩ := hmem
    have hcop : Nat.gcd n k = 1 := hcop0
    have hlt : (n : ℝ) + (k : ℝ) * β < T := hlt0
    have hne : ¬ (n = 0 ∧ k = 0) := by
      rintro ⟨rfl, rfl⟩
      simp at hcop
    show ((n : ℝ) + (k : ℝ) * β) ∈ powerPrimitiveTwoBaseIntegralSolutionsBelow T
    exact ⟨(hchar _).mpr ⟨n, k, rfl⟩, pos_of_coordinates_ne_zero hβ hne, hlt,
      (coprime_coordinates_iff_no_nontrivial_commonOutputPower hβirr hchar hne).mp hcop⟩

/-- The exact count of power-primitive positive solutions below `T`. -/
theorem ncard_powerPrimitiveTwoBaseIntegralSolutionsBelow {β : ℝ} (hβ : 0 < β)
    (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    (T : ℝ) :
    (powerPrimitiveTwoBaseIntegralSolutionsBelow T).ncard
      = (primitiveCoordinatePairsBelow β T).ncard := by
  rw [powerPrimitiveTwoBaseIntegralSolutionsBelow_eq_image hβ hβirr hchar T]
  exact Set.ncard_image_of_injective _
    (IntegerExponent.Irrational.injective_nat_add_mul hβirr)

/-- **Exact finite count identity.**  Every positive solution below `T` is a perfect power of
a power-primitive one, and the bookkeeping is exact:
`N T = ∑ g ∈ Finset.Icc 1 G, P (T / g)` with `G = ⌈T⌉₊ + ⌈T / β⌉₊`. -/
theorem ncard_twoBaseIntegralSolutionsBelow_eq_sum_powerPrimitive
    {β : ℝ} (hβ : 0 < β) (hβirr : Irrational β)
    (hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β)
    (T : ℝ) :
    (twoBaseIntegralSolutionsBelow T).ncard =
      ∑ g ∈ Finset.Icc 1 (⌈T⌉₊ + ⌈T / β⌉₊),
        (powerPrimitiveTwoBaseIntegralSolutionsBelow (T / (g : ℝ))).ncard := by
  rw [ncard_twoBaseIntegralSolutionsBelow hβ hβirr hchar T,
    ncard_coordinatePairsBelow_eq_sum_primitive hβ T]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [ncard_powerPrimitiveTwoBaseIntegralSolutionsBelow hβ hβirr hchar (T / (g : ℝ))]

/-- **Frequency of a fixed common power degree.**  Unconditionally, the positive solutions
below `T` whose outputs are both perfect `r`-th powers are exactly `r` times the positive
solutions below `T / r`. -/
theorem commonOutputPowerSolutionsBelow_eq_image {T : ℝ} {r : ℕ} (hr : 0 < r) :
    commonOutputPowerSolutionsBelow T r =
      (fun y : ℝ => (r : ℝ) * y) '' twoBaseIntegralSolutionsBelow (T / (r : ℝ)) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := hrR.ne'
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨_hsol, hpos, hlt, hpow⟩ := hx
    have hbound : x / (r : ℝ) < T / (r : ℝ) := by
      rw [div_lt_iff₀ hrR, div_mul_cancel₀ T hrne]
      exact hlt
    refine ⟨x / (r : ℝ), ⟨(isCommonOutputPower_iff_twoBaseIntegralSolution_div hr).mp hpow,
      div_pos hpos hrR, hbound⟩, ?_⟩
    show (r : ℝ) * (x / (r : ℝ)) = x
    rw [mul_comm (r : ℝ) (x / (r : ℝ)), div_mul_cancel₀ x hrne]
  · rw [Set.image_subset_iff]
    intro y hy
    obtain ⟨hsol, hpos, hlt⟩ := hy
    have hdiv : ((r : ℝ) * y) / (r : ℝ) = y := mul_div_cancel_left₀ y hrne
    have hpow : IsCommonOutputPower ((r : ℝ) * y) r :=
      (isCommonOutputPower_iff_twoBaseIntegralSolution_div hr).mpr (by rw [hdiv]; exact hsol)
    show ((r : ℝ) * y) ∈ commonOutputPowerSolutionsBelow T r
    exact ⟨twoBaseIntegralSolution_of_isCommonOutputPower hpow, mul_pos hrR hpos,
      (lt_div_iff₀' hrR).mp hlt, hpow⟩

/-- The exact count of positive solutions below `T` with a common `r`-th power degree. -/
theorem ncard_commonOutputPowerSolutionsBelow {T : ℝ} {r : ℕ} (hr : 0 < r) :
    (commonOutputPowerSolutionsBelow T r).ncard
      = (twoBaseIntegralSolutionsBelow (T / (r : ℝ))).ncard := by
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  rw [commonOutputPowerSolutionsBelow_eq_image hr]
  refine Set.ncard_image_of_injective _ ?_
  intro a b h
  exact mul_left_cancel₀ hrne h

/-! ## The conditional package -/

/-- **Conditional summary.**  If the Alaoglu--Erdős conjecture fails, the canonical primitive
generator `β` makes the perfect-power classification and the exact counts explicit at once:
the common perfect-power degrees at `n + k β` are the common divisors of the coordinates, the
greatest one is `Nat.gcd n k`, the matched affine decompositions are classified by the same
coordinates, and the count of positive solutions below any real bound splits exactly over the
degrees. -/
theorem exists_primitiveGenerator_with_perfectPowerContent
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ β : ℝ, 0 < β ∧ Irrational β ∧ IsLeastTwoBaseNonintegerSolution β ∧
      (∀ n k e : ℕ, 0 < e →
        (IsCommonOutputPower ((n : ℝ) + (k : ℝ) * β) e ↔ e ∣ n ∧ e ∣ k)) ∧
      (∀ n k : ℕ, ¬ (n = 0 ∧ k = 0) →
        IsGreatest {e : ℕ | 0 < e ∧ IsCommonOutputPower ((n : ℝ) + (k : ℝ) * β) e}
          (Nat.gcd n k)) ∧
      (∀ n k r d : ℕ, 0 < d →
        (IsMatchedAffineDecomposition ((n : ℝ) + (k : ℝ) * β) r d ↔
          r ≤ n ∧ d ∣ (n - r) ∧ d ∣ k)) ∧
      ∀ T : ℝ, (twoBaseIntegralSolutionsBelow T).ncard =
        ∑ g ∈ Finset.Icc 1 (⌈T⌉₊ + ⌈T / β⌉₊),
          (powerPrimitiveTwoBaseIntegralSolutionsBelow (T / (g : ℝ))).ncard := by
  obtain ⟨_w, _d, _a, _c, β, _, _, _, _, _, _, _, _, _, _, _, _,
      hβirr, hβleast, hunique, _⟩ :=
    exists_canonical_primitiveGenerator_of_not_alaogluErdosConjecture hfail
  have hβpos : 0 < β := hβleast.pos
  have hinj : Function.Injective
      (fun nk : ℕ × ℕ ↦ (nk.1 : ℝ) + (nk.2 : ℝ) * β) :=
    IntegerExponent.Irrational.injective_nat_add_mul hβirr
  have hchar : ∀ x : ℝ, TwoBaseIntegralSolution x ↔
      ∃ n k : ℕ, x = (n : ℝ) + (k : ℝ) * β := by
    intro x
    constructor
    · intro hx
      obtain ⟨nk, hnk, _⟩ := (hunique x).mp hx
      exact ⟨nk.1, nk.2, hnk⟩
    · rintro ⟨n, k, hnk⟩
      apply (hunique x).mpr
      refine ⟨(n, k), hnk, ?_⟩
      intro nk hnk'
      apply hinj
      exact hnk'.symm.trans hnk
  refine ⟨β, hβpos, hβirr, hβleast, ?_, ?_, ?_, ?_⟩
  · intro n k e he
    exact isCommonOutputPower_coordinates_iff hβirr hchar he
  · intro n k hnk
    exact isGreatest_commonOutputPowerDegree_coordinates hβirr hchar hnk
  · intro n k r d hd
    exact isMatchedAffineDecomposition_coordinates_iff hβirr hchar hd
  · intro T
    exact ncard_twoBaseIntegralSolutionsBelow_eq_sum_powerPrimitive hβpos hβirr hchar T

end LeanProofs.TwoBaseIntegerExponent

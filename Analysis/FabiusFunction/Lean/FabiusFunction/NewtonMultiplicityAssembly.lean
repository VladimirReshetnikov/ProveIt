import FabiusFunction.ShiftDifferenceWeights

/-!
# Assembling the Newton components of a scale multiplicity

For a weight sequence `w : ℕ → M` the corpus writes
`weightedScaleMultiplicity b w n` for the total weight
`w 0 + ⋯ + w (v_b n)` carried by the geometric layers of `n` in base
`b`.  The exponents volume records, for an integer-valued polynomial
`P` with Newton expansion `P h = ∑_{r ≤ d} c r * C(h, r)`, the
zero-multiplicity formula

`m_P n = ∑_{r ≤ d} c r * C(v₂ n + 1, r + 1)`.

`Fabius.weightedScaleMultiplicity_choose` already proves the single
Newton component: the Pascal weight `h ↦ C(h, r)` has multiplicity
`C(v_b n + 1, r + 1)`, over `ℕ` and for an arbitrary base.  This
module assembles those components into the signed sum over `r`.

The content of the assembly is that `Fabius.inclusivePrefixSum` is
linear in its weight sequence.  Additivity over a finite index set is
`Finset.sum_comm` and holds in every additive commutative monoid;
compatibility with a scalar is `Finset.mul_sum`.  Signed Newton
coefficients force leaving `ℕ`, so the assembled statements live in a
commutative ring `R`, the Pascal component being transported there by
`Nat.cast`.

## Scope

This is the multiplicity half of the volume's Newton–Rvachev theorem
and nothing else.  The analytic factorization of the canonical
products needs `Φ` at a general weight sequence, which the corpus does
not have; no statement here proves or approaches it.

`weight_eq_sum_choose_fwdDiff` records the Gregory–Newton reading of
the coefficients: for a weight sequence `a` valued in an additive
commutative group, `a m = ∑_{r ≤ m} C(m, r) • (Δʳa) 0`.  In
`weightedScaleMultiplicity_eq_sum_fwdDiff` the vanishing of `(Δʳa) 0`
for `r > d` is a *hypothesis*, not a conclusion.  Three links are
left informal here: that a rational polynomial of degree at most `d`
which is integer-valued on `ℕ` has *identically* vanishing `(d+1)`-st
forward difference on `ℕ`, whence `Δʳa 0 = 0` for every `r > d`; that
`Δ^s` applied to a Newton sum returns the coefficient `c s`, which is
what would make the coefficients unique; and that the Newton
coefficients of a polynomial integer-valued on `ℕ` are themselves
integers (Pólya).  None is proved in this module.

## Main declarations

* `inclusivePrefixSum_sum` — a prefix sum of a finite sum of weight
  sequences is the finite sum of the prefix sums;
* `weightedScaleMultiplicity_sum` — the same for multiplicities;
* `inclusivePrefixSum_const_mul` and
  `weightedScaleMultiplicity_const_mul` — a constant left factor
  passes through a prefix sum and through a multiplicity;
* `weightedScaleMultiplicity_natCast_choose` — the Pascal component,
  cast into an additive commutative monoid with one;
* `weightedScaleMultiplicity_newton_finset` — the assembled formula
  over an arbitrary finite set of Newton indices;
* `weightedScaleMultiplicity_newton` — the volume's display, over
  `range (d + 1)`;
* `weightedScaleMultiplicity_newton_int` and
  `weightedScaleMultiplicity_newton_two` — the integer and dyadic
  specializations;
* `weight_eq_sum_choose_fwdDiff` and
  `weight_eq_sum_choose_fwdDiff_of_vanishing` — the Gregory–Newton
  reading of the coefficients;
* `weightedScaleMultiplicity_eq_sum_fwdDiff` — the truncated
  Gregory–Newton reading fed into `weightedScaleMultiplicity_newton`;
* `padicValNat_two_four`, `choose_two_expansion`, `sqNewtonCoeff`,
  `sqNewtonCoeff_expand`, `weightedScaleMultiplicity_sq_four_direct`,
  `weightedScaleMultiplicity_sq_four` and
  `sqNewtonCoeff_shift_discriminates` — the worked example
  `P h = h * h = C(h, 1) + 2 * C(h, 2)` and its numeric guards.
-/

set_option autoImplicit false

open Finset fwdDiff

namespace Fabius

/-- **Additivity in the weight sequence.**  The inclusive prefix sum
of a finite sum of weight sequences is the finite sum of their
inclusive prefix sums.  This is `Finset.sum_comm`, and it needs
nothing beyond an additive commutative monoid. -/
theorem inclusivePrefixSum_sum {M ι : Type*} [AddCommMonoid M]
    (s : Finset ι) (f : ι → ℕ → M) (n : ℕ) :
    inclusivePrefixSum (fun h ↦ ∑ i ∈ s, f i h) n =
      ∑ i ∈ s, inclusivePrefixSum (f i) n := by
  simp only [inclusivePrefixSum]
  exact Finset.sum_comm

/-- The same additivity, read off at the geometric layers of `n`:
a weighted scale multiplicity is additive in its weight sequence. -/
theorem weightedScaleMultiplicity_sum {M ι : Type*} [AddCommMonoid M]
    (b : ℕ) (s : Finset ι) (f : ι → ℕ → M) (n : ℕ) :
    weightedScaleMultiplicity b (fun h ↦ ∑ i ∈ s, f i h) n =
      ∑ i ∈ s, weightedScaleMultiplicity b (f i) n :=
  inclusivePrefixSum_sum s f (padicValNat b n)

/-- **Compatibility with a scalar.**  A constant left factor passes
through an inclusive prefix sum. -/
theorem inclusivePrefixSum_const_mul {R : Type*}
    [NonUnitalNonAssocSemiring R] (c : R) (g : ℕ → R) (n : ℕ) :
    inclusivePrefixSum (fun h ↦ c * g h) n =
      c * inclusivePrefixSum g n := by
  rw [inclusivePrefixSum, inclusivePrefixSum, Finset.mul_sum]

/-- A constant left factor passes through a weighted scale
multiplicity. -/
theorem weightedScaleMultiplicity_const_mul {R : Type*}
    [NonUnitalNonAssocSemiring R] (b : ℕ) (c : R) (g : ℕ → R)
    (n : ℕ) :
    weightedScaleMultiplicity b (fun h ↦ c * g h) n =
      c * weightedScaleMultiplicity b g n :=
  inclusivePrefixSum_const_mul c g (padicValNat b n)

/-- **The Pascal component in a ring.**  The image of
`weightedScaleMultiplicity_choose` under `Nat.cast`: the weight
`h ↦ (C(h, r) : R)` has multiplicity `(C(v_b n + 1, r + 1) : R)`.

The hockey-stick identity is not reproved; the cast is pushed through
the finite sum by `Nat.cast_sum`. -/
theorem weightedScaleMultiplicity_natCast_choose {R : Type*}
    [AddCommMonoidWithOne R] (b n r : ℕ) :
    weightedScaleMultiplicity b (fun h ↦ ((h.choose r : ℕ) : R)) n =
      (((padicValNat b n + 1).choose (r + 1) : ℕ) : R) := by
  have hsum :
      ((weightedScaleMultiplicity b (fun h ↦ h.choose r) n : ℕ) : R) =
        weightedScaleMultiplicity b
          (fun h ↦ ((h.choose r : ℕ) : R)) n := by
    rw [weightedScaleMultiplicity, weightedScaleMultiplicity,
      inclusivePrefixSum, inclusivePrefixSum, Nat.cast_sum]
  rw [← hsum, weightedScaleMultiplicity_choose]

/-- **The assembled Newton formula.**  For coefficients `c : ℕ → R`
in a commutative ring and any finite set `s` of Newton indices,

`m (∑_{r ∈ s} c r * C(·, r)) n = ∑_{r ∈ s} c r * C(v_b n + 1, r + 1)`.

The base `b` is arbitrary, exactly as in the component theorem
`weightedScaleMultiplicity_choose`. -/
theorem weightedScaleMultiplicity_newton_finset {R : Type*}
    [NonAssocSemiring R] (b : ℕ) (s : Finset ℕ) (c : ℕ → R)
    (n : ℕ) :
    weightedScaleMultiplicity b
        (fun h ↦ ∑ r ∈ s, c r * ((h.choose r : ℕ) : R)) n =
      ∑ r ∈ s,
        c r * (((padicValNat b n + 1).choose (r + 1) : ℕ) : R) := by
  have hadd :
      weightedScaleMultiplicity b
          (fun h ↦ ∑ r ∈ s, c r * ((h.choose r : ℕ) : R)) n =
        ∑ r ∈ s,
          weightedScaleMultiplicity b
            (fun h ↦ c r * ((h.choose r : ℕ) : R)) n :=
    weightedScaleMultiplicity_sum b s
      (fun r h ↦ c r * ((h.choose r : ℕ) : R)) n
  rw [hadd]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hmul :
      weightedScaleMultiplicity b
          (fun h ↦ c r * ((h.choose r : ℕ) : R)) n =
        c r *
          weightedScaleMultiplicity b
            (fun h ↦ ((h.choose r : ℕ) : R)) n :=
    weightedScaleMultiplicity_const_mul b (c r)
      (fun h ↦ ((h.choose r : ℕ) : R)) n
  have hchoose :
      weightedScaleMultiplicity b
          (fun h ↦ ((h.choose r : ℕ) : R)) n =
        (((padicValNat b n + 1).choose (r + 1) : ℕ) : R) :=
    weightedScaleMultiplicity_natCast_choose b n r
  rw [hmul, hchoose]

/-- **The volume's display `(p1:eq:mP)`.**  The Newton indices run
over `range (d + 1)`, i.e. `0 ≤ r ≤ d`. -/
theorem weightedScaleMultiplicity_newton {R : Type*}
    [NonAssocSemiring R] (b : ℕ) (c : ℕ → R) (d n : ℕ) :
    weightedScaleMultiplicity b
        (fun h ↦ ∑ r ∈ range (d + 1),
          c r * ((h.choose r : ℕ) : R)) n =
      ∑ r ∈ range (d + 1),
        c r * (((padicValNat b n + 1).choose (r + 1) : ℕ) : R) :=
  weightedScaleMultiplicity_newton_finset b (range (d + 1)) c n

/-- The integer specialization.  The Newton coefficients of a
polynomial integer-valued on `ℕ` are integers (Pólya; not formalized
here), and they may be negative. -/
theorem weightedScaleMultiplicity_newton_int (b : ℕ) (c : ℕ → ℤ)
    (d n : ℕ) :
    weightedScaleMultiplicity b
        (fun h ↦ ∑ r ∈ range (d + 1),
          c r * ((h.choose r : ℕ) : ℤ)) n =
      ∑ r ∈ range (d + 1),
        c r * (((padicValNat b n + 1).choose (r + 1) : ℕ) : ℤ) :=
  weightedScaleMultiplicity_newton b c d n

/-- The dyadic specialization, which is the volume's display with the
`2`-adic valuation `v₂` written out. -/
theorem weightedScaleMultiplicity_newton_two (c : ℕ → ℤ) (d n : ℕ) :
    weightedScaleMultiplicity 2
        (fun h ↦ ∑ r ∈ range (d + 1),
          c r * ((h.choose r : ℕ) : ℤ)) n =
      ∑ r ∈ range (d + 1),
        c r * (((padicValNat 2 n + 1).choose (r + 1) : ℕ) : ℤ) :=
  weightedScaleMultiplicity_newton_int 2 c d n

/-- **Gregory–Newton coefficients at a natural argument.**  The value
of a weight sequence at `m` is the binomial combination of its
iterated forward differences at `0`:
`a m = ∑_{r ≤ m} C(m, r) • (Δʳa) 0`.

This is `weight_shift_eq_sum_fwdDiff` based at `0`; it exhibits
`Δʳa 0` as a valid choice of the volume's coefficients `c r`.  That
the choice is forced — that `Δˢ` applied to a Newton sum returns
`c s` — is not formalized here. -/
theorem weight_eq_sum_choose_fwdDiff {G : Type*} [AddCommGroup G]
    (a : ℕ → G) (m : ℕ) :
    a m = ∑ r ∈ range (m + 1), m.choose r • Δ_[1]^[r] a 0 := by
  have hshift := weight_shift_eq_sum_fwdDiff a m 0
  rwa [Nat.zero_add] at hshift

/-- If all iterated forward differences of `a` at `0` above index `d`
vanish, the Gregory–Newton sum truncates to `range (d + 1)`,
uniformly in `m`.

The vanishing hypothesis is what "`a` is a polynomial weight
sequence of degree at most `d`" supplies; that condition in fact
supplies more, since `Δ^{d+1}a` then vanishes at every point and not
only at `0`.  It is assumed here, not derived. -/
theorem weight_eq_sum_choose_fwdDiff_of_vanishing {G : Type*}
    [AddCommGroup G] (a : ℕ → G) (d : ℕ)
    (hvan : ∀ r, d < r → Δ_[1]^[r] a 0 = 0) (m : ℕ) :
    a m = ∑ r ∈ range (d + 1), m.choose r • Δ_[1]^[r] a 0 := by
  have hm : m + 1 ≤ m + d + 1 := by omega
  have hd : d + 1 ≤ m + d + 1 := by omega
  have h1 : ∑ r ∈ range (m + 1), m.choose r • Δ_[1]^[r] a 0 =
      ∑ r ∈ range (m + d + 1), m.choose r • Δ_[1]^[r] a 0 := by
    refine Finset.sum_subset
      (Finset.range_subset_range.mpr hm) fun r _ hr ↦ ?_
    simp only [Finset.mem_range] at hr
    have hlt : m < r := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, zero_nsmul]
  have h2 : ∑ r ∈ range (d + 1), m.choose r • Δ_[1]^[r] a 0 =
      ∑ r ∈ range (m + d + 1), m.choose r • Δ_[1]^[r] a 0 := by
    refine Finset.sum_subset
      (Finset.range_subset_range.mpr hd) fun r _ hr ↦ ?_
    simp only [Finset.mem_range] at hr
    have hlt : d < r := by omega
    rw [hvan r hlt, nsmul_zero]
  rw [h2, ← h1]
  exact weight_eq_sum_choose_fwdDiff a m

/-- **The Newton formula with the coefficients named.**  If the
iterated forward differences of a ring-valued weight sequence `a`
vanish at `0` above index `d`, then the multiplicity of `a` is the
signed sum of the volume, with `c r = (Δʳa) 0` literally.

This is `weightedScaleMultiplicity_newton` composed with
`weight_eq_sum_choose_fwdDiff_of_vanishing`. -/
theorem weightedScaleMultiplicity_eq_sum_fwdDiff {R : Type*}
    [CommRing R] (b : ℕ) (a : ℕ → R) (d : ℕ)
    (hvan : ∀ r, d < r → Δ_[1]^[r] a 0 = 0) (n : ℕ) :
    weightedScaleMultiplicity b a n =
      ∑ r ∈ range (d + 1),
        Δ_[1]^[r] a 0 *
          (((padicValNat b n + 1).choose (r + 1) : ℕ) : R) := by
  have hfun : a = fun m ↦ ∑ r ∈ range (d + 1),
      Δ_[1]^[r] a 0 * ((m.choose r : ℕ) : R) := by
    funext m
    rw [weight_eq_sum_choose_fwdDiff_of_vanishing a d hvan m]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    exact (nsmul_eq_mul _ _).trans (mul_comm _ _)
  calc
    weightedScaleMultiplicity b a n =
        weightedScaleMultiplicity b
          (fun m ↦ ∑ r ∈ range (d + 1),
            Δ_[1]^[r] a 0 * ((m.choose r : ℕ) : R)) n :=
      congrArg (fun w : ℕ → R ↦ weightedScaleMultiplicity b w n) hfun
    _ = ∑ r ∈ range (d + 1),
          Δ_[1]^[r] a 0 *
            (((padicValNat b n + 1).choose (r + 1) : ℕ) : R) :=
      weightedScaleMultiplicity_newton b
        (fun r ↦ Δ_[1]^[r] a 0) d n

/-- `v₂(4) = 2`: the layers of `4` are the heights `0, 1, 2`. -/
theorem padicValNat_two_four : padicValNat 2 4 = 2 := by
  have hb : 1 < 2 := by decide
  have h4 : (4 : ℕ) = 2 ^ 2 := by decide
  have hv : padicValNat 2 (2 ^ 2) = 2 := padicValNat_base_pow hb 2
  rw [h4]
  exact hv

/-- The Newton expansion of the square over `ℕ`:
`m + 2 * C(m, 2) = m * m`. -/
theorem choose_two_expansion (m : ℕ) :
    m + 2 * m.choose 2 = m * m := by
  induction m with
  | zero => decide
  | succ k ih =>
      have hc : (k + 1).choose 2 = k + k.choose 2 := by
        simpa using Nat.choose_succ_succ' k 1
      have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [hc, hsq, ← ih]
      ring

/-- The Newton coefficients of the polynomial `P h = h * h`, namely
`c = (0, 1, 2)`, extended by `0`.  See `sqNewtonCoeff_expand`. -/
def sqNewtonCoeff (r : ℕ) : ℤ :=
  if r = 1 then 1 else if r = 2 then 2 else 0

/-- `sqNewtonCoeff` really does expand `h ↦ h * h` in the Pascal
basis: `h * h = C(h, 1) + 2 * C(h, 2)`. -/
theorem sqNewtonCoeff_expand (h : ℕ) :
    ∑ r ∈ range 3, sqNewtonCoeff r * ((h.choose r : ℕ) : ℤ) =
      (h : ℤ) * (h : ℤ) := by
  have hexpand :
      ∑ r ∈ range 3, sqNewtonCoeff r * ((h.choose r : ℕ) : ℤ) =
        sqNewtonCoeff 0 * ((h.choose 0 : ℕ) : ℤ) +
          sqNewtonCoeff 1 * ((h.choose 1 : ℕ) : ℤ) +
          sqNewtonCoeff 2 * ((h.choose 2 : ℕ) : ℤ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hc0 : sqNewtonCoeff 0 = 0 := by decide
  have hc1 : sqNewtonCoeff 1 = 1 := by decide
  have hc2 : sqNewtonCoeff 2 = 2 := by decide
  have hz : (h : ℤ) + 2 * ((h.choose 2 : ℕ) : ℤ) =
      (h : ℤ) * (h : ℤ) := by
    exact_mod_cast choose_two_expansion h
  rw [hexpand, hc0, hc1, hc2, Nat.choose_one_right, zero_mul,
    one_mul, zero_add]
  exact hz

/-- **Numeric guard, direct side.**  With the weight `h ↦ h * h` the
layers of `4` are the heights `0, 1, 2`, so the multiplicity is
`0 + 1 + 4 = 5`. -/
theorem weightedScaleMultiplicity_sq_four_direct :
    weightedScaleMultiplicity 2 (fun h ↦ (h : ℤ) * (h : ℤ)) 4
      = 5 := by
  rw [weightedScaleMultiplicity, padicValNat_two_four,
    inclusivePrefixSum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **Numeric guard, assembled side.**  The same value `5` obtained
from `weightedScaleMultiplicity_newton_finset`, i.e. as
`∑_{r ≤ 2} c r * C(3, r + 1) = 0 * 3 + 1 * 3 + 2 * 1`.

Together with `sqNewtonCoeff_shift_discriminates` this pins the shift
`r ↦ r + 1` in the volume's display. -/
theorem weightedScaleMultiplicity_sq_four :
    weightedScaleMultiplicity 2
        (fun h ↦ ∑ r ∈ range 3,
          sqNewtonCoeff r * ((h.choose r : ℕ) : ℤ)) 4 = 5 := by
  have hnewton := weightedScaleMultiplicity_newton_finset 2
    (range 3) sqNewtonCoeff 4
  rw [padicValNat_two_four] at hnewton
  exact hnewton.trans (by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      sqNewtonCoeff]
    norm_num)

/-- **The shift `r ↦ r + 1` is not cosmetic.**  On the same
coefficients, with `v₂(4) = 2` already substituted, the two nearest
variants of
the volume's display take the values `9` and `1`, neither of which is
the true multiplicity `5` computed in
`weightedScaleMultiplicity_sq_four_direct`. -/
theorem sqNewtonCoeff_shift_discriminates :
    (∑ r ∈ range 3,
        sqNewtonCoeff r * (((3 : ℕ).choose r : ℕ) : ℤ)) = 9 ∧
      (∑ r ∈ range 3,
        sqNewtonCoeff r * (((2 : ℕ).choose (r + 1) : ℕ) : ℤ)) = 1 := by
  constructor <;>
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        sqNewtonCoeff]
      norm_num

end Fabius

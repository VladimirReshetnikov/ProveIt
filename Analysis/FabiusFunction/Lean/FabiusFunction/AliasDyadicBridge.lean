import FabiusFunction.HalfIntegerAliasIdentity
import FabiusFunction.EffectiveFlatness
import FabiusFunction.DyadicAnalytic
import FabiusFunction.CyclicCharacterSums

/-!
# The alias coefficients as a half-range cosine transform of dyadic values

The spectra volume's displays `p1:eq:A-Up-DCT` and `p1:eq:A-F-DCT`: the
half-integer alias coefficient `A_{N,r}` is the finite cosine transform

`A_{N,r} = N⁻¹ [1 + 2 ∑_{j=1}^{N-1} up(j/N) cos(π r j/N)]`,

and for `N = 2^n` the samples are the exact rational dyadic values of the
Fabius function, `up(j/2^n) = F((2^n - j)/2^n) = fabiusDyadic n (2^n - j)`.
Together with `foldedCoefficient_eq_tsum` this is the bridge between the
infinite sinc product (the alias class of `Φ` on the half-integers) and the
`q`-binomial side of the corpus (the dyadic values computed by
`fabiusDyadic`, whose `q`-binomial closed form is
`qBinomialThueMorseTranslatedFormulaIn_eq_fabiusAtInverseTwoPow`).

The general tool is a fold of a sum over `ℤ/2Nℤ` of an even function onto
the half range `1 ≤ k ≤ N-1`, `sum_zmod_even_eq_fold`.  For odd `r` the
half-range cosine sum vanishes (`sum_Ico_cos_alias_angle_odd`), which turns
the display into the volume's sign form `p1:eq:A-F-DCT` with `1 - up` in place
of `up` (`foldedCoefficient_eq_halfRange_cos_odd`).
-/

set_option autoImplicit false

namespace Fabius

open Finset

/-- A sum over `ℤ/nℤ` is a sum over `range n` through `ZMod.val`. -/
theorem sum_zmod_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n]
    (f : ZMod n → M) :
    ∑ j : ZMod n, f j = ∑ k ∈ range n, f (k : ZMod n) := by
  refine sum_nbij' (fun j => j.val) (fun k => (k : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro j _
    exact mem_range.mpr (ZMod.val_lt j)
  · intro k _
    exact mem_univ _
  · intro j _
    exact ZMod.natCast_zmod_val j
  · intro k hk
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp hk)]
  · intro j _
    rw [ZMod.natCast_zmod_val]

/-- **Half-range fold.**  For an even function on `ℤ/2Nℤ`,
`∑_j f(j) = f(0) + f(N) + 2 ∑_{1 ≤ k ≤ N-1} f(k)`. -/
theorem sum_zmod_even_eq_fold (N : ℕ) [NeZero N] (f : ZMod (2 * N) → ℂ)
    (hf : ∀ j, f (-j) = f j) :
    ∑ j : ZMod (2 * N), f j
      = f 0 + f (N : ZMod (2 * N)) + 2 * ∑ k ∈ Ico 1 N, f (k : ZMod (2 * N)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hsplit := sum_range_add (fun k : ℕ => f (k : ZMod (2 * N))) N N
  rw [show N + N = 2 * N by ring] at hsplit
  rw [sum_zmod_eq_sum_range, hsplit, range_eq_Ico,
    sum_eq_sum_Ico_succ_bot hN, sum_eq_sum_Ico_succ_bot hN]
  have hrefl : ∑ k ∈ Ico 1 N, f (((N + k : ℕ)) : ZMod (2 * N))
      = ∑ k ∈ Ico 1 N, f (k : ZMod (2 * N)) := by
    refine sum_nbij' (fun k => N - k) (fun k => N - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      rw [mem_Ico] at hk ⊢
      omega
    · intro k hk
      rw [mem_Ico] at hk ⊢
      omega
    · intro k hk
      rw [mem_Ico] at hk
      omega
    · intro k hk
      rw [mem_Ico] at hk
      omega
    · intro k hk
      rw [mem_Ico] at hk
      rw [← hf ((N - k : ℕ) : ZMod (2 * N))]
      congr 1
      have h1 : N + k = 2 * N - (N - k) := by omega
      have h2 : ((2 * N : ℕ) : ZMod (2 * N)) = 0 := ZMod.natCast_self (2 * N)
      rw [h1, Nat.cast_sub (by omega), h2, zero_sub]
  rw [hrefl]
  simp only [Nat.add_zero, Nat.cast_zero]
  ring

/-- The cosine factor of the sample sum is even in the residue. -/
theorem cos_alias_angle_neg (N : ℕ) [NeZero N] (r j : ZMod (2 * N)) :
    Complex.cos ((Real.pi * r.val * (-j).val / N : ℝ) : ℂ)
      = Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ) := by
  by_cases hj : j = 0
  · subst hj
    simp
  · have hval : (-j).val = 2 * N - j.val := by
      rw [ZMod.neg_val, if_neg hj]
    have hlt : j.val < 2 * N := ZMod.val_lt j
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    rw [hval, ← Complex.cos_int_mul_two_pi_sub _ (r.val : ℤ)]
    congr 1
    rw [Nat.cast_sub hlt.le]
    push_cast
    field_simp
    ring

/-- **`p1:eq:A-Up-DCT`**: the alias coefficient as a half-range cosine transform
of the samples `up(k/N)`, `1 ≤ k ≤ N-1`. -/
theorem foldedCoefficient_eq_halfRange_cos (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] (r : ZMod (2 * N)) :
    foldedCoefficient F N r
      = (N : ℂ)⁻¹ * (1 + 2 * ∑ k ∈ Ico 1 N,
          (rvachevUp F ((k : ℝ) / N) : ℂ) * Complex.cos ((Real.pi * r.val * k / N : ℝ) : ℂ)) := by
  rw [foldedCoefficient_eq_sum_cos]
  congr 1
  rw [sum_zmod_even_eq_fold N _ (fun j => by rw [gridSample_neg, cos_alias_angle_neg])]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the two end samples
  have h0 : gridSample F N 0 = 1 := by
    rw [show (0 : ZMod (2 * N)) = ((0 : ℕ) : ZMod (2 * N)) by simp,
      gridSample_natCast_of_le F hF N (Nat.zero_le N)]
    simp [rvachevUp_zero F hF]
  have hNN : gridSample F N (N : ZMod (2 * N)) = 0 := by
    rw [gridSample_natCast_of_le F hF N le_rfl, div_self hN.ne', rvachevUp_one F hF]
    simp
  rw [h0, hNN]
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div, Complex.ofReal_zero,
    Complex.cos_zero, mul_one, zero_mul, add_zero]
  congr 2
  refine sum_congr rfl fun k hk => ?_
  rw [mem_Ico] at hk
  have hval : ((k : ℕ) : ZMod (2 * N)).val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [hval, gridSample_natCast_of_le F hF N hk.2.le]

/-- **`p1:eq:A-F-DCT` at dyadic level**: for `N = 2^n` the samples are the exact
rational dyadic values, `up(k/2^n) = F((2^n-k)/2^n) = fabiusDyadic n (2^n - k)`. -/
theorem foldedCoefficient_two_pow_eq_fabiusDyadic (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (r : ZMod (2 * 2 ^ n)) :
    foldedCoefficient F (2 ^ n) r
      = ((2 : ℂ) ^ n)⁻¹ * (1 + 2 * ∑ k ∈ Ico 1 (2 ^ n),
          ((fabiusDyadic n (2 ^ n - k) : ℝ) : ℂ) *
            Complex.cos ((Real.pi * r.val * k / 2 ^ n : ℝ) : ℂ)) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hup : ∀ k : ℕ, k < 2 ^ n →
      rvachevUp F ((k : ℝ) / 2 ^ n) = (fabiusDyadic n (2 ^ n - k) : ℝ) := by
    intro k hk
    rw [fabiusDyadic_cast F hF n (2 ^ n - k) (Nat.sub_le _ _),
      rvachevUp_eq_fabiusReal_one_sub_abs, abs_of_nonneg (by positivity),
      Nat.cast_sub hk.le]
    congr 1
    push_cast
    rw [sub_div, div_self h2.ne']
  have hsum : ∑ k ∈ (Ico 1 (2 ^ n) : Finset ℕ),
        (rvachevUp F ((k : ℝ) / 2 ^ n) : ℂ) *
          Complex.cos ((Real.pi * r.val * k / 2 ^ n : ℝ) : ℂ)
      = ∑ k ∈ (Ico 1 (2 ^ n) : Finset ℕ),
        ((fabiusDyadic n (2 ^ n - k) : ℝ) : ℂ) *
          Complex.cos ((Real.pi * r.val * k / 2 ^ n : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rw [hup k hk.2]
  rw [foldedCoefficient_eq_halfRange_cos F hF]
  simp only [Nat.cast_pow, Nat.cast_ofNat, hsum]

/-! ## The sign form for odd residues (`p1:eq:A-F-DCT`) -/

/-- The full cosine sum over a period vanishes for every nonzero residue `r`. -/
theorem sum_cos_alias_angle_eq_zero (N : ℕ) [NeZero N] (r : ZMod (2 * N)) (hr : r ≠ 0) :
    ∑ j : ZMod (2 * N), Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ) = 0 := by
  have h2 : (2 : ℂ) * ∑ j : ZMod (2 * N), Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ)
      = ∑ j : ZMod (2 * N), ZMod.stdAddChar (j * r)
        + ∑ j : ZMod (2 * N), ZMod.stdAddChar (j * -r) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [Complex.two_cos, stdAddChar_mul_eq_exp, mul_neg, stdAddChar_neg_mul_eq_exp]
  rw [sum_stdAddChar_mul, sum_stdAddChar_mul, if_neg hr, if_neg (neg_ne_zero.mpr hr),
    add_zero] at h2
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- For odd `r` the half-range cosine sum vanishes: `∑_{1 ≤ k < N} cos(π r k/N) = 0`. -/
theorem sum_Ico_cos_alias_angle_odd (N : ℕ) [NeZero N] (r : ZMod (2 * N)) (hr : Odd r.val) :
    ∑ k ∈ Ico 1 N, Complex.cos ((Real.pi * r.val * k / N : ℝ) : ℂ) = 0 := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [ZMod.val_zero] at hr
    exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hr
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hfold := sum_zmod_even_eq_fold N
    (fun j => Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ)) (cos_alias_angle_neg N r)
  rw [sum_cos_alias_angle_eq_zero N r hr0] at hfold
  have h0 : Complex.cos ((Real.pi * r.val * (0 : ZMod (2 * N)).val / N : ℝ) : ℂ) = 1 := by
    simp
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNN : Complex.cos ((Real.pi * r.val * (N : ZMod (2 * N)).val / N : ℝ) : ℂ) = -1 := by
    have hval : (N : ZMod (2 * N)).val = N := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hang : (Real.pi * r.val * (N : ZMod (2 * N)).val / N : ℝ) = (r.val : ℕ) * Real.pi := by
      rw [hval]
      field_simp
    rw [hang, ← Complex.ofReal_cos, Real.cos_nat_mul_pi, Odd.neg_one_pow hr]
    push_cast
    ring
  have hsum : ∑ k ∈ Ico 1 N,
        Complex.cos ((Real.pi * r.val * ((k : ℕ) : ZMod (2 * N)).val / N : ℝ) : ℂ)
      = ∑ k ∈ Ico 1 N, Complex.cos ((Real.pi * r.val * k / N : ℝ) : ℂ) := by
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [h0, hNN, hsum] at hfold
  linear_combination (-1 / 2 : ℂ) * hfold

/-- **`p1:eq:A-F-DCT`** in the form `F = 1 - up`: for odd `r`,
`A_{N,r} = N⁻¹ [1 - 2 ∑_{1 ≤ k < N} (1 - up(k/N)) cos(π r k/N)]`. -/
theorem foldedCoefficient_eq_halfRange_cos_odd (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] (r : ZMod (2 * N)) (hr : Odd r.val) :
    foldedCoefficient F N r
      = (N : ℂ)⁻¹ * (1 - 2 * ∑ k ∈ Ico 1 N,
          (1 - (rvachevUp F ((k : ℝ) / N) : ℂ)) *
            Complex.cos ((Real.pi * r.val * k / N : ℝ) : ℂ)) := by
  rw [foldedCoefficient_eq_halfRange_cos F hF]
  congr 1
  have h := sum_Ico_cos_alias_angle_odd N r hr
  simp only [sub_mul, one_mul, sum_sub_distrib, h]
  ring

/-! ## The discrete energy identity in its odd form (`p1:eq:discrete-energy`)

Both sides of `sum_foldedCoefficient_sq` are sums of an even function over
`ℤ/2Nℤ`, so `sum_zmod_even_eq_fold` applies to each.  For even `N` the two
end residues contribute `1` and `0` on each side, and every even residue
strictly between `0` and `N` contributes nothing to the coefficient side, so
the fold leaves exactly the volume's statement: the odd coefficients below `N`
carry all the energy. -/

/-- The sample side of the energy identity, folded:
`∑_{j ∈ ℤ/2Nℤ} P(j/N)² = 1 + 2 ∑_{1 ≤ k < N} up(k/N)²`. -/
theorem sum_gridSample_sq_eq_fold (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] :
    ∑ j : ZMod (2 * N), gridSample F N j ^ 2
      = 1 + 2 * ∑ k ∈ Ico 1 N, (rvachevUp F ((k : ℝ) / N) : ℂ) ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [sum_zmod_even_eq_fold N (fun j => gridSample F N j ^ 2)
    (fun j => by rw [gridSample_neg])]
  have h0 : gridSample F N 0 = 1 := by
    rw [show (0 : ZMod (2 * N)) = ((0 : ℕ) : ZMod (2 * N)) by simp,
      gridSample_natCast_of_le F hF N (Nat.zero_le N)]
    simp [rvachevUp_zero F hF]
  have hNN : gridSample F N (N : ZMod (2 * N)) = 0 := by
    rw [gridSample_natCast_of_le F hF N le_rfl, div_self hN.ne', rvachevUp_one F hF]
    simp
  rw [h0, hNN]
  have hk : ∀ k ∈ Ico 1 N, gridSample F N ((k : ℕ) : ZMod (2 * N)) ^ 2
      = (rvachevUp F ((k : ℝ) / N) : ℂ) ^ 2 := by
    intro k hk
    rw [mem_Ico] at hk
    rw [gridSample_natCast_of_le F hF N hk.2.le]
  rw [sum_congr rfl hk]
  ring

/-- The coefficient side, folded: for even `N`,
`∑_{r ∈ ℤ/2Nℤ} A_{N,r}² = 1 + 2 ∑_{1 ≤ k < N} A_{N,k}²`. -/
theorem sum_foldedCoefficient_sq_eq_fold (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] (hNe : Even N) :
    ∑ r : ZMod (2 * N), foldedCoefficient F N r ^ 2
      = 1 + 2 * ∑ k ∈ Ico 1 N, foldedCoefficient F N ((k : ℕ) : ZMod (2 * N)) ^ 2 := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [sum_zmod_even_eq_fold N (fun r => foldedCoefficient F N r ^ 2)
    (fun r => by rw [foldedCoefficient_neg F hF])]
  rw [foldedCoefficient_zero F hF N]
  obtain ⟨m, hm⟩ := hNe
  have hNval : (N : ZMod (2 * N)) = ((2 * m : ℕ) : ZMod (2 * N)) := by
    congr 1
    omega
  have hzero : foldedCoefficient F N (N : ZMod (2 * N)) = 0 := by
    rw [hNval]
    exact foldedCoefficient_two_mul_eq_zero F hF N (by omega) (by omega)
  rw [hzero]
  ring

/-- Every even residue strictly between `0` and `N` contributes nothing. -/
theorem foldedCoefficient_sq_eq_zero_of_even (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] {k : ℕ} (hk0 : 1 ≤ k) (hkN : k < N) (hke : Even k) :
    foldedCoefficient F N ((k : ℕ) : ZMod (2 * N)) ^ 2 = 0 := by
  obtain ⟨s, hs⟩ := hke
  have hks : k = 2 * s := by omega
  rw [hks, foldedCoefficient_two_mul_eq_zero F hF N (by omega) (by omega)]
  ring

/-- **`p1:eq:discrete-energy`.**  For even `N` the energy of the folded spectrum
sits entirely on the odd residues below `N`:

`∑_{1 ≤ r < N, r odd} A_{N,r}² = N⁻¹ (1 + 2 ∑_{1 ≤ j < N} up(j/N)²) - 1/2`. -/
theorem sum_odd_foldedCoefficient_sq (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] (hNe : Even N) :
    ∑ k ∈ (Ico 1 N).filter (fun k => Odd k),
        foldedCoefficient F N ((k : ℕ) : ZMod (2 * N)) ^ 2
      = (N : ℂ)⁻¹ * (1 + 2 * ∑ k ∈ Ico 1 N, (rvachevUp F ((k : ℝ) / N) : ℂ) ^ 2) - 1 / 2 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  -- the even residues drop out of the half-range sum
  have hfilter : ∑ k ∈ Ico 1 N, foldedCoefficient F N ((k : ℕ) : ZMod (2 * N)) ^ 2
      = ∑ k ∈ (Ico 1 N).filter (fun k => Odd k),
          foldedCoefficient F N ((k : ℕ) : ZMod (2 * N)) ^ 2 := by
    refine (sum_filter_of_ne ?_).symm
    intro k hk hne
    rw [mem_Ico] at hk
    by_contra hodd
    exact hne (foldedCoefficient_sq_eq_zero_of_even F hF N hk.1 hk.2
      (Nat.not_odd_iff_even.mp hodd))
  have hfold := sum_foldedCoefficient_sq_eq_fold F hF N hNe
  rw [hfilter] at hfold
  have henergy := sum_foldedCoefficient_sq F hF N
  rw [sum_gridSample_sq_eq_fold F hF N] at henergy
  rw [hfold] at henergy
  linear_combination henergy / 2

/-! ## The inverse transform in cosine form (`p1:eq:inverse-DCT`)

The reconstruction `P(j/N) = ½ ∑_r A_{N,r} χ(rj)` becomes a real cosine sum by
the same `r ↦ -r` pairing that produced the forward cosine form, and then the
half-range fold leaves only the odd residues below `N`. -/

/-- Pairing `r` with `-r` turns the reconstruction sum into a cosine sum. -/
theorem sum_char_mul_foldedCoefficient_eq_sum_cos (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] (j : ZMod (2 * N)) :
    ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * foldedCoefficient F N r
      = ∑ r : ZMod (2 * N),
          foldedCoefficient F N r * Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ) := by
  have hneg : ∑ r : ZMod (2 * N), ZMod.stdAddChar (-(r * j)) * foldedCoefficient F N r
      = ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * foldedCoefficient F N r := by
    refine Fintype.sum_equiv (Equiv.neg (ZMod (2 * N))) _ _ fun r => ?_
    simp only [Equiv.neg_apply]
    rw [foldedCoefficient_neg F hF, neg_mul, neg_neg]
  have h2 : (2 : ℂ) * ∑ r : ZMod (2 * N), ZMod.stdAddChar (r * j) * foldedCoefficient F N r
      = 2 * ∑ r : ZMod (2 * N),
          foldedCoefficient F N r * Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ) := by
    rw [two_mul]
    nth_rewrite 2 [← hneg]
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    have hangle : (Real.pi * j.val * r.val / N : ℝ) = (Real.pi * r.val * j.val / N : ℝ) := by
      ring
    rw [stdAddChar_mul_eq_exp N j r, hangle]
    rw [show -(r * j) = -(r * j) from rfl]
    have hneg' : ZMod.stdAddChar (-(r * j))
        = Complex.exp (-((Real.pi * r.val * j.val / N : ℝ) : ℂ) * Complex.I) := by
      have := stdAddChar_neg_mul_eq_exp N j r
      rwa [hangle] at this
    rw [hneg']
    rw [show (2 : ℂ) * (foldedCoefficient F N r *
        Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ))
      = foldedCoefficient F N r *
        (2 * Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ)) by ring, Complex.two_cos]
    ring
  exact mul_left_cancel₀ two_ne_zero h2

/-- The cosine factor is even in the frequency as well as in the sample index. -/
theorem cos_alias_angle_neg_left (N : ℕ) [NeZero N] (r j : ZMod (2 * N)) :
    Complex.cos ((Real.pi * (-r).val * j.val / N : ℝ) : ℂ)
      = Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ) := by
  have h := cos_alias_angle_neg N j r
  have h1 : (Real.pi * j.val * (-r).val / N : ℝ) = (Real.pi * (-r).val * j.val / N : ℝ) := by
    ring
  have h2 : (Real.pi * j.val * r.val / N : ℝ) = (Real.pi * r.val * j.val / N : ℝ) := by
    ring
  rwa [h1, h2] at h

/-- **`p1:eq:inverse-DCT`.**  For even `N`, every grid sample is reconstructed from
the odd folded classes below `N`:

`P(j/N) = ½ + ∑_{1 ≤ r < N, r odd} A_{N,r} cos(π r j / N)`. -/
theorem gridSample_eq_half_add_sum_odd (F : BoundedFabius) (hF : IsFabius F)
    (N : ℕ) [NeZero N] (hNe : Even N) (j : ZMod (2 * N)) :
    gridSample F N j
      = 1 / 2 + ∑ r ∈ (Ico 1 N).filter (fun r => Odd r),
          foldedCoefficient F N ((r : ℕ) : ZMod (2 * N)) *
            Complex.cos ((Real.pi * r * j.val / N : ℝ) : ℂ) := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [gridSample_eq_sum_foldedCoefficient F N j,
    sum_char_mul_foldedCoefficient_eq_sum_cos F hF N j,
    sum_zmod_even_eq_fold N
      (fun r => foldedCoefficient F N r *
        Complex.cos ((Real.pi * r.val * j.val / N : ℝ) : ℂ))
      (fun r => by rw [foldedCoefficient_neg F hF, cos_alias_angle_neg_left])]
  -- the two end frequencies
  rw [foldedCoefficient_zero F hF N]
  obtain ⟨m, hm⟩ := hNe
  have hNval : (N : ZMod (2 * N)) = ((2 * m : ℕ) : ZMod (2 * N)) := by
    congr 1
    omega
  have hzero : foldedCoefficient F N (N : ZMod (2 * N)) = 0 := by
    rw [hNval]
    exact foldedCoefficient_two_mul_eq_zero F hF N (by omega) (by omega)
  rw [hzero]
  simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, mul_zero, zero_div,
    Complex.ofReal_zero, Complex.cos_zero, mul_one, zero_mul, add_zero]
  -- restrict the half-range sum to the odd frequencies
  have hval : ∀ r ∈ Ico 1 N, ((r : ℕ) : ZMod (2 * N)).val = r := by
    intro r hr
    rw [mem_Ico] at hr
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hfilter : ∑ r ∈ Ico 1 N,
        foldedCoefficient F N ((r : ℕ) : ZMod (2 * N)) *
          Complex.cos ((Real.pi * ((r : ℕ) : ZMod (2 * N)).val * j.val / N : ℝ) : ℂ)
      = ∑ r ∈ (Ico 1 N).filter (fun r => Odd r),
          foldedCoefficient F N ((r : ℕ) : ZMod (2 * N)) *
            Complex.cos ((Real.pi * r * j.val / N : ℝ) : ℂ) := by
    rw [← sum_filter_of_ne (p := fun r => Odd r)]
    · refine sum_congr rfl fun r hr => ?_
      rw [mem_filter] at hr
      rw [hval r hr.1]
    · intro r hr hne
      rw [mem_Ico] at hr
      by_contra hodd
      obtain ⟨s, hs⟩ := Nat.not_odd_iff_even.mp hodd
      apply hne
      have hrs : r = 2 * s := by omega
      rw [hrs, foldedCoefficient_two_mul_eq_zero F hF N (by omega) (by omega), zero_mul]
  rw [hfilter]
  ring

end Fabius

import FabiusFunction.PaperStatements

/-!
# Prose-level results from *Arithmetic of the Fabius function*

This file exposes mathematical assertions used in the prose and in proofs of
Juan Arias de Reyna, *Arithmetic of the Fabius function*,
arXiv:1702.06487v3, which are not themselves numbered theorem environments.
The numbered results remain collected in `FabiusFunction.PaperStatements`.

The results below are grouped into elementary analytic consequences, exact
arithmetic assertions used inside the paper's proofs, the reordered dyadic
formula, and the denominator consequences stated after Conjecture 16.  Several
lemmas deliberately expose stronger boundary cases or weaker hypotheses than
the prose needs.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Interval
open Finset Set

namespace Fabius

noncomputable section

/-! ## Elementary analytic consequences -/

/-- Every moment `c_n` of Rvachev's function is strictly positive.

This is the sharp form of `Fabius.moment_nonneg` below, and the exact analogue
of `Fabius.halfMoment_pos` for the half-moment sequence.  It matters because a
moment routinely appears in a denominator or inside a `padicValRat`, where the
nonnegativity statement is useless and `moment n ≠ 0` is what is needed; that
is available here as `(moment_pos n).ne'`.

Placement note: by symmetry with `halfMoment_pos` the long-term home of this
lemma is `FabiusFunction.Arithmetic`, where `moment` itself is defined, but the
proof is not available there: `Arithmetic` is upstream of both
`FabiusFunction.NormalizedEvenMoments` (which supplies
`moment_eq_momentNumerator_div`) and `FabiusFunction.Parity` (which supplies
`momentNumerator_pos`).  The upstream-most module in which both are in scope is
`FabiusFunction.TwoAdic`; this file is used instead so that the lemma sits next
to the `moment_nonneg` it sharpens. -/
theorem moment_pos (n : ℕ) : 0 < moment n := by
  rw [moment_eq_momentNumerator_div]
  refine div_pos ?_ ?_
  · exact_mod_cast momentNumerator_pos n
  · exact_mod_cast Nat.mul_pos (oddDoubleFactorial_pos (n + 1))
      (evenMersenneProduct_pos n)

/-- The recurrence in Proposition 1 shows that every moment `c_n` is
nonnegative.  Superseded by the sharp `Fabius.moment_pos` above, of which this
is now a direct consequence; it is kept under its own name for the prose of
the paper, which asserts only nonnegativity. -/
theorem moment_nonneg (n : ℕ) : 0 ≤ moment n :=
  (moment_pos n).le

/-- The partition-of-unity identity used after equation (32). -/
theorem rvachev_add_one_sub_eq_one
    (F : BoundedFabius) (hF : IsFabius F) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    rvachevUp F t + rvachevUp F (1 - t) = 1 := by
  have hleft : rvachevUp F t = fabiusReal F (1 - t) := by
    unfold rvachevUp
    split_ifs with h
    · have ht0 : t = 0 := le_antisymm h ht.1
      subst t
      norm_num
    · rfl
  have hright : rvachevUp F (1 - t) = fabiusReal F t := by
    unfold rvachevUp
    split_ifs with h
    · have ht1 : t = 1 := by linarith [ht.2]
      subst t
      norm_num
    · congr 1
      ring
  rw [hleft, hright, hF.symmetry t ht]
  ring

/-- Rvachev's function is strictly positive on the interior of its support.

This is the paper-facing name for `Fabius.rvachevUp_pos_of_mem_Ioo`, which is
the canonical home of the statement in `FabiusFunction.Monotonicity` (reached
here through `FabiusFunction.PaperStatements`).  It is kept as a one-line
forwarder so that references in the prose index continue to resolve. -/
theorem rvachev_pos_of_mem_Ioo
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    0 < rvachevUp F x :=
  rvachevUp_pos_of_mem_Ioo F hF hx

/-- Positivity characterizes the interior `(-1,1)` of the support of
Rvachev's function. -/
theorem rvachev_pos_iff_mem_Ioo
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    0 < rvachevUp F x ↔ x ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · intro hpos
    by_contra hx
    rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF hx] at hpos
    norm_num at hpos
  · exact rvachev_pos_of_mem_Ioo F hF

/-- The zero set of Rvachev's function is the complement of its open support. -/
theorem rvachevUp_eq_zero_iff_not_mem_Ioo
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    rvachevUp F x = 0 ↔ x ∉ Ioo (-1 : ℝ) 1 := by
  constructor
  · intro hx hxmem
    exact (ne_of_gt (rvachev_pos_of_mem_Ioo F hF hxmem)) hx
  · exact rvachevUp_eq_zero_of_not_mem_Ioo F hF

/-- The ordinary (rather than topological) support of Rvachev's function is
exactly `(-1,1)`.

This is the paper-facing name for `Fabius.support_rvachevUp`, which is the
canonical home of the statement in `FabiusFunction.Monotonicity` (reached here
through `FabiusFunction.PaperStatements`).  It is kept as a one-line forwarder
so that references in the prose index continue to resolve. -/
theorem support_rvachev_eq
    (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) = Ioo (-1 : ℝ) 1 :=
  support_rvachevUp F hF

/-- The derivative is positive on the increasing half of the bump, as stated
in Section 2. -/
theorem deriv_rvachev_pos_of_mem_Ioo_neg_zero
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 0) :
    0 < deriv (rvachevUp F) x := by
  rw [(rvachev_hasDerivAt F hF x).deriv]
  have hpos : 0 < rvachevUp F (2 * x + 1) :=
    rvachev_pos_of_mem_Ioo F hF (by constructor <;> linarith [hx.1, hx.2])
  have hzero : rvachevUp F (2 * x - 1) = 0 := by
    have harg : 2 * x - 1 ≤ 0 := by linarith [hx.2]
    rw [rvachevUp, if_pos harg]
    exact hF.zero_of_nonpos _ (by linarith [hx.2])
  rw [hzero]
  linarith

/-- The derivative is negative on the decreasing half of the bump, as stated
in Section 2. -/
theorem deriv_rvachev_neg_of_mem_Ioo_zero_one
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (rvachevUp F) x < 0 := by
  rw [(rvachev_hasDerivAt F hF x).deriv]
  have hpos : 0 < rvachevUp F (2 * x - 1) :=
    rvachev_pos_of_mem_Ioo F hF (by constructor <;> linarith [hx.1, hx.2])
  have hzero : rvachevUp F (2 * x + 1) = 0 := by
    have harg : ¬ 2 * x + 1 ≤ 0 := by linarith [hx.1]
    rw [rvachevUp, if_neg harg]
    exact hF.zero_of_nonpos _ (by linarith [hx.1])
  rw [hzero]
  linarith

/-- The fold defining `rvachevUp` identifies a reciprocal-power-of-two Fabius
value with the reflected Rvachev value.  This structural identity needs only
boundedness, not the Fabius equations.  The statement includes the endpoint
`n = 0`, where the folded argument is zero. -/
theorem rvachev_one_sub_inverse_two_pow_eq_fabiusReal
    (F : BoundedFabius) (n : ℕ) :
    rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) =
      fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  have hinv : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by norm_num)
  rw [rvachevUp_eq_fabiusReal_one_sub F (by linarith)]
  congr 1
  ring

set_option linter.unusedVariables false in
/-- Backwards-compatible `IsFabius`-specialized form of
`rvachev_one_sub_inverse_two_pow_eq_fabiusReal`, used before equation (14).
The hypothesis `hF` is retained solely for source compatibility; the fold
identity itself holds for every bounded candidate. -/
theorem rvachev_one_sub_inverse_two_pow_eq_fabius
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    rvachevUp F (1 - ((2 : ℝ) ^ n)⁻¹) =
      fabiusReal F (((2 : ℝ) ^ n)⁻¹) :=
  rvachev_one_sub_inverse_two_pow_eq_fabiusReal F n

/-- Every derivative of the signed global Fabius function vanishes at zero. -/
theorem iteratedDeriv_extendedFabius_zero
    (F : BoundedFabius) (hF : IsFabius F) (order : ℕ) :
    iteratedDeriv order (extendedFabius F) 0 = 0 := by
  rw [iteratedDeriv_extendedFabius F hF, mul_zero,
    extendedFabius_eq_zero_of_nonpos F hF (by norm_num)]
  ring

/-- Every derivative at `2^scale` vanishes as soon as `order + scale` is
positive.  In particular, this includes positive-order derivatives at the
previously omitted endpoint `2^0 = 1`. -/
theorem iteratedDeriv_extendedFabius_two_pow_eq_zero_of_one_le_add
    (F : BoundedFabius) (hF : IsFabius F)
    (scale order : ℕ) (horderScale : 1 ≤ order + scale) :
    iteratedDeriv order (extendedFabius F) ((2 : ℝ) ^ scale) = 0 := by
  rw [iteratedDeriv_extendedFabius F hF]
  have hzero : extendedFabius F ((2 : ℝ) ^ (order + scale)) = 0 := by
    have hzeroAtOrigin : extendedFabius F 0 = 0 :=
      extendedFabius_eq_zero_of_nonpos F hF (by norm_num)
    have htranslate := extendedFabius_add_pow_two F hF (order + scale)
      horderScale (x := 0) (by norm_num) (by positivity)
    rw [zero_add, hzeroAtOrigin, neg_zero] at htranslate
    exact htranslate
  rw [show (2 : ℝ) ^ order * (2 : ℝ) ^ scale =
      (2 : ℝ) ^ (order + scale) by rw [pow_add], hzero]
  ring

/-- Every positive-order derivative of the global Fabius extension vanishes at
the endpoint `1`. -/
theorem iteratedDeriv_extendedFabius_one_eq_zero
    (F : BoundedFabius) (hF : IsFabius F)
    (order : ℕ) (horder : 1 ≤ order) :
    iteratedDeriv order (extendedFabius F) 1 = 0 := by
  simpa using iteratedDeriv_extendedFabius_two_pow_eq_zero_of_one_le_add
    F hF 0 order (by simpa using horder)

/-- For a positive `scale`, every derivative vanishes at the positive power of
two `2^scale` (hence at an even integer).  This is the flatness assertion used
in the negative-index case of Proposition 10. -/
theorem iteratedDeriv_extendedFabius_two_pow_eq_zero
    (F : BoundedFabius) (hF : IsFabius F)
    (scale order : ℕ) (hscale : 1 ≤ scale) :
    iteratedDeriv order (extendedFabius F) ((2 : ℝ) ^ scale) = 0 :=
  iteratedDeriv_extendedFabius_two_pow_eq_zero_of_one_le_add F hF scale order (by omega)

/-- Exact total evaluation of every derivative on the nonnegative
power-of-two grid.  The only nonzero case is the normalization
`extendedFabius F (2^0) = extendedFabius F 1 = 1`; every positive derivative
at `1` and every derivative at a positive power of two vanishes. -/
theorem iteratedDeriv_extendedFabius_two_pow_eq_ite
    (F : BoundedFabius) (hF : IsFabius F) (scale order : ℕ) :
    iteratedDeriv order (extendedFabius F) ((2 : ℝ) ^ scale) =
      if scale = 0 ∧ order = 0 then 1 else 0 := by
  by_cases hzero : scale = 0 ∧ order = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simpa using extendedFabius_one F hF
  · rw [if_neg hzero]
    exact iteratedDeriv_extendedFabius_two_pow_eq_zero_of_one_le_add
      F hF scale order (by omega)

/-! ## Exact arithmetic assertions used inside proofs -/

/-- The literal all-index form of the oddness half of Theorem 21: every
Reshetnikov number, including `R_0 = 1`, is an odd natural number.  Only this
oddness assertion extends to `n = 0`; the valuation half of Theorem 21 still
requires `1 ≤ n`. -/
theorem theorem_twenty_one_odd_all (n : ℕ) :
    IsOddNatural (reshetnikov n) := by
  cases n with
  | zero =>
      refine ⟨1, odd_one, ?_⟩
      norm_num [reshetnikov, fabiusAtInverseTwoPow, fabiusDyadic,
        thueMorseSign, binaryWeight, evenMersenneProduct]
  | succ n =>
      exact (theorem_twenty_one (n + 1) (by omega)).1

/-- The literal all-natural-number form of Theorem 9.  It follows from the
stronger all-index oddness theorem above. -/
theorem theorem_nine_all (n : ℕ) :
    IsNatural (reshetnikov n) := by
  obtain ⟨m, _hm, hm⟩ := theorem_twenty_one_odd_all n
  exact ⟨m, hm⟩

/-- The odd multiplier `N_n` introduced in the proof of Theorem 20. -/
def reshetnikovMultiplier (n : ℕ) : ℕ :=
  oddDoubleFactorial n * evenMersenneProduct (n / 2)

/-- The multiplier `N_n` is odd. -/
theorem reshetnikovMultiplier_odd (n : ℕ) :
    Odd (reshetnikovMultiplier n) := by
  exact (odd_oddDoubleFactorial n).mul (odd_evenMersenneProduct (n / 2))

/-- The multipliers in the proof of Theorem 20 form a divisibility chain. -/
theorem reshetnikovMultiplier_dvd {k n : ℕ} (hkn : k ≤ n) :
    reshetnikovMultiplier k ∣ reshetnikovMultiplier n := by
  have hodd : oddDoubleFactorial k ∣ oddDoubleFactorial n := by
    refine ⟨oddFactorProduct k n, ?_⟩
    exact (oddDoubleFactorial_mul_interval k n hkn).symm
  have hhalf : k / 2 ≤ n / 2 := Nat.div_le_div_right hkn
  have heven : evenMersenneProduct (k / 2) ∣ evenMersenneProduct (n / 2) := by
    refine ⟨∏ j ∈ Ico (k / 2 + 1) (n / 2 + 1), (2 ^ (2 * j) - 1), ?_⟩
    exact (evenMersenneProduct_mul_interval (k / 2) (n / 2) hhalf).symm
  exact Nat.mul_dvd_mul hodd heven

/-- Corrected form of a proof-internal sentence in Theorem 20: the paper
omits the leading `2`.  For `1 ≤ k ≤ n`, `2 d_k N_n` is natural. -/
theorem two_mul_halfMoment_mul_reshetnikovMultiplier_isNatural
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsNatural (2 * halfMoment k * reshetnikovMultiplier n) := by
  obtain ⟨q, hq⟩ := reshetnikovMultiplier_dvd hkn
  obtain ⟨r, hr⟩ := theorem_nine k hk
  refine ⟨r * q, ?_⟩
  push_cast
  rw [← hr, proposition_six k hk]
  have hqRat := congrArg (fun z : ℕ => (z : ℚ)) hq
  dsimp [reshetnikovMultiplier] at hqRat ⊢
  push_cast at hqRat ⊢
  rw [hqRat]
  ring

/-- In the induction used for Theorem 20, the corrected products
`2 d_k N_n` are in fact odd natural numbers. -/
theorem two_mul_halfMoment_mul_reshetnikovMultiplier_isOddNatural
    {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsOddNatural (2 * halfMoment k * reshetnikovMultiplier n) := by
  apply isOddNatural_of_isNatural_of_odd_num
    (two_mul_halfMoment_mul_reshetnikovMultiplier_isNatural hk hkn)
  have hodd := (theorem_twenty k hk).2
  have hproduct := odd_num_den_mul_nat (reshetnikovMultiplier n) hodd
    (reshetnikovMultiplier_odd n)
  simpa [mul_assoc] using hproduct.1

/-- The two-adic valuation of `R_n` equals that of `2 d_n`, as observed in
the proofs of Theorems 9 and 20. -/
theorem reshetnikov_padicVal_two_eq_two_mul_halfMoment
    (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (reshetnikov n) =
      padicValRat 2 (2 * halfMoment n) := by
  obtain ⟨m, hmOdd, hm⟩ := (theorem_twenty_one n hn).1
  have hmVal : padicValRat 2 (m : ℚ) = 0 := by
    rw [padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hmOdd.not_two_dvd_nat]
    norm_num
  rw [hm, hmVal, (theorem_twenty n hn).1]

/-- The odd-index valuation identity stated before Theorem 20. -/
theorem two_mul_halfMoment_odd_padicVal_eq_momentNumerator (n : ℕ) :
    padicValRat 2 (2 * halfMoment (2 * n + 1)) =
      padicValRat 2 (momentNumerator n : ℚ) := by
  rw [(theorem_twenty (2 * n + 1) (by omega)).1, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd
      (proposition_nineteen n).not_two_dvd_nat]
  norm_num

/-! ## The reordered dyadic formula -/

/-- The unnumbered `q / 2^n` grid formula immediately preceding equation
(32), parameterized by `a = q + 2^n`.  Expanding `fabiusDyadic` gives the
paper's displayed finite double sum verbatim. -/
theorem rvachev_shifted_dyadic_eq_fabiusDyadic
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    rvachevUp F (((a : ℝ) - (2 : ℝ) ^ n) / (2 : ℝ) ^ n) =
      (fabiusDyadic n a : ℝ) := by
  let x : ℝ := (a : ℝ) / (2 : ℝ) ^ n
  have hx2 : x ≤ 2 := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity)]
    rw [pow_succ] at ha
    have ha' : a ≤ 2 * 2 ^ n := by simpa [mul_comm] using ha
    exact_mod_cast ha'
  have hext : extendedFabius F x = rvachevUp F (x - 1) :=
    extendedFabius_eq_rvachevUp_sub_one F hF hx2
  have harg : ((a : ℝ) - (2 : ℝ) ^ n) / (2 : ℝ) ^ n = x - 1 := by
    dsimp only [x]
    field_simp
  calc
    rvachevUp F (((a : ℝ) - (2 : ℝ) ^ n) / (2 : ℝ) ^ n) =
        rvachevUp F (x - 1) := by rw [harg]
    _ = extendedFabius F x := hext.symm
    _ = (fabiusDyadic n a : ℝ) := by
      simpa only [x] using (fabiusDyadic_cast_extended F hF n a ha).symm

/-- The unnumbered displayed formula immediately before equation (32), with
`a = q + 2^n`.  This is the expanded form of
`rvachev_shifted_dyadic_eq_fabiusDyadic`. -/
theorem rvachev_shifted_dyadic_eq_sum
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    rvachevUp F (((a : ℝ) - (2 : ℝ) ^ n) / (2 : ℝ) ^ n) =
      (((2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
        ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
          ∑ k : Fin (n / 2 + 1),
            (Nat.choose n (2 * k.val) : ℚ) *
              ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) *
                moment k.val : ℚ) : ℝ) := by
  rw [rvachev_shifted_dyadic_eq_fabiusDyadic F hF n a ha]
  rfl

/-- Equation (33), the version of equation (32) with the moment sum outside
the Thue--Morse sum. -/
theorem fabiusDyadic_eq_reordered_sum (n a : ℕ) :
    fabiusDyadic n a =
      (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
        ∑ k : Fin (n / 2 + 1),
          (Nat.choose n (2 * k.val) : ℚ) * moment k.val *
            ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
              ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) := by
  unfold fabiusDyadic
  congr 1
  calc
    (∑ h : Fin a, (thueMorseSign h.val : ℚ) *
        ∑ k : Fin (n / 2 + 1),
          (Nat.choose n (2 * k.val) : ℚ) *
            ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) * moment k.val) =
        ∑ h : Fin a, ∑ k : Fin (n / 2 + 1),
          (thueMorseSign h.val : ℚ) *
            ((Nat.choose n (2 * k.val) : ℚ) *
              ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) *
                moment k.val) := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Finset.mul_sum]
    _ = ∑ k : Fin (n / 2 + 1), ∑ h : Fin a,
          (thueMorseSign h.val : ℚ) *
            ((Nat.choose n (2 * k.val) : ℚ) *
              ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) *
                moment k.val) := Finset.sum_comm
    _ = ∑ k : Fin (n / 2 + 1),
          (Nat.choose n (2 * k.val) : ℚ) * moment k.val *
            ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
              ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      ring

/-- Analytic form of equation (33) on its stated first-block range. -/
theorem rvachev_one_sub_dyadic_eq_reordered_sum
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    (rvachevUp F (1 - (a : ℝ) / (2 : ℝ) ^ n) : ℝ) =
      ((2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial *
        ∑ k : Fin (n / 2 + 1),
          (Nat.choose n (2 * k.val) : ℚ) * moment k.val *
            ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
              ((2 : ℚ) * a - 2 * h.val - 1) ^ (n - 2 * k.val) : ℚ) := by
  let x : ℝ := (a : ℝ) / (2 : ℝ) ^ n
  have hx2 : x ≤ 2 := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity)]
    rw [pow_succ] at ha
    have ha' : a ≤ 2 * 2 ^ n := by simpa [mul_comm] using ha
    exact_mod_cast ha'
  have hext : extendedFabius F x = rvachevUp F (x - 1) :=
    extendedFabius_eq_rvachevUp_sub_one F hF hx2
  have heven := rvachev_even F hF (1 - x)
  have hup : rvachevUp F (1 - x) = extendedFabius F x := by
    rw [hext]
    convert heven.symm using 1
    all_goals ring_nf
  rw [hup, ← fabiusDyadic_cast_extended F hF n a ha,
    fabiusDyadic_eq_reordered_sum]

/-! ## Consequences stated after Conjecture 16 -/

/-- The two displayed formulas following Conjecture 16.  They are stated in
`ℚ` because `H_n` is defined rationally; Conjecture 16 additionally says it is
an odd natural number. -/
theorem conjecture_sixteen_denominator_formulas
    (hconj : conjecture_sixteen) (n : ℕ) (hn : 1 ≤ n) :
    (dyadicDenominator (2 * n - 1) : ℚ) =
        (2 : ℚ) ^ (1 + (2 * n - 1).choose 2) *
          (2 * n - 1).factorial * conjecturalH n ∧
    (dyadicDenominator (2 * n) : ℚ) =
        (2 : ℚ) ^ (1 + (2 * n).choose 2) *
          (2 * n + 1).factorial * conjecturalH (n + 1) := by
  have hoddFormula (m : ℕ) (hm : 1 ≤ m) :
      (dyadicDenominator (2 * m - 1) : ℚ) =
        (2 : ℚ) ^ (1 + (2 * m - 1).choose 2) *
          (2 * m - 1).factorial * conjecturalH m := by
    unfold conjecturalH conjecturalK normalizedDyadicDenominator
    have hpow : (2 : ℚ) ^ (2 * m - 1).choose 2 ≠ 0 := by positivity
    have hfac : (((2 * m - 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp [hpow, hfac]
    rw [pow_add]
    norm_num
    ring
  constructor
  · exact hoddFormula n hn
  · have ha := hconj.1 (n := n) hn
    unfold normalizedDyadicDenominator at ha
    have hpowEven : (2 : ℚ) ^ (2 * n).choose 2 ≠ 0 := by positivity
    have hpowOdd : (2 : ℚ) ^ (2 * n + 1).choose 2 ≠ 0 := by positivity
    calc
      (dyadicDenominator (2 * n) : ℚ) =
          (2 : ℚ) ^ (2 * n).choose 2 *
            ((dyadicDenominator (2 * n) : ℚ) /
              (2 : ℚ) ^ (2 * n).choose 2) := by field_simp
      _ = (2 : ℚ) ^ (2 * n).choose 2 *
            ((dyadicDenominator (2 * n + 1) : ℚ) /
              (2 : ℚ) ^ (2 * n + 1).choose 2) := by rw [ha]
      _ = (2 : ℚ) ^ (1 + (2 * n).choose 2) *
            (2 * n + 1).factorial * conjecturalH (n + 1) := by
        unfold conjecturalH conjecturalK normalizedDyadicDenominator
        rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
        have hfac : (((2 * n + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hpowEven, hpowOdd, hfac]
        rw [pow_add]
        norm_num
        ring

end

end Fabius

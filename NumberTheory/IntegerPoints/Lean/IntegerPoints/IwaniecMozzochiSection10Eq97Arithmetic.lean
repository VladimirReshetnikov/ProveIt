import IntegerPoints.IwaniecMozzochiSection10Eq102Reduction
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# The elementary (9.7) error mass in Iwaniec--Mozzochi Section 10

This file proves the arithmetic remainder estimate left explicit by
`IwaniecMozzochiSection10Eq102Reduction`.  The proof follows paper lines
985--990, with a deliberately softer square-root bound for the harmonic
number.  That softer bound is already strong enough for the catalogue target
`x^(1/44)` and has two useful formal advantages: it avoids an asymptotic
logarithm and it treats `c = 1` without a separate global argument.

The main ingredients are kept reusable.

* `section10Eq97RoundResidue a c h` is the exact centered integer selected by
  `round (a*h/c)`.  Its absolute value divided by `c` is precisely
  `nearestIntDist (a*h/c)`, and it lies in the congruence class `-a*h mod c`.
* `section10Eq97Kernel B c` is a finite symmetric harmonic envelope.  Its
  total mass is at most `1 + 2*B*c*harmonic c`.  The value at zero is exactly
  one, so Lean's convention `1 / 0 = 0` never changes the intended capped
  reciprocal.
* the existing congruence-fibre theorem then contributes `5*H/c`.  The
  short-cell condition `mu1*G < c` controls the zero residue, while all
  nonzero residues contribute a harmonic number.
* finally `harmonic c <= 3*sqrt c`, `c <= H`, and the exact definitions of
  `G` and `N` reduce both contributions to
  `sqrt(G/N)*sqrt H = sqrt M*x^(-5/22) <= x^(1/44)`.

No analytic modular-transformation input is used here.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

open IMReductionEq75

noncomputable section

/-! ## A sharpened upper half of (8.2) -/

/-- Before using `G >= 1`, the elementary proof of the upper half of (8.2)
actually gives `beta*N <= 4/G`.  Keeping this factor of `G` is what turns the
nonzero residue classes in (9.7) into the required square-root scale. -/
theorem section10_eq97_beta_mul_shiftLength_le_four_div_Gscale
    {x H M : Real} {a c h : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    betaIM x a c h * shiftLength x M <= 4 / Gscale x H M := by
  have hmain' : InMainRange x H M := hmain
  rcases hmain with
    ⟨hx, hxM, _hMx, hH, _hHupper, _hHlower, _hHlowerTwo, _hMlower⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hMPos : 0 < M := (Real.rpow_pos_of_pos hxPos theta0).trans hxM
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hNPos : 0 < shiftLength x M := section8_shiftLength_pos hmain'
  have hGPos : 0 < Gscale x H M :=
    zero_lt_one.trans_le (iwaniecMozzochi_eq66_holds x H M hmain').1
  rcases fareyPoint_geometry hmain' hfarey with
    ⟨_hm, _hv0, _hv1, hsum, _hcoefficient, hmLower, _hmUpper⟩
  have hhUpper := (mem_intRange_four_mul hHPos hh).2
  have hnum : x * (h : Real) <= x * (4 * H) :=
    mul_le_mul_of_nonneg_left hhUpper hxPos.le
  have hden : M ^ 3 <=
      ((fareyPoint x a c : Real) + fareyFrac x a c) ^ 3 := by
    rw [hsum]
    exact pow_le_pow_left₀ hMPos.le hmLower 3
  have hbetaUpper : betaIM x a c h <= x * (4 * H) / M ^ 3 := by
    rw [betaIM_eq_section8Beta hmain' hfarey]
    unfold section8Beta
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  calc
    betaIM x a c h * shiftLength x M <=
        (x * (4 * H) / M ^ 3) * shiftLength x M :=
      mul_le_mul_of_nonneg_right hbetaUpper hNPos.le
    _ = 4 * (Gscale x H M)⁻¹ := by
      rw [← section8_gscale_inv x H M]
      ring
    _ = 4 / Gscale x H M := by rw [div_eq_mul_inv]

/-! ## The exact centered residue selected by `round` -/

/-- The centered integer residue attached to `a*h/c`.  The sign is selected
so that the value lies in the congruence class used by
`sum_tsum_residueClass_le`. -/
def section10Eq97RoundResidue (a c h : Nat) : Int :=
  round (((a : Real) * h) / c) * c - (a : Int) * h

/-- The centered residue is congruent to `-a*h` modulo `c`.  This statement is
valid for modulus one as well. -/
theorem section10Eq97RoundResidue_modEq (a c h : Nat) :
    section10Eq97RoundResidue a c h ≡ -((a : Int) * (h : Int))
      [ZMOD (c : Int)] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨-round (((a : Real) * h) / c), ?_⟩
  unfold section10Eq97RoundResidue
  ring

/-- The absolute centered residue divided by `c` is exactly the distance of
`a*h/c` to the nearest integer. -/
theorem section10Eq97RoundResidue_abs_div
    {a c h : Nat} (hc : 0 < c) :
    nearestIntDist (((a : Real) * h) / c) =
      |(section10Eq97RoundResidue a c h : Real)| / c := by
  have hcReal : (0 : Real) < c := by exact_mod_cast hc
  have hcNe : (c : Real) ≠ 0 := hcReal.ne'
  have hcast :
      (section10Eq97RoundResidue a c h : Real) =
        (round (((a : Real) * h) / c) : Real) * c - (a : Real) * h := by
    simp only [section10Eq97RoundResidue, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast]
  unfold nearestIntDist
  have hid :
      (a : Real) * h / c - (round (((a : Real) * h) / c) : Real) =
        -(section10Eq97RoundResidue a c h : Real) / c := by
    rw [hcast]
    field_simp [hcNe]
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hcReal]

/-- The centered residue lies in the deliberately slack window `[-c,c]`.
The sharper `|k| <= c/2` follows from `abs_sub_round`; the slack window makes
the finite harmonic kernel especially simple. -/
theorem section10Eq97RoundResidue_abs_le
    {a c h : Nat} (hc : 0 < c) :
    |(section10Eq97RoundResidue a c h : Real)| <= c := by
  have hcReal : (0 : Real) < c := by exact_mod_cast hc
  have hdist :
      nearestIntDist (((a : Real) * h) / c) <= (1 / 2 : Real) := by
    unfold nearestIntDist
    exact abs_sub_round _
  rw [section10Eq97RoundResidue_abs_div hc] at hdist
  have hhalf :
      |(section10Eq97RoundResidue a c h : Real)| <= (1 / 2 : Real) * c :=
    (div_le_iff₀ hcReal).mp hdist
  nlinarith

/-! ## A finite symmetric harmonic kernel -/

/-- A symmetric majorant for the capped reciprocal after `beta*N` has been
bounded by `B`.  The special value at zero is essential: it is the intended
value of `min{1,+infinity}`, whereas Lean's ordinary reciprocal of zero is
zero. -/
def section10Eq97Kernel (B : Real) (c : Nat) (k : Int) : Real :=
  if |(k : Real)| <= c then
    if k = 0 then 1 else B * c / |(k : Real)|
  else 0

theorem section10Eq97Kernel_nonneg
    {B : Real} (hB : 0 <= B) (c : Nat) (k : Int) :
    0 <= section10Eq97Kernel B c k := by
  unfold section10Eq97Kernel
  split_ifs with hwindow hzero
  · norm_num
  · exact div_nonneg (mul_nonneg hB (Nat.cast_nonneg c)) (abs_nonneg _)
  · exact le_rfl

/-- The kernel has finite support in the integer interval `[-c,c]`. -/
theorem summable_section10Eq97Kernel (B : Real) (c : Nat) :
    Summable (section10Eq97Kernel B c) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Icc (-(c : Int)) (c : Int)).subset
  intro k hk
  change section10Eq97Kernel B c k ≠ 0 at hk
  have hwindow : |(k : Real)| <= (c : Real) := by
    by_contra h
    have hnot : ¬ |(k : Real)| <= (c : Real) := h
    exact hk (by simp [section10Eq97Kernel, hnot])
  rw [Set.mem_Icc]
  constructor
  · exact_mod_cast (abs_le.mp hwindow).1
  · exact_mod_cast (abs_le.mp hwindow).2

private theorem section10Eq97_sum_inv_succ_eq_harmonic (c : Nat) :
    (∑ n ∈ Finset.range c, (((n + 1 : Nat) : Real))⁻¹) =
      (harmonic c : Real) := by
  rw [harmonic, Rat.cast_sum]
  simp

/-- Exact mass of the nonnegative symmetric kernel. -/
theorem tsum_section10Eq97Kernel
    {B : Real} (c : Nat) :
    ∑' k : Int, section10Eq97Kernel B c k =
      1 + 2 * B * c * (harmonic c : Real) := by
  let J : Int -> Real := section10Eq97Kernel B c
  have hJ : Summable J := summable_section10Eq97Kernel B c
  have hposSupport :
      ∀ n : Nat, n ∉ Finset.range (c + 1) -> J (n : Int) = 0 := by
    intro n hn
    have hnge : c + 1 <= n := Nat.le_of_not_gt (by
      simpa [Finset.mem_range] using hn)
    have hcn : c < n := by omega
    have hnot : ¬ |((n : Int) : Real)| <= (c : Real) := by
      simp only [Int.cast_natCast,
        abs_of_nonneg (show (0 : Real) <= (n : Real) from Nat.cast_nonneg n)]
      have hcnReal : (c : Real) < (n : Real) := by exact_mod_cast hcn
      exact not_le_of_gt hcnReal
    change section10Eq97Kernel B c (n : Int) = 0
    rw [section10Eq97Kernel, if_neg hnot]
  have hnegSupport :
      ∀ n : Nat, n ∉ Finset.range c -> J (-(n + 1 : Int)) = 0 := by
    intro n hn
    have hcn : c <= n := Nat.le_of_not_gt (by
      simpa [Finset.mem_range] using hn)
    have hnot :
        ¬ |((-(n + 1 : Int) : Int) : Real)| <= (c : Real) := by
      simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
        abs_neg, abs_of_nonneg (by positivity : (0 : Real) <= (n : Real) + 1)]
      have hcnReal : (c : Real) < (n : Real) + 1 := by
        exact_mod_cast (Nat.lt_succ_of_le hcn)
      exact not_le_of_gt hcnReal
    change section10Eq97Kernel B c (-(n + 1 : Int)) = 0
    rw [section10Eq97Kernel, if_neg hnot]
  have hpos :
      (∑' n : Nat, J (n : Int)) =
        1 + B * c * (harmonic c : Real) := by
    rw [tsum_eq_sum (s := Finset.range (c + 1)) hposSupport]
    rw [Finset.sum_range_succ']
    have htail :
        (∑ n ∈ Finset.range c, J ((n + 1 : Nat) : Int)) =
          B * c * (harmonic c : Real) := by
      calc
        (∑ n ∈ Finset.range c, J ((n + 1 : Nat) : Int)) =
            ∑ n ∈ Finset.range c, B * c * (((n + 1 : Nat) : Real))⁻¹ := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnlt : n < c := Finset.mem_range.mp hn
          have hn1 : (n + 1 : Nat) <= c := Nat.succ_le_iff.mpr hnlt
          have hwindow :
              |((((n + 1 : Nat) : Int) : Real))| <= (c : Real) := by
            simp only [Int.cast_natCast,
              abs_of_nonneg
                (show (0 : Real) <= ((n + 1 : Nat) : Real) from Nat.cast_nonneg _)]
            exact_mod_cast hn1
          change section10Eq97Kernel B c ((n + 1 : Nat) : Int) = _
          rw [section10Eq97Kernel, if_pos hwindow]
          have hn1ne : ((n + 1 : Nat) : Int) ≠ 0 := by omega
          rw [if_neg hn1ne, Int.cast_natCast,
            abs_of_nonneg
              (show (0 : Real) <= ((n + 1 : Nat) : Real) from Nat.cast_nonneg _),
            div_eq_mul_inv]
        _ = B * c *
            (∑ n ∈ Finset.range c, (((n + 1 : Nat) : Real))⁻¹) := by
          rw [Finset.mul_sum]
        _ = B * c * (harmonic c : Real) := by
          rw [section10Eq97_sum_inv_succ_eq_harmonic]
    rw [htail]
    simp [J, section10Eq97Kernel]
    ring
  have hneg :
      (∑' n : Nat, J (-(n + 1 : Int))) =
        B * c * (harmonic c : Real) := by
    rw [tsum_eq_sum (s := Finset.range c) hnegSupport]
    calc
      (∑ n ∈ Finset.range c, J (-(n + 1 : Int))) =
          ∑ n ∈ Finset.range c, B * c * (((n + 1 : Nat) : Real))⁻¹ := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnlt : n < c := Finset.mem_range.mp hn
        have hn1 : (n + 1 : Nat) <= c := Nat.succ_le_iff.mpr hnlt
        have hwindow :
            |((-(n + 1 : Int) : Int) : Real)| <= (c : Real) := by
          simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
            abs_neg, abs_of_nonneg (by positivity : (0 : Real) <= (n : Real) + 1)]
          exact_mod_cast hn1
        change section10Eq97Kernel B c (-(n + 1 : Int)) = _
        rw [section10Eq97Kernel, if_pos hwindow]
        have hn1ne : (-(n + 1 : Int)) ≠ 0 := by omega
        rw [if_neg hn1ne, Int.cast_neg, Int.cast_add, Int.cast_natCast,
          Int.cast_one, abs_neg,
          abs_of_nonneg
            (show (0 : Real) <= (n : Real) + 1 by positivity),
          div_eq_mul_inv]
        norm_num
      _ = B * c *
          (∑ n ∈ Finset.range c, (((n + 1 : Nat) : Real))⁻¹) := by
        rw [Finset.mul_sum]
      _ = B * c * (harmonic c : Real) := by
        rw [section10Eq97_sum_inv_succ_eq_harmonic]
  rw [tsum_of_nat_of_neg_add_one
    (hJ.comp_injective Nat.cast_injective)
    (hJ.comp_injective (@Int.negSucc.inj)), hpos, hneg]
  ring

/-- A square-root majorant for the harmonic number.  It is intentionally
looser than `1 + log c`, but exactly matches the slack available in (9.7). -/
theorem harmonic_le_three_mul_sqrt
    {c : Nat} (hc : 1 <= c) :
    (harmonic c : Real) <= 3 * Real.sqrt c := by
  have hcReal : (1 : Real) <= c := by exact_mod_cast hc
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg c)
    (show (0 : Real) < 1 / 2 by norm_num)
  have hsqrt : (c : Real) ^ ((1 : Real) / 2) = Real.sqrt c := by
    rw [Real.sqrt_eq_rpow]
  have hlogSqrt : Real.log c <= 2 * Real.sqrt c := by
    rw [hsqrt] at hlog
    nlinarith
  have hsqrtOne : 1 <= Real.sqrt c := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hcReal
  calc
    (harmonic c : Real) <= 1 + Real.log c := harmonic_le_one_add_log c
    _ <= 1 + 2 * Real.sqrt c := by
      simpa [add_comm] using add_le_add_left hlogSqrt 1
    _ <= 3 * Real.sqrt c := by nlinarith

/-! ## Pointwise domination of the capped reciprocal -/

/-- The exact round residue is bounded by the harmonic kernel whenever
`beta*N <= B`.  The zero-residue branch is proved separately, so no reciprocal
of zero is used. -/
theorem section10_eq97_minInv_le_kernel
    {a c h : Nat} {beta N B : Real}
    (hc : 0 < c) (hbeta : 0 < beta) (hN : 0 < N)
    (hbetaN : beta * N <= B) :
    minInv 1
        (nearestIntDist (((a : Real) * h) / c) / (beta * N)) <=
      section10Eq97Kernel B c (section10Eq97RoundResidue a c h) := by
  let k := section10Eq97RoundResidue a c h
  have hbetaNPos : 0 < beta * N := mul_pos hbeta hN
  have hB : 0 < B := hbetaNPos.trans_le hbetaN
  have hkWindow : |(k : Real)| <= (c : Real) :=
    section10Eq97RoundResidue_abs_le hc
  rw [section10Eq97RoundResidue_abs_div hc]
  by_cases hk : k = 0
  · have hk' : section10Eq97RoundResidue a c h = 0 := by
      simpa [k] using hk
    simp [hk', section10Eq97Kernel, minInv]
  · have hk' : section10Eq97RoundResidue a c h ≠ 0 := by
      simpa [k] using hk
    have hkAbs : 0 < |(k : Real)| := abs_pos.mpr (by exact_mod_cast hk)
    have hcReal : (0 : Real) < c := by exact_mod_cast hc
    have hdist : 0 < |(k : Real)| / (c : Real) := div_pos hkAbs hcReal
    have hquot : 0 < (|(k : Real)| / (c : Real)) / (beta * N) :=
      div_pos hdist hbetaNPos
    rw [section10Eq97Kernel, if_pos hkWindow, if_neg hk']
    calc
      minInv 1 ((|(k : Real)| / (c : Real)) / (beta * N)) <=
          1 / ((|(k : Real)| / (c : Real)) / (beta * N)) :=
        minInv_le_inv hquot
      _ = (beta * N) * c / |(k : Real)| := by
        field_simp [hkAbs.ne', hcReal.ne', hbetaNPos.ne']
      _ <= B * c / |(k : Real)| := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbetaN (Nat.cast_nonneg c)) hkAbs.le

/-- A single capped reciprocal is bounded by the full congruence-class sum of
the harmonic kernel. -/
theorem section10_eq97_minInv_le_residue_tsum
    {a c h : Nat} {beta N B : Real}
    (hc : 0 < c) (hbeta : 0 < beta) (hN : 0 < N)
    (hbetaN : beta * N <= B) :
    minInv 1
        (nearestIntDist (((a : Real) * h) / c) / (beta * N)) <=
      ∑' k : Int,
        if k ≡ -((a : Int) * (h : Int)) [ZMOD (c : Int)] then
          section10Eq97Kernel B c k else 0 := by
  let J : Int -> Real := fun k =>
    if k ≡ -((a : Int) * (h : Int)) [ZMOD (c : Int)] then
      section10Eq97Kernel B c k else 0
  have hkernel : Summable (section10Eq97Kernel B c) :=
    summable_section10Eq97Kernel B c
  have hB : 0 <= B := (mul_pos hbeta hN).le.trans hbetaN
  have hJ : Summable J := by
    apply hkernel.of_nonneg_of_le
    · intro k
      simp only [J]
      split_ifs
      · exact section10Eq97Kernel_nonneg hB c k
      · exact le_rfl
    · intro k
      simp only [J]
      split_ifs
      · exact le_rfl
      · exact section10Eq97Kernel_nonneg hB c k
  let k0 := section10Eq97RoundResidue a c h
  have hk0 :
      k0 ≡ -((a : Int) * (h : Int)) [ZMOD (c : Int)] :=
    section10Eq97RoundResidue_modEq a c h
  calc
    minInv 1
        (nearestIntDist (((a : Real) * h) / c) / (beta * N)) <=
        section10Eq97Kernel B c k0 :=
      section10_eq97_minInv_le_kernel hc hbeta hN hbetaN
    _ = J k0 := by simp [J, hk0]
    _ <= ∑' k : Int, J k :=
      hJ.le_tsum k0 (fun k _hk => by
        simp only [J]
        split_ifs
        · exact section10Eq97Kernel_nonneg hB c k
        · exact le_rfl)

/-! ## Congruence averaging of the finite Fourier shell -/

/-- The complete capped-reciprocal mass on `(H,4H]` has the expected
`H/c` congruence-fibre gain. -/
theorem section10_eq97_minInv_sum_le
    {x H M : Real} {a c : Nat}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    ∑ h ∈ intRange H (4 * H),
        minInv 1
          (nearestIntDist (((a : Real) * h) / c) /
            (betaIM x a c h * shiftLength x M)) <=
      5 * H / c *
        (1 + 8 * (c : Real) / Gscale x H M *
          (harmonic c : Real)) := by
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hc : 0 < c := zero_lt_one.trans_le hfarey.1
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hG : 0 < Gscale x H M :=
    zero_lt_one.trans_le (iwaniecMozzochi_eq66_holds x H M hmain).1
  let B : Real := 4 / Gscale x H M
  have hB : 0 <= B := by dsimp [B]; positivity
  have hpoint (h : Nat) (hh : h ∈ intRange H (4 * H)) :
      minInv 1
          (nearestIntDist (((a : Real) * h) / c) /
            (betaIM x a c h * shiftLength x M)) <=
        ∑' k : Int,
          if k ≡ -((a : Int) * (h : Int)) [ZMOD (c : Int)] then
            section10Eq97Kernel B c k else 0 := by
    exact section10_eq97_minInv_le_residue_tsum hc
      (betaIM_pos_of_mem_intRange hmain hfarey hh) hN
      (section10_eq97_beta_mul_shiftLength_le_four_div_Gscale
        hmain hfarey hh)
  calc
    ∑ h ∈ intRange H (4 * H),
        minInv 1
          (nearestIntDist (((a : Real) * h) / c) /
            (betaIM x a c h * shiftLength x M)) <=
        ∑ h ∈ intRange H (4 * H),
          ∑' k : Int,
            if k ≡ -((a : Int) * (h : Int)) [ZMOD (c : Int)] then
              section10Eq97Kernel B c k else 0 :=
      Finset.sum_le_sum hpoint
    _ <= 5 * H / c *
        ∑' k : Int, section10Eq97Kernel B c k :=
      sum_tsum_residueClass_le hH hfarey.1 hfarey.2.1 hfarey.2.2.1
        (section10Eq97Kernel_nonneg hB c)
        (summable_section10Eq97Kernel B c)
    _ = 5 * H / c *
        (1 + 8 * (c : Real) / Gscale x H M *
          (harmonic c : Real)) := by
      rw [tsum_section10Eq97Kernel (B := B)]
      dsimp [B]
      ring

/-! ## Scale absorption -/

private theorem section10_eq97_sqrt_rpow
    {x r : Real} (hx : 0 <= x) :
    Real.sqrt (x ^ r) = x ^ (r / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    (x ^ r) ^ ((1 : Real) / 2) = x ^ (r * ((1 : Real) / 2)) :=
      (Real.rpow_mul hx r ((1 : Real) / 2)).symm
    _ = x ^ (r / 2) := by
      congr 1
      ring

/-- Exact normalization of the elementary scale left after congruence
averaging.  Choosing `16` rather than the sharp `8` makes the three-halves
power have the rational constant `64`. -/
theorem section10_eq97_scale_identity
    {x H M : Real} (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) :
    (x * H / (16 * M ^ 3)) ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real)) /
          Gscale x H M * Real.sqrt H =
      64 * Real.sqrt M * x ^ (-(5 : Real) / 22) := by
  have hbeta0 : 0 < x * H / (16 * M ^ 3) := by positivity
  have hN : 0 < shiftLength x M := by
    rw [shiftLength_eq_mul_rpow]
    positivity
  have hG : 0 < Gscale x H M := by
    unfold Gscale
    positivity
  have hbetaPow :
      0 < (x * H / (16 * M ^ 3)) ^ (-(3 : Real) / 2) :=
    Real.rpow_pos_of_pos hbeta0 _
  have hNPow : 0 < shiftLength x M ^ (-(2 : Real)) :=
    Real.rpow_pos_of_pos hN _
  have hsqrtH : 0 < Real.sqrt H := Real.sqrt_pos.2 hH
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hxPow : 0 < x ^ (-(5 : Real) / 22) :=
    Real.rpow_pos_of_pos hx _
  have hlogBeta0 :
      Real.log (x * H / (16 * M ^ 3)) =
        Real.log x + Real.log H - Real.log 16 - 3 * Real.log M := by
    rw [Real.log_div (mul_ne_zero hx.ne' hH.ne')
        (mul_ne_zero (by norm_num) (pow_ne_zero 3 hM.ne')),
      Real.log_mul hx.ne' hH.ne',
      Real.log_mul (by norm_num : (16 : Real) ≠ 0) (pow_ne_zero 3 hM.ne'),
      Real.log_pow]
    ring
  have hshiftPow : 0 < x ^ (-(3 : Real) / 11) :=
    Real.rpow_pos_of_pos hx _
  have hlogN :
      Real.log (shiftLength x M) =
        Real.log M - (3 : Real) / 11 * Real.log x := by
    rw [shiftLength_eq_mul_rpow,
      Real.log_mul hM.ne' hshiftPow.ne', Real.log_rpow hx]
    ring
  have hlogG :
      Real.log (Gscale x H M) =
        3 * Real.log M -
          (Real.log x + Real.log (shiftLength x M) + Real.log H) := by
    unfold Gscale
    rw [Real.log_div (pow_ne_zero 3 hM.ne')
        (mul_ne_zero (mul_ne_zero hx.ne' hN.ne') hH.ne'),
      Real.log_pow,
      Real.log_mul (mul_ne_zero hx.ne' hN.ne') hH.ne',
      Real.log_mul hx.ne' hN.ne']
    ring
  have hlog16 : Real.log (16 : Real) = 4 * Real.log 2 := by
    calc
      Real.log (16 : Real) = Real.log ((2 : Real) ^ 4) := by norm_num
      _ = 4 * Real.log 2 := Real.log_pow 2 4
  have hlog64 : Real.log (64 : Real) = 6 * Real.log 2 := by
    calc
      Real.log (64 : Real) = Real.log ((2 : Real) ^ 6) := by norm_num
      _ = 6 * Real.log 2 := Real.log_pow 2 6
  have hlogLeft :
      Real.log
          ((x * H / (16 * M ^ 3)) ^ (-(3 : Real) / 2) *
            shiftLength x M ^ (-(2 : Real)) /
            Gscale x H M * Real.sqrt H) =
        (-(3 : Real) / 2) * Real.log (x * H / (16 * M ^ 3)) +
          (-(2 : Real)) * Real.log (shiftLength x M) -
          Real.log (Gscale x H M) + Real.log H / 2 := by
    rw [Real.log_mul
        (div_ne_zero (mul_ne_zero hbetaPow.ne' hNPow.ne') hG.ne') hsqrtH.ne',
      Real.log_div (mul_ne_zero hbetaPow.ne' hNPow.ne') hG.ne',
      Real.log_mul hbetaPow.ne' hNPow.ne',
      Real.log_rpow hbeta0, Real.log_rpow hN,
      Real.log_sqrt hH.le]
  have hlogRight :
      Real.log (64 * Real.sqrt M * x ^ (-(5 : Real) / 22)) =
        Real.log 64 + Real.log M / 2 +
          (-(5 : Real) / 22) * Real.log x := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) hsqrtM.ne') hxPow.ne',
      Real.log_mul (by norm_num : (64 : Real) ≠ 0) hsqrtM.ne',
      Real.log_sqrt hM.le, Real.log_rpow hx]
  apply Real.log_injOn_pos
    (Set.mem_Ioi.2 (mul_pos (div_pos (mul_pos hbetaPow hNPow) hG) hsqrtH))
    (Set.mem_Ioi.2 (mul_pos (mul_pos (by norm_num) hsqrtM) hxPow))
  rw [hlogLeft, hlogRight, hlogBeta0, hlogG, hlogN, hlog16, hlog64]
  ring

/-- The normalized scale is at most `64*x^(1/44)` on the main range. -/
theorem section10_eq97_scale_le
    {x H M : Real} (hmain : InMainRange x H M) :
    (x * H / (16 * M ^ 3)) ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real)) /
          Gscale x H M * Real.sqrt H <=
      64 * x ^ ((1 : Real) / 44) := by
  rcases hmain with
    ⟨hx, hxM, hMsqrt, hH, hHupper, hHlower, hHlowerTwo, hMlower⟩
  have hmain' : InMainRange x H M :=
    ⟨hx, hxM, hMsqrt, hH, hHupper, hHlower, hHlowerTwo, hMlower⟩
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hMPos : 0 < M := (Real.rpow_pos_of_pos hxPos theta0).trans hxM
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  rw [section10_eq97_scale_identity hxPos hHPos hMPos]
  have hsqrtM : Real.sqrt M <= x ^ ((1 : Real) / 4) := by
    calc
      Real.sqrt M <= Real.sqrt (Real.sqrt x) := by
        apply Real.sqrt_le_sqrt
        rw [Real.sqrt_eq_rpow]
        exact hMsqrt.le
      _ = Real.sqrt (x ^ ((1 : Real) / 2)) := by
        congr 1
        exact Real.sqrt_eq_rpow x
      _ = x ^ ((1 : Real) / 4) := by
        rw [section10_eq97_sqrt_rpow hxPos.le]
        congr 1
        ring
  have hxneg : 0 <= x ^ (-(5 : Real) / 22) := Real.rpow_nonneg hxPos.le _
  calc
    64 * Real.sqrt M * x ^ (-(5 : Real) / 22) <=
        64 * x ^ ((1 : Real) / 4) * x ^ (-(5 : Real) / 22) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrtM (by norm_num)) hxneg
    _ = 64 * x ^ ((1 : Real) / 44) := by
      rw [mul_assoc, ← Real.rpow_add hxPos]
      congr 1
      norm_num

/-! ## Completion of the arithmetic (9.7) estimate -/

/-- An explicit uniform bound for the complete weighted (9.7) error mass.
The constant depends only on `mu1`, as permitted by the public quantifier
order. -/
theorem section10ThetaErrorMass_le_explicit
    {chi : Real -> Real} {mu1 x H M : Real} {a c : Nat}
    (hchi : IsDyadicPartition chi) (hmu1 : 0 < mu1)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hshort : mu1 * Gscale x H M < c) :
    section10ThetaErrorMass chi x H M a c <=
      (8000 * (1 + mu1⁻¹)) * x ^ ((1 : Real) / 44) := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hN : 0 < shiftLength x M := section8_shiftLength_pos hmain
  have hG : 0 < Gscale x H M :=
    zero_lt_one.trans_le (iwaniecMozzochi_eq66_holds x H M hmain).1
  have hcNat : 0 < c := zero_lt_one.trans_le hfarey.1
  have hc : (0 : Real) < c := by exact_mod_cast hcNat
  have hcH : (c : Real) <= H := hfarey.2.1
  let beta0 : Real := x * H / (16 * M ^ 3)
  have hbeta0 : 0 < beta0 := by dsimp [beta0]; positivity
  have hbetaLower (h : Nat) (hh : h ∈ intRange H (4 * H)) :
      beta0 <= betaIM x a c h := by
    dsimp [beta0]
    calc
      x * H / (16 * M ^ 3) <= x * H / (8 * M ^ 3) := by
        apply div_le_div_of_nonneg_left (mul_nonneg hx.le hH.le)
          (by positivity)
        nlinarith [pow_pos hM 3]
      _ <= betaIM x a c h :=
        x_mul_H_div_eight_mul_M_cube_le_betaIM hmain hfarey hh
  have hbetaRpow (h : Nat) (hh : h ∈ intRange H (4 * H)) :
      betaIM x a c h ^ (-(3 : Real) / 2) <=
        beta0 ^ (-(3 : Real) / 2) :=
    Real.rpow_le_rpow_of_nonpos hbeta0 (hbetaLower h hh) (by norm_num)
  have hcoeff (h : Nat) (hh : h ∈ intRange H (4 * H)) :
      ‖((chi (h / H) / (Real.pi * h) : Real) : Complex)‖ <= 1 / H := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc
      |chi (h / H) / (Real.pi * h)| <= 1 / (Real.pi * H) :=
        psiH_coefficient_abs_le hchi hH hh
      _ <= 1 / H := by
        apply one_div_le_one_div_of_le hH
        simpa using mul_le_mul_of_nonneg_right
          ((show (1 : Real) <= 2 by norm_num).trans Real.two_le_pi) hH.le
  let W : Nat -> Real := fun h =>
    minInv 1
      (nearestIntDist (((a : Real) * h) / c) /
        (betaIM x a c h * shiftLength x M))
  have hWnonneg (h : Nat) : 0 <= W h := by
    unfold W
    apply minInv_nonneg (by norm_num)
    have hbetaNonneg : 0 <= betaIM x a c h := by
      unfold betaIM
      positivity
    exact div_nonneg (by unfold nearestIntDist; positivity)
      (mul_nonneg hbetaNonneg hN.le)
  have hsumW :
      ∑ h ∈ intRange H (4 * H), W h <=
        5 * H / c *
          (1 + 8 * (c : Real) / Gscale x H M *
            (harmonic c : Real)) := by
    simpa [W] using section10_eq97_minInv_sum_le hmain hfarey
  have hcommonNonneg :
      0 <= (1 / H) * beta0 ^ (-(3 : Real) / 2) *
        shiftLength x M ^ (-(2 : Real)) := by positivity
  have hmass :
      section10ThetaErrorMass chi x H M a c <=
        ((1 / H) * beta0 ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real))) *
          (5 * H / c *
            (1 + 8 * (c : Real) / Gscale x H M *
              (harmonic c : Real))) := by
    unfold section10ThetaErrorMass section10ThetaRemainder
    calc
      ∑ h ∈ intRange H (4 * H),
          ‖((chi (h / H) / (Real.pi * h) : Real) : Complex)‖ *
            (betaIM x a c h ^ (-(3 : Real) / 2) *
              shiftLength x M ^ (-(2 : Real)) * W h) <=
          ∑ h ∈ intRange H (4 * H),
            ((1 / H) * beta0 ^ (-(3 : Real) / 2) *
              shiftLength x M ^ (-(2 : Real))) * W h := by
        apply Finset.sum_le_sum
        intro h hh
        have hNpow : 0 <= shiftLength x M ^ (-(2 : Real)) :=
          Real.rpow_nonneg hN.le _
        have hbetapow : 0 <= betaIM x a c h ^ (-(3 : Real) / 2) :=
          Real.rpow_nonneg (betaIM_pos_of_mem_intRange hmain hfarey hh).le _
        calc
          ‖((chi (h / H) / (Real.pi * h) : Real) : Complex)‖ *
              (betaIM x a c h ^ (-(3 : Real) / 2) *
                shiftLength x M ^ (-(2 : Real)) * W h) <=
              (1 / H) *
                (betaIM x a c h ^ (-(3 : Real) / 2) *
                  shiftLength x M ^ (-(2 : Real)) * W h) :=
            mul_le_mul_of_nonneg_right (hcoeff h hh)
              (mul_nonneg (mul_nonneg hbetapow hNpow) (hWnonneg h))
          _ <= (1 / H) *
                (beta0 ^ (-(3 : Real) / 2) *
                  shiftLength x M ^ (-(2 : Real)) * W h) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hbetaRpow h hh) hNpow)
              (hWnonneg h)
          _ = ((1 / H) * beta0 ^ (-(3 : Real) / 2) *
                shiftLength x M ^ (-(2 : Real))) * W h := by ring
      _ = ((1 / H) * beta0 ^ (-(3 : Real) / 2) *
            shiftLength x M ^ (-(2 : Real))) *
          ∑ h ∈ intRange H (4 * H), W h := by rw [Finset.mul_sum]
      _ <= ((1 / H) * beta0 ^ (-(3 : Real) / 2) *
            shiftLength x M ^ (-(2 : Real))) *
          (5 * H / c *
            (1 + 8 * (c : Real) / Gscale x H M *
              (harmonic c : Real))) :=
        mul_le_mul_of_nonneg_left hsumW hcommonNonneg
  have hharm : (harmonic c : Real) <= 3 * Real.sqrt c :=
    harmonic_le_three_mul_sqrt hfarey.1
  have hsqrtC : Real.sqrt c <= Real.sqrt H := Real.sqrt_le_sqrt hcH
  have hsqrtHOne : 1 <= Real.sqrt H := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hmain.2.2.2.1
  have hGc : Gscale x H M / c <= 1 / mu1 := by
    apply le_of_lt
    apply (div_lt_iff₀ hc).2
    have hdiv : Gscale x H M < (c : Real) / mu1 := by
      apply (lt_div_iff₀ hmu1).2
      simpa [mul_comm] using hshort
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hbracket :
      Gscale x H M / c + 8 * (harmonic c : Real) <=
        (1 / mu1 + 24) * Real.sqrt H := by
    calc
      Gscale x H M / c + 8 * (harmonic c : Real) <=
          1 / mu1 + 8 * (3 * Real.sqrt c) :=
        add_le_add hGc (mul_le_mul_of_nonneg_left hharm (by norm_num))
      _ = 1 / mu1 + 24 * Real.sqrt c := by ring
      _ <= 1 / mu1 + 24 * Real.sqrt H := by
        nlinarith [hsqrtC]
      _ <= (1 / mu1 + 24) * Real.sqrt H := by
        have hmuInv : 0 <= 1 / mu1 := by positivity
        have hprod :
            0 <= (1 / mu1) * (Real.sqrt H - 1) :=
          mul_nonneg hmuInv (sub_nonneg.mpr hsqrtHOne)
        nlinarith
  have hrearrange :
      ((1 / H) * beta0 ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real))) *
        (5 * H / c *
          (1 + 8 * (c : Real) / Gscale x H M *
            (harmonic c : Real))) =
      5 * (beta0 ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real)) / Gscale x H M) *
          (Gscale x H M / c + 8 * (harmonic c : Real)) := by
    field_simp [hH.ne', hc.ne', hG.ne']
  rw [hrearrange] at hmass
  have hbaseScale :
      beta0 ^ (-(3 : Real) / 2) *
            shiftLength x M ^ (-(2 : Real)) /
            Gscale x H M * Real.sqrt H <=
        64 * x ^ ((1 : Real) / 44) := by
    simpa [beta0] using section10_eq97_scale_le hmain
  have hscaleNonneg :
      0 <= 5 * (beta0 ^ (-(3 : Real) / 2) *
        shiftLength x M ^ (-(2 : Real)) / Gscale x H M) := by positivity
  calc
    section10ThetaErrorMass chi x H M a c <=
        5 * (beta0 ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real)) / Gscale x H M) *
          (Gscale x H M / c + 8 * (harmonic c : Real)) := hmass
    _ <= 5 * (beta0 ^ (-(3 : Real) / 2) *
          shiftLength x M ^ (-(2 : Real)) / Gscale x H M) *
          ((1 / mu1 + 24) * Real.sqrt H) :=
      mul_le_mul_of_nonneg_left hbracket hscaleNonneg
    _ = 5 * (1 / mu1 + 24) *
          ((beta0 ^ (-(3 : Real) / 2) *
            shiftLength x M ^ (-(2 : Real)) / Gscale x H M) *
            Real.sqrt H) := by ring
    _ <= 5 * (1 / mu1 + 24) *
          (64 * x ^ ((1 : Real) / 44)) := by
      have hcoef : 0 <= 5 * (1 / mu1 + 24) := by positivity
      exact mul_le_mul_of_nonneg_left hbaseScale hcoef
    _ <= (8000 * (1 + mu1⁻¹)) * x ^ ((1 : Real) / 44) := by
      have hmuInv : 0 <= mu1⁻¹ := inv_nonneg.mpr hmu1.le
      have hxpow : 0 <= x ^ ((1 : Real) / 44) := Real.rpow_nonneg hx.le _
      calc
        5 * (1 / mu1 + 24) * (64 * x ^ ((1 : Real) / 44)) =
            (320 * (mu1⁻¹ + 24)) * x ^ ((1 : Real) / 44) := by
          rw [one_div]
          ring
        _ <= (8000 * (1 + mu1⁻¹)) * x ^ ((1 : Real) / 44) := by
          apply mul_le_mul_of_nonneg_right _ hxpow
          nlinarith

/-- The elementary residue-class/harmonic-sum estimate required by the
Section 10 reduction is unconditional. -/
theorem iwaniecMozzochi_section10_eq97ArithmeticBound_holds :
    iwaniecMozzochi_section10_eq97ArithmeticBound := by
  intro chi mu1 hchi hmu1
  refine ⟨8000 * (1 + mu1⁻¹), by positivity, ?_⟩
  intro x H M a c hmain hfarey hshort
  exact section10ThetaErrorMass_le_explicit hchi hmu1 hmain hfarey hshort

end

end LeanProofs.IntegerPoints

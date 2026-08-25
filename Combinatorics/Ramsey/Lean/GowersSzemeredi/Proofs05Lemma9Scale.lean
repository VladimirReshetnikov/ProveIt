import GowersSzemeredi.Proofs05Lemma9Induction

/-!
# The quantitative scale schedule for Lemma 5.9

This module discharges the analytic-arithmetic part left separate from the
combinatorial refinement engine.  Two estimates are kept independent:

* the exact recursive threshold
  `R 0 = T`, `R (n + 1) = (R n + 2) ^ K` guarantees that the shorter
  `floor(t^(1/K)) - 1` branch remains above the next applicability threshold;
* after `n` shorter branches, the current length is at least
  `r^(1 / K^n) / 4`.  The repaired simultaneous threshold makes every ideal
  root in this invariant at least `16`.  Consequently the loss of a floor and
  a subtraction by one costs at most another factor two.

The second invariant is deliberately weaker than the sharp product of the
rounding losses.  Its fixed denominator is what makes the final target and
all intermediate diameter estimates follow from the same calculation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Uniform lower bounds for the two Section 5 constants -/

theorem section5PolynomialPartitionThreshold_ge_sixteen
    {k : Nat} (hk : 1 <= k) :
    16 <= polynomialPartitionThreshold k := by
  have hkpow : 1 <= k ^ 3 := one_le_pow₀ hk
  have hexponent : 1 <= 40 * k ^ 3 := by omega
  have hinner : 2 <= 2 ^ (40 * k ^ 3) := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : 1 <= (2 : Nat)) hexponent
  have hweyl : 4 <= 2 ^ (2 ^ (40 * k ^ 3)) := by
    calc
      4 = 2 ^ (2 : Nat) := by norm_num
      _ <= 2 ^ (2 ^ (40 * k ^ 3)) :=
        pow_le_pow_right₀ (by norm_num : 1 <= (2 : Nat)) hinner
  unfold polynomialPartitionThreshold weylThreshold
  rw [pow_two]
  nlinarith

theorem section5PolynomialPartitionConstant_ge_sixteen
    {k : Nat} (hk : 1 <= k) :
    16 <= polynomialPartitionConstant k := by
  have hfactorial : 1 <= Nat.factorial k := Nat.factorial_pos k
  have hexponent : 4 <= (k + 1) ^ 2 := by nlinarith
  have hpower : 16 <= 2 ^ ((k + 1) ^ 2) := by
    calc
      16 = 2 ^ (4 : Nat) := by norm_num
      _ <= 2 ^ ((k + 1) ^ 2) :=
        pow_le_pow_right₀ (by norm_num : 1 <= (2 : Nat)) hexponent
  unfold polynomialPartitionConstant
  calc
    16 = 1 ^ 2 * 16 := by norm_num
    _ <= (Nat.factorial k) ^ 2 * 2 ^ ((k + 1) ^ 2) :=
      Nat.mul_le_mul (pow_le_pow_left₀ (by omega) hfactorial 2) hpower

/-! ## Real roots and the one-step rounding loss -/

private theorem section5IteratedRoot_succ (x : Real) (hx : 0 <= x)
    (K n : Nat) (hK : 0 < K) :
    (x ^ (K : Real)⁻¹) ^ ((K ^ n : Nat) : Real)⁻¹ =
      x ^ ((K ^ (n + 1) : Nat) : Real)⁻¹ := by
  rw [← Real.rpow_mul hx]
  congr 1
  push_cast [pow_succ]
  field_simp

private theorem section5Root_targetExponent (x : Real) (hx : 0 <= x)
    (K n : Nat) (hK : 0 < K) :
    (x ^ (K : Real)⁻¹) ^
        (2 * (K : Real) ^ n)⁻¹ =
      x ^ (2 * (K : Real) ^ (n + 1))⁻¹ := by
  rw [← Real.rpow_mul hx]
  congr 1
  push_cast [pow_succ]
  field_simp

private theorem section5Root_globalExponent (x : Real) (hx : 0 <= x)
    (K n : Nat) (hK : 0 < K) :
    (x ^ (K : Real)⁻¹) ^
        (-((K : Real) ^ n)⁻¹) =
      x ^ (-((K : Real) ^ (n + 1))⁻¹) := by
  rw [← Real.rpow_mul hx]
  congr 1
  push_cast [pow_succ]
  field_simp

/-- Taking the final ideal root of the repaired integral threshold recovers
the base `2*T` strictly. -/
private theorem section5ClosedThreshold_lt_finalRoot
    {T K q r : Nat} (hK : 0 < K)
    (hthreshold : (2 * T) ^ (K ^ (q - 1)) < r) :
    (2 * T : Nat) <
      (r : Real) ^ ((K ^ (q - 1) : Nat) : Real)⁻¹ := by
  have hn : K ^ (q - 1) ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt hK)
  have hcast :
      (((2 * T) ^ (K ^ (q - 1)) : Nat) : Real) < (r : Real) := by
    exact_mod_cast hthreshold
  have hrpow := Real.rpow_lt_rpow (show (0 : Real) <=
      ((2 * T) ^ (K ^ (q - 1)) : Nat) by positivity) hcast
      (show (0 : Real) < ((K ^ (q - 1) : Nat) : Real)⁻¹ by positivity)
  have hpowCast :
      (((2 * T) ^ (K ^ (q - 1)) : Nat) : Real) =
        ((2 * T : Nat) : Real) ^ (K ^ (q - 1)) := by
    norm_cast
  rw [hpowCast,
    Real.pow_rpow_inv_natCast
      (show (0 : Real) <= ((2 * T : Nat) : Real) by positivity) hn] at hrpow
  exact hrpow

/-- If a positive iterated root is at least `16`, then its original base is
also at least `16`. -/
private theorem section5Sixteen_le_of_iteratedRoot
    {x : Real} (hx : 0 <= x) {K n : Nat} (hK : 1 <= K)
    (hlarge : 16 <= x ^ ((K ^ n : Nat) : Real)⁻¹) :
    16 <= x := by
  have hexponentPos :
      (0 : Real) < ((K ^ n : Nat) : Real)⁻¹ := by positivity
  have hxOne : (1 : Real) <= x := by
    by_contra hnot
    have hxLe : x <= 1 := le_of_not_ge hnot
    have hrootLe :
        x ^ ((K ^ n : Nat) : Real)⁻¹ <= 1 :=
      Real.rpow_le_one hx hxLe hexponentPos.le
    linarith
  have hpowOne : 1 <= K ^ n := one_le_pow₀ hK
  have hpowOneReal : (1 : Real) <= (K ^ n : Nat) := by exact_mod_cast hpowOne
  have hexponentLeOne : ((K ^ n : Nat) : Real)⁻¹ <= 1 := by
    have := (inv_le_inv₀ (by positivity : (0 : Real) < (K ^ n : Nat))
      (by norm_num : (0 : Real) < 1)).2 hpowOneReal
    simpa using this
  have hrootLeBase : x ^ ((K ^ n : Nat) : Real)⁻¹ <= x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hxOne hexponentLeOne
  exact hlarge.trans hrootLeBase

private theorem section5Sqrt_le_quarter {x : Real} (hx : 16 <= x) :
    x ^ (2 : Real)⁻¹ <= x / 4 := by
  have hx0 : 0 <= x := by linarith
  have hsqrtFour : (4 : Real) <= x ^ (2 : Real)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) hx0
      (by norm_num : (0 : Real) < 2)).2
    calc
      (4 : Real) ^ (2 : Real) = 16 := by norm_num [Real.rpow_natCast]
      _ <= x := hx
  have hsquare : (x ^ (2 : Real)⁻¹) ^ (2 : Nat) = x :=
    Real.rpow_inv_natCast_pow hx0 (by norm_num)
  nlinarith

private theorem section5Four_root_le_two (K : Nat) (hK : 2 <= K) :
    (4 : Real) ^ (K : Real)⁻¹ <= 2 := by
  apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num)
    (by positivity : (0 : Real) < K)).2
  rw [Real.rpow_natCast]
  exact_mod_cast (show 4 <= 2 ^ K by
    calc
      4 = 2 ^ (2 : Nat) := by norm_num
      _ <= 2 ^ K :=
        pow_le_pow_right₀ (by norm_num : 1 <= (2 : Nat)) hK)

/-- For a number at least four, flooring and then subtracting one retains at
least half of the original real value. -/
private theorem section5Half_le_floor_sub_one {x : Real} (hx : 4 <= x) :
    x / 2 <= (Nat.floor x - 1 : Nat) := by
  have hfloorOne : 1 <= Nat.floor x :=
    (Nat.one_le_floor_iff x).2 (by linarith)
  rw [Nat.cast_sub hfloorOne, Nat.cast_one]
  have hfloor := Nat.sub_one_lt_floor x
  nlinarith

/-- A quarter of the next ideal root lies below the shorter rounded branch.
This is the inductive step in the fixed `/4` invariant. -/
private theorem section5QuarterRoot_le_floorRoot_sub_one
    {x t : Real} {K : Nat} (hx : 0 <= x)
    (hxRoot : 16 <= x ^ (K : Real)⁻¹)
    (hK : 2 <= K) (ht : x / 4 <= t) :
    x ^ (K : Real)⁻¹ / 4 <=
      (Nat.floor (t ^ (K : Real)⁻¹) - 1 : Nat) := by
  have hquarterNonneg : 0 <= x / 4 := by positivity
  have hrootMono :
      (x / 4) ^ (K : Real)⁻¹ <= t ^ (K : Real)⁻¹ :=
    Real.rpow_le_rpow hquarterNonneg ht (by positivity)
  have hfourRootPos : 0 < (4 : Real) ^ (K : Real)⁻¹ := by positivity
  have hrootHalf :
      x ^ (K : Real)⁻¹ / 2 <=
        (x / 4) ^ (K : Real)⁻¹ := by
    rw [Real.div_rpow hx (by norm_num)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx _)
      hfourRootPos (section5Four_root_le_two K hK)
  have hcurrentRootHalf :
      x ^ (K : Real)⁻¹ / 2 <= t ^ (K : Real)⁻¹ :=
    hrootHalf.trans hrootMono
  have hcurrentRootFour : (4 : Real) <= t ^ (K : Real)⁻¹ := by
    nlinarith
  have hfloorHalf := section5Half_le_floor_sub_one hcurrentRootFour
  nlinarith

/-! ## The two schedule estimates -/

private theorem section5RoundingThreshold_base_le
    (T K n : Nat) (hK : 1 <= K) :
    T <= polynomialPartitionIteratedRoundingThreshold T K n := by
  induction n with
  | zero => simp [polynomialPartitionIteratedRoundingThreshold]
  | succ n ih =>
      rw [polynomialPartitionIteratedRoundingThreshold]
      have hbase : 1 <=
          polynomialPartitionIteratedRoundingThreshold T K n + 2 := by omega
      calc
        T <= polynomialPartitionIteratedRoundingThreshold T K n := ih
        _ <= polynomialPartitionIteratedRoundingThreshold T K n + 2 := by omega
        _ = (polynomialPartitionIteratedRoundingThreshold T K n + 2) ^ 1 := by
          rw [pow_one]
        _ <= (polynomialPartitionIteratedRoundingThreshold T K n + 2) ^ K :=
          pow_le_pow_right₀ hbase hK

/-- The `/4` invariant implies the strong local diameter bound.  The final
iterated root being at least `16` supplies the only lower-bound hypothesis on
the real base. -/
private theorem section5LocalDiameter_of_quarterInvariant
    {x : Real} (hx : 0 <= x) {t K q : Nat} (hK : 2 <= K) (hq : 1 <= q)
    (hlarge : 16 <= x ^ ((K ^ (q - 1) : Nat) : Real)⁻¹)
    (hlower : x / 4 <= t) :
    (t : Real) ^ (-(2 * (K : Real)⁻¹)) <=
      x ^ (-((K : Real) ^ q)⁻¹) := by
  have hxSixteen := section5Sixteen_le_of_iteratedRoot hx (by omega : 1 <= K) hlarge
  have hsqrt : x ^ (2 : Real)⁻¹ <= (t : Real) :=
    (section5Sqrt_le_quarter hxSixteen).trans hlower
  have hsqrtPos : 0 < x ^ (2 : Real)⁻¹ := by
    exact Real.rpow_pos_of_pos (by linarith) _
  have hnegative : -(2 * (K : Real)⁻¹) <= 0 := by
    have : (0 : Real) <= (K : Real)⁻¹ := inv_nonneg.mpr (by positivity)
    linarith
  have hfirst :
      (t : Real) ^ (-(2 * (K : Real)⁻¹)) <=
        (x ^ (2 : Real)⁻¹) ^ (-(2 * (K : Real)⁻¹)) :=
    Real.rpow_le_rpow_of_nonpos hsqrtPos hsqrt hnegative
  have hcompose :
      (x ^ (2 : Real)⁻¹) ^ (-(2 * (K : Real)⁻¹)) =
        x ^ (-(K : Real)⁻¹) := by
    rw [← Real.rpow_mul hx]
    congr 1
    field_simp
  have hKPow : K <= K ^ q := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by omega : 1 <= K) hq
  have hKPowReal : (K : Real) <= (K : Real) ^ q := by exact_mod_cast hKPow
  have hinverse : ((K : Real) ^ q)⁻¹ <= (K : Real)⁻¹ :=
    (inv_le_inv₀ (by positivity : (0 : Real) < (K : Real) ^ q)
      (by positivity : (0 : Real) < K)).2 hKPowReal
  have hxOne : (1 : Real) <= x := by linarith
  calc
    (t : Real) ^ (-(2 * (K : Real)⁻¹)) <=
        (x ^ (2 : Real)⁻¹) ^ (-(2 * (K : Real)⁻¹)) := hfirst
    _ = x ^ (-(K : Real)⁻¹) := hcompose
    _ <= x ^ (-((K : Real) ^ q)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_le hxOne (neg_le_neg hinverse)

/-- At the last stage, the `/4` invariant turns the live half-exponent bound
on `v` into the one-polynomial target bound. -/
private theorem section5FinalTarget_of_quarterInvariant
    {x t : Real} (hx : 0 <= x) (hxSixteen : 16 <= x)
    {K : Nat} (hK : 2 <= K) (hlower : x / 4 <= t) :
    x ^ (2 * (K : Real))⁻¹ <= t ^ (K : Real)⁻¹ := by
  have hsqrtQuarter := section5Sqrt_le_quarter hxSixteen
  have hsqrtRoot :
      (x ^ (2 : Real)⁻¹) ^ (K : Real)⁻¹ <=
        (x / 4) ^ (K : Real)⁻¹ :=
    Real.rpow_le_rpow (Real.rpow_nonneg hx _) hsqrtQuarter (by positivity)
  have hquarterRoot :
      (x / 4) ^ (K : Real)⁻¹ <= t ^ (K : Real)⁻¹ :=
    Real.rpow_le_rpow (by positivity) hlower (by positivity)
  have hcompose :
      (x ^ (2 : Real)⁻¹) ^ (K : Real)⁻¹ =
        x ^ (2 * (K : Real))⁻¹ := by
    rw [← Real.rpow_mul hx]
    congr 1
    field_simp
  rw [← hcompose]
  exact hsqrtRoot.trans hquarterRoot

/-! ## Recursive construction of the maximal-target schedule -/

/-- Quantitative induction with a movable ideal scale `x`.  In the recursive
call `x` becomes `x^(1/K)`; the final-root hypothesis and the global scale are
definitionally transported by the three composition lemmas above. -/
private theorem section5MaximalTargets_schedule_aux
    (k : Nat) (hk : 1 <= k) :
    forall (q t v : Nat) (x : Real),
      1 <= q -> 0 <= x ->
      polynomialPartitionIteratedRoundingThreshold
          (polynomialPartitionThreshold k) (polynomialPartitionConstant k)
          (q - 1) < t ->
      16 <= x ^
        (((polynomialPartitionConstant k) ^ (q - 1) : Nat) : Real)⁻¹ ->
      x / 4 <= t ->
      1 <= v ->
      (v : Real) <=
        x ^ (2 * (polynomialPartitionConstant k : Real) ^ q)⁻¹ ->
      section5StrongRefinementSchedule k
        (x ^ (-((polynomialPartitionConstant k : Real) ^ q)⁻¹)) t
        (section5MaximalTargets (polynomialPartitionConstant k) q t v) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro t v x hq hx hthreshold hlarge hlower hv hvupper
      let K := polynomialPartitionConstant k
      let T := polynomialPartitionThreshold k
      have hKSixteen : 16 <= K := by
        simpa only [K] using section5PolynomialPartitionConstant_ge_sixteen hk
      have hKSq : 2 <= K := by omega
      have hKPos : 0 < K := by omega
      match q with
      | 0 => omega
      | 1 =>
          have hxSixteen : 16 <= x := by
            simpa only [Nat.sub_self, pow_zero, Nat.cast_one, inv_one,
              Real.rpow_one, K] using hlarge
          have hthresholdHead : polynomialPartitionThreshold k < t := by
            simpa only [Nat.sub_self, polynomialPartitionIteratedRoundingThreshold,
              T] using hthreshold
          have htarget :
              (v : Real) <=
                (t : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ := by
            calc
              (v : Real) <=
                  x ^ (2 * (polynomialPartitionConstant k : Real))⁻¹ := by
                simpa only [pow_one] using hvupper
              _ <= (t : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ :=
                section5FinalTarget_of_quarterInvariant hx hxSixteen hKSq hlower
          have hdiameter :
              (t : Real) ^
                  (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) <=
                x ^ (-(polynomialPartitionConstant k : Real)⁻¹) := by
            simpa only [pow_one] using
              section5LocalDiameter_of_quarterInvariant hx hKSq
                (by norm_num) hlarge hlower
          simpa only [section5MaximalTargets, pow_one] using
            (show section5StrongRefinementSchedule k
                (x ^ (-(polynomialPartitionConstant k : Real)⁻¹)) t [v] from
              ⟨hthresholdHead, hv, htarget, hdiameter, trivial, trivial⟩)
      | n + 2 =>
          let y : Real := (t : Real) ^ (K : Real)⁻¹
          let u : Nat := Nat.floor y
          let x' : Real := x ^ (K : Real)⁻¹
          have hthreshold' :
              polynomialPartitionIteratedRoundingThreshold T K (n + 1) < t := by
            simpa only [T, K, show n + 2 - 1 = n + 1 by omega] using hthreshold
          have hlarge' :
              16 <= x ^ ((K ^ (n + 1) : Nat) : Real)⁻¹ := by
            simpa only [K, show n + 2 - 1 = n + 1 by omega] using hlarge
          have hthresholdHead : polynomialPartitionThreshold k < t := by
            have hbase : T <=
                polynomialPartitionIteratedRoundingThreshold T K (n + 1) :=
              section5RoundingThreshold_base_le T K (n + 1) (by omega)
            have : T < t := hbase.trans_lt hthreshold'
            simpa only [T] using this
          have hyNonneg : 0 <= y := by positivity
          have hyUpper : (u : Real) <= y := Nat.floor_le hyNonneg
          have hpowerThreshold :
              (polynomialPartitionIteratedRoundingThreshold T K n + 2) ^ K < t := by
            simpa only [polynomialPartitionIteratedRoundingThreshold] using hthreshold'
          have hrootThreshold :
              (polynomialPartitionIteratedRoundingThreshold T K n + 2 : Nat) <= u := by
            apply Nat.le_floor
            apply le_of_lt
            apply (Real.lt_rpow_inv_iff_of_pos (by positivity)
              (show (0 : Real) <= t by positivity)
              (show (0 : Real) < K by positivity)).2
            simpa only [Real.rpow_natCast] using
              (show
                ((polynomialPartitionIteratedRoundingThreshold T K n + 2 : Nat) : Real) ^ K <
                  (t : Real) by
                exact_mod_cast hpowerThreshold)
          have hu : 1 <= u := by
            have : 1 <= polynomialPartitionIteratedRoundingThreshold T K n + 2 := by
              omega
            exact this.trans hrootThreshold
          have hchildThreshold :
              polynomialPartitionIteratedRoundingThreshold T K n < u - 1 := by
            omega
          have hx'Large :
              16 <= x' ^ ((K ^ n : Nat) : Real)⁻¹ := by
            dsimp only [x']
            rw [section5IteratedRoot_succ x hx K n hKPos]
            exact hlarge'
          have hxRoot : 16 <= x ^ (K : Real)⁻¹ := by
            simpa only [x'] using
              section5Sixteen_le_of_iteratedRoot
                (Real.rpow_nonneg hx _) (by omega : 1 <= K) hx'Large
          have hchildLower : x' / 4 <= (u - 1 : Nat) := by
            have hraw := section5QuarterRoot_le_floorRoot_sub_one
              (K := K) hx hxRoot hKSq hlower
            simpa only [x', u, y] using hraw
          have hchildV :
              (v : Real) <= x' ^ (2 * (K : Real) ^ (n + 1))⁻¹ := by
            dsimp only [x']
            rw [section5Root_targetExponent x hx K (n + 1) hKPos]
            simpa only [K] using hvupper
          have htail :
              section5StrongRefinementSchedule k
                (x' ^ (-((K : Real) ^ (n + 1))⁻¹)) (u - 1)
                (section5MaximalTargets K (n + 1) (u - 1) v) := by
            apply ih (n + 1) (by omega) (u - 1) v x'
            · omega
            · exact Real.rpow_nonneg hx _
            · simpa only [T, K, Nat.add_sub_cancel] using hchildThreshold
            · simpa only [K, Nat.add_sub_cancel] using hx'Large
            · exact hchildLower
            · exact hv
            · simpa only [K] using hchildV
          have htailGlobal :
              section5StrongRefinementSchedule k
                (x ^ (-((K : Real) ^ (n + 2))⁻¹)) (u - 1)
                (section5MaximalTargets K (n + 1) (u - 1) v) := by
            rw [← section5Root_globalExponent x hx K (n + 1) hKPos]
            exact htail
          have hdiameter :
              (t : Real) ^ (-(2 * (K : Real)⁻¹)) <=
                x ^ (-((K : Real) ^ (n + 2))⁻¹) := by
            apply section5LocalDiameter_of_quarterInvariant hx hKSq (by omega)
            · exact hlarge'
            · exact hlower
          have hschedule := section5StrongRefinementSchedule_cons_of_min
            hthresholdHead hu (by simpa only [u, y, K] using hyUpper)
            (by simpa only [K] using hdiameter) htailGlobal
          simpa only [section5MaximalTargets, u, y, x', K] using hschedule

/-! ## Discharge of the live quantitative propositions -/

/-- The repaired simultaneous threshold proves all three obligations in the
canonical maximal-target schedule: strict applicability, target size, and
the strong local diameter bound. -/
theorem lemma_5_9_maximal_target_bounds_holds :
    lemma_5_9_maximal_target_bounds := by
  intro k q r v hk hq hthreshold hv hvupper
  let T := polynomialPartitionThreshold k
  let K := polynomialPartitionConstant k
  have hTSixteen : 16 <= T := by
    simpa only [T] using section5PolynomialPartitionThreshold_ge_sixteen hk
  have hKSixteen : 16 <= K := by
    simpa only [K] using section5PolynomialPartitionConstant_ge_sixteen hk
  have hrounding :
      polynomialPartitionIteratedRoundingThreshold T K (q - 1) + 3 <=
        simultaneousPolynomialThreshold k q := by
    apply polynomialPartitionIteratedRoundingThreshold_le_roundingSafe
    · simpa only [T] using (show 3 <= T by omega)
    · simpa only [K] using (show 3 <= K by omega)
  have hexact :
      polynomialPartitionIteratedRoundingThreshold T K (q - 1) < r := by
    omega
  have hclosed : (2 * T) ^ (K ^ (q - 1)) < r := by
    simpa only [simultaneousPolynomialThreshold, T, K] using hthreshold
  have hfinalRootStrict :
      (2 * T : Nat) < (r : Real) ^ ((K ^ (q - 1) : Nat) : Real)⁻¹ :=
    section5ClosedThreshold_lt_finalRoot (by omega) hclosed
  have hfinalRootLarge :
      16 <= (r : Real) ^ ((K ^ (q - 1) : Nat) : Real)⁻¹ := by
    have hbase : (16 : Real) <= ((2 * T : Nat) : Real) := by
      exact_mod_cast (show 16 <= 2 * T by omega)
    exact hbase.trans hfinalRootStrict.le
  have hlower : (r : Real) / 4 <= r := by
    have hrNonneg : (0 : Real) <= r := by positivity
    nlinarith
  apply section5MaximalTargets_schedule_aux k hk q r v (r : Real) hq
    (by positivity)
  · simpa only [T, K] using hexact
  · simpa only [K] using hfinalRootLarge
  · exact hlower
  · exact hv
  · exact hvupper

/-- The exact schedule proposition consumed by the compiled combinatorial
engine. -/
theorem lemma_5_9_scale_schedule_holds : lemma_5_9_scale_schedule :=
  lemma_5_9_scale_schedule_holds_of_maximal_target_bounds
    lemma_5_9_maximal_target_bounds_holds

end LeanProofs.GowersSzemeredi

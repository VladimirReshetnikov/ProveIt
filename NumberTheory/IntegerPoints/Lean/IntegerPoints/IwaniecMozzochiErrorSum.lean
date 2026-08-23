import IntegerPoints.DivisorCardinalityBound
import IntegerPoints.IwaniecMozzochi
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The elementary error sum in Iwaniec--Mozzochi section 3

This file proves the estimate

`E(x,y,M) = sum_(m ~ M) (1 + y * ||x/m||)^(-1)
             <<_epsilon (1 + M/y) x^epsilon`.

The generic algebraic-distribution lemma in `IntegerPoints.Lemma3` is not
strong enough here: at the upper end of the range it loses a factor of order
`sqrt x`.  The proof below instead uses the arithmetic special to `x/m`.
For each `m` put

`q = m * round(x/m)`.

Then `q` is a positive integer at most `2x`, and all `m` in a fixed fibre are
divisors of `q`.  The divisor-function bound therefore makes every fibre
subpolynomial.  Moreover

`||x/m|| = |x-q|/m >= |x-q|/(2M)`.

It remains to sum a one-dimensional reciprocal kernel centred at the real
number `x`; splitting at `floor x` reduces both halves to a harmonic sum.  A
second half of the requested epsilon absorbs that logarithm.

The argument deliberately keeps `x` real.  In particular, it neither rounds
`x` nor assumes that the centre of the reciprocal kernel is integral.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

namespace IMErrorSum

noncomputable section

/-- The integral product attached to a summand of the error sum. -/
def roundedProduct (x : ℝ) (m : ℕ) : ℕ :=
  m * (round (x / m)).toNat

/-- Basic bounds for a member of a dyadic block. -/
private theorem mem_dyadic_cast_bounds {M : ℝ} (hM : 1 ≤ M) {m : ℕ}
    (hm : m ∈ dyadic M) :
    0 < m ∧ M < (m : ℝ) ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, intRange, Finset.mem_Ioc] at hm
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
  have hMfloor : M < (⌊M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one M
  have hfloor_m : ⌊M⌋₊ + 1 ≤ m := Nat.succ_le_iff.mpr hm.1
  have hMlt : M < (m : ℝ) := by
    exact hMfloor.trans_le (by exact_mod_cast hfloor_m)
  have hmUpper : (m : ℝ) ≤ 2 * M := by
    calc
      (m : ℝ) ≤ (⌊2 * M⌋₊ : ℝ) := by exact_mod_cast hm.2
      _ ≤ 2 * M := Nat.floor_le (by positivity)
  exact ⟨hmpos, hMlt, hmUpper⟩

/-- In the range used by section 3, `round (x/m)` is positive.  The endpoint
`x/m = 1/2` is harmless because Mathlib rounds a half toward positive
infinity. -/
private theorem round_div_pos {x M : ℝ} (_hx : 1 ≤ x) (hM : 1 ≤ M)
    (hMx : M ≤ x) {m : ℕ} (hm : m ∈ dyadic M) :
    0 < round (x / m) := by
  obtain ⟨hmpos, _, hmUpper⟩ := mem_dyadic_cast_bounds hM hm
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hhalf : (1 : ℝ) / 2 ≤ x / m := by
    rw [le_div_iff₀ hmposR]
    nlinarith
  have hroundR : (0 : ℝ) < (round (x / m) : ℝ) := by
    linarith [sub_half_lt_round (x / m)]
  exact_mod_cast hroundR

/-- Casting `roundedProduct` back to the reals recovers the defining
integer product. -/
private theorem roundedProduct_cast {x M : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M)
    (hMx : M ≤ x) {m : ℕ} (hm : m ∈ dyadic M) :
    (roundedProduct x m : ℝ) = (m : ℝ) * (round (x / m) : ℝ) := by
  have hk := (round_div_pos hx hM hMx hm).le
  have hkNat : ((round (x / m)).toNat : ℤ) = round (x / m) :=
    Int.toNat_of_nonneg hk
  rw [roundedProduct, Nat.cast_mul]
  congr 1
  exact_mod_cast hkNat

/-- The products of all summands lie in the finite set of positive integers
at most `2x`.  This also handles the potential `q = 0` problem explicitly. -/
theorem roundedProduct_mem_upTo {x M : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M)
    (hMx : M ≤ x) {m : ℕ} (hm : m ∈ dyadic M) :
    roundedProduct x m ∈ upTo (2 * x) := by
  obtain ⟨hmpos, _, hmUpper⟩ := mem_dyadic_cast_bounds hM hm
  have hkpos := round_div_pos hx hM hMx hm
  have hkNat : ((round (x / m)).toNat : ℤ) = round (x / m) :=
    Int.toNat_of_nonneg hkpos.le
  have hkNatPos : 0 < (round (x / m)).toNat := by
    rw [← Int.ofNat_lt, hkNat]
    exact hkpos
  have hqpos : 1 ≤ roundedProduct x m := by
    rw [roundedProduct]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hmpos.ne' hkNatPos.ne')
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hqUpper : (roundedProduct x m : ℝ) ≤ 2 * x := by
    rw [roundedProduct_cast hx hM hMx hm]
    calc
      (m : ℝ) * (round (x / m) : ℝ)
          ≤ (m : ℝ) * (x / m + 1 / 2) :=
        mul_le_mul_of_nonneg_left (round_le_add_half (x / m)) (by positivity)
      _ = x + (m : ℝ) / 2 := by
        field_simp [hmposR.ne']
      _ ≤ x + M := by linarith
      _ ≤ 2 * x := by linarith
  rw [upTo, Finset.mem_Icc]
  exact ⟨hqpos, (Nat.le_floor_iff (by positivity)).2 hqUpper⟩

/-- The distance in a summand is the distance from `x` to its associated
integer product, divided by `m`. -/
private theorem nearestIntDist_div_eq {x M : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M)
    (hMx : M ≤ x) {m : ℕ} (hm : m ∈ dyadic M) :
    nearestIntDist (x / m) = |x - roundedProduct x m| / m := by
  obtain ⟨hmpos, _, _⟩ := mem_dyadic_cast_bounds hM hm
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  rw [nearestIntDist, roundedProduct_cast hx hM hMx hm]
  have hid : x / (m : ℝ) - (round (x / m) : ℝ) =
      (x - (m : ℝ) * (round (x / m) : ℝ)) / m := by
    field_simp [hmposR.ne']
  rw [hid, abs_div, abs_of_pos hmposR]

/-- Every summand is bounded by the reciprocal kernel attached to its
integer product. -/
theorem summand_le_kernel {x y M : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hM : 1 ≤ M) (hMx : M ≤ x) {m : ℕ} (hm : m ∈ dyadic M) :
    (1 + nearestIntDist (x / m) * y)⁻¹ ≤
      (1 + (y / (2 * M)) * |x - roundedProduct x m|)⁻¹ := by
  obtain ⟨hmpos, _, hmUpper⟩ := mem_dyadic_cast_bounds hM hm
  have hmposR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hdist : |x - roundedProduct x m| / (2 * M) ≤ nearestIntDist (x / m) := by
    rw [nearestIntDist_div_eq hx hM hMx hm]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hmposR hmUpper
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hnear0 : 0 ≤ nearestIntDist (x / m) := by
    unfold nearestIntDist
    exact abs_nonneg _
  have hscale0 : 0 ≤ y / (2 * M) := by positivity
  have hleft : 0 < 1 + nearestIntDist (x / m) * y :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hnear0 hy0)
  have hright : 0 < 1 + (y / (2 * M)) * |x - roundedProduct x m| :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hscale0 (abs_nonneg _))
  apply (inv_le_inv₀ hleft hright).2
  have hmul := mul_le_mul_of_nonneg_right hdist hy0
  convert add_le_add_left hmul 1 using 1 <;> ring

/-- In one product fibre, all values of `m` are divisors of the product. -/
theorem roundedProduct_fiber_subset_divisors {x M : ℝ} {q : ℕ} (hq0 : q ≠ 0) :
    (dyadic M).filter (fun m ↦ roundedProduct x m = q) ⊆ q.divisors := by
  intro m hm
  rw [Finset.mem_filter] at hm
  rw [Nat.mem_divisors]
  exact ⟨by
    rw [← hm.2]
    exact dvd_mul_right m (round (x / m)).toNat, hq0⟩

/-- The reciprocal kernel about a real centre. -/
def kernel (a x : ℝ) (q : ℕ) : ℝ :=
  (1 + a * |x - q|)⁻¹

/-- A harmonic upper bound for the discrete reciprocal kernel.  The two
copies arise by splitting the integers immediately below and above
`floor x`; the centre `x` itself is not assumed integral. -/
private theorem kernel_sum_le {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    ∑ q ∈ upTo (2 * x), kernel a x q ≤
      2 + 2 * a⁻¹ * (1 + Real.log (2 * x)) := by
  classical
  let N : ℕ := ⌊2 * x⌋₊
  let n : ℕ := ⌊x⌋₊
  let S : Finset ℕ := Finset.Icc 1 N
  let L : Finset ℕ := S.filter (fun q ↦ q ≤ n)
  let R : Finset ℕ := S.filter (fun q ↦ ¬ q ≤ n)
  let w : ℕ → ℝ := fun j ↦ (1 + a * j)⁻¹

  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.floor_pos.mpr (by linarith)
  have hnN : n ≤ N := by
    dsimp [n, N]
    exact Nat.floor_le_floor (by linarith)
  have hnCast : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hxpos.le
  have hxN : x < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one x

  have hL : ∑ q ∈ L, kernel a x q ≤ ∑ j ∈ Finset.range (N + 1), w j := by
    let f : ℕ → ℕ := fun q ↦ n - q
    have hfmem : ∀ q ∈ L, f q ∈ Finset.range (N + 1) := by
      intro q hq
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (Nat.sub_le n q) (Nat.lt_succ_of_le hnN)
    have hfinj : Set.InjOn f L := by
      intro q₁ hq₁ q₂ hq₂ heq
      have hq₁n : q₁ ≤ n := (Finset.mem_filter.1 hq₁).2
      have hq₂n : q₂ ≤ n := (Finset.mem_filter.1 hq₂).2
      dsimp [f] at heq
      omega
    have hpoint : ∀ q ∈ L, kernel a x q ≤ w (f q) := by
      intro q hq
      have hqn : q ≤ n := (Finset.mem_filter.1 hq).2
      have hqnCast : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
      have hqCast : (q : ℝ) ≤ x := hqnCast.trans hnCast
      have hdist : ((f q : ℕ) : ℝ) ≤ |x - q| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hqCast)]
        dsimp [f]
        rw [Nat.cast_sub hqn]
        exact sub_le_sub_right hnCast _
      dsimp [w, kernel]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hdist ha.le) 1
    calc
      ∑ q ∈ L, kernel a x q ≤ ∑ q ∈ L, w (f q) :=
        Finset.sum_le_sum hpoint
      _ = ∑ j ∈ L.image f, w j := (Finset.sum_image hfinj).symm
      _ ≤ ∑ j ∈ Finset.range (N + 1), w j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hfmem) (by
            intro j _ _
            dsimp [w]
            positivity)

  have hR : ∑ q ∈ R, kernel a x q ≤ ∑ j ∈ Finset.range (N + 1), w j := by
    let f : ℕ → ℕ := fun q ↦ q - (n + 1)
    have hfmem : ∀ q ∈ R, f q ∈ Finset.range (N + 1) := by
      intro q hq
      have hqS : q ∈ S := (Finset.mem_filter.1 hq).1
      have hqN : q ≤ N := (Finset.mem_Icc.1 hqS).2
      rw [Finset.mem_range]
      exact lt_of_le_of_lt (Nat.sub_le q (n + 1)) (Nat.lt_succ_of_le hqN)
    have hfinj : Set.InjOn f R := by
      intro q₁ hq₁ q₂ hq₂ heq
      have hq₁n : n < q₁ := Nat.lt_of_not_ge (Finset.mem_filter.1 hq₁).2
      have hq₂n : n < q₂ := Nat.lt_of_not_ge (Finset.mem_filter.1 hq₂).2
      dsimp [f] at heq
      omega
    have hpoint : ∀ q ∈ R, kernel a x q ≤ w (f q) := by
      intro q hq
      have hnq : n < q := Nat.lt_of_not_ge (Finset.mem_filter.1 hq).2
      have hxq : x ≤ (q : ℝ) := by
        have hnOneQ : n + 1 ≤ q := Nat.succ_le_iff.mpr hnq
        exact hxN.le.trans (by exact_mod_cast hnOneQ)
      have hdist : ((f q : ℕ) : ℝ) ≤ |x - q| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxq)]
        dsimp [f]
        rw [Nat.cast_sub (Nat.succ_le_iff.mpr hnq)]
        norm_num
        linarith
      dsimp [w, kernel]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      simpa [add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hdist ha.le) 1
    calc
      ∑ q ∈ R, kernel a x q ≤ ∑ q ∈ R, w (f q) :=
        Finset.sum_le_sum hpoint
      _ = ∑ j ∈ R.image f, w j := (Finset.sum_image hfinj).symm
      _ ≤ ∑ j ∈ Finset.range (N + 1), w j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hfmem) (by
            intro j _ _
            dsimp [w]
            positivity)

  have hW : ∑ j ∈ Finset.range (N + 1), w j ≤
      1 + a⁻¹ * (harmonic N : ℝ) := by
    rw [Finset.sum_range_succ']
    have htail : ∑ j ∈ Finset.range N, w (j + 1) ≤
        a⁻¹ * (harmonic N : ℝ) := by
      calc
        ∑ j ∈ Finset.range N, w (j + 1)
            ≤ ∑ j ∈ Finset.range N, a⁻¹ * ((j + 1 : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro j hj
          dsimp [w]
          have : a * ((j + 1 : ℕ) : ℝ) ≤
              1 + a * ((j + 1 : ℕ) : ℝ) := by linarith
          calc
            (1 + a * ((j + 1 : ℕ) : ℝ))⁻¹
                ≤ (a * ((j + 1 : ℕ) : ℝ))⁻¹ :=
              (inv_le_inv₀ (by positivity) (by positivity)).2 this
            _ = a⁻¹ * ((j + 1 : ℕ) : ℝ)⁻¹ := by
              rw [mul_inv_rev, mul_comm]
        _ = a⁻¹ * (harmonic N : ℝ) := by
          rw [harmonic, Rat.cast_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Rat.cast_inv, Rat.cast_natCast]
    simpa [w, add_comm] using add_le_add_left htail 1

  have hH : (harmonic N : ℝ) ≤ 1 + Real.log (2 * x) := by
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNupper : (N : ℝ) ≤ 2 * x := by
      dsimp [N]
      exact Nat.floor_le (by positivity)
    have hlogN : Real.log N ≤ Real.log (2 * x) :=
      Real.log_le_log hNposR hNupper
    exact (harmonic_le_one_add_log N).trans (by
      simpa [add_comm] using add_le_add_left hlogN 1)
  have hWinv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hS : S = upTo (2 * x) := by rfl
  have hsplit :
      (∑ q ∈ S, kernel a x q) =
        (∑ q ∈ L, kernel a x q) + (∑ q ∈ R, kernel a x q) := by
    dsimp [L, R]
    exact (Finset.sum_filter_add_sum_filter_not S (fun q ↦ q ≤ n)
      (f := kernel a x)).symm
  rw [← hS, hsplit]
  calc
    (∑ q ∈ L, kernel a x q) + ∑ q ∈ R, kernel a x q
        ≤ 2 * (∑ j ∈ Finset.range (N + 1), w j) := by linarith
    _ ≤ 2 * (1 + a⁻¹ * (harmonic N : ℝ)) := by nlinarith
    _ ≤ 2 * (1 + a⁻¹ * (1 + Real.log (2 * x))) := by
      nlinarith [mul_le_mul_of_nonneg_left hH hWinv]
    _ = 2 + 2 * a⁻¹ * (1 + Real.log (2 * x)) := by ring

/-- Specialisation of the kernel bound to the scale appearing in the error
sum. -/
theorem scaled_kernel_sum_le {x y M : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hM : 1 ≤ M) :
    ∑ q ∈ upTo (2 * x), kernel (y / (2 * M)) x q ≤
      2 + 4 * (M / y) * (1 + Real.log (2 * x)) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have h := kernel_sum_le (x := x) (a := y / (2 * M)) (by positivity) hx
  calc
    ∑ q ∈ upTo (2 * x), kernel (y / (2 * M)) x q
        ≤ 2 + 2 * (y / (2 * M))⁻¹ * (1 + Real.log (2 * x)) := h
    _ = 2 + 4 * (M / y) * (1 + Real.log (2 * x)) := by
      field_simp [hypos.ne', hMpos.ne']
      ring

end

end IMErrorSum

open IMErrorSum

/-- The elementary error-sum estimate from section 3 of Iwaniec--Mozzochi. -/
theorem iwaniecMozzochi_section3_errorSumBound_holds :
    iwaniecMozzochi_section3_errorSumBound := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hAone, hA⟩ :=
    DivisorCardinality.exists_one_le_card_divisors_bound δ hδ
  let B : ℝ := 6 + 4 / δ
  let C : ℝ := A * B * (2 : ℝ) ^ ε
  refine ⟨C, ?_⟩
  intro x y M hx hy hM hMx

  have hA0 : 0 ≤ A := le_trans zero_le_one hAone
  have h2xpow : 1 ≤ (2 * x) ^ δ :=
    Real.one_le_rpow (by linarith) hδ.le

  have hmaps : ∀ m ∈ dyadic M, roundedProduct x m ∈ upTo (2 * x) :=
    fun m hm ↦ IMErrorSum.roundedProduct_mem_upTo hx hM hMx hm

  have hfibre : ∀ q ∈ upTo (2 * x),
      ∑ m ∈ (dyadic M).filter (fun m ↦ roundedProduct x m = q),
          (1 + nearestIntDist (x / m) * y)⁻¹ ≤
        A * (q : ℝ) ^ δ * kernel (y / (2 * M)) x q := by
    intro q hq
    have hq' := hq
    rw [upTo, Finset.mem_Icc] at hq'
    have hqpos : 1 ≤ q := hq'.1
    have hq0 : q ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hqpos)
    have hsubset :
        (dyadic M).filter (fun m ↦ roundedProduct x m = q) ⊆ q.divisors :=
      IMErrorSum.roundedProduct_fiber_subset_divisors hq0
    have hkernel0 : 0 ≤ kernel (y / (2 * M)) x q := by
      dsimp [kernel]
      positivity
    calc
      ∑ m ∈ (dyadic M).filter (fun m ↦ roundedProduct x m = q),
          (1 + nearestIntDist (x / m) * y)⁻¹
          ≤ ∑ m ∈ (dyadic M).filter (fun m ↦ roundedProduct x m = q),
              kernel (y / (2 * M)) x q := by
            apply Finset.sum_le_sum
            intro m hm
            have hm' := Finset.mem_filter.1 hm
            simpa [kernel, hm'.2] using
              IMErrorSum.summand_le_kernel hx hy hM hMx hm'.1
      _ = (((dyadic M).filter (fun m ↦ roundedProduct x m = q)).card : ℝ) *
            kernel (y / (2 * M)) x q := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((q.divisors.card : ℕ) : ℝ) * kernel (y / (2 * M)) x q := by
          apply mul_le_mul_of_nonneg_right _ hkernel0
          exact_mod_cast Finset.card_le_card hsubset
      _ ≤ (A * (q : ℝ) ^ δ) * kernel (y / (2 * M)) x q := by
          apply mul_le_mul_of_nonneg_right (hA q hqpos) hkernel0
      _ = A * (q : ℝ) ^ δ * kernel (y / (2 * M)) x q := rfl

  have hqpow : ∀ q ∈ upTo (2 * x), (q : ℝ) ^ δ ≤ (2 * x) ^ δ := by
    intro q hq
    have hq' := hq
    rw [upTo, Finset.mem_Icc] at hq'
    have hqle : (q : ℝ) ≤ 2 * x :=
      (Nat.le_floor_iff (by positivity)).1 hq'.2
    exact Real.rpow_le_rpow (by positivity) hqle hδ.le

  have hgrouped :
      sawtoothErrorSum x y M ≤
        A * (2 * x) ^ δ *
          ∑ q ∈ upTo (2 * x), kernel (y / (2 * M)) x q := by
    rw [sawtoothErrorSum,
      ← Finset.sum_fiberwise_of_maps_to hmaps]
    calc
      ∑ q ∈ upTo (2 * x),
          ∑ m ∈ (dyadic M).filter (fun m ↦ roundedProduct x m = q),
            (1 + nearestIntDist (x / m) * y)⁻¹
          ≤ ∑ q ∈ upTo (2 * x),
              A * (q : ℝ) ^ δ * kernel (y / (2 * M)) x q :=
        Finset.sum_le_sum hfibre
      _ ≤ ∑ q ∈ upTo (2 * x),
              A * (2 * x) ^ δ * kernel (y / (2 * M)) x q := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hqpow q hq) hA0)
            (by dsimp [kernel]; positivity)
      _ = A * (2 * x) ^ δ *
            ∑ q ∈ upTo (2 * x), kernel (y / (2 * M)) x q := by
          rw [Finset.mul_sum]

  have hkernel := IMErrorSum.scaled_kernel_sum_le hx hy hM
  have hlog : Real.log (2 * x) ≤ (2 * x) ^ δ / δ :=
    Real.log_le_rpow_div (by positivity) hδ
  have hr : 0 ≤ M / y := by positivity
  have hkernelAbsorb :
      2 + 4 * (M / y) * (1 + Real.log (2 * x)) ≤
        B * (1 + M / y) * (2 * x) ^ δ := by
    have honeLog : 1 + Real.log (2 * x) ≤
        (1 + 1 / δ) * (2 * x) ^ δ := by
      calc
        1 + Real.log (2 * x) ≤ 1 + (2 * x) ^ δ / δ := by linarith
        _ ≤ (2 * x) ^ δ + (2 * x) ^ δ / δ := by linarith
        _ = (1 + 1 / δ) * (2 * x) ^ δ := by ring
    have hT0 : 0 ≤ (2 * x) ^ δ := by positivity
    have hlogMul :
        4 * (M / y) * (1 + Real.log (2 * x)) ≤
          4 * (M / y) * ((1 + 1 / δ) * (2 * x) ^ δ) :=
      mul_le_mul_of_nonneg_left honeLog (mul_nonneg (by norm_num) hr)
    calc
      2 + 4 * (M / y) * (1 + Real.log (2 * x))
          ≤ 2 + 4 * (M / y) * ((1 + 1 / δ) * (2 * x) ^ δ) :=
        by linarith
      _ ≤ (6 + 4 / δ) * (1 + M / y) * (2 * x) ^ δ := by
        have hinvδ : 0 ≤ 1 / δ := by positivity
        have hcoef : 4 * (1 + 1 / δ) ≤ 6 + 4 / δ := by
          calc
            4 * (1 + 1 / δ) = 4 + 4 / δ := by ring
            _ ≤ 6 + 4 / δ := by linarith
        have hrpart :
            4 * (M / y) * ((1 + 1 / δ) * (2 * x) ^ δ) ≤
              (6 + 4 / δ) * (M / y) * (2 * x) ^ δ := by
          have hcoefr := mul_le_mul_of_nonneg_right hcoef hr
          have hcoefrT := mul_le_mul_of_nonneg_right hcoefr hT0
          calc
            4 * (M / y) * ((1 + 1 / δ) * (2 * x) ^ δ) =
                (4 * (1 + 1 / δ)) * (M / y) * (2 * x) ^ δ := by ring
            _ ≤ (6 + 4 / δ) * (M / y) * (2 * x) ^ δ := hcoefrT
        have hbase : 2 ≤ (6 + 4 / δ) * (2 * x) ^ δ := by
          calc
            2 ≤ 6 + 4 / δ := by linarith
            _ = (6 + 4 / δ) * 1 := by ring
            _ ≤ (6 + 4 / δ) * (2 * x) ^ δ :=
              mul_le_mul_of_nonneg_left h2xpow (by linarith)
        calc
          2 + 4 * (M / y) * ((1 + 1 / δ) * (2 * x) ^ δ) ≤
              (6 + 4 / δ) * (2 * x) ^ δ +
                (6 + 4 / δ) * (M / y) * (2 * x) ^ δ :=
            add_le_add hbase hrpart
          _ = (6 + 4 / δ) * (1 + M / y) * (2 * x) ^ δ := by ring
      _ = B * (1 + M / y) * (2 * x) ^ δ := by rfl

  have hmain : sawtoothErrorSum x y M ≤
      A * B * (1 + M / y) * ((2 * x) ^ δ * (2 * x) ^ δ) := by
    calc
      sawtoothErrorSum x y M
          ≤ A * (2 * x) ^ δ *
              ∑ q ∈ upTo (2 * x), kernel (y / (2 * M)) x q := hgrouped
      _ ≤ A * (2 * x) ^ δ *
              (2 + 4 * (M / y) * (1 + Real.log (2 * x))) :=
        mul_le_mul_of_nonneg_left hkernel (mul_nonneg hA0 (by positivity))
      _ ≤ A * (2 * x) ^ δ *
              (B * (1 + M / y) * (2 * x) ^ δ) :=
        mul_le_mul_of_nonneg_left hkernelAbsorb (mul_nonneg hA0 (by positivity))
      _ = A * B * (1 + M / y) * ((2 * x) ^ δ * (2 * x) ^ δ) := by ring

  have hpow : (2 * x) ^ δ * (2 * x) ^ δ = (2 : ℝ) ^ ε * x ^ ε := by
    calc
      (2 * x) ^ δ * (2 * x) ^ δ = (2 * x) ^ (δ + δ) := by
        rw [← Real.rpow_add (by positivity)]
      _ = (2 * x) ^ ε := by congr 1; dsimp [δ]; ring
      _ = (2 : ℝ) ^ ε * x ^ ε := Real.mul_rpow (by positivity) (by positivity)

  calc
    sawtoothErrorSum x y M
        ≤ A * B * (1 + M / y) * ((2 * x) ^ δ * (2 * x) ^ δ) := hmain
    _ = C * (1 + M * y⁻¹) * x ^ ε := by
      rw [hpow]
      dsimp [C]
      rw [div_eq_mul_inv]
      ring

end LeanProofs.IntegerPoints

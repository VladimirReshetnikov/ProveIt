import IntegerPoints.IwaniecMozzochiErrorSum
import IntegerPoints.IwaniecMozzochiPsiDecomposition

/-!
# Iwaniec--Mozzochi Section 3: reduction from (3.2) to (2.1)

This file proves the corrected reduction `iwaniecMozzochi_reduction_eq32`.
There are two bookkeeping points which the paper suppresses in `O`-notation.

* The dyadic Fourier decomposition has a separate `H = 1 / 2` block.  Its
  estimate comes from `DeltaHalfHMBound`; the estimates for `H = 2^j` come
  from `DeltaHMBound`.
* There are `ceil (logb 2 y)` integral dyadic blocks.  We take
  `y = M * x^(-theta)` and bound this cardinality by an explicit constant
  times `x^(epsilon / 3)`.  The individual block estimates use
  `epsilon / 3`, so this logarithm does not get hidden in an implied
  constant.

The strict lower range condition `x^theta < M` implies `1 < y`; in
particular, the apparent endpoint `y = 1` never occurs in this reduction.
All constants returned by the input propositions are normalized with `max C 0`
before they are multiplied by nonnegative quantities.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

namespace IMReductionEq32

/-- Sum the pointwise Fourier-decomposition error over one dyadic `m`-block.
The equality preceding the triangle inequality also records explicitly the
interchange of the finite `m`- and `j`-sums. -/
private theorem summed_decomposition_bound
    {chi : Real → Real} {C x y M : Real} {n : Nat}
    (hpoint : ∀ t : Real,
      |sawtooth t + psiH chi (1 / 2 : Real) t +
          ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) t| ≤
        C * (1 + nearestIntDist t * y)⁻¹) :
    |deltaM x M + deltaHM chi x (1 / 2 : Real) M +
        ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
      C * sawtoothErrorSum x y M := by
  have hexact :
      (∑ m ∈ dyadic M,
          (sawtooth (x / m) + psiH chi (1 / 2 : Real) (x / m) +
            ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) (x / m))) =
        deltaM x M + deltaHM chi x (1 / 2 : Real) M +
          ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M := by
    calc
      (∑ m ∈ dyadic M,
          (sawtooth (x / m) + psiH chi (1 / 2 : Real) (x / m) +
            ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) (x / m))) =
          (∑ m ∈ dyadic M, sawtooth (x / m)) +
            (∑ m ∈ dyadic M, psiH chi (1 / 2 : Real) (x / m)) +
            ∑ m ∈ dyadic M,
              ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) (x / m) := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ m ∈ dyadic M, sawtooth (x / m)) +
            (∑ m ∈ dyadic M, psiH chi (1 / 2 : Real) (x / m)) +
            ∑ j ∈ Finset.range n,
              ∑ m ∈ dyadic M, psiH chi ((2 : Real) ^ j) (x / m) := by
                rw [Finset.sum_comm]
      _ = deltaM x M + deltaHM chi x (1 / 2 : Real) M +
            ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M := by
              rfl
  rw [← hexact]
  calc
    |∑ m ∈ dyadic M,
        (sawtooth (x / m) + psiH chi (1 / 2 : Real) (x / m) +
          ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) (x / m))| ≤
        ∑ m ∈ dyadic M,
          |sawtooth (x / m) + psiH chi (1 / 2 : Real) (x / m) +
            ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) (x / m)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ dyadic M,
          C * (1 + nearestIntDist (x / m) * y)⁻¹ :=
      Finset.sum_le_sum fun m _hm ↦ hpoint (x / m)
    _ = C * sawtoothErrorSum x y M := by
      unfold sawtoothErrorSum
      rw [Finset.mul_sum]

/-- Every integral dyadic scale in `range (ceil (logb 2 y))` lies below the
chosen Fourier cutoff `y`. -/
private theorem dyadic_scale_le_cutoff {y : Real} (hy : 0 < y) {j : Nat}
    (hj : j ∈ Finset.range ⌈Real.logb 2 y⌉₊) :
    (2 : Real) ^ j ≤ y := by
  have hjceil : j < ⌈Real.logb 2 y⌉₊ := Finset.mem_range.mp hj
  have hjlog : (j : Real) < Real.logb 2 y := (Nat.lt_ceil).mp hjceil
  have hjy : (2 : Real) ^ (j : Real) < y :=
    (Real.lt_logb_iff_rpow_lt (b := 2) (x := (j : Real)) (y := y)
      (by norm_num) hy).mp hjlog
  simpa [Real.rpow_natCast] using hjy.le

/-- An explicit small-power bound for the number of Fourier blocks.  The
slightly coarse comparison `y <= x` keeps the constant independent of the
particular dyadic block `M`. -/
private theorem ceil_logb_cutoff_le_small_power
    {x y delta : Real} (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hdelta : 0 < delta) :
    (⌈Real.logb 2 y⌉₊ : Real) ≤
      (1 + 1 / (delta * Real.log 2)) * x ^ delta := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy0 : 0 ≤ Real.logb 2 y := by
    rw [← Real.logb_one]
    exact Real.logb_le_logb_of_le (by norm_num) zero_lt_one hy
  have hceil : (⌈Real.logb 2 y⌉₊ : Real) ≤ Real.logb 2 y + 1 :=
    (Nat.ceil_lt_add_one hlogy0).le
  have hlogyx : Real.logb 2 y ≤ Real.logb 2 x :=
    Real.logb_le_logb_of_le (by norm_num) hy0 hyx
  have hlogx : Real.logb 2 x ≤ x ^ delta / (delta * Real.log 2) := by
    calc
      Real.logb 2 x = Real.log x / Real.log 2 := rfl
      _ ≤ (x ^ delta / delta) / Real.log 2 :=
        div_le_div_of_nonneg_right (Real.log_le_rpow_div hx0 hdelta) hlogtwo.le
      _ = x ^ delta / (delta * Real.log 2) := by ring
  have hxpower : 1 ≤ x ^ delta := Real.one_le_rpow hx hdelta.le
  calc
    (⌈Real.logb 2 y⌉₊ : Real) ≤ Real.logb 2 y + 1 := hceil
    _ ≤ x ^ delta / (delta * Real.log 2) + 1 :=
      by linarith [hlogyx.trans hlogx]
    _ ≤ x ^ delta / (delta * Real.log 2) + x ^ delta :=
      by linarith [hxpower]
    _ = (1 + 1 / (delta * Real.log 2)) * x ^ delta := by ring

end IMReductionEq32

open IMReductionEq32

/-- The corrected Section 3 Fourier reduction: bounds for all positive
integral dyadic blocks, together with the separate half block, imply the
dyadic sawtooth estimate (2.1). -/
theorem iwaniecMozzochi_reduction_eq32_holds :
    iwaniecMozzochi_reduction_eq32 := by
  intro chi hchi theta htheta0 hthetahalf hblocks hhalf
  unfold DeltaMBound
  intro epsilon hepsilon
  let delta : Real := epsilon / 3
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity

  obtain ⟨Cpsi, hpsi⟩ := iwaniecMozzochi_section3_psiDecomposition_holds chi hchi
  obtain ⟨Cerror, herror⟩ :=
    iwaniecMozzochi_section3_errorSumBound_holds delta hdelta
  obtain ⟨Cblocks, hblocks'⟩ := hblocks delta hdelta
  obtain ⟨Chalf, hhalf'⟩ := hhalf delta hdelta

  let A : Real := max Cpsi 0
  let E : Real := max Cerror 0
  let B : Real := max Cblocks 0
  let H : Real := max Chalf 0
  let L : Real := 1 + 1 / (delta * Real.log 2)
  have hA0 : 0 ≤ A := by simp [A]
  have hE0 : 0 ≤ E := by simp [E]
  have hB0 : 0 ≤ B := by simp [B]
  have hH0 : 0 ≤ H := by simp [H]
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity

  refine ⟨2 * A * E + H + B * L, ?_⟩
  intro x M hx hxM hMsqrt
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hx0 : 0 ≤ x := hxpos.le
  have hMpos : 0 < M := by
    have honeTheta : 1 ≤ x ^ theta := Real.one_le_rpow hx htheta0.le
    linarith
  have hMone : 1 ≤ M := by
    have honeTheta : 1 ≤ x ^ theta := Real.one_le_rpow hx htheta0.le
    linarith

  let y : Real := M * x ^ (-theta)
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  have hyone : 1 < y := by
    calc
      (1 : Real) = x ^ theta * x ^ (-theta) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      _ < M * x ^ (-theta) :=
        mul_lt_mul_of_pos_right hxM (Real.rpow_pos_of_pos hxpos _)
      _ = y := rfl
  have hyone' : 1 ≤ y := hyone.le

  have hgap : 0 < (1 : Real) / 2 - theta := by linarith
  have hygap : y < x ^ ((1 : Real) / 2 - theta) := by
    calc
      y = M * x ^ (-theta) := rfl
      _ < x ^ ((1 : Real) / 2) * x ^ (-theta) :=
        mul_lt_mul_of_pos_right hMsqrt (Real.rpow_pos_of_pos hxpos _)
      _ = x ^ ((1 : Real) / 2 - theta) := by
        rw [← Real.rpow_add hxpos]
        congr 1
  have hyx : y ≤ x := by
    calc
      y ≤ x ^ ((1 : Real) / 2 - theta) := hygap.le
      _ ≤ x ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith [hgap])
      _ = x := by simp
  have hMx : M ≤ x := by
    calc
      M ≤ x ^ ((1 : Real) / 2) := hMsqrt.le
      _ ≤ x ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := by simp

  let n : Nat := ⌈Real.logb 2 y⌉₊
  have hn : (n : Real) ≤ L * x ^ delta := by
    simpa [n, L] using
      ceil_logb_cutoff_le_small_power hx hyone' hyx hdelta

  have hpoint : ∀ t : Real,
      |sawtooth t + psiH chi (1 / 2 : Real) t +
          ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) t| ≤
        A * (1 + nearestIntDist t * y)⁻¹ := by
    intro t
    have hraw := hpsi t y hyone'
    have hterm0 : 0 ≤ (1 + nearestIntDist t * y)⁻¹ := by
      apply inv_nonneg.mpr
      have hdist : 0 ≤ nearestIntDist t := by
        unfold nearestIntDist
        positivity
      positivity
    change
      |sawtooth t + psiH chi (1 / 2 : Real) t +
          ∑ j ∈ Finset.range ⌈Real.logb 2 y⌉₊,
            psiH chi ((2 : Real) ^ j) t| ≤
        A * (1 + nearestIntDist t * y)⁻¹
    exact hraw.trans
      (mul_le_mul_of_nonneg_right (show Cpsi ≤ A by simp [A]) hterm0)

  have htotal :
      |deltaM x M + deltaHM chi x (1 / 2 : Real) M +
          ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
        A * sawtoothErrorSum x y M :=
    summed_decomposition_bound hpoint

  have hMy : M * y⁻¹ = x ^ theta := by
    rw [show y = M * x ^ (-theta) by rfl, mul_inv,
      Real.rpow_neg hx0 theta, inv_inv]
    field_simp [hMpos.ne']
  have hthetaPower : 1 ≤ x ^ theta := Real.one_le_rpow hx htheta0.le
  have herrorFactor0 :
      0 ≤ (1 + M * y⁻¹) * x ^ delta := by positivity
  have herrorRaw := herror x y M hx hyone' hMone hMx
  have herrorNormalized :
      sawtoothErrorSum x y M ≤
        E * (1 + M * y⁻¹) * x ^ delta :=
    calc
      sawtoothErrorSum x y M ≤
          Cerror * (1 + M * y⁻¹) * x ^ delta := herrorRaw
      _ = Cerror * ((1 + M * y⁻¹) * x ^ delta) := by ring
      _ ≤ E * ((1 + M * y⁻¹) * x ^ delta) :=
        mul_le_mul_of_nonneg_right (show Cerror ≤ E by simp [E]) herrorFactor0
      _ = E * (1 + M * y⁻¹) * x ^ delta := by ring
  have herrorFinal :
      sawtoothErrorSum x y M ≤ 2 * E * x ^ (theta + delta) := by
    calc
      sawtoothErrorSum x y M ≤
          E * (1 + M * y⁻¹) * x ^ delta := herrorNormalized
      _ = E * (1 + x ^ theta) * x ^ delta := by rw [hMy]
      _ ≤ E * (2 * x ^ theta) * x ^ delta := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 delta)
        apply mul_le_mul_of_nonneg_left _ hE0
        linarith
      _ = 2 * E * (x ^ theta * x ^ delta) := by ring
      _ = 2 * E * x ^ (theta + delta) := by
        rw [Real.rpow_add hxpos theta delta]

  have hhalfNormalized :
      |deltaHM chi x (1 / 2 : Real) M| ≤ H * x ^ (theta + delta) := by
    exact (hhalf' x M hx hxM hMsqrt).trans
      (mul_le_mul_of_nonneg_right (show Chalf ≤ H by simp [H])
        (Real.rpow_nonneg hx0 _))

  have hblockPoint : ∀ j ∈ Finset.range n,
      |deltaHM chi x ((2 : Real) ^ j) M| ≤
        B * x ^ (theta + delta) := by
    intro j hj
    have hjcut : (2 : Real) ^ j ≤ M * x ^ (-theta) := by
      change (2 : Real) ^ j ≤ y
      apply dyadic_scale_le_cutoff hypos
      simpa [n] using hj
    exact (hblocks' x M j hx hxM hMsqrt hjcut).trans
      (mul_le_mul_of_nonneg_right (show Cblocks ≤ B by simp [B])
        (Real.rpow_nonneg hx0 _))

  have hblockSum :
      |∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
        B * L * x ^ (theta + 2 * delta) := by
    calc
      |∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
          ∑ j ∈ Finset.range n,
            |deltaHM chi x ((2 : Real) ^ j) M| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n, B * x ^ (theta + delta) :=
        Finset.sum_le_sum hblockPoint
      _ = (n : Real) * (B * x ^ (theta + delta)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
      _ ≤ (L * x ^ delta) * (B * x ^ (theta + delta)) :=
        mul_le_mul_of_nonneg_right hn
          (mul_nonneg hB0 (Real.rpow_nonneg hx0 _))
      _ = B * L * x ^ (theta + 2 * delta) := by
        have hpowThetaDelta :
            x ^ (theta + delta) = x ^ theta * x ^ delta :=
          Real.rpow_add hxpos theta delta
        have hpowThetaTwoDelta :
            x ^ (theta + 2 * delta) =
              x ^ theta * (x ^ delta * x ^ delta) := by
          rw [show 2 * delta = delta + delta by ring,
            Real.rpow_add hxpos theta (delta + delta),
            Real.rpow_add hxpos delta delta]
        rw [hpowThetaDelta, hpowThetaTwoDelta]
        ring

  have hexponentError : theta + delta ≤ theta + epsilon := by
    dsimp [delta]
    linarith
  have hexponentBlocks : theta + 2 * delta ≤ theta + epsilon := by
    dsimp [delta]
    linarith
  have hpowError : x ^ (theta + delta) ≤ x ^ (theta + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx hexponentError
  have hpowBlocks : x ^ (theta + 2 * delta) ≤ x ^ (theta + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hx hexponentBlocks

  have htotalFinal :
      |deltaM x M + deltaHM chi x (1 / 2 : Real) M +
          ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
        (2 * A * E) * x ^ (theta + epsilon) := by
    calc
      |deltaM x M + deltaHM chi x (1 / 2 : Real) M +
          ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
          A * sawtoothErrorSum x y M := htotal
      _ ≤ A * (2 * E * x ^ (theta + delta)) :=
        mul_le_mul_of_nonneg_left herrorFinal hA0
      _ = (2 * A * E) * x ^ (theta + delta) := by ring
      _ ≤ (2 * A * E) * x ^ (theta + epsilon) :=
        mul_le_mul_of_nonneg_left hpowError (by positivity)
  have hhalfFinal :
      |deltaHM chi x (1 / 2 : Real) M| ≤ H * x ^ (theta + epsilon) :=
    hhalfNormalized.trans (mul_le_mul_of_nonneg_left hpowError hH0)
  have hblocksFinal :
      |∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
        (B * L) * x ^ (theta + epsilon) := by
    exact hblockSum.trans (mul_le_mul_of_nonneg_left hpowBlocks
      (mul_nonneg hB0 hL0))

  calc
    |deltaM x M| =
        |(deltaM x M + deltaHM chi x (1 / 2 : Real) M +
            ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M) -
          deltaHM chi x (1 / 2 : Real) M -
          ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| := by
            congr 1
            ring
    _ ≤ |deltaM x M + deltaHM chi x (1 / 2 : Real) M +
            ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| +
          |deltaHM chi x (1 / 2 : Real) M| +
          |∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| := by
      calc
        |(deltaM x M + deltaHM chi x (1 / 2 : Real) M +
              ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M) -
            deltaHM chi x (1 / 2 : Real) M -
            ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| ≤
            |(deltaM x M + deltaHM chi x (1 / 2 : Real) M +
                ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M) -
              deltaHM chi x (1 / 2 : Real) M| +
              |∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| :=
          abs_sub _ _
        _ ≤ (|deltaM x M + deltaHM chi x (1 / 2 : Real) M +
                ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| +
              |deltaHM chi x (1 / 2 : Real) M|) +
               |∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M| := by
          have htriangle := abs_sub
            (deltaM x M + deltaHM chi x (1 / 2 : Real) M +
              ∑ j ∈ Finset.range n, deltaHM chi x ((2 : Real) ^ j) M)
            (deltaHM chi x (1 / 2 : Real) M)
          linarith
        _ = _ := by ring
    _ ≤ (2 * A * E) * x ^ (theta + epsilon) +
          H * x ^ (theta + epsilon) +
          (B * L) * x ^ (theta + epsilon) :=
      add_le_add (add_le_add htotalFinal hhalfFinal) hblocksFinal
    _ = (2 * A * E + H + B * L) * x ^ (theta + epsilon) := by ring

end LeanProofs.IntegerPoints

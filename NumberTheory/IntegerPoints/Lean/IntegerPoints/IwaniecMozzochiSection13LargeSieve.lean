import IntegerPoints.IwaniecMozzochiSection13Holder
import IntegerPoints.IwaniecMozzochiSection13FactorBounds
import IntegerPoints.IwaniecMozzochiEq1313
import Mathlib.Tactic

/-!
# The missing double-large-sieve bridge in Iwaniec--Mozzochi Section 13

Bombieri--Iwaniec, *On the order of zeta (1/2 + it)*, Lemma 2.4, gives in
dimension `r` a double-large-sieve estimate with the explicit factor

`(2 * pi^2)^r * product_j (1 + X_j * Y_j)`.

After expanding the second moment in the present application, its two spacing
sums are the Farey-pair count `fareyMajorantPairCount` and the eight-variable
count `b2Count`; the coefficient weights contribute `L^(-4)`.  Neither this
application of the quoted lemma nor the required phase-coordinate bookkeeping
has yet been formalized in the repository.  Accordingly, the theorem below
takes precisely that one paper-shaped second-moment inequality as an explicit
theorem parameter.  It does not introduce an opaque proposition or assert the
analytic estimate unconditionally.

The reduction consumes the already formalized uniform forms of (13.12) and
(13.13), the literal product comparison (13.9), and the finite Holder step.  A
single resulting constant is chosen before the `Fin 8 x Fin 9` block indices.
The formal range permits arbitrary `muOne > 0`, so `C` need not be at least
one.  The elementary cardinality argument below retains the resulting
`muOne`-dependent loss instead of silently imposing the paper convention
`C \gg 1`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

noncomputable section

/-! ## Endpoint-safe cardinality for arbitrary positive `muOne` -/

/-- If `muOne < C`, the half-open denominator interval has cardinality at most
`(2 + muOne^(-1)) C`.  This is the version of the range-cardinality estimate
which remains valid when the formal parameter `muOne` is smaller than one. -/
private theorem section13_fareyDenominators_card_le_muOne
    {muOne C : ℝ} (hmuOne : 0 < muOne) (hmuC : muOne < C) :
    ((fareyDenominators C).card : ℝ) ≤ (2 + 1 / muOne) * C := by
  have hC : 0 < C := hmuOne.trans hmuC
  have hceilUpper : (⌈2 * C⌉₊ : ℝ) < 2 * C + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsub : ⌈2 * C⌉₊ - ⌈C⌉₊ ≤ ⌈2 * C⌉₊ := Nat.sub_le _ _
  have hone : 1 ≤ C / muOne :=
    (one_le_div₀ hmuOne).2 hmuC.le
  unfold fareyDenominators
  rw [Nat.card_Ico]
  calc
    ((⌈2 * C⌉₊ - ⌈C⌉₊ : ℕ) : ℝ) ≤ (⌈2 * C⌉₊ : ℝ) := by
      exact_mod_cast hsub
    _ ≤ 2 * C + 1 := hceilUpper.le
    _ ≤ 2 * C + C / muOne := by
      simpa only [add_comm] using add_le_add_left hone (2 * C)
    _ = (2 + 1 / muOne) * C := by ring

/-- The exact coprime index set has a `muOne`-uniform paper-shaped cardinality
bound as soon as `muOne < C`. -/
private theorem section13BigBIndexSet_card_le_muOne
    {A C muOne : ℝ} (hA : 0 ≤ A) (hmuOne : 0 < muOne)
    (hmuC : muOne < C) :
    ((section13BigBIndexSet A C).card : ℝ) ≤
      (2 * (2 + 1 / muOne)) * A * C := by
  classical
  have hsubset :
      section13BigBIndexSet A C ⊆
        fareyMajorantNumerators A ×ˢ fareyDenominators C := by
    unfold section13BigBIndexSet
    exact Finset.filter_subset _ _
  have hcardNat := Finset.card_le_card hsubset
  have hnum := eq1312_fareyMajorantNumerators_card_le hA
  have hden := section13_fareyDenominators_card_le_muOne hmuOne hmuC
  calc
    ((section13BigBIndexSet A C).card : ℝ) ≤
        ((fareyMajorantNumerators A ×ˢ fareyDenominators C).card : ℝ) := by
      exact_mod_cast hcardNat
    _ = ((fareyMajorantNumerators A).card : ℝ) *
        ((fareyDenominators C).card : ℝ) := by simp
    _ ≤ (2 * A) * ((2 + 1 / muOne) * C) :=
      mul_le_mul hnum hden (Nat.cast_nonneg _) (by positivity)
    _ = (2 * (2 + 1 / muOne)) * A * C := by ring

/-- The finite Holder bound with the honest cardinality constant available
from the formal short-denominator hypothesis. -/
private theorem section13_bigB_fourth_le_muOne_mul_secondMoment_sq
    {x G A C K L t₁ t₂ muOne : ℝ}
    (hA : 0 ≤ A) (hmuOne : 0 < muOne) (hmuC : muOne < C) :
    bigB x G A C K L t₁ t₂ ^ 4 ≤
      (2 * (2 + 1 / muOne)) ^ 2 * G ^ 4 * A ^ 2 / C ^ 2 *
        section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := by
  have hC : 0 < C := hmuOne.trans hmuC
  have hcard := section13BigBIndexSet_card_le_muOne hA hmuOne hmuC
  have hcardSq : ((section13BigBIndexSet A C).card : ℝ) ^ 2 ≤
      ((2 * (2 + 1 / muOne)) * A * C) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have hfactor : 0 ≤ (G / C) ^ 4 := by positivity
  have hmoment : 0 ≤ section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 :=
    sq_nonneg _
  calc
    bigB x G A C K L t₁ t₂ ^ 4 ≤
        (G / C) ^ 4 * ((section13BigBIndexSet A C).card : ℝ) ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 :=
      section13_bigB_fourth_le_indexCard_sq_mul_secondMoment_sq
        x G A C K L t₁ t₂
    _ ≤ (G / C) ^ 4 *
          ((2 * (2 + 1 / muOne)) * A * C) ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardSq hfactor) hmoment
    _ = (2 * (2 + 1 / muOne)) ^ 2 * G ^ 4 * A ^ 2 / C ^ 2 *
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 := by
      field_simp [hC.ne']

/-! ## Exact monomial bookkeeping -/

/-- Exact algebra behind the first line of the final display in Section 13.
The two real-power epsilon factors are deliberately left separate. -/
private theorem section13_largeSieve_monomial_identity
    {x A C H N M G K L eta : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) (_hH : 0 < H)
    (_hN : 0 < N) (_hM : 0 < M) (hK : 0 < K) (hL : 0 < L) :
    G ^ 4 * A ^ 2 / C ^ 2 *
        ((L ^ 4)⁻¹ *
          (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) *
          (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * N ^ (-(5 : ℝ)) * M ^ 7 *
            (A * C) ^ (1 + eta)) *
          (K * L) ^ (2 + eta)) =
      (G ^ 4 * A ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) * H⁻¹ *
          N ^ (-(5 : ℝ)) * M ^ 7 * K ^ 3 * L ^ 2 * x ^ (-(3 : ℝ) / 2)) *
        (A * C) ^ eta * (K * L) ^ eta := by
  have hAC : 0 < A * C := mul_pos hA hC
  have hKL : 0 < K * L := mul_pos hK hL
  have hACeta : (A * C) ^ (1 + eta) = (A * C) * (A * C) ^ eta := by
    rw [Real.rpow_add hAC, Real.rpow_one]
  have hKLeta : (K * L) ^ (2 + eta) = (K * L) ^ 2 * (K * L) ^ eta := by
    rw [Real.rpow_add hKL, Real.rpow_two]
  have hxcombine : x ^ ((1 : ℝ) / 2) * x ^ (-(2 : ℝ)) =
      x ^ (-(3 : ℝ) / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hAcombine : A ^ 2 * A ^ (-(3 : ℝ) / 2) * A =
      A ^ ((3 : ℝ) / 2) := by
    have hAneg : 0 < A ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hA _
    have hAright : 0 < A ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hA _
    apply Real.log_injOn_pos
      (Set.mem_Ioi.2 (mul_pos (mul_pos (pow_pos hA 2) hAneg) hA))
      (Set.mem_Ioi.2 hAright)
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero 2 hA.ne') hAneg.ne') hA.ne',
      Real.log_mul (pow_ne_zero 2 hA.ne') hAneg.ne', Real.log_pow,
      Real.log_rpow hA, Real.log_rpow hA]
    ring
  have hCcombine : (C ^ 2)⁻¹ * C ^ (-(3 : ℝ) / 2) * C⁻¹ * C =
      C ^ (-(7 : ℝ) / 2) := by
    have hC2inv : 0 < (C ^ 2)⁻¹ := inv_pos.2 (pow_pos hC 2)
    have hCneg : 0 < C ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hC _
    have hCinv : 0 < C⁻¹ := inv_pos.2 hC
    have hCright : 0 < C ^ (-(7 : ℝ) / 2) := Real.rpow_pos_of_pos hC _
    apply Real.log_injOn_pos
      (Set.mem_Ioi.2 (mul_pos (mul_pos (mul_pos hC2inv hCneg) hCinv) hC))
      (Set.mem_Ioi.2 hCright)
    rw [Real.log_mul
        (mul_ne_zero (mul_ne_zero hC2inv.ne' hCneg.ne') hCinv.ne') hC.ne',
      Real.log_mul (mul_ne_zero hC2inv.ne' hCneg.ne') hCinv.ne',
      Real.log_mul hC2inv.ne' hCneg.ne', Real.log_inv, Real.log_pow,
      Real.log_rpow hC, Real.log_inv, Real.log_rpow hC]
    ring
  have hACbase :
      A ^ 2 / C ^ 2 * (A * C) ^ (-(3 : ℝ) / 2) * C⁻¹ * (A * C) =
        A ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) := by
    rw [Real.mul_rpow hA.le hC.le, div_eq_mul_inv]
    calc
      A ^ 2 * (C ^ 2)⁻¹ *
            (A ^ (-(3 : ℝ) / 2) * C ^ (-(3 : ℝ) / 2)) * C⁻¹ * (A * C) =
          (A ^ 2 * A ^ (-(3 : ℝ) / 2) * A) *
            ((C ^ 2)⁻¹ * C ^ (-(3 : ℝ) / 2) * C⁻¹ * C) := by ring
      _ = A ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) := by
        rw [hAcombine, hCcombine]
  have hLcancel : (L ^ 4)⁻¹ * L ^ 4 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 4 hL.ne')
  have hKproduct : K * (K * L) ^ 2 = K ^ 3 * L ^ 2 := by ring
  rw [hACeta, hKLeta]
  calc
    G ^ 4 * A ^ 2 / C ^ 2 *
          ((L ^ 4)⁻¹ *
            (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) *
            (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * N ^ (-(5 : ℝ)) * M ^ 7 *
              ((A * C) * (A * C) ^ eta)) *
            ((K * L) ^ 2 * (K * L) ^ eta)) =
        G ^ 4 *
          (A ^ 2 / C ^ 2 * (A * C) ^ (-(3 : ℝ) / 2) * C⁻¹ * (A * C)) *
          H⁻¹ * N ^ (-(5 : ℝ)) * M ^ 7 *
          ((L ^ 4)⁻¹ * L ^ 4) * (K * (K * L) ^ 2) *
          (x ^ ((1 : ℝ) / 2) * x ^ (-(2 : ℝ))) *
          (A * C) ^ eta * (K * L) ^ eta := by ring
    _ = (G ^ 4 * A ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) * H⁻¹ *
          N ^ (-(5 : ℝ)) * M ^ 7 * K ^ 3 * L ^ 2 * x ^ (-(3 : ℝ) / 2)) *
        (A * C) ^ eta * (K * L) ^ eta := by
      rw [hACbase, hLcancel, hKproduct, hxcombine]
      ring

/-- The same identity with the five scale-independent constants left in the
form in which the analytic estimates produce them. -/
private theorem section13_largeSieve_algebra
    {x A C H N M G K L eta q d p u v : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C) (hH : 0 < H)
    (hN : 0 < N) (hM : 0 < M) (hK : 0 < K) (hL : 0 < L) :
    (q * G ^ 4 * A ^ 2 / C ^ 2) *
        (d * (L ^ 4)⁻¹ *
          (p * (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4)) *
          (u * (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * N ^ (-(5 : ℝ)) * M ^ 7 *
            (A * C) ^ (1 + eta))) *
          (v * (K * L) ^ (2 + eta))) =
      (q * d * p * u * v) *
        (G ^ 4 * A ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) * H⁻¹ *
          N ^ (-(5 : ℝ)) * M ^ 7 * K ^ 3 * L ^ 2 * x ^ (-(3 : ℝ) / 2)) *
        (A * C) ^ eta * (K * L) ^ eta := by
  calc
    (q * G ^ 4 * A ^ 2 / C ^ 2) *
          (d * (L ^ 4)⁻¹ *
            (p * (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4)) *
            (u * (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * N ^ (-(5 : ℝ)) * M ^ 7 *
              (A * C) ^ (1 + eta))) *
            (v * (K * L) ^ (2 + eta))) =
        (q * d * p * u * v) *
          (G ^ 4 * A ^ 2 / C ^ 2 *
            ((L ^ 4)⁻¹ *
              (x ^ ((1 : ℝ) / 2) * (A * C) ^ (-(3 : ℝ) / 2) * K * L ^ 4) *
              (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * N ^ (-(5 : ℝ)) * M ^ 7 *
                (A * C) ^ (1 + eta)) *
              (K * L) ^ (2 + eta))) := by ring
    _ = (q * d * p * u * v) *
        (G ^ 4 * A ^ ((3 : ℝ) / 2) * C ^ (-(7 : ℝ) / 2) * H⁻¹ *
          N ^ (-(5 : ℝ)) * M ^ 7 * K ^ 3 * L ^ 2 * x ^ (-(3 : ℝ) / 2)) *
        (A * C) ^ eta * (K * L) ^ eta := by
      rw [section13_largeSieve_monomial_identity hx hA hC hH hN hM hK hL]
      ring

/-! ## Uniform elementary scale bounds for the 72 blocks -/

/-- Crude polynomial upper bounds sufficient to absorb the two epsilon losses.
The powers are intentionally generous; only their uniformity matters. -/
private theorem section13_block_epsilon_scale_bounds
    {x C H M : ℝ} (jK : Fin 8) (jL : Fin 9)
    (hmain : InMainRange x H M) (hC : 0 < C) (hCH : C ≤ H) :
    Ascale x C M * C ≤ x ^ 3 ∧
      section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL ≤
        16384 * x ^ 5 := by
  rcases hmain with ⟨hx, hxM, hMx, hH, hHupper, hHlower, hHlower2, hMlower⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have htheta0 : 0 ≤ theta0 := by norm_num [theta0]
  have hxTheta : 1 ≤ x ^ theta0 := Real.one_le_rpow hx htheta0
  have hMone : 1 ≤ M := hxTheta.trans hxM.le
  have hM0 : 0 < M := zero_lt_one.trans_le hMone
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hxNegTheta : x ^ (-theta0) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num [theta0])
  have hHleM : H ≤ M := by
    calc
      H ≤ M * x ^ (-theta0) := hHupper
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hxNegTheta hM0.le
      _ = M := by ring
  have hxHalfLe : x ^ ((1 : ℝ) / 2) ≤ x := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) / 2 ≤ 1))
  have hMleX : M ≤ x := hMx.le.trans hxHalfLe
  have hHleX : H ≤ x := hHleM.trans hMleX
  have hCleX : C ≤ x := hCH.trans hHleX
  rcases section13_namedScales_pos hx0 hC hH0 hM0 with
    ⟨hN0, _hG0, hA0, hK0, hL0, _hX0⟩
  have hxNegThree : x ^ (-(3 : ℝ) / 11) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hNleM : shiftLength x M ≤ M := by
    rw [shiftLength_eq_mul_rpow]
    calc
      M * x ^ (-(3 : ℝ) / 11) ≤ M * 1 :=
        mul_le_mul_of_nonneg_left hxNegThree hM0.le
      _ = M := by ring
  have hMtwoOne : 1 ≤ M ^ 2 := one_le_pow₀ hMone
  have hAleXC : Ascale x C M ≤ x * C := by
    unfold Ascale
    apply (div_le_iff₀ (pow_pos hM0 2)).2
    exact le_mul_of_one_le_right (mul_nonneg hx0.le hC.le) hMtwoOne
  have hAleX2 : Ascale x C M ≤ x ^ 2 := by
    calc
      Ascale x C M ≤ x * C := hAleXC
      _ ≤ x * x := mul_le_mul_of_nonneg_left hCleX hx0.le
      _ = x ^ 2 := by ring
  have hACbound : Ascale x C M * C ≤ x ^ 3 := by
    calc
      Ascale x C M * C ≤ x ^ 2 * x :=
        mul_le_mul hAleX2 hCleX hC.le (sq_nonneg x)
      _ = x ^ 3 := by ring
  have hNtwoMtwo : shiftLength x M ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ hN0.le hNleM 2
  have hMtwoMthree : M ^ 2 ≤ M ^ 3 := by
    calc
      M ^ 2 = M ^ 2 * 1 := by ring
      _ ≤ M ^ 2 * M := mul_le_mul_of_nonneg_left hMone (sq_nonneg M)
      _ = M ^ 3 := by ring
  have hNtwoMthree : shiftLength x M ^ 2 ≤ M ^ 3 :=
    hNtwoMtwo.trans hMtwoMthree
  have hKleXC : Kscale x C M ≤ x * C := by
    unfold Kscale
    apply (div_le_iff₀ (pow_pos hM0 3)).2
    exact mul_le_mul_of_nonneg_left hNtwoMthree
      (mul_nonneg hx0.le hC.le)
  have hKleX2 : Kscale x C M ≤ x ^ 2 := by
    calc
      Kscale x C M ≤ x * C := hKleXC
      _ ≤ x * x := mul_le_mul_of_nonneg_left hCleX hx0.le
      _ = x ^ 2 := by ring
  have hMleMthree : M ≤ M ^ 3 := le_self_pow₀ hMone (by norm_num)
  have hNleMthree : shiftLength x M ≤ M ^ 3 := hNleM.trans hMleMthree
  have hLleXCH : Lscale x C H M ≤ x * C * H := by
    unfold Lscale
    apply (div_le_iff₀ (pow_pos hM0 3)).2
    exact mul_le_mul_of_nonneg_left hNleMthree
      (mul_nonneg (mul_nonneg hx0.le hC.le) hH0.le)
  have hLleX3 : Lscale x C H M ≤ x ^ 3 := by
    calc
      Lscale x C H M ≤ x * C * H := hLleXCH
      _ ≤ x * x * x := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hCleX hx0.le) hHleX hH0.le (by positivity)
      _ = x ^ 3 := by ring
  have hKbUpper : section12KBlockScale (Kscale x C M) jK ≤
      128 * Kscale x C M := section12KBlockScale_upper hK0.le jK
  have hLbUpper : section12LBlockScale (Lscale x C H M) jL ≤
      128 * Lscale x C H M := section12LBlockScale_upper hL0.le jL
  have hKb0 : 0 < section12KBlockScale (Kscale x C M) jK := by
    unfold section12KBlockScale
    positivity
  have hLb0 : 0 < section12LBlockScale (Lscale x C H M) jL := by
    unfold section12LBlockScale
    positivity
  have hblockProduct :
      section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL ≤
        16384 * x ^ 5 := by
    calc
      section12KBlockScale (Kscale x C M) jK *
            section12LBlockScale (Lscale x C H M) jL ≤
          (128 * Kscale x C M) * (128 * Lscale x C H M) :=
        mul_le_mul hKbUpper hLbUpper hLb0.le (by positivity)
      _ ≤ (128 * x ^ 2) * (128 * x ^ 3) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hKleX2 (by norm_num))
          (mul_le_mul_of_nonneg_left hLleX3 (by norm_num))
          (by positivity) (by positivity)
      _ = 16384 * x ^ 5 := by ring
  exact ⟨hACbound, hblockProduct⟩

/-- The block version of the exact Section 13 core scale loses only the fixed
factor `128^5` from the finite comparable-block cover. -/
private theorem section13_block_core_scale_le
    {x C H M : ℝ} (jK : Fin 8) (jL : Fin 9)
    (hmain : InMainRange x H M) (hC : 0 < C) (hCH : C ≤ H) :
    Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
        C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
        section12KBlockScale (Kscale x C M) jK ^ 3 *
        section12LBlockScale (Lscale x C H M) jL ^ 2 *
        x ^ (-(3 : ℝ) / 2) ≤
      128 ^ 5 * x ^ ((14 : ℝ) / 11) := by
  rcases section13_namedScales_pos_of_mainRange hmain hC with
    ⟨_hN0, _hG0, _hA0, hK0, hL0, _hX0⟩
  have hKbUpper : section12KBlockScale (Kscale x C M) jK ≤
      128 * Kscale x C M := section12KBlockScale_upper hK0.le jK
  have hLbUpper : section12LBlockScale (Lscale x C H M) jL ≤
      128 * Lscale x C H M := section12LBlockScale_upper hL0.le jL
  have hKb0 : 0 < section12KBlockScale (Kscale x C M) jK := by
    unfold section12KBlockScale
    positivity
  have hLb0 : 0 < section12LBlockScale (Lscale x C H M) jL := by
    unfold section12LBlockScale
    positivity
  have hKbPow : section12KBlockScale (Kscale x C M) jK ^ 3 ≤
      (128 * Kscale x C M) ^ 3 :=
    pow_le_pow_left₀ hKb0.le hKbUpper 3
  have hLbPow : section12LBlockScale (Lscale x C H M) jL ^ 2 ≤
      (128 * Lscale x C H M) ^ 2 :=
    pow_le_pow_left₀ hLb0.le hLbUpper 2
  have hx0 : 0 < x := zero_lt_one.trans_le hmain.1
  have hH0 : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM0 : 0 < M :=
    (Real.rpow_pos_of_pos hx0 theta0).trans hmain.2.1
  have htransport :
      Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
          C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
          section12KBlockScale (Kscale x C M) jK ^ 3 *
          section12LBlockScale (Lscale x C H M) jL ^ 2 *
          x ^ (-(3 : ℝ) / 2) ≤
        128 ^ 5 *
          (Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
            C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
            Kscale x C M ^ 3 * Lscale x C H M ^ 2 *
            x ^ (-(3 : ℝ) / 2)) := by
    calc
      Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
            C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
            section12KBlockScale (Kscale x C M) jK ^ 3 *
            section12LBlockScale (Lscale x C H M) jL ^ 2 *
            x ^ (-(3 : ℝ) / 2) ≤
          Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
            C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
            (128 * Kscale x C M) ^ 3 * (128 * Lscale x C H M) ^ 2 *
            x ^ (-(3 : ℝ) / 2) := by
        gcongr
      _ = 128 ^ 5 *
          (Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
            C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
            Kscale x C M ^ 3 * Lscale x C H M ^ 2 *
            x ^ (-(3 : ℝ) / 2)) := by ring
  exact htransport.trans <| mul_le_mul_of_nonneg_left
    (section13_core_scale_le_fourteen_elevenths hmain hC hCH) (by norm_num)

/-- The complete elementary scale absorption, including both epsilon factors,
uniformly over all 72 blocks. -/
private theorem section13_block_scale_with_epsilon_le
    {x C H M eta : ℝ} (jK : Fin 8) (jL : Fin 9)
    (hmain : InMainRange x H M) (hC : 0 < C) (hCH : C ≤ H)
    (heta : 0 ≤ eta) :
    (Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
        C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
        section12KBlockScale (Kscale x C M) jK ^ 3 *
        section12LBlockScale (Lscale x C H M) jL ^ 2 *
        x ^ (-(3 : ℝ) / 2)) *
      (Ascale x C M * C) ^ eta *
      (section12KBlockScale (Kscale x C M) jK *
        section12LBlockScale (Lscale x C H M) jL) ^ eta ≤
    (128 ^ 5 * 16384 ^ eta) * x ^ ((14 : ℝ) / 11 + 8 * eta) := by
  have hx : 1 ≤ x := hmain.1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hcore := section13_block_core_scale_le jK jL hmain hC hCH
  rcases section13_block_epsilon_scale_bounds jK jL hmain hC hCH with
    ⟨hAC, hKL⟩
  rcases section13_namedScales_pos_of_mainRange hmain hC with
    ⟨_hN0, _hG0, hA0, hK0, hL0, _hX0⟩
  have hAC0 : 0 ≤ Ascale x C M * C := (mul_pos hA0 hC).le
  have hKL0 : 0 ≤ section12KBlockScale (Kscale x C M) jK *
      section12LBlockScale (Lscale x C H M) jL :=
    mul_nonneg (section12KBlockScale_nonneg hK0.le jK)
      (section12LBlockScale_nonneg hL0.le jL)
  have hACpow : (Ascale x C M * C) ^ eta ≤ x ^ (3 * eta) := by
    calc
      (Ascale x C M * C) ^ eta ≤ (x ^ 3) ^ eta :=
        Real.rpow_le_rpow hAC0 hAC heta
      _ = x ^ (3 * eta) := by
        rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le]
        norm_num
  have hKLpow :
      (section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL) ^ eta ≤
        16384 ^ eta * x ^ (5 * eta) := by
    calc
      (section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL) ^ eta ≤
          (16384 * x ^ 5) ^ eta := Real.rpow_le_rpow hKL0 hKL heta
      _ = 16384 ^ eta * (x ^ 5) ^ eta :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ = 16384 ^ eta * x ^ (5 * eta) := by
        rw [← Real.rpow_natCast x 5, ← Real.rpow_mul hx0.le]
        norm_num
  have hxcombine :
      x ^ ((14 : ℝ) / 11) * x ^ (3 * eta) * x ^ (5 * eta) =
        x ^ ((14 : ℝ) / 11 + 8 * eta) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    (Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
          C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
          section12KBlockScale (Kscale x C M) jK ^ 3 *
          section12LBlockScale (Lscale x C H M) jL ^ 2 *
          x ^ (-(3 : ℝ) / 2)) *
        (Ascale x C M * C) ^ eta *
        (section12KBlockScale (Kscale x C M) jK *
          section12LBlockScale (Lscale x C H M) jL) ^ eta ≤
      (128 ^ 5 * x ^ ((14 : ℝ) / 11)) * x ^ (3 * eta) *
        (16384 ^ eta * x ^ (5 * eta)) := by
      gcongr
    _ = (128 ^ 5 * 16384 ^ eta) * x ^ ((14 : ℝ) / 11 + 8 * eta) := by
      rw [← hxcombine]
      ring

/-! ## Conditional completion of the Section 13 block estimate -/

/-- The exact quoted double-large-sieve application, together with the
already formalized uniform forms of (13.12) and (13.13), implies the public
72-block Section 13 bound.

The first hypothesis is deliberately an inline theorem parameter.  Its
constants `mu` and `D` are absolute: they are chosen before every scale,
Mellin parameter, and finite block index. -/
theorem iwaniecMozzochi_section13_bigBBound_of_doubleLargeSieve_of_eq1312_of_eq1313
    (hDoubleLargeSieve :
      ∃ mu D : ℝ, 0 < mu ∧ 0 < D ∧
        ∀ x A C K L t₁ t₂ : ℝ,
          0 < x → 0 < A → 0 < C → 0 < K → 0 < L →
          section13BigBSecondMoment x A C K L t₁ t₂ ^ 2 ≤
            D * (L ^ 4)⁻¹ * section13LargeSieveProduct x A C K L *
              (fareyMajorantPairCount
                (mu / (K * L))
                (mu * x ^ (-(1 : ℝ) / 4) * (A * C) ^ ((3 : ℝ) / 4) *
                  K ^ (-(1 : ℝ) / 2) / L)
                A C : ℝ) *
              (b2Count mu (section13XScale x A C) (section13XScale x A C)
                K L : ℝ))
    (h1312 : iwaniecMozzochi_eq1312)
    (h1313 : iwaniecMozzochi_eq1313) :
    iwaniecMozzochi_section13_bigBBound := by
  obtain ⟨mu, D, hmu, hD, hDoubleLargeSieve⟩ := hDoubleLargeSieve
  unfold iwaniecMozzochi_eq1312 at h1312
  unfold iwaniecMozzochi_eq1313 at h1313
  unfold iwaniecMozzochi_section13_bigBBound
  intro muOne epsilon hmuOne hepsilon
  let eta : ℝ := epsilon / 8
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨CpairRaw, hpairRaw⟩ := h1312 muOne mu eta hmuOne hmu heta
  obtain ⟨CtupleRaw, htupleRaw⟩ := h1313 muOne mu eta hmuOne hmu heta
  let Cpair : ℝ := max CpairRaw 0
  let Ctuple : ℝ := max CtupleRaw 0
  let qHolder : ℝ := (2 * (2 + 1 / muOne)) ^ 2
  let qProduct : ℝ := 33 * (1 + 2 / muOne) ^ 2 * (1 + 2 / muOne ^ 2)
  let Cfour : ℝ :=
    qHolder * D * qProduct * Cpair * Ctuple * 128 ^ 5 * 16384 ^ eta
  let R : ℝ := max Cfour 1
  refine ⟨72 * R, ?_⟩
  intro x C H M t₁ t₂ hmain hshort hCH
  have hx : 1 ≤ x := hmain.1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hGbounds := iwaniecMozzochi_eq66_holds x H M hmain
  have hG0 : 0 < Gscale x H M := zero_lt_one.trans_le hGbounds.1
  have hmuC : muOne < C := by
    calc
      muOne ≤ muOne * Gscale x H M := by
        calc
          muOne = muOne * 1 := by ring
          _ ≤ muOne * Gscale x H M :=
            mul_le_mul_of_nonneg_left hGbounds.1 hmuOne.le
      _ < C := hshort
  have hC0 : 0 < C := hmuOne.trans hmuC
  rcases section13_namedScales_pos_of_mainRange hmain hC0 with
    ⟨hN0, _hGnamed, hA0, hKbase0, hLbase0, hX0⟩
  have hH0 : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM0 : 0 < M := (Real.rpow_pos_of_pos hx0 theta0).trans hmain.2.1
  have hCpair0 : 0 ≤ Cpair := by simp [Cpair]
  have hCtuple0 : 0 ≤ Ctuple := by simp [Ctuple]
  have hqHolder0 : 0 ≤ qHolder := by
    dsimp [qHolder]
    exact sq_nonneg _
  have hqProduct0 : 0 ≤ qProduct := by
    dsimp [qProduct]
    positivity
  have hCfour0 : 0 ≤ Cfour := by
    dsimp [Cfour]
    positivity
  have hanalyticCoefficient0 :
      0 ≤ qHolder * D * qProduct * Cpair * Ctuple := by
    positivity
  have hRone : 1 ≤ R := by simp [R]
  have hR0 : 0 ≤ R := zero_le_one.trans hRone
  have hblocks : ∀ jK : Fin 8, ∀ jL : Fin 9,
      bigB x (Gscale x H M) (Ascale x C M) C
          (section12KBlockScale (Kscale x C M) jK)
          (section12LBlockScale (Lscale x C H M) jL) t₁ t₂ ≤
        R * x ^ (theta0 + epsilon) := by
    intro jK jL
    let Kb : ℝ := section12KBlockScale (Kscale x C M) jK
    let Lb : ℝ := section12LBlockScale (Lscale x C H M) jL
    have hKb0 : 0 < Kb := by
      dsimp [Kb, section12KBlockScale]
      positivity
    have hLb0 : 0 < Lb := by
      dsimp [Lb, section12LBlockScale]
      positivity
    have hpairTarget0 : 0 ≤
        x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
          (Ascale x C M * C) ^ (1 + eta) := by positivity
    have htupleTarget0 : 0 ≤ (Kb * Lb) ^ (2 + eta) :=
      Real.rpow_nonneg (mul_nonneg hKb0.le hLb0.le) _
    have hpair :
        (fareyMajorantPairCount
          (mu / (Kb * Lb))
          (mu * x ^ (-(1 : ℝ) / 4) *
            (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
            Kb ^ (-(1 : ℝ) / 2) / Lb)
          (Ascale x C M) C : ℝ) ≤
        Cpair *
          (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) *
            M ^ 7 * (Ascale x C M * C) ^ (1 + eta)) := by
      have hraw := hpairRaw x C H M jK jL hmain hshort hCH
      have hnormalized := hraw.trans <|
        mul_le_mul_of_nonneg_right (le_max_left CpairRaw 0) hpairTarget0
      simpa only [Kb, Lb, Cpair] using hnormalized
    have htuple :
        (b2Count mu (section13XScale x (Ascale x C M) C)
          (section13XScale x (Ascale x C M) C) Kb Lb : ℝ) ≤
        Ctuple * (Kb * Lb) ^ (2 + eta) := by
      have hraw := htupleRaw x C H M jK jL hmain hshort hCH
      have hnormalized := hraw.trans <|
        mul_le_mul_of_nonneg_right (le_max_left CtupleRaw 0) htupleTarget0
      simpa only [Kb, Lb, Ctuple, section13XScale] using hnormalized
    have hproduct :
        section13LargeSieveProduct x (Ascale x C M) C Kb Lb ≤
          qProduct *
            (x ^ ((1 : ℝ) / 2) *
              (Ascale x C M * C) ^ (-(3 : ℝ) / 2) * Kb * Lb ^ 4) := by
      simpa only [Kb, Lb, qProduct] using
        section13_block_largeSieveProduct_le_muOne
          jK jL hmuOne hmain hshort hCH
    have hmomentRaw :=
      hDoubleLargeSieve x (Ascale x C M) C Kb Lb t₁ t₂
        hx0 hA0 hC0 hKb0 hLb0
    have hmoment :
        section13BigBSecondMoment x (Ascale x C M) C Kb Lb t₁ t₂ ^ 2 ≤
          D * (Lb ^ 4)⁻¹ *
            (qProduct *
              (x ^ ((1 : ℝ) / 2) *
                (Ascale x C M * C) ^ (-(3 : ℝ) / 2) * Kb * Lb ^ 4)) *
            (Cpair *
              (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) *
                M ^ 7 * (Ascale x C M * C) ^ (1 + eta))) *
            (Ctuple * (Kb * Lb) ^ (2 + eta)) := by
      calc
        section13BigBSecondMoment x (Ascale x C M) C Kb Lb t₁ t₂ ^ 2 ≤
            D * (Lb ^ 4)⁻¹ * section13LargeSieveProduct x (Ascale x C M) C Kb Lb *
              (fareyMajorantPairCount
                (mu / (Kb * Lb))
                (mu * x ^ (-(1 : ℝ) / 4) *
                  (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
                  Kb ^ (-(1 : ℝ) / 2) / Lb)
                (Ascale x C M) C : ℝ) *
              (b2Count mu (section13XScale x (Ascale x C M) C)
                (section13XScale x (Ascale x C M) C) Kb Lb : ℝ) := hmomentRaw
        _ ≤ D * (Lb ^ 4)⁻¹ *
              (qProduct *
                (x ^ ((1 : ℝ) / 2) *
                  (Ascale x C M * C) ^ (-(3 : ℝ) / 2) * Kb * Lb ^ 4)) *
              (Cpair *
                (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) *
                  M ^ 7 * (Ascale x C M * C) ^ (1 + eta))) *
              (Ctuple * (Kb * Lb) ^ (2 + eta)) := by
          gcongr
    have hholder :=
      section13_bigB_fourth_le_muOne_mul_secondMoment_sq
        (x := x) (G := Gscale x H M) (A := Ascale x C M) (C := C)
        (K := Kb) (L := Lb) (t₁ := t₁) (t₂ := t₂)
        hA0.le hmuOne hmuC
    have hprefix0 : 0 ≤
        qHolder * Gscale x H M ^ 4 * Ascale x C M ^ 2 / C ^ 2 := by
      dsimp [qHolder]
      positivity
    have hscale :=
      section13_block_scale_with_epsilon_le
        jK jL hmain hC0 hCH heta.le
    have hfourth :
        bigB x (Gscale x H M) (Ascale x C M) C Kb Lb t₁ t₂ ^ 4 ≤
          Cfour * x ^ ((14 : ℝ) / 11 + epsilon) := by
      calc
        bigB x (Gscale x H M) (Ascale x C M) C Kb Lb t₁ t₂ ^ 4 ≤
            (qHolder * Gscale x H M ^ 4 * Ascale x C M ^ 2 / C ^ 2) *
              section13BigBSecondMoment x (Ascale x C M) C Kb Lb t₁ t₂ ^ 2 := by
          simpa only [qHolder] using hholder
        _ ≤ (qHolder * Gscale x H M ^ 4 * Ascale x C M ^ 2 / C ^ 2) *
            (D * (Lb ^ 4)⁻¹ *
              (qProduct *
                (x ^ ((1 : ℝ) / 2) *
                  (Ascale x C M * C) ^ (-(3 : ℝ) / 2) * Kb * Lb ^ 4)) *
              (Cpair *
                (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) *
                  M ^ 7 * (Ascale x C M * C) ^ (1 + eta))) *
              (Ctuple * (Kb * Lb) ^ (2 + eta))) :=
          mul_le_mul_of_nonneg_left hmoment hprefix0
        _ = (qHolder * D * qProduct * Cpair * Ctuple) *
            (Gscale x H M ^ 4 * Ascale x C M ^ ((3 : ℝ) / 2) *
              C ^ (-(7 : ℝ) / 2) * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
              Kb ^ 3 * Lb ^ 2 * x ^ (-(3 : ℝ) / 2)) *
            (Ascale x C M * C) ^ eta * (Kb * Lb) ^ eta := by
          exact section13_largeSieve_algebra
            hx0 hA0 hC0 hH0 hN0 hM0 hKb0 hLb0
        _ ≤ (qHolder * D * qProduct * Cpair * Ctuple) *
            ((128 ^ 5 * 16384 ^ eta) *
              x ^ ((14 : ℝ) / 11 + 8 * eta)) := by
          simpa only [Kb, Lb, mul_assoc] using
            mul_le_mul_of_nonneg_left
              (a := qHolder * D * qProduct * Cpair * Ctuple)
              hscale hanalyticCoefficient0
        _ = Cfour * x ^ ((14 : ℝ) / 11 + epsilon) := by
          dsimp [Cfour, eta]
          have hexp : (14 : ℝ) / 11 + 8 * (epsilon / 8) =
              (14 : ℝ) / 11 + epsilon := by ring
          rw [hexp]
          ring
    have hCfourRfour : Cfour ≤ R ^ 4 := by
      exact (le_max_left Cfour 1).trans (le_self_pow₀ hRone (by norm_num))
    have hexponent : (14 : ℝ) / 11 + epsilon ≤ 4 * (theta0 + epsilon) := by
      norm_num [theta0]
      linarith
    have hpower : x ^ ((14 : ℝ) / 11 + epsilon) ≤
        x ^ (4 * (theta0 + epsilon)) :=
      Real.rpow_le_rpow_of_exponent_le hx hexponent
    have htargetPow :
        (R * x ^ (theta0 + epsilon)) ^ 4 =
          R ^ 4 * x ^ (4 * (theta0 + epsilon)) := by
      rw [mul_pow]
      congr 1
      calc
        (x ^ (theta0 + epsilon)) ^ 4 =
            x ^ ((theta0 + epsilon) * (4 : ℕ)) :=
          (Real.rpow_mul_natCast hx0.le _ 4).symm
        _ = x ^ (4 * (theta0 + epsilon)) := by
          congr 1
          ring
    have hfourthTarget :
        bigB x (Gscale x H M) (Ascale x C M) C Kb Lb t₁ t₂ ^ 4 ≤
          (R * x ^ (theta0 + epsilon)) ^ 4 := by
      calc
        bigB x (Gscale x H M) (Ascale x C M) C Kb Lb t₁ t₂ ^ 4 ≤
            Cfour * x ^ ((14 : ℝ) / 11 + epsilon) := hfourth
        _ ≤ R ^ 4 * x ^ (4 * (theta0 + epsilon)) :=
          mul_le_mul hCfourRfour hpower
            (Real.rpow_nonneg hx0.le _) (pow_nonneg hR0 4)
        _ = (R * x ^ (theta0 + epsilon)) ^ 4 := htargetPow.symm
    have hbigB0 : 0 ≤
        bigB x (Gscale x H M) (Ascale x C M) C Kb Lb t₁ t₂ :=
      bigB_nonneg hG0.le hC0.le
    have htarget0 : 0 ≤ R * x ^ (theta0 + epsilon) :=
      mul_nonneg hR0 (Real.rpow_nonneg hx0.le _)
    exact (pow_le_pow_iff_left₀ hbigB0 htarget0 (by norm_num : (4 : ℕ) ≠ 0)).1
      hfourthTarget
  calc
    section12BigB x (Gscale x H M) (Ascale x C M) C
        (Kscale x C M) (Lscale x C H M) t₁ t₂ ≤
      72 * (R * x ^ (theta0 + epsilon)) :=
        section12BigB_le_72_mul hblocks
    _ = (72 * R) * x ^ (theta0 + epsilon) := by ring

end

end LeanProofs.IntegerPoints

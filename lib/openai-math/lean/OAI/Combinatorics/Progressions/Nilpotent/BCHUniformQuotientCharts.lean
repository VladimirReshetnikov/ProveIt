/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.BoundedFreeWords
import OAI.Combinatorics.Progressions.Estimates.FiniteSeriesCoefficientBounds
import OAI.Combinatorics.Progressions.Estimates.FrozenCosetVariation
import OAI.Combinatorics.Progressions.Fourier.TorusCircleActions
import OAI.Combinatorics.Progressions.Geometry.QuotientCoordinateRadius

namespace OAI

section

namespace Erdos3

def bchProductCoefficientBase (s : ℕ) : ℕ :=
  2 * s + 4 + finiteSeriesDenominator s +
    (s + 1) * ((s + 1) * finiteSeriesNumeratorBound s) + finiteSeriesNumeratorBound s

def bchProductCoefficientHeight (s n : ℕ) : ℕ :=
  bchProductCoefficientBase s ^ ((s + 2) * (n + 2))

theorem bchProductCoefficientBase_pos (s : ℕ) : 0 < bchProductCoefficientBase s := by
  unfold bchProductCoefficientBase
  omega

theorem bchProductDenominator_le_height (s n : ℕ) :
    bchProductDenominator s n ≤ bchProductCoefficientHeight s n := by
  let B := bchProductCoefficientBase s
  have hB : 1 ≤ B := bchProductCoefficientBase_pos s
  have hD : finiteSeriesDenominator s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  unfold bchProductDenominator bchProductCoefficientHeight
  change finiteSeriesDenominator s * (finiteSeriesDenominator s ^ n) ^ s ≤ B ^ ((s + 2) * (n + 2))
  calc
    _ ≤ B * (B ^ n) ^ s := Nat.mul_le_mul hD (Nat.pow_le_pow_left (Nat.pow_le_pow_left hD _) _)
    _ = B ^ (1 + n * s) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right hB (by nlinarith)

theorem bchProductNumeratorBound_le_height (s n : ℕ) :
    bchProductNumeratorBound s n ≤ bchProductCoefficientHeight s n := by
  let B := bchProductCoefficientBase s
  let A := (s + 1) * ((s + 1) * finiteSeriesNumeratorBound s)
  have hB : 1 ≤ B := bchProductCoefficientBase_pos s
  have hD : finiteSeriesDenominator s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hA : A ≤ B := by dsimp [A, B, bchProductCoefficientBase]; omega
  have hs : s + 1 ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hU : finiteSeriesNumeratorBound s ≤ B := by dsimp [B, bchProductCoefficientBase]; omega
  have hsum : finiteSeriesDenominator s ^ n + (s + 1) * (A ^ n + finiteSeriesDenominator s ^ n) ≤
      B ^ (n + 1) := by
    calc
      _ ≤ B ^ n + (s + 1) * (B ^ n + B ^ n) :=
        Nat.add_le_add (Nat.pow_le_pow_left hD _)
          (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.pow_le_pow_left hA _) (Nat.pow_le_pow_left hD _)))
      _ = (2 * s + 3) * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul_right _ (by dsimp [B, bchProductCoefficientBase]; omega)
      _ = _ := (pow_succ' B n).symm
  unfold bchProductNumeratorBound bchProductCoefficientHeight
  change (s + 1) * finiteSeriesNumeratorBound s *
    (finiteSeriesDenominator s ^ n + (s + 1) * (A ^ n + finiteSeriesDenominator s ^ n)) ^ s ≤
      B ^ ((s + 2) * (n + 2))
  calc
    _ ≤ (B * B) * (B ^ (n + 1)) ^ s :=
      Nat.mul_le_mul (Nat.mul_le_mul hs hU) (Nat.pow_le_pow_left hsum _)
    _ = B ^ (2 + (n + 1) * s) := by rw [← pow_two, ← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hB (by nlinarith)

variable {X : Type*}

theorem bchProductWordCoefficient_height (s : ℕ) (xs : List X) (w : FreeMonoid X)
    (hw : w.length ≤ s) :
    RationalHeightLE (freeWordCoefficients (bchProductPolynomial s xs) w)
      (bchProductCoefficientHeight s xs.length) := by
  exact ((bchProductPolynomial_coefficient_bound s xs).rationalHeight
    (bchProductDenominator_pos s xs.length) w hw).mono
      (max_le (bchProductDenominator_le_height s xs.length) (bchProductNumeratorBound_le_height s xs.length))

theorem bchProductBracketCoefficient_height (s : ℕ) (xs : List X) {w : FreeSemigroup X}
    (hw : w ∈ bchProductBracketSupport s xs) :
    RationalHeightLE (bchProductBracketCoefficient s xs w)
      (bchProductCoefficientHeight s xs.length * (s + 1)) := by
  have hlen := bchProductBracketSupport_length s xs hw
  have hword := bchProductWordCoefficient_height s xs w.toFreeMonoid
    (by simpa only [freeSemigroup_toFreeMonoid_length] using hlen)
  have hinv : RationalHeightLE ((w.length : ℚ)⁻¹) (s + 1) := by
    have hpos : 0 < w.length := by change 0 < w.tail.length + 1; omega
    have h := rationalHeightLE_fraction (1 : ℤ) (w.length : ℤ)
      (by exact_mod_cast hpos.ne') (H := s + 1) (by simp)
      (by simpa only [Int.natAbs_natCast] using hlen.trans (Nat.le_succ s))
    simpa only [Int.cast_one, Int.cast_natCast, one_div] using h
  rw [bchProductBracketCoefficient, bchProductWordCoefficients_eq, ite_eq_left hlen, div_eq_mul_inv]
  exact hword.mul hinv

variable {ι : Type*} [Fintype ι]

theorem bchProductCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (s : ℕ) (xs : List X) (k : ι) :
    RationalPolynomialHeightLE (bchProductCoordinatePolynomial c s xs k)
      (((bchProductBracketSupport s xs).card + 1) *
        (bchProductCoefficientHeight s xs.length * (s + 1) *
          lieCoordinateHeight (Fintype.card ι) H s) ^ (bchProductBracketSupport s xs).card) := by
  apply RationalPolynomialHeightLE.sum_finset
  intro w hw
  exact RationalPolynomialHeightLE.C_mul (bchProductBracketCoefficient_height s xs hw)
    ((dynkinCoordinatePolynomial_height c hc w k).mono
      (lieCoordinateHeight_mono_length _ _ (bchProductBracketSupport_length s xs hw)))

end Erdos3

end

section

namespace Erdos3

theorem bchProductCoefficientHeight_le_exp (s n C : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hB : bchProductCoefficientBase s ≤ C) (hs : s + 2 ≤ C) :
    (bchProductCoefficientHeight s n : ℝ) ≤ Real.exp ((p + C) ^ 3) := by
  let t : ℝ := p + C
  have hbase : (bchProductCoefficientBase s : ℝ) ≤ t := by
    have h := (Nat.cast_le (α := ℝ)).mpr hB
    dsimp [t]
    linarith
  have hs' : (s : ℝ) + 2 ≤ t := by
    have h : (s : ℝ) + 2 ≤ C := by exact_mod_cast hs
    dsimp [t]
    linarith
  have hn' : (n : ℝ) + 2 ≤ t := by
    have hC : (2 : ℝ) ≤ C := by exact_mod_cast (show 2 ≤ C by omega)
    dsimp [t]
    linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : (bchProductCoefficientBase s : ℝ) ≤ Real.exp (bchProductCoefficientBase s) := by
    have h := Real.add_one_le_exp (bchProductCoefficientBase s)
    linarith
  unfold bchProductCoefficientHeight
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (bchProductCoefficientBase s)) ^ ((s + 2) * (n + 2)) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) he _
    _ = Real.exp ((((s + 2) * (n + 2) : ℕ) : ℝ) * bchProductCoefficientBase s) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t * t * t) := by
      apply Real.exp_le_exp.mpr
      push_cast
      exact mul_le_mul (mul_le_mul hs' hn' (by positivity) ht) hbase (by positivity) (by positivity)
    _ = _ := by congr 1; dsimp [t]; ring

theorem exists_bchProductCoordinatePolynomial_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι : Type*} [Fintype X] [Fintype ι]
      (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ) (xs : List X),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∀ k m, (((bchProductCoordinatePolynomial c s xs k).coeff m).num.natAbs : ℝ) ≤
          Real.exp ((p + C) ^ C) ∧
        (((bchProductCoordinatePolynomial c s xs k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let C := bchProductCoefficientBase s + 5 * s + 10
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro X ι _ _ c H p xs hp hd hX hn hH hc k m
  let t : ℝ := p + C
  have ht : 2 ≤ t := by
    have h : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    linarith
  have hshift : p + 2 ≤ t := by
    have h : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    linarith
  have hs : (s : ℝ) + 1 ≤ t := by
    have h : (s : ℝ) + 1 ≤ C := by exact_mod_cast (show s + 1 ≤ C by dsimp [C]; omega)
    dsimp [t]
    linarith
  have hword : (bchProductCoefficientHeight s xs.length : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    apply (bchProductCoefficientHeight_le_exp s xs.length C hp hn
      (by dsimp [C]; omega) (by dsimp [C]; omega)).trans
    exact Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega))
  have hsbound : ((s + 1 : ℕ) : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    have h1 : t ≤ t ^ (3 * s + 3) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
        (show 1 ≤ 3 * s + 3 by omega)
    have h2 := Real.add_one_le_exp (t ^ (3 * s + 3))
    push_cast
    linarith
  have hlie : (lieCoordinateHeight (Fintype.card ι) H s : ℝ) ≤ Real.exp (t ^ (3 * s + 3)) := by
    apply (lieCoordinateHeight_le_exp (Fintype.card ι) H s hp hd hH).trans
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by linarith) hshift _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hproduct : ((bchProductCoefficientHeight s xs.length * (s + 1) *
        lieCoordinateHeight (Fintype.card ι) H s : ℕ) : ℝ) ≤ Real.exp (t ^ (3 * s + 5)) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ Real.exp (t ^ (3 * s + 3)) * Real.exp (t ^ (3 * s + 3)) * Real.exp (t ^ (3 * s + 3)) :=
        mul_le_mul (mul_le_mul hword hsbound (by positivity) (by positivity)) hlie
          (by positivity) (by positivity)
      _ = Real.exp (3 * t ^ (3 * s + 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show 3 * s + 5 = (3 * s + 3) + 2 by omega, pow_add t (3 * s + 3) 2]
        have hsq : 3 ≤ t ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ t ^ (3 * s + 3))]
  have hcard : ((bchProductBracketSupport s xs).card : ℝ) ≤ t ^ (s + 1) := by
    have h := (Nat.cast_le (α := ℝ)).mpr (bchProductBracketSupport_card_le s xs)
    push_cast at h
    apply h.trans
    calc
      ((s : ℝ) + 1) * ((Fintype.card X : ℝ) + 1) ^ s ≤ t * t ^ s :=
        mul_le_mul hs (pow_le_pow_left₀ (by positivity) (by linarith) _)
          (by positivity) (by positivity)
      _ = _ := (pow_succ' t s).symm
  have hsum := rational_sum_cost_le_exp (bchProductBracketSupport s xs).card
    (bchProductCoefficientHeight s xs.length * (s + 1) * lieCoordinateHeight (Fintype.card ι) H s)
    (p := t - 2) (by linarith) (3 * s + 5) (s + 1)
    (by simpa only [sub_add_cancel] using hproduct) (by simpa only [sub_add_cancel] using hcard)
  have hfinal : (((bchProductBracketSupport s xs).card + 1) *
      (bchProductCoefficientHeight s xs.length * (s + 1) * lieCoordinateHeight (Fintype.card ι) H s) ^
        (bchProductBracketSupport s xs).card : ℕ) ≤ Real.exp (t ^ C) := by
    apply hsum.trans
    apply Real.exp_le_exp.mpr
    rw [sub_add_cancel]
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hheight := bchProductCoordinatePolynomial_height c hc s xs k m
  exact ⟨(Nat.cast_le.mpr hheight.1).trans hfinal, (Nat.cast_le.mpr hheight.2).trans hfinal⟩

theorem exists_bch_product_coordinate_polynomials_exp_height (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι R L : Type*} [Fintype X] [Fintype ι]
      [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
      [IsScalarTower ℚ R L] (e : Module.Basis ι R L) (c : ι → ι → ι → ℚ)
      (H : ℕ) (p : ℝ) (xs : List X),
      (∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k) →
      LieModule.lowerCentralSeries ℚ L L s = ⊥ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ P : ι → MvPolynomial (X × ι) ℚ,
        (∀ (f : X → L) k,
          MvPolynomial.aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (P k) =
            e.repr (lieBCHList s f xs) k) ∧
        (∀ k, (P k).totalDegree ≤ s) ∧
        (∀ k, (P k).support.card ≤ (s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s) ∧
        ∀ k m, (((P k).coeff m).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          (((P k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_bchProductCoordinatePolynomial_exp_budget s
  refine ⟨C, hC, ?_⟩
  intro X ι R L _ _ _ _ _ _ _ _ e c H p xs hstructure hnil hp hd hX hn hH hc
  refine ⟨bchProductCoordinatePolynomial c s xs, ?_,
    bchProductCoordinatePolynomial_totalDegree c s xs,
    bchProductCoordinatePolynomial_support_card c s xs, hbudget c H p xs hp hd hX hn hH hc⟩
  intro f k
  exact bchProductCoordinatePolynomial_eval_over e c hstructure s hnil f xs k

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial

theorem exists_bch_product_box_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X ι L : Type*} [Fintype X] [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (xs : List X) (f : X → L) (B : ℝ),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      LieModule.lowerCentralSeries ℚ L L s = ⊥ →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (xs.length : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      1 ≤ B → (∀ x i, |e.repr (f x) i| ≤ B) →
      ∀ i, |e.repr (lieBCHList s f xs) i| ≤
        ((s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s : ℕ) *
          Real.exp ((p + C) ^ C) * B ^ s := by
  obtain ⟨C, hC, hpoly⟩ := exists_bch_product_coordinate_polynomials_exp_height s
  refine ⟨C, hC, ?_⟩
  intro X ι L _ _ _ _ _ _ e c H p xs f B hstructure hnil hp hd hX hn hH hc hB hf i
  obtain ⟨P, heval, hdegree, hcard, hheight⟩ :=
    hpoly e c H p xs hstructure hnil hp hd hX hn hH hc
  rw [← heval f i]
  have hbound := abs_aeval_le_box_bound (P i)
    (fun xi : X × ι => e.repr (f xi.1) xi.2)
    (Real.exp_nonneg _) hB
    (fun m => (rational_abs_real_le_numerator _).trans (hheight i m).1)
    (fun xi => hf xi.1 xi.2) (hdegree i)
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard i)) (Real.exp_nonneg _))
    (pow_nonneg (by linarith) _)

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_box_expression_le_exp (s a C n d : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hn : n ≤ s) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) *
      Real.exp ((p + s + C) ^ C) * (Real.exp ((p + 2) ^ a)) ^ s ≤
        Real.exp ((p + (C + 3 * s + a + 10)) ^ (C + 3 * s + a + 10)) := by
  let D := C + 3 * s + a + 10
  let t := p + D
  have hD : 3 ≤ D := by dsimp [D]; omega
  have hD' : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hs : (s : ℝ) + 1 ≤ t := by
    have h : s + 1 ≤ D := by dsimp [D]; omega
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    dsimp [t]
    push_cast at h'
    linarith
  have hp2 : p + 2 ≤ t := by dsimp [t]; linarith
  have hn' : (n : ℝ) ≤ t := (Nat.cast_le.mpr hn).trans (by linarith)
  have hd' : (d : ℝ) ≤ t := hd.trans (by linarith)
  have hbase : ((n * d + 1 : ℕ) : ℝ) ≤ t ^ 3 := by
    have hnd := mul_le_mul hn' hd' (Nat.cast_nonneg d) (by linarith : 0 ≤ t)
    push_cast
    nlinarith [sq_nonneg (t - 1)]
  have hcount : (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) ≤ t ^ (3 * s + 1) := by
    push_cast at hbase
    push_cast
    calc
      _ ≤ t * (t ^ 3) ^ s :=
        mul_le_mul hs (pow_le_pow_left₀ (by positivity) hbase s) (by positivity) (by linarith)
      _ = t ^ (3 * s + 1) := by rw [← pow_mul, pow_succ']
  have hcount' : (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) ≤ Real.exp (t ^ (D - 1)) := by
    have he : 3 * s + 1 ≤ D - 1 := by dsimp [D]; omega
    apply hcount.trans
    apply (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) he).trans
    linarith [Real.add_one_le_exp (t ^ (D - 1))]
  have hshift : p + s + C ≤ t := by
    have h : s + C ≤ D := by dsimp [D]; omega
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    dsimp [t]
    push_cast at h'
    linarith
  have hcoef : Real.exp ((p + s + C) ^ C) ≤ Real.exp (t ^ (D - 1)) := by
    apply Real.exp_le_exp.mpr
    apply (pow_le_pow_left₀ (by positivity) hshift C).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ Real.exp (t ^ (D - 1)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ t * t ^ a :=
        mul_le_mul (by linarith : (s : ℝ) ≤ t)
          (pow_le_pow_left₀ (by linarith) hp2 a) (by positivity) (by linarith)
      _ = t ^ (a + 1) := (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  calc
    _ ≤ Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) :=
      mul_le_mul (mul_le_mul hcount' hcoef (by positivity) (by positivity)) hinput
        (by positivity) (by positivity)
    _ = Real.exp (3 * t ^ (D - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ D) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t * t ^ (D - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = t ^ D := by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ D)]
    _ = _ := by simp [t, D]

theorem exists_bch_group_product_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (rs : List (NilpotentLieBCHGroup L s hnil)),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → rs.length ≤ s →
      (H : ℝ) ≤ Real.exp p → (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ r ∈ rs, ∀ i, |e.repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr rs.prod.coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * s + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil rs hstructure hp hd hn hH hc hrs i
  let f : Fin rs.length → L := fun j => (rs.get j).coord
  let xs := List.finRange rs.length
  have hlen : (xs.length : ℝ) ≤ p + s := by
    have hn' : (rs.length : ℝ) ≤ s := by exact_mod_cast hn
    simpa only [xs, List.length_finRange] using hn'.trans (by linarith)
  have hlabels : (Fintype.card (Fin rs.length) : ℝ) ≤ p + s := by
    simpa only [Fintype.card_fin, xs, List.length_finRange] using hlen
  have hbound := hbox e c H (p + s) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) s])) hlabels hlen
    (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) s]))) hc
    (Real.one_le_exp (by positivity))
    (fun j k => hrs (rs.get j) (List.get_mem _ _) k) i
  have hmap : (xs.map (fun j => (⟨f j⟩ : NilpotentLieBCHGroup L s hnil))) = rs := by
    change (List.finRange rs.length).map rs.get = rs
    exact List.map_get_finRange rs
  have hcoord := lieBCHList_group_prod s hnil f xs
  rw [hmap] at hcoord
  rw [← hcoord, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_box_expression_le_exp s a C rs.length (Fintype.card ι) hC hp hn hd)

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_bounded_product_box_expression_le_exp (s a C n k d : ℕ)
    (hC : 2 ≤ C) (hn : n ≤ k) {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (n * d + 1) ^ s : ℕ) : ℝ) * Real.exp ((p + k + C) ^ C) *
      (Real.exp ((p + 2) ^ a)) ^ s ≤
      Real.exp ((p + (C + 3 * (s + k) + a + 10)) ^ (C + 3 * (s + k) + a + 10)) := by
  have hcount : (s + 1) * (n * d + 1) ^ s ≤ (s + k + 1) * (n * d + 1) ^ (s + k) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoef : Real.exp ((p + k + C) ^ C) ≤ Real.exp ((p + (s + k) + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ (Real.exp ((p + 2) ^ a)) ^ (s + k) :=
    pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (by omega)
  apply le_trans (mul_le_mul (mul_le_mul (Nat.cast_le.mpr hcount) hcoef
    (by positivity) (by positivity)) hinput (by positivity) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    bch_box_expression_le_exp (s + k) a C n d hC hp (by omega) hd

theorem exists_bch_fixed_product_exp_bound (s a k : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (rs : List (NilpotentLieBCHGroup L s hnil)),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → rs.length ≤ k →
      (H : ℝ) ≤ Real.exp p → (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ r ∈ rs, ∀ i, |e.repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr rs.prod.coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * (s + k) + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil rs hstructure hp hd hn hH hc hrs i
  let f : Fin rs.length → L := fun j => (rs.get j).coord
  let xs := List.finRange rs.length
  have hlen : (xs.length : ℝ) ≤ p + k := by
    have hn' : (rs.length : ℝ) ≤ k := by exact_mod_cast hn
    simpa only [xs, List.length_finRange] using hn'.trans (by linarith)
  have hlabels : (Fintype.card (Fin rs.length) : ℝ) ≤ p + k := by
    simpa only [Fintype.card_fin, xs, List.length_finRange] using hlen
  have hbound := hbox e c H (p + k) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) k])) hlabels hlen
    (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))) hc
    (Real.one_le_exp (by positivity)) (fun j z => hrs (rs.get j) (List.get_mem _ _) z) i
  have hmap : xs.map (fun j => (⟨f j⟩ : NilpotentLieBCHGroup L s hnil)) = rs := by
    change (List.finRange rs.length).map rs.get = rs
    exact List.map_get_finRange rs
  have hcoord := lieBCHList_group_prod s hnil f xs
  rw [hmap] at hcoord
  rw [← hcoord, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_bounded_product_box_expression_le_exp s a C rs.length k (Fintype.card ι) hC hn hp hd)

end Erdos3

end

section

namespace Erdos3

open Module

theorem bch_triple_box_expression_le_exp (s a C d : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) :
    (((s + 1) * (3 * d + 1) ^ s : ℕ) : ℝ) * Real.exp ((p + 3 + C) ^ C) *
      (Real.exp ((p + 2) ^ a)) ^ s ≤
      Real.exp ((p + (C + 3 * (s + 3) + a + 10)) ^ (C + 3 * (s + 3) + a + 10)) := by
  have hcount : (s + 1) * (3 * d + 1) ^ s ≤ (s + 3 + 1) * (3 * d + 1) ^ (s + 3) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
  have hcoef : Real.exp ((p + 3 + C) ^ C) ≤ Real.exp ((p + (s + 3) + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) s]
  have hinput : (Real.exp ((p + 2) ^ a)) ^ s ≤ (Real.exp ((p + 2) ^ a)) ^ (s + 3) :=
    pow_le_pow_right₀ (Real.one_le_exp (by positivity)) (by omega)
  apply le_trans (mul_le_mul (mul_le_mul (Nat.cast_le.mpr hcount) hcoef
    (by positivity) (by positivity)) hinput (by positivity) (by positivity))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    bch_box_expression_le_exp (s + 3) a C 3 d hC hp (by omega) hd

theorem exists_bch_triple_product_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (u v w : NilpotentLieBCHGroup L s hnil),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ i, |e.repr u.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      (∀ i, |e.repr v.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      (∀ i, |e.repr w.coord i| ≤ Real.exp ((p + 2) ^ a)) →
      ∀ i, |e.repr (u * v * w).coord i| ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hbox⟩ := exists_bch_product_box_bound s
  refine ⟨C + 3 * (s + 3) + a + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil u v w hstructure hp hd hH hc hu hv hw i
  let f : Fin 3 → L := ![u.coord, v.coord, w.coord]
  let xs : List (Fin 3) := [0, 1, 2]
  have hcoords (j : Fin 3) (k : ι) : |e.repr (f j) k| ≤ Real.exp ((p + 2) ^ a) := by
    fin_cases j
    · exact hu k
    · exact hv k
    · exact hw k
  have hbound := hbox e c H (p + 3) xs f (Real.exp ((p + 2) ^ a)) hstructure hnil
    (by linarith) (hd.trans (by linarith))
    (by norm_num only [Fintype.card_fin, Nat.cast_ofNat]; linarith)
    (by simp only [xs, List.length_cons, List.length_nil]; norm_num; linarith)
    (hH.trans (Real.exp_le_exp.mpr (by linarith))) hc
    (Real.one_le_exp (by positivity)) hcoords i
  have heq : lieBCHList s f xs = (u * v * w).coord := by
    simpa [xs, f, mul_assoc] using
      (lieBCHList_group_prod s hnil f xs).symm
  rw [heq, Fintype.card_fin] at hbound
  exact hbound.trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      bch_triple_box_expression_le_exp s a C (Fintype.card ι) hC hp hd)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped NNReal

theorem coordinateLipschitzBound_power_budget (d D : ℕ) (hD : 2 ≤ D) (B : ℝ≥0)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hB : (B : ℝ) ≤ Real.exp ((p + D) ^ D)) :
    (coordinateLipschitzBound d d B : ℝ) ≤
      Real.exp ((p + ((D + 2) * 2 : ℕ)) ^ ((D + 2) * 2)) := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hq : 0 ≤ (p + D) ^ D := by positivity
  have hpq : p ≤ (p + D) ^ D := by
    calc
      p ≤ p + D := by linarith
      _ ≤ (p + D) ^ D := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + D)
          (by omega : 1 ≤ D)
  apply (coordinateLipschitzBound_le_exp d d B hq (hd.trans hpq) (hd.trans hpq) hB).trans
  apply Real.exp_le_exp.mpr
  have hshift := shifted_power_budget_le (p := p + D - 2) (by linarith) D 2
  rw [show p + D - 2 + 2 = p + D by ring] at hshift
  apply hshift.trans
  apply pow_le_pow_left₀ (by positivity)
  have hDE : D ≤ (D + 2) * 2 := by omega
  exact add_le_add le_rfl (Nat.cast_le.mpr hDE)

theorem exists_bch_conjugation_basis_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (a : NilpotentLieBCHGroup L s hnil),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
      ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤
        Real.exp ((p + D) ^ D) := by
  classical
  obtain ⟨D, hD, hprod⟩ := exists_bch_triple_product_exp_bound s r
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil a hstructure hp hd hH hc ha i k
  apply hprod e c H p hnil a ⟨e i⟩ a⁻¹ hstructure hp hd hH hc ha
  · intro j
    change |e.repr (e i) j| ≤ _
    rw [Basis.repr_self_apply]
    split_ifs
    · simpa only [abs_one] using Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ r)
    · simpa only [abs_zero] using Real.exp_nonneg ((p + 2) ^ r)
  · intro j
    change |e.repr (-a.coord) j| ≤ _
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using ha j

namespace NilpotentLieBCHGroup

theorem exists_uniform_left_lipschitz_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      letI := rightMetricSpace (hnil := hnil) e
      ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∀ a : NilpotentLieBCHGroup L s hnil,
          (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
          LipschitzWith C (fun x => a * x) := by
  obtain ⟨D, hD, hbound⟩ := exists_bch_conjugation_basis_exp_bound s r
  refine ⟨(D + 2) * 2, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil hstructure hp hd hH hc
  let := rightMetricSpace (hnil := hnil) e
  let B : ℝ≥0 := ⟨Real.exp ((p + D) ^ D), Real.exp_nonneg _⟩
  refine ⟨coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B,
    coordinateLipschitzBound_pos _ _ _,
    coordinateLipschitzBound_power_budget _ D hD B hp hd le_rfl, ?_⟩
  intro a ha
  exact lipschitz_mul_left_of_basis_bound e a B (hbound e c H p hnil a hstructure hp hd hH hc ha)

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Quotient

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

theorem quotientMetricSpace_lipschitz_left (a : NilpotentLieBCHGroup L s hnil) {C : ℝ≥0}
    (hLip : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith C (fun x => a * x)) :
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith C (fun x : _ ⧸ Γ => a • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact lipschitz_quotient_left_smul Γ hΓ a hLip

theorem quotientMetricSpace_lipschitz_orbit (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith 1 (fun a : NilpotentLieBCHGroup L s hnil => a • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact lipschitz_quotient_orbit Γ hΓ x

theorem quotientMetricSpace_dist_action_le (a b : NilpotentLieBCHGroup L s hnil) {C : ℝ≥0}
    (hLip : letI := rightMetricSpace (hnil := hnil) e; LipschitzWith C (fun x => a * x))
    (x y : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    dist (a • x) (b • y) ≤ C * dist x y + dist a b := by
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  apply (dist_triangle (a • x) (a • y) (b • y)).trans
  apply add_le_add ((quotientMetricSpace_lipschitz_left e Γ hΓ a hLip).dist_le_mul x y)
  simpa only [NNReal.coe_one, one_mul] using (quotientMetricSpace_lipschitz_orbit e Γ hΓ y).dist_le_mul a b

end Quotient

theorem exists_uniform_quotient_left_lipschitz_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∀ (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
          (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
          (a : NilpotentLieBCHGroup L s hnil),
          (∀ i, |e.repr a.coord i| ≤ Real.exp ((p + 2) ^ r)) →
          letI := quotientMetricSpace e Γ hΓ
          LipschitzWith C (fun x : _ ⧸ Γ => a • x) := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_left_lipschitz_exp_bound s r
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil hstructure hp hd hH hc
  obtain ⟨C, hC, hCp, hLip⟩ := hbound e c H p hnil hstructure hp hd hH hc
  refine ⟨C, hC, hCp, ?_⟩
  intro Γ hΓ a ha
  exact quotientMetricSpace_lipschitz_left e Γ hΓ a (hLip a ha)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_coordinate_chart_metric_bounds
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z * x) → LipschitzWith C (fun x => z⁻¹ * x) →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l →
        letI := quotientMetricSpace e Γ hΓ
        ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
          let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
          dist (q v) (q w) ≤ (C : ℝ) * (bchBoxMetricConstant s (Fintype.card ι) H 1 : ℝ) * dist v w ∧
          dist v w ≤ (bchInverseBoxConstant s (Fintype.card ι) H 1 : ℝ) * C * dist (q v) (q w) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC z hleft hleftInv r hr hr1 hsmall
  let := quotientMetricSpace e Γ hΓ
  intro v w hv hw
  have hC' : (0 : ℝ) < C := hC
  have hR : (C : ℝ) * (Fintype.card ι + 1) * r ≤
      bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C)).mpr
    calc
      ((C : ℝ) * (Fintype.card ι + 1) * r) * (4 * C) =
          4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hsmall
  have hball (u : ι → ℝ) (hu : ∀ i, |u i| ≤ r) :
      dist (z * (basisHomeomorph e).symm u) z ≤
        bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    have hlog : dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 ≤ (Fintype.card ι + 1) * r := by
      calc
        _ = dist 1 ((basisHomeomorph (hnil := hnil) e).symm u) := dist_comm _ _
        _ ≤ coordinateL2Norm (basisHomeomorph e ((basisHomeomorph (hnil := hnil) e).symm u)) :=
          dist_one_le_coordinateL2Norm e _
        _ = coordinateL2Norm u := by rw [Homeomorph.apply_symm_apply]
        _ ≤ _ := coordinateL2Norm_le_card_bound u hr hu
    have htrans := hleft.dist_le_mul ((basisHomeomorph (hnil := hnil) e).symm u) 1
    rw [mul_one] at htrans
    calc
      _ ≤ (C : ℝ) * dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 := htrans
      _ ≤ (C : ℝ) * ((Fintype.card ι + 1) * r) := mul_le_mul_of_nonneg_left hlog C.coe_nonneg
      _ = (C : ℝ) * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hR
  have hq := quotient_dist_eq_on_ball_of_lattice_grid e c hstructure hc Γ hΓ l hl hgrid C hC z
    hleftInv (hball v hv) (hball w hw)
  have hv1 (i) : |v i| ≤ (1 : ℝ) := (hv i).trans hr1
  have hw1 (i) : |w i| ≤ (1 : ℝ) := (hw i).trans hr1
  have hforward := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc 1 le_rfl).dist_le_mul v hv1 w hw1
  have hinverse := dist_coordinates_le_bchInverseBoxConstant e c hstructure hc 1 le_rfl
    ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hv1 i)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hw1 i)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hinverse
  dsimp only
  rw [hq]
  constructor
  · apply (hleft.dist_le_mul _ _).trans
    exact (mul_le_mul_of_nonneg_left hforward C.coe_nonneg).trans_eq (by ring)
  · have hback : dist ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w) ≤
        (C : ℝ) * dist (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w) := by
      have hb := hleftInv.dist_le_mul
        (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w)
      rw [inv_mul_cancel_left, inv_mul_cancel_left] at hb
      exact hb
    exact hinverse.trans ((mul_le_mul_of_nonneg_left hback (bchInverseBoxConstant _ _ _ _).coe_nonneg).trans_eq (by ring))

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

omit [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L] in
theorem centralBCHFlow_period (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    realBCHLine (hnil := hnil) v 1 • x = x := by
  apply central_smul_eq_self_of_mem Γ
  · simpa only [realBCHLine_one] using hperiod
  · exact realBCHLine_commute v hv 1

theorem centralBCHFlow_isometry (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0) (r : ℝ) :
    letI := quotientMetricSpace e Γ hΓ
    Isometry (fun x : NilpotentLieBCHGroup L s hnil ⧸ Γ => realBCHLine (hnil := hnil) v r • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact isometry_quotient_central_smul Γ hΓ (realBCHLine (hnil := hnil) v r) (realBCHLine_commute v hv r)

theorem centralBCHFlow_displacement (v : L) (r : ℝ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    dist (realBCHLine (hnil := hnil) v r • x) x ≤ coordinateL2Norm (e.equivFun v) * |r| := by
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  have h := (quotientMetricSpace_lipschitz_orbit e Γ hΓ x).dist_le_mul (realBCHLine (hnil := hnil) v r) 1
  have hbound := realBCHLine_dist_one_le (hnil := hnil) e v r
  simp only [one_smul, NNReal.coe_one, one_mul] at h
  exact h.trans (hbound.trans_eq (mul_comm _ _))

noncomputable def centralBCHCircleAction (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    CircleFourier.IsometricCircleAction (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientMetricSpace e Γ hΓ
  exact CircleFourier.isometricCircleActionOfFlow (fun r x => realBCHLine (hnil := hnil) v r • x)
    (fun x => by rw [realBCHLine_zero, one_smul])
    (fun r t x => by rw [realBCHLine_add, mul_smul])
    (centralBCHFlow_period Γ v hv hperiod)
    (centralBCHFlow_isometry e Γ hΓ v hv)
    ⟨coordinateL2Norm (e.equivFun v), coordinateL2Norm_nonneg _⟩
    (centralBCHFlow_displacement e Γ hΓ v)

theorem centralBCHCircleAction_act_coe (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (r : ℝ) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    (centralBCHCircleAction e Γ hΓ v hv hperiod).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := hnil) v r • x := by
  let := quotientMetricSpace e Γ hΓ
  dsimp only [centralBCHCircleAction, CircleFourier.isometricCircleActionOfFlow]
  exact CircleFourier.periodicFlowAct_coe _ _ r x

theorem centralBCHCircleAction_displacement (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (hperiod : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (t : CircleFourier.Circle) (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    dist ((centralBCHCircleAction e Γ hΓ v hv hperiod).act t x) x ≤
      coordinateL2Norm (e.equivFun v) * ‖t‖ := by
  let := quotientMetricSpace e Γ hΓ
  dsimp only [centralBCHCircleAction, CircleFourier.isometricCircleActionOfFlow]
  exact CircleFourier.periodicFlowAct_displacement _ _
    ⟨coordinateL2Norm (e.equivFun v), coordinateL2Norm_nonneg _⟩
    (centralBCHFlow_displacement e Γ hΓ v) t x

theorem centralBCHCircleAction_commutes (v w : L)
    (hv : ∀ z : L, ⁅v, z⁆ = 0) (hw : ∀ z : L, ⁅w, z⁆ = 0)
    (hvΓ : (⟨v⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ)
    (hwΓ : (⟨w⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ) :
    letI := quotientMetricSpace e Γ hΓ
    (centralBCHCircleAction e Γ hΓ v hv hvΓ).Commutes (centralBCHCircleAction e Γ hΓ w hw hwΓ) := by
  let := quotientMetricSpace e Γ hΓ
  intro t u x
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective u
  simp only [centralBCHCircleAction_act_coe]
  rw [← mul_smul, ← mul_smul, (realBCHLine_commute v hv r (realBCHLine (hnil := hnil) w q)).eq]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_uniform_quotient_isometric_radius_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
      (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ),
      0 < l → (∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) →
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := rightMetricSpace (hnil := hnil) e
      letI := quotientMetricSpace e Γ hΓ
      ∃ R : ℝ, 0 < R ∧ 1 / R ≤ Real.exp ((p + D) ^ D) ∧
        ∀ z : NilpotentLieBCHGroup L s hnil,
          (∀ i, |e.repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
          ∀ x y : NilpotentLieBCHGroup L s hnil, dist x z ≤ R → dist y z ≤ R →
            dist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  obtain ⟨A, hA, hgap⟩ := exists_bchLatticeSeparationRadius_inv_exp_bound s
  obtain ⟨B, hB, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s a
  refine ⟨A + B + 5, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil Γ hΓ l hl hgrid hstructure hc hp hd hH hlp
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨C, hC, hCp, hleft⟩ := hleft e c H p hnil hstructure hp hd hH hc
  let δ := bchLatticeSeparationRadius s (Fintype.card ι) H l
  have hδ : 0 < δ := bchLatticeSeparationRadius_pos _ _ _ _
  have hC' : (0 : ℝ) < C := hC
  refine ⟨δ / (4 * C), by positivity,
    quotient_radius_inverse_power_budget A B hA hB hδ hC' hp (hgap _ _ _ _ hp hd hH hlp) hCp, ?_⟩
  intro z hz x y hx hy
  have hzinv : ∀ i, |e.repr z⁻¹.coord i| ≤ Real.exp ((p + 2) ^ a) := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hz i
  exact quotient_dist_eq_on_ball_of_lattice_grid e c hstructure hc Γ hΓ l hl hgrid C hC z
    (hleft z⁻¹ hzinv) hx hy

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_uniform_quotient_chart_metric_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
      (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ),
      0 < l → (∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) →
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := quotientMetricSpace e Γ hΓ
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : NilpotentLieBCHGroup L s hnil,
            (∀ i, |e.repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
              let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
              dist (q v) (q w) ≤ K * dist v w ∧ dist v w ≤ K * dist (q v) (q w) := by
  obtain ⟨A, hA, hgap⟩ := exists_bchLatticeSeparationRadius_inv_exp_bound s
  obtain ⟨B, hB, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s a
  obtain ⟨E, hE, hforward⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  obtain ⟨F, hF, hinverse⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  refine ⟨A + B + E + F + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil Γ hΓ l hl hgrid hstructure hc hp hd hH hlp
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨C, hC, hCp, hleft⟩ := hleft e c H p hnil hstructure hp hd hH hc
  let δ := bchLatticeSeparationRadius s (Fintype.card ι) H l
  have hδ : 0 < δ := bchLatticeSeparationRadius_pos _ _ _ _
  let r := quotientCoordinateRadius δ (C : ℝ) (Fintype.card ι)
  let U := bchBoxMetricConstant s (Fintype.card ι) H 1
  let V := bchInverseBoxConstant s (Fintype.card ι) H 1
  have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨hrp, hCU, hVC⟩ := quotient_chart_parameter_budget A B E F hA hB hE hF
    hδ C.coe_nonneg U.coe_nonneg hp (Fintype.card ι) hd
    (hgap _ _ _ _ hp hd hH hlp) hCp
    (hforward _ _ 1 _ hp hd hH hunit) (hinverse _ _ 1 _ hp hd hH hunit)
  let K : ℝ≥0 := max (C * U) (V * C)
  have hK : (K : ℝ) ≤ Real.exp ((p + (A + B + E + F + 10 : ℕ)) ^ (A + B + E + F + 10)) := by
    simpa only [K, NNReal.coe_max, NNReal.coe_mul] using max_le hCU hVC
  have hKU : (C : ℝ) * U ≤ (K : ℝ) := by exact_mod_cast (le_max_left (C * U) (V * C))
  have hKV : (V : ℝ) * C ≤ (K : ℝ) := by exact_mod_cast (le_max_right (C * U) (V * C))
  refine ⟨r, quotientCoordinateRadius_pos hδ _, quotientCoordinateRadius_le_one hδ _, hrp, K, hK, ?_⟩
  intro z hz v w hv hw
  have hzinv (i) : |e.repr z⁻¹.coord i| ≤ Real.exp ((p + 2) ^ a) := by
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hz i
  obtain ⟨hvw, hwv⟩ := quotient_coordinate_chart_metric_bounds e c hstructure hc Γ hΓ l hl hgrid
    C hC z (hleft z hz) (hleft z⁻¹ hzinv) r (quotientCoordinateRadius_pos hδ _).le
    (quotientCoordinateRadius_le_one hδ _) (quotientCoordinateRadius_small hδ _) v w hv hw
  exact ⟨hvw.trans (mul_le_mul_of_nonneg_right hKU dist_nonneg),
    hwv.trans (mul_le_mul_of_nonneg_right hKV dist_nonneg)⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI

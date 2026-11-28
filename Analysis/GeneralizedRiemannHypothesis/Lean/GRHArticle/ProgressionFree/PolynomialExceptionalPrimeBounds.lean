import GRHArticle.ProgressionFree.PolynomialPrimeDivisorTail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Exceptional prime-divisor probabilities over large finite fields

The linear threshold is `q-7`. At higher degrees the half bound on
irreducibles makes the threshold greater than `q`, and the binomial
majorant is bounded by a power of `q⁻¹`.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Finset
open scoped Classical

/-- The part of the unit charge budget allotted to prime factors of degree `d`. -/
noncomputable def polynomialExceptionalTheta (q d : ℕ) : ℝ :=
  if d = 1 then 1-8/(q : ℝ) else 8/((q : ℝ)*(d : ℝ)*((d : ℝ)-1))

theorem polynomialExceptionalTheta_nonneg {q : ℕ} (hq : 16 ≤ q) (d : ℕ) :
    0 ≤ polynomialExceptionalTheta q d := by
  have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
  unfold polynomialExceptionalTheta
  split_ifs with hd
  · exact sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr (by linarith))
  · by_cases hz : d = 0
    · simp [hz]
    · have hd' : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
      have hdsub : 0 ≤ (d : ℝ)-1 := by linarith
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) hdsub)

private theorem sum_polynomialExceptionalTheta_tail {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ∑ i ∈ range n, polynomialExceptionalTheta q (i+2) =
      8/(q : ℝ) - (8/(q : ℝ))/((n : ℝ)+1) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, polynomialExceptionalTheta, if_neg (show n+2 ≠ 1 by omega)]
    push_cast
    have h₁ : 0 < (n : ℝ)+1 := by positivity
    have h₂ : 0 < (n : ℝ)+2 := by positivity
    rw [show (n : ℝ)+2-1 = (n : ℝ)+1 by ring,
      show (n : ℝ)+1+1 = (n : ℝ)+2 by ring]
    field_simp [hq0.ne',h₁.ne',h₂.ne']
    ring

/-- The total charge over any finite set of distinct positive degrees is
at most one. -/
theorem sum_polynomialExceptionalTheta_le_one {q : ℕ} (hq : 16 ≤ q) (S : Finset ℕ)
    (hS : ∀ d ∈ S, 0 < d) : ∑ d ∈ S, polynomialExceptionalTheta q d ≤ 1 := by
  let n := S.sup id
  let T := (range n).image (fun i ↦ i+2)
  have hone : 1 ∉ T := by
    intro h
    obtain ⟨i,_,he⟩ := mem_image.mp h
    omega
  have hsub : S ⊆ insert 1 T := by
    intro d hd
    by_cases he : d = 1
    · subst d
      exact mem_insert_self _ _
    have hpos := hS d hd
    have hdn : d ≤ n := Finset.le_sup (f := id) hd
    exact mem_insert_of_mem (mem_image.mpr ⟨d-2,mem_range.mpr (by omega),by omega⟩)
  calc
    _ ≤ ∑ d ∈ insert 1 T, polynomialExceptionalTheta q d :=
      sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ ↦ polynomialExceptionalTheta_nonneg hq d)
    _ = 1 - (8/(q : ℝ))/((n : ℝ)+1) := by
      rw [sum_insert hone]
      unfold T
      rw [sum_image (fun i _ j _ h ↦ Nat.add_right_cancel h),
        sum_polynomialExceptionalTheta_tail (by omega), polynomialExceptionalTheta, if_pos rfl]
      ring
    _ ≤ _ := sub_le_self _ (by positivity)

variable {F : Type*} [Field F] [Fintype F]

/-- The first integer number of degree-`d` primes above the allowed fraction. -/
noncomputable def polynomialExceptionalThreshold (F : Type*) [Field F] [Fintype F] (d : ℕ) : ℕ :=
  ⌊polynomialExceptionalTheta (Fintype.card F) d * (polynomialIrreducibleCount F d : ℝ)⌋₊ + 1

theorem polynomialExceptionalThreshold_le_iff (hq : 16 ≤ Fintype.card F) (d r : ℕ) :
    polynomialExceptionalThreshold F d ≤ r ↔
      polynomialExceptionalTheta (Fintype.card F) d * (polynomialIrreducibleCount F d : ℝ) < (r : ℝ) := by
  rw [polynomialExceptionalThreshold, ← Nat.lt_iff_add_one_le]
  exact Nat.floor_lt (mul_nonneg (polynomialExceptionalTheta_nonneg hq d) (Nat.cast_nonneg _))

theorem polynomialExceptionalThreshold_one (hq : 16 ≤ Fintype.card F) :
    polynomialExceptionalThreshold F 1 = Fintype.card F-7 := by
  let q := Fintype.card F
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have he : polynomialExceptionalTheta q 1 * (q : ℝ) = ((q-8 : ℕ) : ℝ) := by
    rw [polynomialExceptionalTheta, if_pos rfl, Nat.cast_sub (show 8 ≤ q by omega)]
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hq'.ne']
    norm_num
  rw [polynomialExceptionalThreshold, polynomialIrreducibleCount_one, he, Nat.floor_natCast]
  omega

/-- The polynomial factors in the high-degree threshold grow more slowly
than powers of any base at least sixteen. -/
private theorem degreeProduct_le_power {q d : ℕ} (hq : 16 ≤ q) (hd : 2 ≤ d) :
    d^2 * (d-1) ≤ 4 * q^(d-2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hd
  clear hd
  simp only [Nat.add_sub_cancel_left]
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h₁ : 2+(n+1) ≤ 2*(2+n) := by omega
    have h₂ : 2+(n+1)-1 ≤ 2*((2+n)-1) := by omega
    calc
      _ ≤ (2*(2+n))^2 * (2*((2+n)-1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h₁ _) h₂
      _ = 8 * ((2+n)^2 * ((2+n)-1)) := by ring
      _ ≤ q * (4*q^n) := Nat.mul_le_mul (by omega) ih
      _ = _ := by rw [pow_succ]; ring

private theorem degreeProduct_le_power_real {q d : ℕ} (hq : 16 ≤ q) (hd : 2 ≤ d) :
    (d : ℝ)^2 * ((d : ℝ)-1) ≤ 4 * (q : ℝ)^(d-2) := by
  have h := Nat.cast_le (α := ℝ).mpr (degreeProduct_le_power hq hd)
  push_cast [Nat.cast_sub (show 1 ≤ d by omega)] at h
  exact h

private theorem binomial_le_three_ratio_pow (I t : ℕ) (ht : 0 < t) :
    (I.choose t : ℝ) ≤ (3*(I : ℝ)/(t : ℝ))^t := by
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have htp : 0 < (t : ℝ)^t := pow_pos ht' _
  have hexp : Real.exp (t : ℝ) = (Real.exp 1)^t := by
    simpa only [mul_one] using Real.exp_nat_mul 1 t
  calc
    _ ≤ (I : ℝ)^t / (t.factorial : ℝ) := Nat.choose_le_pow_div t I
    _ = ((I : ℝ)/(t : ℝ))^t * ((t : ℝ)^t/(t.factorial : ℝ)) := by
      rw [div_pow, div_mul_div_comm, mul_comm ((t : ℝ)^t) (t.factorial : ℝ),
        mul_div_mul_right _ _ htp.ne']
    _ ≤ ((I : ℝ)/(t : ℝ))^t * Real.exp (t : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (t : ℝ) (Nat.cast_nonneg t) t) (by positivity)
    _ = ((I : ℝ)/(t : ℝ) * Real.exp 1)^t := by rw [hexp, mul_pow]
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_mul_eq_mul_div, mul_comm (3 : ℝ)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (Nat.cast_nonneg _)) ht'.le

private theorem binomial_linear_bound {q : ℕ} (hq : 16 ≤ q) :
    (q.choose (q-7) : ℝ)/(q : ℝ)^(q-7) ≤ (q : ℝ)⁻¹^(q-14) := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  rw [Nat.choose_symm (show 7 ≤ q by omega)]
  calc
    _ ≤ (q : ℝ)^7/(q : ℝ)^(q-7) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow q 7) (by positivity)
    _ = _ := by
      rw [show q-7 = 7+(q-14) by omega, pow_add, inv_pow]
      exact div_mul_cancel_left₀ (pow_ne_zero 7 hq'.ne') _

/-- The higher-degree threshold strictly exceeds the field size. -/
theorem polynomialExceptionalThreshold_gt_card (hq : 16 ≤ Fintype.card F) {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card F < polynomialExceptionalThreshold F d := by
  let q := Fintype.card F
  let Q := (q : ℝ)
  let D := (d : ℝ)
  let I := (polynomialIrreducibleCount F d : ℝ)
  have hq0 : 0 < Q := Nat.cast_pos.mpr (by omega)
  have hd2 : 2 ≤ D := by dsimp [D]; exact_mod_cast hd
  have hd0 : 0 < D := by linarith
  have hdm : 0 < D-1 := by linarith
  have hden : 0 < Q*D*(D-1) := by positivity
  have hI : Q^d ≤ 2*(D*I) := by
    dsimp [Q,q,D,I]
    exact_mod_cast pow_card_le_twice_degree_mul_polynomialIrreducibleCount F d (by omega)
  have hd' : D^2*(D-1) ≤ 4*Q^(d-2) := degreeProduct_le_power_real hq hd
  have hpow : Q^d = Q^2*Q^(d-2) := by rw [← pow_add, Nat.add_sub_of_le hd]
  have hscaled : Q*(Q*D*(D-1))*D ≤ (8*I)*D := by
    calc
      _ = Q^2*(D^2*(D-1)) := by ring
      _ ≤ Q^2*(4*Q^(d-2)) := mul_le_mul_of_nonneg_left hd' (by positivity)
      _ = 4*Q^d := by rw [hpow]; ring
      _ ≤ _ := by linarith only [hI]
  have htheta : Q ≤ polynomialExceptionalTheta q d * I := by
    rw [polynomialExceptionalTheta, if_neg (show d ≠ 1 by omega), div_mul_eq_mul_div]
    exact (le_div_iff₀ hden).mpr ((mul_le_mul_iff_right₀ hd0).mp (by simpa only [mul_comm D] using hscaled))
  have hfloor : polynomialExceptionalTheta q d * I < (polynomialExceptionalThreshold F d : ℝ) := by
    rw [polynomialExceptionalThreshold, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  exact Nat.cast_lt (α := ℝ).mp (htheta.trans_lt hfloor)

private theorem theta_mul_power_bound {q d : ℕ} (hq : 16 ≤ q) (hd : 2 ≤ d) :
    3*(q : ℝ) ≤ polynomialExceptionalTheta q d * (q : ℝ)^d := by
  let Q := (q : ℝ)
  let D := (d : ℝ)
  have hq0 : 0 < Q := Nat.cast_pos.mpr (by omega)
  have hd2 : 2 ≤ D := by dsimp [D]; exact_mod_cast hd
  have hd0 : 0 < D := by linarith
  have hdm : 0 < D-1 := by linarith
  have hden : 0 < Q*D*(D-1) := by positivity
  have hp : D^2*(D-1) ≤ 4*Q^(d-2) := degreeProduct_le_power_real hq hd
  have hsmall : D*(D-1) ≤ 2*Q^(d-2) := by
    have ht := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ D*(D-1) by positivity)
    linarith only [hp,ht]
  have hpow : Q^d = Q^2*Q^(d-2) := by rw [← pow_add, Nat.add_sub_of_le hd]
  change 3*Q ≤ polynomialExceptionalTheta q d * Q^d
  rw [polynomialExceptionalTheta, if_neg (show d ≠ 1 by omega), div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  calc
    _ = (3*Q^2)*(D*(D-1)) := by ring
    _ ≤ (3*Q^2)*(2*Q^(d-2)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = 6*Q^d := by rw [hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private theorem binomial_higher_bound (hq : 16 ≤ Fintype.card F) {d : ℕ} (hd : 2 ≤ d) :
    let t := polynomialExceptionalThreshold F d
    ((polynomialIrreducibleCount F d).choose t : ℝ)/(Fintype.card F : ℝ)^(d*t) ≤
      (Fintype.card F : ℝ)⁻¹^Fintype.card F := by
  let q := Fintype.card F
  let Q := (q : ℝ)
  let I := polynomialIrreducibleCount F d
  let θ := polynomialExceptionalTheta q d
  let t := polynomialExceptionalThreshold F d
  have hq0 : 0 < Q := Nat.cast_pos.mpr (by omega)
  have hq1 : (1 : ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast (show 1 ≤ q by omega)
  have ht : q < t := polynomialExceptionalThreshold_gt_card hq hd
  have ht0 : 0 < t := Nat.zero_lt_of_lt ht
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht0
  have hθ : 0 < θ := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hdsub : 0 < (d : ℝ)-1 := by linarith
    rw [show θ = polynomialExceptionalTheta q d from rfl, polynomialExceptionalTheta, if_neg (show d ≠ 1 by omega)]
    exact div_pos (by norm_num) (mul_pos (mul_pos hq0 (by positivity)) hdsub)
  have hθt : θ*(I : ℝ) ≤ (t : ℝ) := by
    apply le_of_lt
    change _ < ((⌊θ*(I : ℝ)⌋₊+1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hratio : 3*(I : ℝ)/(t : ℝ) ≤ 3/θ := by
    apply (div_le_div_iff₀ htR hθ).mpr
    have := mul_le_mul_of_nonneg_left hθt (show (0 : ℝ) ≤ 3 by norm_num)
    linarith
  have hbase : (3*(I : ℝ)/(t : ℝ))/Q^d ≤ Q⁻¹ := by
    apply (div_le_div_of_nonneg_right hratio (by positivity)).trans
    rw [div_div]
    apply (div_le_iff₀ (by positivity : 0 < θ * Q^d)).mpr
    have he : 3 ≤ θ*Q^d/Q := (le_div_iff₀ hq0).mpr (theta_mul_power_bound hq hd)
    simpa only [div_eq_mul_inv, mul_comm (Q⁻¹)] using he
  change (I.choose t : ℝ)/Q^(d*t) ≤ Q⁻¹^q
  calc
    _ ≤ (3*(I : ℝ)/(t : ℝ))^t / Q^(d*t) :=
      div_le_div_of_nonneg_right (binomial_le_three_ratio_pow I t ht0) (by positivity)
    _ = ((3*(I : ℝ)/(t : ℝ))/Q^d)^t := by rw [pow_mul, ← div_pow]
    _ ≤ Q⁻¹^t := pow_le_pow_left₀ (by positivity) hbase t
    _ ≤ _ := pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq1) ht.le

/-- The degree-specific exceptional probability majorant from the article. -/
noncomputable def polynomialExceptionalBound (q d : ℕ) : ℝ :=
  (q : ℝ)⁻¹ ^ (if d = 1 then q-14 else q)

theorem polynomialExceptionalBound_le_linear {q : ℕ} (hq : 16 ≤ q) (d : ℕ) :
    polynomialExceptionalBound q d ≤ (q : ℝ)⁻¹^(q-14) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  unfold polynomialExceptionalBound
  split_ifs
  · exact le_rfl
  · exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq1) (Nat.sub_le _ _)

private theorem binomial_exceptional_bound (hq : 16 ≤ Fintype.card F) {d : ℕ} (hd : 0 < d) :
    let t := polynomialExceptionalThreshold F d
    ((polynomialIrreducibleCount F d).choose t : ℝ)/(Fintype.card F : ℝ)^(d*t) ≤
      polynomialExceptionalBound (Fintype.card F) d := by
  dsimp only
  by_cases h : d = 1
  · subst d
    simpa only [polynomialExceptionalThreshold_one hq, polynomialIrreducibleCount_one,
      one_mul, polynomialExceptionalBound, if_pos rfl, if_true] using binomial_linear_bound hq
  · simpa only [polynomialExceptionalBound, if_neg h] using
      binomial_higher_bound hq (show 2 ≤ d by omega)

/-- Exceptional-prime probability for the monic degree layer. -/
theorem monicLayer_exceptional_prime_bound (F : Type*) [Field F] [Fintype F]
    (hq : 16 ≤ Fintype.card F) (d n : ℕ) (hd : 0 < d) :
    let S := (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d)
    let E := (monicLayer F n).filter (fun g ↦ polynomialExceptionalThreshold F d ≤ (S.filter (· ∣ g)).card)
    (E.card : ℝ)/Fintype.card F^n ≤ polynomialExceptionalBound (Fintype.card F) d :=
  (monicLayer_prime_divisor_tail F d n (polynomialExceptionalThreshold F d)).trans (binomial_exceptional_bound hq hd)

/-- The same bound on every prescribed nonzero leading-coefficient layer. -/
theorem leadingCoeffLayer_exceptional_prime_bound (u : Fˣ)
    (hq : 16 ≤ Fintype.card F) (d n : ℕ) (hd : 0 < d) :
    let S := (polynomialSmoothPrimes F d).filter (fun p ↦ p.natDegree = d)
    let E := (polynomialDegreeLayer F n).filter (fun g ↦ g.leadingCoeff = (u : F) ∧
      polynomialExceptionalThreshold F d ≤ (S.filter (· ∣ g)).card)
    (E.card : ℝ)/Fintype.card F^n ≤ polynomialExceptionalBound (Fintype.card F) d :=
  (leadingCoeffLayer_prime_divisor_tail u d n (polynomialExceptionalThreshold F d)).trans
    (binomial_exceptional_bound hq hd)

end GRHArticle.ProgressionFree

import DiophantineConsistency.SelectiveCoefficientBounds

/-!
# Coefficient bounds for degree-separated quadratic source words

No isolation or source certificate is needed: all collisions, including
unmonitored ones, are controlled by the coordinate one-norm.
-/

namespace DiophantineConsistency.SplitCoefficientBounds

open Polynomial Finset
open SelectiveQuadraticCoding SelectiveCoefficientBounds
open scoped BigOperators

/-- The three independent homogeneous layers, without a dummy coordinate. -/
noncomputable def product {m : ℕ} (w : Fin (m+1) → ℕ) (y : Fin (m+1) → ℤ)
    (D0 D1 D2 : ℤ[X]) : ℤ[X] :=
  encoded w y^2*D2+encoded w y*D1+D0

/-- Linear convolution costs one factor of the coordinate one-norm. -/
theorem abs_coeff_linear_mul_le {m : ℕ} (w : Fin (m+1) → ℕ)
    (y : Fin (m+1) → ℤ) (D : ℤ[X]) (H : ℤ) (hH : 0≤H)
    (hD : ∀ i,|D.coeff i|≤H) (n : ℕ) :
    |(encoded w y*D).coeff n|≤H*∑ i,|y i| := by
  exact SelectiveCoefficientBounds.abs_coeff_encoded_mul_le w y D H hH hD n

/-- Uniform coefficient bound for the complete split source polynomial. -/
theorem abs_coeff_product_le {m : ℕ} (w : Fin (m+1) → ℕ)
    (y : Fin (m+1) → ℤ) (D0 D1 D2 : ℤ[X]) (H : ℤ) (hH : 0≤H)
    (hD0 : ∀ i,|D0.coeff i|≤H) (hD1 : ∀ i,|D1.coeff i|≤H)
    (hD2 : ∀ i,|D2.coeff i|≤H) (n : ℕ) :
    |(product w y D0 D1 D2).coeff n|≤H*((∑ i,|y i|)^2+(∑ i,|y i|)+1) := by
  rw [product,coeff_add,coeff_add]
  calc
    |(encoded w y^2*D2).coeff n+(encoded w y*D1).coeff n+D0.coeff n| ≤
        |(encoded w y^2*D2).coeff n|+|(encoded w y*D1).coeff n|+|D0.coeff n| := by
      have hab := abs_add_le ((encoded w y^2*D2).coeff n) ((encoded w y*D1).coeff n)
      have habc := abs_add_le ((encoded w y^2*D2).coeff n+(encoded w y*D1).coeff n) (D0.coeff n)
      linarith only [hab,habc]
    _≤H*(∑ i,|y i|)^2+H*(∑ i,|y i|)+H :=
      add_le_add (add_le_add (abs_coeff_square_mul_le w y D2 H hH hD2 n)
        (abs_coeff_linear_mul_le w y D1 H hH hD1 n)) (hD0 n)
    _=H*((∑ i,|y i|)^2+(∑ i,|y i|)+1) := by ring

/-- Positive bounded natural coordinates give the dimension-dependent bound.
The coordinates themselves may be zero; only the common upper bound is positive. -/
theorem abs_coeff_bounded_nat_le {m : ℕ} (w : Fin (m+1) → ℕ)
    (y : Fin (m+1) → ℕ) (D0 D1 D2 : ℤ[X]) (H : ℤ) (hH : 0≤H)
    (hD0 : ∀ i,|D0.coeff i|≤H) (hD1 : ∀ i,|D1.coeff i|≤H)
    (hD2 : ∀ i,|D2.coeff i|≤H) {b : ℕ} (hb : 0<b) (hy : ∀ i,y i≤b) (n : ℕ) :
    |(product w (fun i => (y i:ℤ)) D0 D1 D2).coeff n|≤
      (((m+1:ℕ):ℤ)^2+((m+1:ℕ):ℤ)+1)*H*(b:ℤ)^2 := by
  let d : ℤ := (m+1:ℕ)
  let s : ℤ := ∑ i,|(y i:ℤ)|
  have hs0 : 0≤s := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsum : s≤d*(b:ℤ) := by
    calc s≤∑ _i : Fin (m+1),(b:ℤ) := by
           apply Finset.sum_le_sum
           intro i _
           rw [abs_of_nonneg (Int.natCast_nonneg _)]
           exact_mod_cast hy i
         _=d*(b:ℤ) := by simp [d]
  have hbZ : 1≤(b:ℤ) := by exact_mod_cast hb
  have hb2 : (b:ℤ)≤(b:ℤ)^2 := by nlinarith only [mul_nonneg (show 0≤(b:ℤ)-1 by omega) (show 0≤(b:ℤ) by omega)]
  have hdb := mul_le_mul_of_nonneg_left hb2 (show 0≤d by dsimp [d]; positivity)
  have h1b2 : 1≤(b:ℤ)^2 := by nlinarith only [hbZ,hb2]
  have hs2 := pow_le_pow_left₀ hs0 hsum 2
  have hform : s^2+s+1≤(d^2+d+1)*(b:ℤ)^2 := by nlinarith only [hs2,hsum,hdb,h1b2]
  have hbound := abs_coeff_product_le w (fun i => (y i:ℤ)) D0 D1 D2 H hH hD0 hD1 hD2 n
  calc
    |(product w (fun i => (y i:ℤ)) D0 D1 D2).coeff n|≤H*(s^2+s+1) := hbound
    _≤H*((d^2+d+1)*(b:ℤ)^2) := mul_le_mul_of_nonneg_left hform hH
    _=(((m+1:ℕ):ℤ)^2+((m+1:ℕ):ℤ)+1)*H*(b:ℤ)^2 := by dsimp [d]; ring

/-- For 31 coordinates the exact elementary factor is 31^2+31+1=993. -/
theorem abs_coeff_bounded_nat_le_31 (w : Fin 31 → ℕ) (y : Fin 31 → ℕ)
    (D0 D1 D2 : ℤ[X]) (H : ℤ) (hH : 0≤H)
    (hD0 : ∀ i,|D0.coeff i|≤H) (hD1 : ∀ i,|D1.coeff i|≤H)
    (hD2 : ∀ i,|D2.coeff i|≤H) {b : ℕ} (hb : 0<b) (hy : ∀ i,y i≤b) (n : ℕ) :
    |(product w (fun i => (y i:ℤ)) D0 D1 D2).coeff n|≤993*H*(b:ℤ)^2 := by
  simpa using abs_coeff_bounded_nat_le (m:=30) w y D0 D1 D2 H hH hD0 hD1 hD2 hb hy n

/-- A possibly rounded-up power-of-two base gives a strict quarter-base bound. -/
theorem quarter_base_bound_31 (w : Fin 31 → ℕ) (y : Fin 31 → ℕ)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hD0 : ∀ i,|D0.coeff i|≤H) (hD1 : ∀ i,|D1.coeff i|≤H)
    (hD2 : ∀ i,|D2.coeff i|≤H) {b t : ℕ} (hb : 0<b) (ht : 2≤t)
    (hy : ∀ i,y i≤b) (hbase : 4096*H*(b:ℤ)^2≤(2:ℤ)^t) (n : ℕ) :
    |(product w (fun i => (y i:ℤ)) D0 D1 D2).coeff n|<2^(t-2) := by
  have hc := abs_coeff_bounded_nat_le_31 w y D0 D1 D2 H hH.le hD0 hD1 hD2 hb hy n
  have hpos : 0<H*(b:ℤ)^2 := by positivity
  have hpow : (2:ℤ)^t=4*2^(t-2) := by
    simpa [mul_comm] using (pow_sub_mul_pow (2:ℤ) ht).symm
  nlinarith only [hc,hpos,hbase,hpow]

/-- The strict bound in the exact division notation of `SparseBorrowCarry`. -/
theorem quarter_base_div_bound_31 (w : Fin 31 → ℕ) (y : Fin 31 → ℕ)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hD0 : ∀ i,|D0.coeff i|≤H) (hD1 : ∀ i,|D1.coeff i|≤H)
    (hD2 : ∀ i,|D2.coeff i|≤H) {b t : ℕ} (hb : 0<b) (ht : 2≤t)
    (hy : ∀ i,y i≤b) (hbase : 4096*H*(b:ℤ)^2≤(2:ℤ)^t) (n : ℕ) :
    |(product w (fun i => (y i:ℤ)) D0 D1 D2).coeff n|<(2:ℤ)^t/4 := by
  have hc := quarter_base_bound_31 w y D0 D1 D2 hH hD0 hD1 hD2 hb ht hy hbase n
  have hpow : (2:ℤ)^t=4*2^(t-2) := by
    simpa [mul_comm] using (pow_sub_mul_pow (2:ℤ) ht).symm
  omega

end DiophantineConsistency.SplitCoefficientBounds

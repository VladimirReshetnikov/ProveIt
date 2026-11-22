import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`EnergyInequality.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Rational weighted Cauchy–Schwarz, and the powered inequality used to
recover a Mertens bound from the gcd energy. The index set may be empty. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.EnergyInequality
open scoped BigOperators

theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w t μ : ι → ℚ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, μ i * t i)^2 ≤
      (∑ i ∈ s, (μ i)^2 / w i) * (∑ i ∈ s, w i * (t i)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · exact fun i hi => div_nonneg (sq_nonneg _) (hw i hi).le
  · exact fun i hi => mul_nonneg (hw i hi).le (sq_nonneg _)
  · intro i hi
    apply le_of_eq
    field_simp [(hw i hi).ne']

theorem recover {ι : Type*} (s : Finset ι) (w t μ : ι → ℚ) (M K : ℚ)
    (hw : ∀ i ∈ s, 0 < w i) (hm : ∑ i ∈ s, μ i * t i = M)
    (hk : ∑ i ∈ s, (μ i)^2 / w i ≤ K) :
    M^2 ≤ K * ∑ i ∈ s, w i * (t i)^2 := by
  rw [← hm]
  exact (weighted_cauchy s w t μ hw).trans
    (mul_le_mul_of_nonneg_right hk (Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi).le (sq_nonneg _)))

theorem recover_eight {ι : Type*} (s : Finset ι) (w t μ : ι → ℚ) (M : ℚ)
    (hw : ∀ i ∈ s, 0 < w i) (hm : ∑ i ∈ s, μ i * t i = M)
    (hk : ∑ i ∈ s, (μ i)^2 / w i ≤ 8) :
    M^2 ≤ 8 * ∑ i ∈ s, w i * (t i)^2 :=
  recover s w t μ M 8 hw hm hk

theorem power_transfer (M E K B : ℚ) (r : ℕ) (hK : 0 ≤ K)
    (hm : M^2 ≤ K*E) (he : E^r ≤ B) :
    M^(2*r) ≤ K^r*B := by
  calc
    M^(2*r) = (M^2)^r := pow_mul M 2 r
    _ ≤ (K*E)^r := pow_le_pow_left₀ (sq_nonneg M) hm r
    _ = K^r*E^r := mul_pow _ _ _
    _ ≤ K^r*B := mul_le_mul_of_nonneg_left he (pow_nonneg hK r)

/-- Telescoping majorant for a tail of the reciprocal squares. -/
theorem square_tail (b : ℚ) (hb : 0 < b) (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / (b + i + 1)^2 ≤ 1/b - 1/(b+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℚ) := n.cast_nonneg
    have hp : 0 < b+n := by linarith
    have hq : 0 < b+n+1 := by linarith
    have step : 1/(b+n+1)^2 ≤ 1/(b+n) - 1/(b+n+1) := by
      calc
        _ ≤ 1/((b+n)*(b+n+1)) := by
          apply (div_le_div_iff₀ (sq_pos_of_pos hq) (mul_pos hp hq)).2
          nlinarith
        _ = _ := by field_simp [hp.ne', hq.ne']; ring
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc]
    linarith

/-- Offset form of ∑ from m=2 through n+2 of 1/m² ≤ 3/4.
The term m=2 is isolated. -/
theorem square_tail_after_one (n : ℕ) :
    (1:ℚ)/4 + (∑ i ∈ Finset.range n, 1 / ((2:ℚ)+i+1)^2) ≤ 3/4 := by
  have tail := square_tail 2 (by decide) n
  have hp : 0 ≤ 1 / (2+(n:ℚ)) := by
    apply div_nonneg (by decide)
    have := n.cast_nonneg (α := ℚ)
    linarith
  linarith

/-- A convenient bound for ∑ from d=1 through n of 1/d². -/
theorem reciprocal_square_sum (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / ((i:ℚ)+1)^2 ≤ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.sum_range_succ']
    have tail := square_tail 1 (by decide) n
    have hp : 0 ≤ 1 / (1+(n:ℚ)) := by
      apply div_nonneg (by decide)
      have := n.cast_nonneg (α := ℚ)
      linarith
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
      one_pow, div_one, add_comm (1:ℚ) _] at *
    linarith

/-- Positive weights bounded below by d²/4 suffice for the absolute
constant eight. Here i=0 indexes the divisor d=1. -/
theorem bounded_inverse_mass (n : ℕ) (w μ : ℕ → ℚ)
    (hw : ∀ i < n, ((i:ℚ)+1)^2 ≤ 4*w i) (hμ : ∀ i < n, (μ i)^2 ≤ 1) :
    ∑ i ∈ Finset.range n, (μ i)^2 / w i ≤ 8 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, 4 * (1 / ((i:ℚ)+1)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hlt := Finset.mem_range.mp hi
      have hi0 := i.cast_nonneg (α := ℚ)
      have hsq : 0 < ((i:ℚ)+1)^2 := sq_pos_of_pos (by linarith)
      have hwi := hw i hlt
      have hwpos : 0 < w i := by linarith
      calc
        (μ i)^2 / w i ≤ 1 / w i := div_le_div_of_nonneg_right (hμ i hlt) hwpos.le
        _ ≤ 4 / ((i:ℚ)+1)^2 := by
          apply (div_le_div_iff₀ hwpos hsq).2
          simpa using hwi
        _ = _ := by ring
    _ = 4 * ∑ i ∈ Finset.range n, 1 / ((i:ℚ)+1)^2 := (Finset.mul_sum ..).symm
    _ ≤ 8 := by linarith [reciprocal_square_sum n]

/-- Every multiple of k in 0,...,d−1 when k divides d. -/
def block (d k : ℕ) : Finset ℕ :=
  (Finset.range (d/k)).image (fun z => k*z)

def excluded (d : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (d-1)).biUnion (fun i =>
    if i+2 ∣ d then (block d (i+2)).product (block d (i+2)) else ∅)

/-- Count the pairs of residues avoiding simultaneous divisibility by
any divisor 2,...,d of d. -/
def jordanPairs (d : ℕ) : ℕ :=
  (((Finset.range d).product (Finset.range d)) \ excluded d).card

theorem mem_block {d k x : ℕ} (hp : 0 < k) (hk : k ∣ d) :
    x ∈ block d k ↔ x < d ∧ k ∣ x := by
  obtain ⟨m,rfl⟩ := hk
  simp only [block, Finset.mem_image, Finset.mem_range, Nat.mul_div_cancel_left _ hp]
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨Nat.mul_lt_mul_of_pos_left hz hp, ⟨z,rfl⟩⟩
  · rintro ⟨hlt,z,rfl⟩
    exact ⟨z,(Nat.mul_lt_mul_left hp).mp hlt,rfl⟩

theorem excluded_iff {d x y : ℕ} (hx : x < d) (hy : y < d) :
    (x,y) ∈ excluded d ↔ ∃ k, 2 ≤ k ∧ k ≤ d ∧ k ∣ d ∧ k ∣ x ∧ k ∣ y := by
  simp only [excluded, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i,hi,hm⟩
    split at hm
    · rename_i hk
      have hxy := Finset.mem_product.mp hm
      exact ⟨i+2,by omega,by omega,hk,((mem_block (by omega) hk).mp hxy.1).2,
        ((mem_block (by omega) hk).mp hxy.2).2⟩
    · simp at hm
  · rintro ⟨k,hk,hkd,hd,h1,h2⟩
    refine ⟨k-2,by omega,?_⟩
    rw [show k-2+2=k by omega, if_pos hd]
    exact Finset.mem_product.mpr ⟨(mem_block (by omega) hd).mpr ⟨hx,h1⟩,
      (mem_block (by omega) hd).mpr ⟨hy,h2⟩⟩

theorem excluded_iff_gcd {d x y : ℕ} (hx : x < d) (hy : y < d) :
    (x,y) ∈ excluded d ↔ Nat.gcd (Nat.gcd x y) d ≠ 1 := by
  rw [excluded_iff hx hy]
  constructor
  · rintro ⟨k,hk,_,hd,h1,h2⟩ h
    have hdiv := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) hd
    rw [h] at hdiv
    have := Nat.dvd_one.mp hdiv
    omega
  · intro h
    have hd : 0 < d := by omega
    have hpos := Nat.gcd_pos_of_pos_right (Nat.gcd x y) hd
    have hdiv := Nat.gcd_dvd_right (Nat.gcd x y) d
    have hxy := Nat.gcd_dvd_left (Nat.gcd x y) d
    exact ⟨_,by omega,Nat.le_of_dvd hd hdiv,hdiv,
      Nat.dvd_trans hxy (Nat.gcd_dvd_left x y),Nat.dvd_trans hxy (Nat.gcd_dvd_right x y)⟩

theorem jordanPairs_eq (d : ℕ) : jordanPairs d =
    (((Finset.range d).product (Finset.range d)).filter
      (fun z => Nat.gcd (Nat.gcd z.1 z.2) d = 1)).card := by
  unfold jordanPairs
  apply congrArg Finset.card
  ext z
  rcases z with ⟨x,y⟩
  rw [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hxy,good⟩
    have h := Finset.mem_product.mp hxy
    have e := excluded_iff_gcd (Finset.mem_range.mp h.1) (Finset.mem_range.mp h.2)
    exact ⟨hxy,by by_contra hbad; exact good (e.mpr hbad)⟩
  · rintro ⟨hxy,hg⟩
    have h := Finset.mem_product.mp hxy
    exact ⟨hxy,fun bad => (excluded_iff_gcd (Finset.mem_range.mp h.1)
      (Finset.mem_range.mp h.2)).mp bad hg⟩

theorem squared_reciprocals_from_two (n : ℕ) :
    ∑ i ∈ Finset.range n, 1/((i:ℚ)+2)^2 ≤ 3/4 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Finset.sum_range_succ']
    have h := square_tail_after_one n
    convert h using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add]
    rw [add_comm]
    apply congrArg₂ (· + ·)
    · norm_num
    · apply Finset.sum_congr rfl
      intro i hi
      rw [show (i:ℚ)+1+2 = 2+i+1 by ring]

private theorem excluded_bound (d : ℕ) : ((excluded d).card : ℚ) ≤ (d:ℚ)^2*(3/4) := by
  have hcard : (excluded d).card ≤ ∑ i ∈ Finset.range (d-1), (d/(i+2))^2 := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i hi
    split
    · have hp : ((block d (i+2)).product (block d (i+2))).card = (block d (i+2)).card * (block d (i+2)).card := Finset.card_product ..
      rw [hp]
      have hc : (block d (i+2)).card ≤ d/(i+2) := by
        simpa [block] using (Finset.card_image_le (s := Finset.range (d/(i+2))) (f := fun z => (i+2)*z))
      simpa [Nat.pow_two] using Nat.mul_le_mul hc hc
    · simp
  have castCard : ((excluded d).card : ℚ) ≤ ∑ i ∈ Finset.range (d-1), ((d/(i+2) : ℕ):ℚ)^2 := by
    exact_mod_cast hcard
  calc
    _ ≤ _ := castCard
    _ ≤ ∑ i ∈ Finset.range (d-1), (d:ℚ)^2*(1/((i:ℚ)+2)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hdiv : ((d/(i+2):ℕ):ℚ) ≤ d/((i:ℚ)+2) := by
        simpa using (Nat.cast_div_le (α := ℚ) (m := d) (n := i+2))
      calc
        _ ≤ ((d:ℚ)/((i:ℚ)+2))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv _
        _ = _ := by rw [div_pow]; ring
    _ = (d:ℚ)^2 * ∑ i ∈ Finset.range (d-1), 1/((i:ℚ)+2)^2 := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (squared_reciprocals_from_two _) (sq_nonneg _)

/-- The degree-two Jordan count is at least d²/4, including d=0 with
the finite-grid convention. -/
theorem jordan_quarter (d : ℕ) : (d:ℚ)^2 ≤ 4*(jordanPairs d : ℚ) := by
  have h : d^2 ≤ jordanPairs d + (excluded d).card := by
    simpa [jordanPairs, Nat.pow_two] using
      (Finset.card_le_card_sdiff_add_card (s := (Finset.range d).product (Finset.range d)) (t := excluded d))
  have hq : (d:ℚ)^2 ≤ (jordanPairs d:ℚ) + ((excluded d).card:ℚ) := by exact_mod_cast h
  linarith [excluded_bound d]

theorem jordan_inverse_mass (n : ℕ) (μ : ℕ → ℚ)
    (hμ : ∀ i < n, (μ i)^2 ≤ 1) :
    ∑ i ∈ Finset.range n, (μ i)^2 / (jordanPairs (i+1) : ℚ) ≤ 8 :=
  bounded_inverse_mass n _ μ (fun i _ => by simpa using jordan_quarter (i+1)) hμ

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.EnergyInequality

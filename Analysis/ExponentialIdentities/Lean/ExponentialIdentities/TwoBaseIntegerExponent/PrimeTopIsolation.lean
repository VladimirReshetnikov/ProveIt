import ExponentialIdentities.TwoBaseIntegerExponent.CenteredTrace
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime-top cyclotomic isolation and the coefficient-or-denominator tax

For an odd prime `ℓ` and coprime `P > Q > 0`, the homogeneous cyclotomic factor
`Φ̂_{2ℓ}(P, Q) = (P^ℓ + Q^ℓ)/(P + Q) = ∑_{i<ℓ} P^i (-Q)^{ℓ-1-i}` carries the "fresh" primes of
the level-`ℓ` rational symmetric secant `J_ℓ = (s^ℓ - s^{-ℓ})/(r^ℓ - r^{-ℓ})`.  This file
formalizes the two finite ingredients of the reduced-denominator survival theorem.

* **Order of every fresh prime.**  If a prime `p ≠ ℓ` divides `Φ̂_{2ℓ}(P, Q)`, then
  `p ∤ P Q (P + Q)`, the residue `P Q^{-1}` has exact multiplicative order `2ℓ` in `𝔽_p^×`,
  and hence `2ℓ ∣ p - 1`; in particular `p > 2ℓ` and `p` is a unit at every weight whose
  prime support is below `2ℓ`.  For `k < ℓ` such a prime cannot divide `P^{2k} - Q^{2k}`,
  which is the "unique top-level negative valuation" mechanism.
* **Ultrametric unique-minimum lemma and the coefficient tax.**  If one summand of a finite
  sum of rationals has strictly smaller `p`-adic valuation than every other nonzero summand,
  the sum has exactly that valuation.  Consequently, if the top term has valuation `-d` and
  the lower terms are `p`-integral, then for arbitrary rational coefficients `a_k` with
  `|v_p(a_k)| ≤ C`, the denominator exponent `E = max(0, -v_p(S))` satisfies `2 (E + C) ≥ d`:
  a coefficient system can remove the fresh denominator only by carrying comparable `p`-adic
  mass itself.

Both are finite statements; the asymptotic input (the orbit-uniform Corvaja–Zannier bound) is
a paper citation and is not formalized.
-/

namespace LeanProofs.TwoBaseIntegerExponent.PrimeTopIsolation

open Finset CenteredTrace

/-- The homogeneous cyclotomic factor `Φ̂_{2ℓ}(P,Q) = ∑_{i<ℓ} P^i (-Q)^{ℓ-1-i}`, equal to
`(P^ℓ + Q^ℓ)/(P + Q)` for odd `ℓ`. -/
def homCyclotomic (P Q : ℤ) (ℓ : ℕ) : ℤ := homGeomSum P (-Q) ℓ

theorem homCyclotomic_mul (P Q : ℤ) {ℓ : ℕ} (hℓ : Odd ℓ) :
    (P + Q) * homCyclotomic P Q ℓ = P ^ ℓ + Q ^ ℓ := by
  unfold homCyclotomic homGeomSum
  have := (Commute.all P (-Q)).mul_geom_sum₂ ℓ
  rw [hℓ.neg_pow] at this
  rw [← sub_neg_eq_add, ← sub_neg_eq_add, this]

/-- Reduction modulo `P + Q`: `Φ̂_{2ℓ}(P,Q) ≡ ℓ P^{ℓ-1} (mod P + Q)`. -/
theorem homCyclotomic_cast_of_eq_neg {R : Type*} [CommRing R] (P Q : ℤ) (ℓ : ℕ)
    (h : ((Q : ℤ) : R) = -(P : R)) :
    ((homCyclotomic P Q ℓ : ℤ) : R) = (ℓ : R) * (P : R) ^ (ℓ - 1) := by
  unfold homCyclotomic homGeomSum
  push_cast
  rw [h, neg_neg]
  have hterm : ∀ i ∈ Finset.range ℓ, (P : R) ^ i * (P : R) ^ (ℓ - 1 - i) = (P : R) ^ (ℓ - 1) := by
    intro i hi
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.mp hi
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A prime `p ≠ ℓ` dividing `Φ̂_{2ℓ}(P,Q)` for coprime `P, Q` divides neither `P`, nor `Q`, nor
`P + Q`. -/
theorem not_dvd_of_dvd_homCyclotomic {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    (hodd : Odd ℓ) {P Q : ℤ} (hcop : IsCoprime P Q) (hdvd : (p : ℤ) ∣ homCyclotomic P Q ℓ) :
    ¬ (p : ℤ) ∣ P ∧ ¬ (p : ℤ) ∣ Q ∧ ¬ (p : ℤ) ∣ P + Q := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsum : (p : ℤ) ∣ P ^ ℓ + Q ^ ℓ := by
    rw [← homCyclotomic_mul P Q hodd]; exact Dvd.dvd.mul_left hdvd _
  have hPQ : ¬ (p : ℤ) ∣ P ∧ ¬ (p : ℤ) ∣ Q := by
    constructor
    · intro hP
      have hQ : (p : ℤ) ∣ Q ^ ℓ := by
        have : Q ^ ℓ = (P ^ ℓ + Q ^ ℓ) - P ^ ℓ := by ring
        rw [this]; exact dvd_sub hsum (dvd_pow hP hℓ.ne_zero)
      exact hp'.not_unit (hcop.isUnit_of_dvd' hP (hp'.dvd_of_dvd_pow hQ))
    · intro hQ
      have hP : (p : ℤ) ∣ P ^ ℓ := by
        have : P ^ ℓ = (P ^ ℓ + Q ^ ℓ) - Q ^ ℓ := by ring
        rw [this]; exact dvd_sub hsum (dvd_pow hQ hℓ.ne_zero)
      exact hp'.not_unit (hcop.isUnit_of_dvd' (hp'.dvd_of_dvd_pow hP) hQ)
  refine ⟨hPQ.1, hPQ.2, fun hPQ' => ?_⟩
  -- Modulo `p`, `Q = -P`, so `Φ̂ ≡ ℓ P^{ℓ-1}`; then `p ∣ ℓ P^{ℓ-1}`, forcing `p = ℓ`.
  haveI := Fact.mk hp
  have hcast : ((Q : ℤ) : ZMod p) = -((P : ℤ) : ZMod p) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, ← Int.cast_add]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hPQ'
  have h0 : ((homCyclotomic P Q ℓ : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  rw [homCyclotomic_cast_of_eq_neg P Q ℓ hcast] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · have : (p : ℤ) ∣ (ℓ : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    have hdl : p ∣ ℓ := Int.natCast_dvd_natCast.mp this
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp hdl)
  · have hP : (p : ℤ) ∣ P ^ (ℓ - 1) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact h
    exact hPQ.1 (hp'.dvd_of_dvd_pow hP)

/-- **Order of every fresh prime.**  If a prime `p ≠ ℓ` divides `Φ̂_{2ℓ}(P,Q)` (coprime `P, Q`,
odd prime `ℓ`), then `P Q^{-1}` has exact order `2ℓ` in `ZMod p`. -/
theorem orderOf_eq_two_mul_of_dvd_homCyclotomic {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hpℓ : p ≠ ℓ) (hodd : Odd ℓ) {P Q : ℤ} (hcop : IsCoprime P Q)
    (hdvd : (p : ℤ) ∣ homCyclotomic P Q ℓ) :
    haveI := Fact.mk hp
    orderOf (((P : ℤ) : ZMod p) * ((Q : ℤ) : ZMod p)⁻¹) = 2 * ℓ := by
  haveI := Fact.mk hp
  obtain ⟨hP, hQ, hPQ⟩ := not_dvd_of_dvd_homCyclotomic hp hℓ hpℓ hodd hcop hdvd
  have hP0 : ((P : ℤ) : ZMod p) ≠ 0 := fun h => hP ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hQ0 : ((Q : ℤ) : ZMod p) ≠ 0 := fun h => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  set x : ZMod p := ((P : ℤ) : ZMod p) * ((Q : ℤ) : ZMod p)⁻¹ with hx
  -- `x^ℓ = -1`.
  have hsum : ((P ^ ℓ + Q ^ ℓ : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← homCyclotomic_mul P Q hodd]
    exact Dvd.dvd.mul_left hdvd _
  push_cast at hsum
  have hxℓ : x ^ ℓ = -1 := by
    rw [hx, mul_pow, inv_pow, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hQ0), neg_one_mul,
      eq_neg_iff_add_eq_zero]
    exact hsum
  -- `p` is odd: otherwise `-1 = 1` would give `x^ℓ = 1` and `x^{2ℓ} = 1`, fine, but we need
  -- `-1 ≠ 1`, which holds since `p ≠ 2` (as `2 ∤ P^ℓ + Q^ℓ` for coprime `P, Q`).
  have hp2 : p ≠ 2 := by
    rintro rfl
    -- `P` and `Q` are both odd, so `P + Q` is even.
    push_cast at hP hQ hPQ
    omega
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have : ((2 : ℤ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have h2 : p ∣ 2 := Int.natCast_dvd_natCast.mp (by exact_mod_cast this)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  apply orderOf_eq_of_pow_and_pow_div_prime (by have := hℓ.pos; omega)
  · rw [pow_mul', hxℓ]; norm_num
  · intro q hq hqd
    -- The prime divisors of `2ℓ` are `2` and `ℓ`.
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h2 | hℓ'
    · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
      subst this
      rw [show 2 * ℓ / 2 = ℓ by omega, hxℓ]
      exact hneg
    · have : q = ℓ := (Nat.prime_dvd_prime_iff_eq hq hℓ).mp hℓ'
      subst this
      rw [Nat.mul_div_cancel 2 hℓ.pos]
      intro hsq
      -- `x^2 = 1` gives `x = ±1`; `x = 1` contradicts `x^ℓ = -1`, `x = -1` gives `p ∣ P + Q`.
      have : (x - 1) * (x + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp this with h | h
      · have hx1 : x = 1 := sub_eq_zero.mp h
        rw [hx1, one_pow] at hxℓ
        exact hneg hxℓ.symm
      · have hx1 : x = -1 := eq_neg_of_add_eq_zero_left h
        apply hPQ
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hx, mul_inv_eq_iff_eq_mul₀ hQ0, neg_one_mul] at hx1
        rw [hx1]; ring

/-- Every fresh prime satisfies `2ℓ ∣ p - 1`; in particular `p > 2ℓ`. -/
theorem two_mul_dvd_sub_one_of_dvd_homCyclotomic {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hpℓ : p ≠ ℓ) (hodd : Odd ℓ) {P Q : ℤ} (hcop : IsCoprime P Q)
    (hdvd : (p : ℤ) ∣ homCyclotomic P Q ℓ) : 2 * ℓ ∣ p - 1 ∧ 2 * ℓ < p := by
  haveI := Fact.mk hp
  obtain ⟨hP, hQ, _⟩ := not_dvd_of_dvd_homCyclotomic hp hℓ hpℓ hodd hcop hdvd
  have hP0 : ((P : ℤ) : ZMod p) ≠ 0 := fun h => hP ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hQ0 : ((Q : ℤ) : ZMod p) ≠ 0 := fun h => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hord := orderOf_eq_two_mul_of_dvd_homCyclotomic hp hℓ hpℓ hodd hcop hdvd
  have hx0 : ((P : ℤ) : ZMod p) * ((Q : ℤ) : ZMod p)⁻¹ ≠ 0 := mul_ne_zero hP0 (inv_ne_zero hQ0)
  have hdvd' := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd'
  refine ⟨hdvd', ?_⟩
  have := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd'
  omega

/-- For `k < ℓ`, a fresh prime does not divide `P^{2k} - Q^{2k}`: the lower secant levels are
`p`-integral. -/
theorem not_dvd_pow_sub_pow_of_lt {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    (hodd : Odd ℓ) {P Q : ℤ} (hcop : IsCoprime P Q) (hdvd : (p : ℤ) ∣ homCyclotomic P Q ℓ)
    {k : ℕ} (hk0 : 0 < k) (hk : k < ℓ) : ¬ (p : ℤ) ∣ P ^ (2 * k) - Q ^ (2 * k) := by
  haveI := Fact.mk hp
  intro h
  obtain ⟨hP, hQ, _⟩ := not_dvd_of_dvd_homCyclotomic hp hℓ hpℓ hodd hcop hdvd
  have hQ0 : ((Q : ℤ) : ZMod p) ≠ 0 := fun h => hQ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hord := orderOf_eq_two_mul_of_dvd_homCyclotomic hp hℓ hpℓ hodd hcop hdvd
  have hx : (((P : ℤ) : ZMod p) * ((Q : ℤ) : ZMod p)⁻¹) ^ (2 * k) = 1 := by
    rw [mul_pow, inv_pow, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hQ0), one_mul,
      ← sub_eq_zero, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  have := orderOf_dvd_of_pow_eq_one hx
  rw [hord] at this
  have := Nat.le_of_dvd (by omega) this
  omega

/-! ### The ultrametric unique-minimum lemma and the coefficient tax -/

/-- If `t ≠ 0` and every nonzero `r i` has `p`-adic valuation strictly larger than `v_p t`,
then `t + ∑ r i ≠ 0` and `v_p (t + ∑ r i) = v_p t`. -/
theorem padicValRat_add_sum_eq {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (t : ℚ)
    (ht : t ≠ 0) (r : ι → ℚ)
    (hr : ∀ i ∈ s, r i = 0 ∨ padicValRat p t < padicValRat p (r i)) :
    t + ∑ i ∈ s, r i ≠ 0 ∧ padicValRat p (t + ∑ i ∈ s, r i) = padicValRat p t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ht]
  | insert a s ha ih =>
    have ih := ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha,
      show t + (r a + ∑ i ∈ s, r i) = (t + ∑ i ∈ s, r i) + r a by ring]
    by_cases h0 : r a = 0
    · rw [h0, add_zero]; exact ih
    · have hlt : padicValRat p t < padicValRat p (r a) :=
        (hr a (Finset.mem_insert_self a s)).resolve_left h0
      have hu0 := ih.1
      have hval : padicValRat p (t + ∑ i ∈ s, r i) < padicValRat p (r a) := by
        rw [ih.2]; exact hlt
      have hne : t + ∑ i ∈ s, r i + r a ≠ 0 := by
        intro h
        have : r a = -(t + ∑ i ∈ s, r i) := eq_neg_of_add_eq_zero_right h
        rw [this, padicValRat.neg] at hval
        exact lt_irrefl _ hval
      refine ⟨hne, ?_⟩
      rw [padicValRat.add_eq_of_lt hne hu0 h0 hval, ih.2]

/-- **Unique top-level negative valuation.**  If the top summand `a_top J_top` has valuation
`v_p(a_top) - d` and every other summand is either zero or has valuation `> v_p(a_top) - d`,
the whole sum is nonzero with valuation `v_p(a_top) - d`. -/
theorem padicValRat_sum_eq_top {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (top : ℚ) (htop : top ≠ 0) (r : ι → ℚ)
    (hr : ∀ i ∈ s, r i = 0 ∨ padicValRat p top < padicValRat p (r i)) :
    top + ∑ i ∈ s, r i ≠ 0 ∧ padicValRat p (top + ∑ i ∈ s, r i) = padicValRat p top :=
  padicValRat_add_sum_eq s top htop r hr

/-- **Coefficient-or-denominator tax.**  Let `S = a_top J_top + ∑ a_i J_i` where
`v_p(J_top) = -d`, the lower `J_i` are `p`-integral (or zero), and all nonzero coefficients
satisfy `|v_p(a)| ≤ C`.  Then with `E = max(0, -v_p(S))` one has `d ≤ 2 (E + C)`: removing
the fresh denominator requires coefficients carrying comparable `p`-adic mass. -/
theorem coefficient_tax {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (aTop JTop : ℚ) (a J : ι → ℚ) (d C : ℕ)
    (haTop : aTop ≠ 0) (hJTop : JTop ≠ 0) (hvJ : padicValRat p JTop = -(d : ℤ))
    (hCtop : |padicValRat p aTop| ≤ C)
    (hC : ∀ i ∈ s, a i = 0 ∨ |padicValRat p (a i)| ≤ C)
    (hJ : ∀ i ∈ s, J i = 0 ∨ 0 ≤ padicValRat p (J i)) :
    (d : ℤ) ≤ 2 * (max 0 (-padicValRat p (aTop * JTop + ∑ i ∈ s, a i * J i)) + C) := by
  by_cases hdC : (d : ℤ) ≤ 2 * C
  · have := le_max_left 0 (-padicValRat p (aTop * JTop + ∑ i ∈ s, a i * J i))
    linarith
  rw [not_le] at hdC
  have htop0 : aTop * JTop ≠ 0 := mul_ne_zero haTop hJTop
  have hvtop : padicValRat p (aTop * JTop) = padicValRat p aTop - d := by
    rw [padicValRat.mul haTop hJTop, hvJ]; ring
  have hCtop' := (abs_le.mp hCtop)
  have key := padicValRat_sum_eq_top (p := p) s (aTop * JTop) htop0 (fun i => a i * J i) (by
    intro i hi
    by_cases ha : a i = 0
    · left; rw [ha, zero_mul]
    by_cases hJi : J i = 0
    · left; rw [hJi, mul_zero]
    right
    rw [padicValRat.mul ha hJi, hvtop]
    have h1 := (hC i hi).resolve_left ha
    have h2 := (hJ i hi).resolve_left hJi
    have := (abs_le.mp h1).1
    linarith)
  rw [key.2, hvtop]
  have : (d : ℤ) - C ≤ max 0 (-(padicValRat p aTop - d)) := by
    refine le_trans ?_ (le_max_right _ _)
    linarith
  linarith

end LeanProofs.TwoBaseIntegerExponent.PrimeTopIsolation

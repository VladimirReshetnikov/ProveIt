import Std

/-!
# Integer consequences used in the type-label construction

The degree test in the paper reduces to divisibility of an exponent by
`3*H`. This file checks the resulting divisibility obstruction, stability
under the additive shifts induced by scaling, and the local prime-power
bound for the order of the norm. All statements are about natural numbers.
-/

namespace LabelArithmetic

/-- Two independent divisors obstruct a prime-power multiple whenever that
power is coprime to at least one of the divisors. -/
theorem power_obstruction {A H k ell : Nat} (u : Nat)
    (ha : ¬ A ∣ k) (hh : ¬ H ∣ k) (split : A.Coprime ell ∨ H.Coprime ell) :
    ¬ A*H ∣ k*ell^u := by
  intro h
  cases split with
  | inl hA =>
    exact ha ((hA.pow_right u).dvd_of_dvd_mul_right (Nat.dvd_trans (Nat.dvd_mul_right A H) h))
  | inr hH =>
    exact hh ((hH.pow_right u).dvd_of_dvd_mul_right (Nat.dvd_trans (Nat.dvd_mul_left H A) h))

theorem three_coprime_of_not_dvd {ell : Nat} (h : ¬ 3 ∣ ell) : Nat.Coprime 3 ell := by
  change Nat.gcd 3 ell = 1
  rw [Nat.gcd_rec]
  have hlt := Nat.mod_lt ell (by decide : 0 < 3)
  have hne : ell%3 ≠ 0 := fun he => h (Nat.dvd_iff_mod_eq_zero.mpr he)
  have hr : ell%3 = 1 ∨ ell%3 = 2 := by omega
  cases hr with
  | inl h1 => rw [h1]; decide
  | inr h2 => rw [h2]; decide

/-- `primeDivisors` is the divisor clause in the elementary definition of
primality. Applying it only to the divisor 3 is enough. -/
theorem prime_power_obstruction {H k ell : Nat} (u : Nat)
    (primeDivisors : ∀ d : Nat, d ∣ ell → d = 1 ∨ d = ell)
    (cop : H.Coprime 3) (h3 : ¬ 3 ∣ k) (hH : ¬ H ∣ k) :
    ¬ 3*H ∣ k*ell^u := by
  apply power_obstruction u h3 hH
  by_cases hd : 3 ∣ ell
  · have he : 3 = ell := (primeDivisors 3 hd).resolve_left (by decide)
    exact Or.inr (he ▸ cop)
  · exact Or.inl (three_coprime_of_not_dvd hd)

/-- Any constituent divisor test survives a shift by a multiple of the
joint modulus. In particular this applies separately to 3, H and every
required p^6 once divisibility of the shift modulus has been established. -/
theorem shift_iff {D M k t : Nat} (h : D ∣ M) :
    (D ∣ k + M*t) ↔ D ∣ k :=
  (Nat.dvd_add_iff_left (Nat.dvd_mul_right_of_dvd h t)).symm

theorem selected_shift {H k t : Nat} :
    (¬ 3 ∣ k + (3*H)*t) ∧ (¬ H ∣ k + (3*H)*t) ↔ (¬ 3 ∣ k) ∧ (¬ H ∣ k) := by
  rw [shift_iff (Nat.dvd_mul_right 3 H), shift_iff (Nat.dvd_mul_left H 3)]

/-- In a cyclic group of order `M`, the candidate generator power `k`
has order `M/gcd(M,k)`; that candidate exponent always kills `k` modulo M. -/
theorem mul_order_multiple (M k : Nat) : M ∣ k*(M/(M.gcd k)) := by
  have hk := Nat.gcd_dvd_right M k
  obtain ⟨t, ht⟩ := hk
  refine ⟨t, ?_⟩
  have eq := Nat.mul_div_cancel' (Nat.gcd_dvd_left M k)
  calc k * (M/(M.gcd k)) = ((M.gcd k) * (M/(M.gcd k)))*t := by rw [ht] at ⊢; grind
       _ = M*t := by rw [eq]

/-- Remove the p-part `p^t` of `k` from a bound `p^(v+t) ∣ k*x`.
The coprime part of k contributes no loss. -/
theorem remove_local_part {p k v t k0 x : Nat} (hp : 0 < p) (hc : p.Coprime k0)
    (hk : k = p^t*k0) (h : p^(v+t) ∣ k*x) : p^v ∣ x := by
  have hd : p^t*p^v ∣ p^t*(k0*x) := by
    rw [← Nat.pow_add, Nat.add_comm t v, ← Nat.mul_assoc, ← hk]
    exact h
  exact (hc.pow_left v).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp) hd)

/-- If the p-part lost from the exponent is at most `v` and `p^(2*v)`
divides the group order, the new element's order is still divisible by `p^v`.
In the paper the loss is at most 5 and v is at least 6 away from 3. -/
theorem local_norm_order {M p k v t k0 : Nat}
    (hp : 0 < p) (hc : p.Coprime k0) (hk : k = p^t*k0)
    (budget : t ≤ v) (hM : p^(2*v) ∣ M) : p^v ∣ M/(M.gcd k) := by
  exact remove_local_part hp hc hk
    (Nat.dvd_trans (Nat.pow_dvd_pow p (show v+t ≤ 2*v by omega))
      (Nat.dvd_trans hM (mul_order_multiple M k)))

end LabelArithmetic

#print axioms LabelArithmetic.prime_power_obstruction
#print axioms LabelArithmetic.selected_shift
#print axioms LabelArithmetic.local_norm_order

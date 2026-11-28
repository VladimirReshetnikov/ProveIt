import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Algebraic support for the finite-field label replacement

Checked against Lean 4.35.0 and the Mathlib revision pinned by ProveIt.
These lemmas formalize the root-order obstruction, its power-orbit consequence,
and the scalar nonresonance bound. They do not import or rebuild the GRH project.
-/

namespace LabelReplacement

/-- If the order of `w` has a factor 3 and another prime factor, expressed without
factoring the order, then no prime-power kills `w`. -/
theorem no_prime_power_kills {G : Type*} [Monoid G] {w : G} {K : ℕ}
    (hK : Nat.Coprime 3 K) (hperiod : w ^ (3 * K) = 1)
    (hnotK : w ^ K ≠ 1) (hnot3 : w ^ 3 ≠ 1)
    {ell : ℕ} (hell : ell.Prime) (u : ℕ) : w ^ (ell ^ u) ≠ 1 := by
  intro hkill
  have hord : orderOf w ∣ 3 * K := orderOf_dvd_of_pow_eq_one hperiod
  have hellord : orderOf w ∣ ell ^ u := orderOf_dvd_of_pow_eq_one hkill
  by_cases hthree : ell = 3
  · subst ell
    have hcop : Nat.Coprime (orderOf w) K :=
      (hK.pow_left u).coprime_dvd_left hellord
    exact hnot3 (orderOf_dvd_iff_pow_eq_one.mp
      (hcop.dvd_of_dvd_mul_right hord))
  · have hcop : Nat.Coprime (orderOf w) 3 :=
      (((Nat.coprime_primes Nat.prime_three hell).mpr (Ne.symm hthree)).pow_right u
        |>.coprime_dvd_right hellord).symm
    exact hnotK (orderOf_dvd_iff_pow_eq_one.mp
      (hcop.dvd_of_dvd_mul_left hord))

/-- The elementary nonresonance bound used by the scalar inertia argument.
One of 2 and 3 is different from `ell`, so its full power cannot be absorbed
by `ell^u` or by the small positive integer `j*t`. -/
theorem six_power_not_dvd {s j t ell : ℕ} (hell : ell.Prime)
    (hpositive : 0 < j * t) (hsmall : j * t < 2 ^ s) (u : ℕ) :
    ¬6 ^ s ∣ j * (ell ^ u * t) := by
  intro hdiv
  obtain ⟨p, hp, hpell, hp6⟩ :
      ∃ p : ℕ, p.Prime ∧ p ≠ ell ∧ p ∣ 6 := by
    by_cases htwo : ell = 2
    · exact ⟨3, Nat.prime_three, by omega, by norm_num⟩
    · exact ⟨2, Nat.prime_two, Ne.symm htwo, by norm_num⟩
  have hpower : p ^ s ∣ 6 ^ s := pow_dvd_pow_of_dvd hp6 s
  have hproduct : p ^ s ∣ ell ^ u * (j * t) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hpower.trans hdiv
  have hcop : Nat.Coprime (p ^ s) (ell ^ u) :=
    Nat.coprime_pow_primes s u hp hell hpell
  have hdivsmall : p ^ s ∣ j * t := hcop.dvd_of_dvd_mul_left hproduct
  exact Nat.not_dvd_of_pos_of_lt hpositive
    (hsmall.trans_le (Nat.pow_le_pow_left hp.two_le s)) hdivsmall

/-- A version whose modulus has an arbitrary nonnegative extra exponent. -/
theorem six_power_add_not_dvd {s j t ell : ℕ} (hell : ell.Prime)
    (hpositive : 0 < j * t) (hsmall : j * t < 2 ^ s) (u c : ℕ) :
    ¬6 ^ (s + c) ∣ j * (ell ^ u * t) := by
  intro hdiv
  apply six_power_not_dvd hell hpositive hsmall u
  have hmod : 6 ^ s ∣ 6 ^ (s + c) := by
    rw [pow_add]
    exact dvd_mul_right (6 ^ s) (6 ^ c)
  exact hmod.trans hdiv

/-- Generic Frobenius-style consequence. In a multiplicative group, the map
`x ↦ x^q` has full orbit length `3^(a+1)` on every prime-power of `z`, provided
the stated period and the two root-order exclusions hold.

For the finite-field application use the units group, `K=(A^2+A+1)/3`, and
`A=q^(3^a)`. The finite-field count and construction are proved in the paper.
-/
theorem power_orbit_injective {G : Type*} [Group G] {z : G} {q a K : ℕ}
    (hq : 0 < q) (hK : Nat.Coprime 3 K)
    (hfixed : z ^ (q ^ (3 ^ (a + 1))) = z)
    (hperiod : (z ^ (q ^ (3 ^ a) - 1)) ^ (3 * K) = 1)
    (hnotK : (z ^ (q ^ (3 ^ a) - 1)) ^ K ≠ 1)
    (hnot3 : (z ^ (q ^ (3 ^ a) - 1)) ^ 3 ≠ 1)
    {ell : ℕ} (hell : ell.Prime) (u : ℕ) :
    Set.InjOn (fun i : ℕ ↦ (z ^ (ell ^ u)) ^ (q ^ i))
      (Set.Iio (3 ^ (a + 1))) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : (z ^ (q ^ (3 ^ a) - 1)) ^ (ell ^ u) ≠ 1 :=
    no_prime_power_kills hK hperiod hnotK hnot3 hell u
  have hA : 1 ≤ q ^ (3 ^ a) := Nat.one_le_pow _ _ hq
  have hnotperiod : ¬Function.IsPeriodicPt (fun x : G ↦ x ^ q)
      (3 ^ a) (z ^ (ell ^ u)) := by
    intro h
    have hfix : (z ^ (ell ^ u)) ^ (q ^ (3 ^ a)) = z ^ (ell ^ u) := by
      simpa [Function.IsPeriodicPt, Function.IsFixedPt, pow_iterate] using h
    apply hne
    rw [pow_right_comm]
    apply mul_right_cancel (b := z ^ (ell ^ u))
    simpa [← pow_succ, Nat.sub_add_cancel hA] using hfix
  have hperiod' : Function.IsPeriodicPt (fun x : G ↦ x ^ q)
      (3 ^ (a + 1)) (z ^ (ell ^ u)) := by
    simp [Function.IsPeriodicPt, Function.IsFixedPt, pow_iterate,
      pow_right_comm z (ell ^ u), hfixed]
  have hminimal : Function.minimalPeriod (fun x : G ↦ x ^ q) (z ^ (ell ^ u)) =
      3 ^ (a + 1) := Function.minimalPeriod_eq_prime_pow hnotperiod hperiod'
  simpa [hminimal, pow_iterate] using
    (Function.iterate_injOn_Iio_minimalPeriod
      (f := fun x : G ↦ x ^ q) (x := z ^ (ell ^ u)))

end LabelReplacement

#print axioms LabelReplacement.no_prime_power_kills
#print axioms LabelReplacement.six_power_not_dvd
#print axioms LabelReplacement.six_power_add_not_dvd
#print axioms LabelReplacement.power_orbit_injective

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie
import OAI.Combinatorics.Progressions.Geometry.WeightedSupportDropRename

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedDerivation_mul (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (P Q : MvPolynomial σ R) (d e k : ℕ)
    (hP : P ∈ weightedSupportLE w d) (hQ : Q ∈ weightedSupportLE w e)
    (hDP : D P ∈ weightedSupportDrop w d k) (hDQ : D Q ∈ weightedSupportDrop w e k) :
    D (P * Q) ∈ weightedSupportDrop w (d + e) k := by
  rw [D.leibniz, smul_eq_mul, smul_eq_mul]
  apply (weightedSupportDrop w (d + e) k).add_mem (weightedSupportLE_mul_drop hP hDQ)
  simpa only [Nat.add_comm e d] using weightedSupportLE_mul_drop hQ hDP

theorem weightedDerivation_monomial_one (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k) (a : σ →₀ ℕ) :
    D (monomial a 1) ∈ weightedSupportDrop w (Finsupp.weight w a) k := by
  classical
  have hsingle (i : σ) (n : ℕ) :
      D (monomial (Finsupp.single i n) 1) ∈ weightedSupportDrop w (n * w i) k := by
    induction n with
    | zero =>
        simp only [Finsupp.single_zero, zero_mul]
        change D 1 ∈ _
        rw [D.map_one_eq_zero]
        exact Submodule.zero_mem _
    | succ n ih =>
        have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
        simp only [Finsupp.weight_single, smul_eq_mul] at hp
        have hh := weightedDerivation_mul w D (monomial (Finsupp.single i n) 1)
          (X i) (n * w i) (w i) k hp (weightedSupportLE_X w i) ih (hD i)
        simpa only [X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.succ_mul]
          using hh
  induction a using Finsupp.induction with
  | zero =>
      change D 1 ∈ weightedSupportDrop w 0 k
      rw [D.map_one_eq_zero]
      exact Submodule.zero_mem _
  | @single_add i n a hi hn ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      have hq := weightedSupportLE_monomial w a (1 : R)
      have hh := weightedDerivation_mul w D (monomial (Finsupp.single i n) 1)
        (monomial a 1) (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w a) k hp hq
        (by simpa only [Finsupp.weight_single, smul_eq_mul] using hsingle i n) ih
      simpa only [monomial_mul_monomial, one_mul, map_add] using hh

theorem weightedDerivation_monomial (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k) (a : σ →₀ ℕ) (c : R) :
    D (monomial a c) ∈ weightedSupportDrop w (Finsupp.weight w a) k := by
  have hm : C c * monomial a (1 : R) = monomial a c := by
    change monomial 0 c * monomial a 1 = monomial a c
    rw [monomial_mul_monomial, zero_add, mul_one]
  rw [← hm, D.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero, smul_eq_mul]
  simpa only [zero_add] using weightedSupportLE_mul_drop (weightedSupportLE_C w 0 c)
    (weightedDerivation_monomial_one w D k hD a)

theorem weightedDerivation_apply (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n r : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) :
    D P ∈ weightedSupportDrop w n (r + k) := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportDrop w n (r + k)).sum_mem
  intro a ha
  have hm := weightedDerivation_monomial w D k hD a (P.coeff a)
  intro b hb
  have h1 : Finsupp.weight w b + k ≤ Finsupp.weight w a := hm hb
  have h2 : Finsupp.weight w a + r ≤ n := hP ha
  change Finsupp.weight w b + (r + k) ≤ n
  omega

theorem weightedDerivation_apply_le (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportLE w n) :
    D P ∈ weightedSupportDrop w n k := by
  rw [← weightedSupportDrop_zero] at hP
  simpa only [Nat.zero_add] using weightedDerivation_apply w D k hD hP

theorem weightedDerivation_bracket (w : σ → ℕ)
    (D E : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (a b : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) a)
    (hE : ∀ i, E (X i) ∈ weightedSupportDrop w (w i) b) (i : σ) :
    ⁅D, E⁆ (X i) ∈ weightedSupportDrop w (w i) (a + b) := by
  rw [Derivation.commutator_apply]
  apply (weightedSupportDrop w (w i) (a + b)).sub_mem
  · simpa only [Nat.add_comm b a] using weightedDerivation_apply w D a hD (hE i)
  · exact weightedDerivation_apply w E b hE (hD i)

theorem weightedDerivation_pow (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (k : ℕ)
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k)
    {n r : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportDrop w n r) (m : ℕ) :
    (D.toLinearMap ^ m) P ∈ weightedSupportDrop w n (r + m * k) := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.zero_mul, Nat.add_zero] using hP
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      change D ((D.toLinearMap ^ m) P) ∈ weightedSupportDrop w n (r + (m + 1) * k)
      simpa only [Nat.succ_mul, Nat.add_assoc] using weightedDerivation_apply w D k hD ih

theorem weightedDerivation_pow_eq_zero (w : σ → ℕ)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hD : ∀ i, D (X i) ∈ weightedSupportDrop w (w i) 1)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P ∈ weightedSupportLE w n) :
    (D.toLinearMap ^ (n + 1)) P = 0 := by
  rw [← weightedSupportDrop_zero] at hP
  have h := weightedDerivation_pow w D 1 hD hP (n + 1)
  simp only [Nat.mul_one, Nat.zero_add] at h
  exact weightedSupportDrop_eq_zero (Nat.lt_succ_self n) h

end Erdos3

end

end OAI

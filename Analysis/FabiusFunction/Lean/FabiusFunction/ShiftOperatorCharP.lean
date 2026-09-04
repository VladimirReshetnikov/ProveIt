import FabiusFunction.TouchardPolyCongruence
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
# The shift operator on sequences and linear recurrences in characteristic `p`

The shift `E : (ℕ → A) → (ℕ → A)`, `(E b) n = b (n+1)`, is an `A`-linear endomorphism, so every
polynomial `P ∈ A[Y]` acts on sequences through `aeval E P`.  A sequence `b` satisfies the linear
recurrence with characteristic polynomial `q` exactly when `aeval E q b = 0`, and then
`aeval E P b = 0` for every multiple `P` of `q` (`aeval_shiftEnd_eq_zero_of_dvd`).

In characteristic `p` the Frobenius map turns the recurrence `E^p = E + c` into
`E^{p^m} = E + ∑_{r<m} c^{p^r}` (`mk_X_pow_prime_pow`, `shift_pow_char_pow`), and for `c = 1`
over `ZMod p` the Fermat product `∏_{j<p} (Y + j) = Y^p - Y` gives `E^{N_p} = 1` with
`N_p = 1 + p + ⋯ + p^{p-1}` (`shift_pow_period`).

Applied to Touchard's congruence `B(n+p) ≡ B(n+1) + B(n) (mod p)` this yields the prime-power
shift `B(n+p^m) ≡ m B(n) + B(n+1) (mod p)` (`bell_add_prime_pow_modEq`), its Touchard-polynomial
refinement `T_{n+p^m} ≡ T_{n+1} + T_n ∑_{r=1}^m x^{p^r} (mod p)`
(`touchardPolynomial_add_prime_pow`), and the universal period bound
`B(n + N_p) ≡ B(n) (mod p)` (`bell_add_sum_prime_pow_modEq`).

## Main results

* `shiftEnd`, `shiftEnd_apply`, `shiftEnd_pow_apply`, `aeval_shiftEnd_apply`,
  `aeval_shiftEnd_eq_zero_of_dvd`.
* `mk_X_pow_prime_pow`, `shift_pow_char_pow`.
* `prod_univ_X_sub_C`, `prod_range_X_add_C_natCast`, `shift_pow_period`.
* `bell_add_prime_pow_modEq`, `touchardPolynomial_add_prime_pow`, `bell_add_sum_prime_pow_modEq`,
  `bell_add_mul_sum_prime_pow_modEq`, `period_dvd_of_minimal`, `bell_period_dvd_sum_prime_pow`.
-/

set_option autoImplicit false

open Polynomial Finset

namespace Fabius

section ShiftOperator

variable (A : Type*) [CommRing A]

/-- The shift endomorphism `(E b) n = b (n + 1)` on sequences. -/
noncomputable def shiftEnd : Module.End A (ℕ → A) := LinearMap.funLeft A A (· + 1)

/-- Applying the shift endomorphism advances the sequence index by one. -/
@[simp] theorem shiftEnd_apply (b : ℕ → A) (n : ℕ) : shiftEnd A b n = b (n + 1) := rfl

/-- `(E^k b) n = b (n + k)`. -/
theorem shiftEnd_pow_apply (k : ℕ) (b : ℕ → A) : (shiftEnd A ^ k) b = fun n => b (n + k) := by
  induction k with
  | zero =>
    ext n
    rw [pow_zero, Module.End.one_apply, Nat.add_zero]
  | succ k ih =>
    ext n
    rw [pow_succ', Module.End.mul_apply, ih]
    show b (n + 1 + k) = b (n + (k + 1))
    rw [show n + 1 + k = n + (k + 1) by omega]

/-- The polynomial `P = ∑ P_k Y^k` acts on sequences by `(P b) n = ∑_k P_k b (n + k)`. -/
theorem aeval_shiftEnd_apply (P : A[X]) (b : ℕ → A) :
    aeval (shiftEnd A) P b = fun n => ∑ k ∈ range (P.natDegree + 1), P.coeff k * b (n + k) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  ext n
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.smul_apply, shiftEnd_pow_apply, Pi.smul_apply, smul_eq_mul]

/-- A solution of the recurrence `q` is annihilated by every multiple of `q`. -/
theorem aeval_shiftEnd_eq_zero_of_dvd {q P : A[X]} {b : ℕ → A}
    (hb : aeval (shiftEnd A) q b = 0) (hdvd : q ∣ P) : aeval (shiftEnd A) P b = 0 := by
  obtain ⟨Q, rfl⟩ := hdvd
  rw [mul_comm, map_mul, Module.End.mul_apply, hb, map_zero]

/-- `((Y^k - (Y + c)) b) n = b (n+k) - (b (n+1) + c b n)`. -/
theorem aeval_shiftEnd_X_pow_sub_apply (k : ℕ) (c : A) (b : ℕ → A) (n : ℕ) :
    aeval (shiftEnd A) (X ^ k - (X + C c)) b n = b (n + k) - (b (n + 1) + c * b n) := by
  simp only [map_sub, map_add, aeval_X_pow, aeval_X, aeval_C, LinearMap.sub_apply,
    LinearMap.add_apply, shiftEnd_pow_apply, Module.algebraMap_end_apply, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftEnd_apply]

/-- `((Y^k - 1) b) n = b (n+k) - b n`. -/
theorem aeval_shiftEnd_X_pow_sub_one_apply (k : ℕ) (b : ℕ → A) (n : ℕ) :
    aeval (shiftEnd A) ((X : A[X]) ^ k - 1) b n = b (n + k) - b n := by
  simp only [map_sub, map_one, aeval_X_pow, LinearMap.sub_apply, shiftEnd_pow_apply,
    Module.End.one_apply, Pi.sub_apply]

/-! ### Characteristic `p` -/

variable (p : ℕ) [hp : Fact p.Prime] [CharP A p]

/-- Modulo `Y^p - (Y + c)`, in characteristic `p`: `Y^{p^m} ≡ Y + ∑_{r<m} c^{p^r}`. -/
theorem mk_X_pow_prime_pow (c : A) (m : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(X : A[X]) ^ p - (X + C c)}) (X ^ (p ^ m)) =
      Ideal.Quotient.mk (Ideal.span {(X : A[X]) ^ p - (X + C c)})
        (X + C (∑ r ∈ range m, c ^ (p ^ r))) := by
  have hXp : Ideal.Quotient.mk (Ideal.span {(X : A[X]) ^ p - (X + C c)}) (X ^ p) =
      Ideal.Quotient.mk (Ideal.span {(X : A[X]) ^ p - (X + C c)}) (X + C c) := by
    rw [Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton_self _
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (∑ r ∈ range (m + 1), c ^ (p ^ r)) = c + (∑ r ∈ range m, c ^ (p ^ r)) ^ p := by
      rw [Finset.sum_range_succ', pow_zero, pow_one, sum_pow_char, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← pow_mul, ← pow_succ]
    rw [pow_succ, pow_mul, map_pow, ih, ← map_pow, add_pow_char, ← C_pow, map_add, hXp,
      ← map_add, hs, C_add, add_assoc]

/-- **Prime-power shift for a linear recurrence in characteristic `p`.**
If `b (n+p) = b (n+1) + c b n` for all `n`, then
`b (n + p^m) = b (n+1) + (∑_{r<m} c^{p^r}) b n`. -/
theorem shift_pow_char_pow (c : A) (b : ℕ → A) (hb : ∀ n, b (n + p) = b (n + 1) + c * b n)
    (m n : ℕ) : b (n + p ^ m) = b (n + 1) + (∑ r ∈ range m, c ^ (p ^ r)) * b n := by
  have hq : aeval (shiftEnd A) ((X : A[X]) ^ p - (X + C c)) b = 0 := by
    funext k
    rw [aeval_shiftEnd_X_pow_sub_apply, hb, sub_self, Pi.zero_apply]
  have hdvd : ((X : A[X]) ^ p - (X + C c)) ∣ X ^ (p ^ m) - (X + C (∑ r ∈ range m, c ^ (p ^ r))) :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq).mp (mk_X_pow_prime_pow A p c m))
  have h := congrFun (aeval_shiftEnd_eq_zero_of_dvd A hq hdvd) n
  rw [aeval_shiftEnd_X_pow_sub_apply, Pi.zero_apply, sub_eq_zero] at h
  exact h

end ShiftOperator

/-! ### The Fermat product and the period bound over `ZMod p` -/

section Period

variable (p : ℕ) [hp : Fact p.Prime]

/-- `∏_{a ∈ 𝔽_p} (Y - a) = Y^p - Y`. -/
theorem prod_univ_X_sub_C : ∏ a : ZMod p, ((X : (ZMod p)[X]) - C a) = X ^ p - X := by
  have h := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at h
  have hmonic : ((X : (ZMod p)[X]) ^ p - X).Monic :=
    Polynomial.monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp.out.one_lt)
  have hcard : Multiset.card ((X : (ZMod p)[X]) ^ p - X).roots =
      ((X : (ZMod p)[X]) ^ p - X).natDegree := by
    rw [h, FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt, Finset.card_val,
      Finset.card_univ, ZMod.card]
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [h] at this
  exact this

/-- `∏_{j<p} (Y + j) = Y^p - Y` over `ZMod p`. -/
theorem prod_range_X_add_C_natCast :
    ∏ j ∈ range p, ((X : (ZMod p)[X]) + C (j : ZMod p)) = X ^ p - X := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← prod_univ_X_sub_C p]
  refine Finset.prod_nbij' (fun j => -((j : ℕ) : ZMod p)) (fun a => (-a).val)
    (fun _ _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.mpr (ZMod.val_lt _))
    (fun j hj => ?_) (fun a _ => ?_) (fun j _ => ?_)
  · rw [neg_neg, ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]
  · rw [ZMod.natCast_zmod_val, neg_neg]
  · rw [C_neg, sub_neg_eq_add]

/-- **Period bound.**  If `b (n+p) = b (n+1) + b n` over `ZMod p`, then `b` is periodic with
period `N_p = ∑_{j<p} p^j = (p^p - 1)/(p - 1)`. -/
theorem shift_pow_period (b : ℕ → ZMod p) (hb : ∀ n, b (n + p) = b (n + 1) + b n) (n : ℕ) :
    b (n + ∑ j ∈ range p, p ^ j) = b n := by
  set I : Ideal (ZMod p)[X] := Ideal.span {(X : (ZMod p)[X]) ^ p - (X + C 1)} with hI
  have hq : aeval (shiftEnd (ZMod p)) ((X : (ZMod p)[X]) ^ p - (X + C 1)) b = 0 := by
    funext k
    rw [aeval_shiftEnd_X_pow_sub_apply, hb, one_mul, sub_self, Pi.zero_apply]
  have hpow : ∀ j : ℕ,
      Ideal.Quotient.mk I (X ^ (p ^ j)) = Ideal.Quotient.mk I (X + C ((j : ℕ) : ZMod p)) := by
    intro j
    rw [hI, mk_X_pow_prime_pow (ZMod p) p 1 j]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hN : Ideal.Quotient.mk I (X ^ (∑ j ∈ range p, p ^ j)) = Ideal.Quotient.mk I 1 := by
    rw [← Finset.prod_pow_eq_pow_sum, map_prod, Finset.prod_congr rfl fun j _ => hpow j,
      ← map_prod, prod_range_X_add_C_natCast, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    exact ⟨1, by rw [mul_one, map_one]; ring⟩
  have hdvd : ((X : (ZMod p)[X]) ^ p - (X + C 1)) ∣ X ^ (∑ j ∈ range p, p ^ j) - 1 :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq).mp hN)
  have h := congrFun (aeval_shiftEnd_eq_zero_of_dvd (ZMod p) hq hdvd) n
  rw [aeval_shiftEnd_X_pow_sub_one_apply, Pi.zero_apply, sub_eq_zero] at h
  exact h

end Period

/-! ### Bell numbers and Touchard polynomials modulo `p` -/

section Bell

variable (p : ℕ) [hp : Fact p.Prime]

/-- Touchard's congruence in the form used here: `B(n+p) = B(n+1) + B(n)` in `ZMod p`. -/
theorem bell_add_prime_zmod (n : ℕ) :
    ((Nat.bell (n + p) : ℕ) : ZMod p) = (Nat.bell (n + 1) : ZMod p) + (Nat.bell n : ZMod p) := by
  have := bell_add_prime_modEq p n
  rw [← ZMod.natCast_eq_natCast_iff] at this
  push_cast at this
  rw [this, add_comm]

/-- **Prime-power shift:** `B(n + p^m) ≡ m B(n) + B(n+1) (mod p)`. -/
theorem bell_add_prime_pow_modEq (m n : ℕ) :
    Nat.bell (n + p ^ m) ≡ m * Nat.bell n + Nat.bell (n + 1) [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have h := shift_pow_char_pow (ZMod p) p 1 (fun k => (Nat.bell k : ZMod p))
    (fun k => by rw [bell_add_prime_zmod, one_mul]) m n
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  rw [h]
  ring

/-- **Prime-power shift for Touchard polynomials:**
`T_{n+p^m} = T_{n+1} + (∑_{r=1}^{m} x^{p^r}) T_n` over `ZMod p`. -/
theorem touchardPolynomial_add_prime_pow (m n : ℕ) :
    touchardPolynomial (ZMod p) (n + p ^ m) =
      touchardPolynomial (ZMod p) (n + 1) +
        (∑ r ∈ range m, (X : (ZMod p)[X]) ^ (p ^ (r + 1))) * touchardPolynomial (ZMod p) n := by
  have h := shift_pow_char_pow ((ZMod p)[X]) p (X ^ p) (touchardPolynomial (ZMod p))
    (fun k => by rw [touchardPolynomial_add_prime]) m n
  have hsum : (∑ r ∈ range m, ((X : (ZMod p)[X]) ^ p) ^ (p ^ r)) =
      ∑ r ∈ range m, (X : (ZMod p)[X]) ^ (p ^ (r + 1)) :=
    Finset.sum_congr rfl fun r _ => by rw [← pow_mul, ← pow_succ']
  rw [h, hsum]

/-- **Universal period bound:** `B(n + N_p) ≡ B(n) (mod p)` with `N_p = ∑_{j<p} p^j`. -/
theorem bell_add_sum_prime_pow_modEq (n : ℕ) :
    Nat.bell (n + ∑ j ∈ range p, p ^ j) ≡ Nat.bell n [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  exact shift_pow_period p (fun k => (Nat.bell k : ZMod p)) (fun k => bell_add_prime_zmod p k) n

/-- Every multiple of `N_p` is a period of the Bell numbers modulo `p`. -/
theorem bell_add_mul_sum_prime_pow_modEq (k n : ℕ) :
    Nat.bell (n + k * ∑ j ∈ range p, p ^ j) ≡ Nat.bell n [MOD p] := by
  induction k with
  | zero => simp only [Nat.zero_mul, Nat.add_zero, Nat.ModEq.refl]
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact (bell_add_sum_prime_pow_modEq p _).trans ih

end Bell

/-! ### The least period divides every period -/

/-- If `d` is the least positive period of `b` and `N` is a period, then `d ∣ N`. -/
theorem period_dvd_of_minimal {α : Type*} (b : ℕ → α) {d N : ℕ} (hd : 0 < d)
    (hper_d : ∀ n, b (n + d) = b n) (hmin : ∀ e, 0 < e → (∀ n, b (n + e) = b n) → d ≤ e)
    (hper_N : ∀ n, b (n + N) = b n) : d ∣ N := by
  have hmul : ∀ k n, b (n + d * k) = b n := by
    intro k
    induction k with
    | zero => intro n; rw [Nat.mul_zero, Nat.add_zero]
    | succ k ih => intro n; rw [Nat.mul_succ, ← Nat.add_assoc, hper_d, ih]
  have hr : ∀ n, b (n + N % d) = b n := by
    intro n
    have h := hper_N n
    rw [← Nat.mod_add_div N d, ← Nat.add_assoc, hmul] at h
    exact h
  rcases Nat.eq_zero_or_pos (N % d) with h0 | hpos
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd (hmin _ hpos hr) (not_le.mpr (Nat.mod_lt _ hd))

/-- **The least period of the Bell numbers modulo `p` divides `N_p`.** -/
theorem bell_period_dvd_sum_prime_pow (p : ℕ) [hp : Fact p.Prime] {d : ℕ} (hd : 0 < d)
    (hper : ∀ n, Nat.bell (n + d) ≡ Nat.bell n [MOD p])
    (hmin : ∀ e, 0 < e → (∀ n, Nat.bell (n + e) ≡ Nat.bell n [MOD p]) → d ≤ e) :
    d ∣ ∑ j ∈ range p, p ^ j :=
  period_dvd_of_minimal (fun k => (Nat.bell k : ZMod p)) hd
    (fun n => (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hper n))
    (fun e he hpe => hmin e he fun n => (ZMod.natCast_eq_natCast_iff _ _ _).mp (hpe n))
    (fun n => (ZMod.natCast_eq_natCast_iff _ _ _).mpr (bell_add_sum_prime_pow_modEq p n))

end Fabius

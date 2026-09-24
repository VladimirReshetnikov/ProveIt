import Diophantine.Common.RationalPolynomialDescent
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Theorem 4.1: a polynomial taking only prime values is constant

The coefficient field is the complex numbers, as in the article. Values on the
nonnegative integer grid first force rational coefficients. After clearing a
positive common denominator `l`, let `p` be the prime value at the origin.
Evaluation of the integer polynomial is constant modulo `l * p` on the grid
whose coordinates are multiples of `l * p`. Cancelling `l` shows that every
prime value on that grid is divisible by `p`, hence equals `p`. Polynomial
extensionality on this infinite progression grid proves the result.

The argument includes the polynomial ring with no variables. No restriction to
integer or rational coefficients is added to the statement.
-/

namespace JSWW1976

open MvPolynomial

noncomputable section

/-- Integer polynomial evaluations at coordinatewise multiples of a modulus
agree with the value at the origin modulo that modulus. -/
private theorem modulus_dvd_eval_sub_zero {σ : Type*}
    (A : MvPolynomial σ ℤ) (modulus : ℕ) (v : σ → ℕ) :
    (modulus : ℤ) ∣ eval (fun i => ((modulus * v i : ℕ) : ℤ)) A -
      eval (fun _ : σ => (0 : ℤ)) A := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ modulus).mp
  rw [Int.cast_sub]
  apply sub_eq_zero.mpr
  change (Int.castRingHom (ZMod modulus)) (eval _ A) =
    (Int.castRingHom (ZMod modulus)) (eval _ A)
  rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
  apply congrArg (fun x : σ → ZMod modulus =>
    eval x (map (Int.castRingHom (ZMod modulus)) A))
  funext i
  simp

/-- A complex polynomial taking a positive natural prime value at every
nonnegative integer assignment equals its constant value at the origin. -/
theorem prime_values_polynomial_constant {σ : Type*}
    (P : MvPolynomial σ ℂ)
    (hP : ∀ v : σ → ℕ, ∃ p : ℕ,
      Nat.Prime p ∧ eval (fun i => (v i : ℂ)) P = (p : ℂ)) :
    P = C (eval (fun _ : σ => (0 : ℂ)) P) := by
  classical
  obtain ⟨Q, hQ⟩ := Diophantine.exists_rationalPolynomial_of_nat_values P (by
    intro v
    obtain ⟨p, _, hp⟩ := hP v
    refine ⟨(p : ℚ), ?_⟩
    simpa using hp)
  obtain ⟨l, hl, A, hA⟩ := Diophantine.exists_positive_integer_multiple Q
  have hcast : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
    ext z
    simp
  have hAC : map (Int.castRingHom ℂ) A = C (l : ℂ) * P := by
    have h := congrArg (map (algebraMap ℚ ℂ)) hA
    simpa only [map_map, map_mul, map_C, map_natCast, hcast, hQ] using h
  have hAeval (v : σ → ℕ) :
      (eval (fun i => (v i : ℤ)) A : ℂ) =
        (l : ℂ) * eval (fun i => (v i : ℂ)) P := by
    have h := MvPolynomial.map_eval (Int.castRingHom ℂ) (fun i => (v i : ℤ)) A
    rw [hAC, eval_mul, eval_C] at h
    simpa only [Function.comp_def, Int.coe_castRingHom, Int.cast_natCast] using h
  obtain ⟨p, hp, hpzero⟩ := hP (fun _ => 0)
  have hpzero' : eval (fun _ : σ => (0 : ℂ)) P = (p : ℂ) := by
    simpa using hpzero
  have hAzero : eval (fun _ : σ => (0 : ℤ)) A = (l : ℤ) * (p : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_zero, hpzero'] using
      hAeval (fun _ => 0)
  have hgrid (v : σ → ℕ) :
      eval (fun i => ((l * p * v i : ℕ) : ℂ)) P = (p : ℂ) := by
    obtain ⟨q, hq, hqeval⟩ := hP (fun i => l * p * v i)
    have hAval : eval (fun i => ((l * p * v i : ℕ) : ℤ)) A =
        (l : ℤ) * (q : ℤ) := by
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_mul, Int.cast_natCast, hqeval] using
        hAeval (fun i => l * p * v i)
    have hdiv := modulus_dvd_eval_sub_zero A (l * p) v
    rw [hAval, hAzero, Nat.cast_mul, ← mul_sub] at hdiv
    have hlzero : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
    have hpdiv : (p : ℤ) ∣ (q : ℤ) - (p : ℤ) :=
      (mul_dvd_mul_iff_left hlzero).mp hdiv
    have hpdivq : (p : ℤ) ∣ (q : ℤ) := by
      simpa using dvd_add hpdiv (dvd_refl (p : ℤ))
    have hpdivq' : p ∣ q := by exact_mod_cast hpdivq
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpdivq'
    simpa only [← hpq] using hqeval
  have hinj : Function.Injective (fun n : ℕ => ((l * p * n : ℕ) : ℂ)) := by
    intro a b hab
    dsimp only at hab
    have hnat : l * p * a = l * p * b := by exact_mod_cast hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hl hp.pos) hnat
  have hconstant : P = C (p : ℂ) := by
    apply MvPolynomial.funext_set
      (fun _ : σ => Set.range (fun n : ℕ => ((l * p * n : ℕ) : ℂ)))
      (fun _ => Set.infinite_range_of_injective hinj)
    intro x hx
    choose v hv using fun i => hx i (Set.mem_univ i)
    have hxv : x = fun i => ((l * p * v i : ℕ) : ℂ) :=
      funext fun i => (hv i).symm
    rw [hxv, eval_C]
    exact hgrid v
  simpa only [hpzero'] using hconstant

/-- Jones--Sato--Wada--Wiens (1976), Theorem 4.1, with its full complex
coefficient field and all finite arities, including zero. -/
theorem theorem_4_1 (k : ℕ) (P : MvPolynomial (Fin k) ℂ)
    (hP : ∀ v : Fin k → ℕ, ∃ p : ℕ,
      Nat.Prime p ∧ eval (fun i => (v i : ℂ)) P = (p : ℂ)) :
    P = C (eval (fun _ : Fin k => (0 : ℂ)) P) :=
  prime_values_polynomial_constant P hP

end

end JSWW1976

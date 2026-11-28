import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Arithmetic of the reduced quadratic coefficient in the Fourier frame.
A pair (u,v) represents u+vβ with β²=β−n. Its conjugate generator is 1−β.
There are no project-specific assumptions in these identities. -/

namespace VacuumFrame.Quadratic

abbrev Coeff := ℤ × ℤ

def step (n : ℤ) (c : Coeff) : Coeff := (c.1 + n * c.2, -c.1)

def coeff (n : ℤ) : ℕ → Coeff
  | 0 => (1, 0)
  | m + 1 => step n (coeff n m)

def norm (n : ℤ) (c : Coeff) : ℤ := c.1 ^ 2 + c.1 * c.2 + n * c.2 ^ 2

def trace (c : Coeff) : ℤ := 2 * c.1 + c.2

/-- Realize the coordinate calculations in any commutative ring containing
an element β with β²=β−n. -/
def evaluate {R : Type*} [CommRing R] (β : R) (c : Coeff) : R :=
  (c.1 : R) + (c.2 : R)*β

theorem evaluate_step {R : Type*} [CommRing R] (n : ℤ) (β : R)
    (hβ : β^2 = β - (n : R)) (c : Coeff) :
    evaluate β (step n c) = evaluate β c * (1-β) := by
  simp only [evaluate, step, Int.cast_add, Int.cast_mul, Int.cast_neg]
  linear_combination (c.2 : R)*hβ

theorem evaluate_coeff {R : Type*} [CommRing R] (n : ℤ) (β : R)
    (hβ : β^2 = β - (n : R)) (m : ℕ) :
    evaluate β (coeff n m) = (1-β)^m := by
  induction m with
  | zero => simp [evaluate, coeff]
  | succ m ih => rw [coeff, evaluate_step n β hβ, ih, pow_succ]

theorem norm_eq_product {R : Type*} [CommRing R] (n : ℤ) (β : R)
    (hβ : β^2 = β - (n : R)) (c : Coeff) :
    (norm n c : R) = evaluate β c * evaluate (1-β) c := by
  simp only [norm, evaluate, Int.cast_add, Int.cast_mul, Int.cast_pow]
  linear_combination (c.2 : R)^2*hβ

theorem trace_eq_sum {R : Type*} [CommRing R] (β : R) (c : Coeff) :
    (trace c : R) = evaluate β c + evaluate (1-β) c := by
  simp only [trace, evaluate, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring

theorem norm_step (n : ℤ) (c : Coeff) : norm n (step n c) = n * norm n c := by
  simp only [norm, step]
  ring

theorem norm_coeff (n : ℤ) (m : ℕ) : norm n (coeff n m) = n ^ m := by
  induction m with
  | zero => simp [norm, coeff]
  | succ m ih => rw [coeff, norm_step, ih, pow_succ, mul_comm]

/-- For every positive exponent, the two coefficients reduce to (1,−1) modulo n. -/
theorem coeff_residues (n : ℤ) (m : ℕ) :
    ∃ a b : ℤ, (coeff n (m+1)).1 = 1+n*a ∧ (coeff n (m+1)).2 = -1+n*b := by
  induction m with
  | zero => exact ⟨0, 0, by simp [coeff, step], by simp [coeff, step]⟩
  | succ m ih =>
    obtain ⟨a,b,ha,hb⟩ := ih
    change ∃ A B : ℤ,
      (coeff n (m+1)).1 + n*(coeff n (m+1)).2 = 1+n*A ∧
      -(coeff n (m+1)).1 = -1+n*B
    refine ⟨a-1+n*b, -a, ?_, ?_⟩
    · rw [ha,hb]
      ring
    · rw [ha]
      ring

theorem trace_coeff_sub_one (n : ℤ) (m : ℕ) : n ∣ trace (coeff n (m+1)) - 1 := by
  obtain ⟨a,b,ha,hb⟩ := coeff_residues n m
  refine ⟨2*a+b, ?_⟩
  rw [trace, ha, hb]
  ring

/-- Integral norm and trace have polynomial differences after a coordinate shift by M. -/
theorem norm_shift (n M u v r s : ℤ) :
    M ∣ norm n (u+M*r, v+M*s) - norm n (u,v) := by
  refine ⟨2*u*r+M*r^2+u*s+v*r+M*r*s+n*(2*v*s+M*s^2), ?_⟩
  simp only [norm]
  ring

theorem trace_shift (M u v r s : ℤ) :
    M ∣ trace (u+M*r, v+M*s) - trace (u,v) := by
  refine ⟨2*r+s, ?_⟩
  simp only [trace]
  ring

/-- A literal implementation of coefficient reduction, valid also for signed input. -/
def reduce (M : ℤ) (c : Coeff) : Coeff := (c.1 % M, c.2 % M)

theorem reduce_as_shift (M : ℤ) (c : Coeff) :
    reduce M c = (c.1 + M * -(c.1 / M), c.2 + M * -(c.2 / M)) := by
  simp [reduce, Int.emod_def, sub_eq_add_neg]

theorem reduced_evaluate_congruence {R : Type*} [CommRing R] (n M : ℤ)
    (β : R) (hβ : β^2 = β - (n : R)) (m : ℕ) :
    (M : R) ∣ evaluate β (reduce M (coeff n m)) - (1-β)^m := by
  rw [← evaluate_coeff n β hβ m, reduce_as_shift]
  refine ⟨-(((coeff n m).1 / M : ℤ) : R) - (((coeff n m).2 / M : ℤ) : R)*β, ?_⟩
  simp only [evaluate, Int.cast_add, Int.cast_mul, Int.cast_neg]
  ring

theorem reduced_norm_congruence (n M : ℤ) (m : ℕ) :
    M ∣ norm n (reduce M (coeff n m)) - n^m := by
  rw [← norm_coeff, reduce_as_shift]
  exact norm_shift ..

theorem reduced_trace_congruence (n M : ℤ) (m : ℕ) :
    M ∣ trace (reduce M (coeff n m)) - trace (coeff n m) := by
  rw [reduce_as_shift]
  exact trace_shift ..

/-- The input c from the report: p divides n, the norm of the reduced c is
divisible by p^(2a), and its trace is 1 modulo p, for any positive exponent a. -/
theorem coefficient_certificate {n p : ℤ} (hp : p ∣ n) (a : ℕ) (ha : 0 < a) :
    let m := 2*a
    let M := p^m
    let c := reduce M (coeff n m)
    M ∣ norm n c ∧ p ∣ trace c - 1 := by
  dsimp only
  constructor
  · have h₁ := reduced_norm_congruence n (p^(2*a)) (2*a)
    have h₂ : p^(2*a) ∣ n^(2*a) := pow_dvd_pow_of_dvd hp _
    simpa using dvd_add h₁ h₂
  · have hm : 0 < 2*a := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    have h₁ := reduced_trace_congruence n (p^(2*a)) (2*a)
    have hpM : p ∣ p^(2*a) := dvd_pow_self _ (Nat.ne_of_gt hm)
    have h₂ : p ∣ trace (coeff n (2*a)) - 1 := by
      rw [hk]
      exact hp.trans (trace_coeff_sub_one n k)
    have hsum := dvd_add (hpM.trans h₁) h₂
    convert hsum using 1
    ring

/-- The integral factor inside H_p is 1 modulo p. This applies to arbitrary
coefficients meeting the output of the quadratic certificate. -/
theorem block_factor_residue {p P T tr N : ℤ} (hP : p ∣ P) (hP₀ : P ≠ 0)
    (hT : p ∣ T-1) (htr : p ∣ tr-1) (hN : P^2 ∣ N) :
    p ∣ (P*T^2 + T*tr + N/P) - 1 := by
  obtain ⟨k,hk⟩ := hN
  have hdiv : N/P = P*k :=
    Int.ediv_eq_of_eq_mul_right hP₀ (by rw [hk]; ring)
  obtain ⟨r,hr⟩ := hP
  obtain ⟨s,hs⟩ := hT
  obtain ⟨t,ht⟩ := htr
  have heT : T = 1 + p*s := by omega
  have heTr : tr = 1 + p*t := by omega
  refine ⟨r*T^2 + s + t + p*s*t + r*k, ?_⟩
  rw [hdiv, hr, heT, heTr]
  ring

/-- Adding all blocks preserves the distinguished block's residue whenever
every other block vanishes modulo the chosen prime. -/
theorem sum_residue {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (F : ι → ℤ) (p r : ℤ) (i : ι) (hi : i ∈ S) (hdiag : p ∣ F i - r)
    (hoff : ∀ j ∈ S, j ≠ i → p ∣ F j) :
    p ∣ (∑ j ∈ S, F j) - r := by
  have hrest : p ∣ ∑ j ∈ S.erase i, F j := Finset.dvd_sum (fun j hj =>
    hoff j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))
  rw [← Finset.sum_erase_add S F hi, add_sub_assoc]
  exact dvd_add hrest hdiag

end VacuumFrame.Quadratic

#print axioms VacuumFrame.Quadratic.evaluate_coeff
#print axioms VacuumFrame.Quadratic.norm_eq_product
#print axioms VacuumFrame.Quadratic.trace_eq_sum
#print axioms VacuumFrame.Quadratic.reduced_evaluate_congruence
#print axioms VacuumFrame.Quadratic.coefficient_certificate

#print axioms VacuumFrame.Quadratic.block_factor_residue
#print axioms VacuumFrame.Quadratic.sum_residue

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite Frobenius orthogonality for truncated jets

This independent algebraic core is proposed for a refactor of the raw exponent
calculation in ProveIt's GRH development.  It neither imports that development
nor asserts that the analytic/formal-group integration has been completed.

The endomorphism is abstract: the application takes `f = frobenius R p` on a
characteristic-p quotient of a finite jet algebra. Natural-number multiplicities
are fixed by every ring endomorphism. No reducedness assumption is made.
-/

open scoped BigOperators

namespace FrobeniusJets

variable {R : Type*} [CommRing R]

theorem iterate_add (f : R →+* R) (a b : ℕ) (x : R) :
    (f ^ (a + b)) x = (f ^ a) ((f ^ b) x) := by
  rw [pow_add]
  rfl

theorem iterate_fixed (f : R →+* R) {x : R} (hx : f x = x) (a : ℕ) :
    (f ^ a) x = x := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ']
    change f ((f ^ a) x) = x
    rw [ih, hx]

/-- The finite geometric resolvent of the endomorphism `f`. -/
def resolvent (f : R →+* R) (N : ℕ) (z : R) : R :=
  ∑ j ∈ Finset.range N, (f ^ j) z

/-- The geometric-series identity, including the exact tail. -/
theorem resolvent_sub_map (f : R →+* R) (N : ℕ) (z : R) :
    resolvent f N z - f (resolvent f N z) = z - (f ^ N) z := by
  unfold resolvent
  rw [map_sum, ← Finset.sum_sub_distrib]
  convert Finset.sum_range_sub' (fun j => (f ^ j) z) N using 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ']
    rfl
  · simp

/-- On a nilpotent Frobenius orbit the finite resolvent solves the
Artin--Schreier equation exactly. -/
theorem resolvent_solves (f : R →+* R) (N : ℕ) (z : R)
    (hnil : (f ^ N) z = 0) :
    resolvent f N z - f (resolvent f N z) = z := by
  rw [resolvent_sub_map, hnil, sub_zero]

/-- A solution killed by the N-th iterate is uniquely determined by its
Artin--Schreier difference. -/
theorem resolvent_of_difference (f : R →+* R) (N : ℕ) (y : R) :
    resolvent f N (y - f y) = y - (f ^ N) y := by
  unfold resolvent
  simp only [map_sub]
  convert Finset.sum_range_sub' (fun j => (f ^ j) y) N using 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    rfl
  · simp

theorem nilpotent_solution_eq_resolvent (f : R →+* R) (N : ℕ) {y z : R}
    (hy : y - f y = z) (hnil : (f ^ N) y = 0) :
    y = resolvent f N z := by
  have h := resolvent_of_difference f N y
  rw [hy, hnil, sub_zero] at h
  exact h.symm

theorem nilpotent_solution_unique (f : R →+* R) (N : ℕ) {y y' z : R}
    (hy : y - f y = z) (hy' : y' - f y' = z)
    (hnil : (f ^ N) y = 0) (hnil' : (f ^ N) y' = 0) :
    y = y' := by
  rw [nilpotent_solution_eq_resolvent f N hy hnil,
    nilpotent_solution_eq_resolvent f N hy' hnil']

/-- Absolute difference of natural indices, written without integer coercions. -/
def gap (a b : ℕ) : ℕ := (a - b) + (b - a)

variable {I : Type*} [Fintype I]

/-- The weighted Frobenius moment with gap `e`. -/
def moment (f : R →+* R) (w z : I → R) (e : ℕ) : R :=
  ∑ i, w i * z i * (f ^ e) (z i)

/-- The pairing of two Frobenius translates of a finite vector. -/
def pairing (f : R →+* R) (w z : I → R) (a b : ℕ) : R :=
  ∑ i, w i * (f ^ a) (z i) * (f ^ b) (z i)

theorem pairing_symm (f : R →+* R) (w z : I → R) (a b : ℕ) :
    pairing f w z a b = pairing f w z b a := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairing_add (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (a e : ℕ) :
    pairing f w z a (a + e) = (f ^ a) (moment f w z e) := by
  unfold pairing moment
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_mul, iterate_fixed f (hw i), iterate_add]

/-- Every pairing is a Frobenius iterate of the moment at the absolute gap.
This identity is valid even when `R` is nonreduced. -/
theorem pairing_eq_iterate_moment (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (a b : ℕ) :
    pairing f w z a b = (f ^ min a b) (moment f w z (gap a b)) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    simp only [gap, Nat.sub_eq_zero_of_le hab, zero_add]
    convert pairing_add f w z hw a (b - a) using 1
    rw [Nat.add_sub_of_le hab]
  · rw [min_eq_right hba, pairing_symm]
    simp only [gap, Nat.sub_eq_zero_of_le hba, add_zero]
    convert pairing_add f w z hw b (a - b) using 1
    rw [Nat.add_sub_of_le hba]

theorem pairing_zero_of_moment_zero (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (a b : ℕ)
    (h : moment f w z (gap a b) = 0) :
    pairing f w z a b = 0 := by
  rw [pairing_eq_iterate_moment f w z hw, h, map_zero]

/-- The finite double-sum certificate. No infinite series or coefficientwise
reindexing appears: there is one finite moment for each difference of indices. -/
theorem finite_pairing_identity (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (S T : Finset ℕ) :
    (∑ i, w i * (∑ a ∈ S, (f ^ a) (z i)) *
      (∑ b ∈ T, (f ^ b) (z i))) =
    ∑ a ∈ S, ∑ b ∈ T,
      (f ^ min a b) (moment f w z (gap a b)) := by
  calc
    _ = ∑ i, ∑ a ∈ S, ∑ b ∈ T,
        w i * (f ^ a) (z i) * (f ^ b) (z i) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ a ∈ S, ∑ b ∈ T, pairing f w z a b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact pairing_eq_iterate_moment f w z hw a b

theorem finite_pairing_zero (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (S T : Finset ℕ)
    (hm : ∀ a ∈ S, ∀ b ∈ T, moment f w z (gap a b) = 0) :
    (∑ i, w i * (∑ a ∈ S, (f ^ a) (z i)) *
      (∑ b ∈ T, (f ^ b) (z i))) = 0 := by
  rw [finite_pairing_identity f w z hw]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  rw [hm a ha b hb, map_zero]

/-- The same identity for indexed exponent families. Repetitions are allowed. -/
theorem indexed_pairing_identity {J K : Type*}
    (f : R →+* R) (w z : I → R) (hw : ∀ i, f (w i) = w i)
    (S : Finset J) (T : Finset K) (A : J → ℕ) (B : K → ℕ) :
    (∑ i, w i * (∑ a ∈ S, (f ^ A a) (z i)) *
      (∑ b ∈ T, (f ^ B b) (z i))) =
    ∑ a ∈ S, ∑ b ∈ T,
      (f ^ min (A a) (B b)) (moment f w z (gap (A a) (B b))) := by
  calc
    _ = ∑ i, ∑ a ∈ S, ∑ b ∈ T,
        w i * (f ^ A a) (z i) * (f ^ B b) (z i) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ a ∈ S, ∑ b ∈ T, pairing f w z (A a) (B b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact pairing_eq_iterate_moment f w z hw (A a) (B b)

theorem odd_gap_even_odd (a b : ℕ) : Odd (gap (2 * a) (2 * b + 1)) := by
  rcases le_or_gt a b with hab | hba
  · exact ⟨b - a, by unfold gap; omega⟩
  · exact ⟨a - b - 1, by unfold gap; omega⟩

/-- Inert case: the even Frobenius resolvent is orthogonal to its odd translate.
Only odd moments below the finite cutoff `2*N` are needed. -/
theorem inert_resolvent_pairing_zero (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (N : ℕ)
    (hm : ∀ e, e < 2 * N → Odd e → moment f w z e = 0) :
    (∑ i, w i * resolvent (f ^ 2) N (z i) *
      f (resolvent (f ^ 2) N (z i))) = 0 := by
  have hres (i : I) : resolvent (f ^ 2) N (z i) =
      ∑ a ∈ Finset.range N, (f ^ (2 * a)) (z i) := by
    simp only [resolvent, pow_mul]
  have hfres (i : I) : f (resolvent (f ^ 2) N (z i)) =
      ∑ b ∈ Finset.range N, (f ^ (2 * b + 1)) (z i) := by
    rw [hres, map_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [pow_succ']
    rfl
  simp_rw [hfres, hres]
  rw [indexed_pairing_identity f w z hw]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have haN : a < N := Finset.mem_range.mp ha
  have hbN : b < N := Finset.mem_range.mp hb
  rw [hm _ (by unfold gap; omega) (odd_gap_even_odd a b), map_zero]

/-- Ramified case: all moments below `N` kill the square of the full resolvent. -/
theorem ramified_resolvent_square_zero (f : R →+* R) (w z : I → R)
    (hw : ∀ i, f (w i) = w i) (N : ℕ)
    (hm : ∀ e, e < N → moment f w z e = 0) :
    (∑ i, w i * (resolvent f N (z i)) ^ 2) = 0 := by
  simp only [pow_two, resolvent, ← mul_assoc]
  apply finite_pairing_zero f w z hw
  intro a ha b hb
  have haN : a < N := Finset.mem_range.mp ha
  have hbN : b < N := Finset.mem_range.mp hb
  apply hm
  unfold gap
  omega

/-- If the formal parameter satisfies its inert Artin--Schreier equation and
has nilpotent Frobenius orbit, the raw exponent `Y * F(Y)` sums to zero. -/
theorem inert_raw_exponent_zero (f : R →+* R) (w z y : I → R)
    (hw : ∀ i, f (w i) = w i) (N : ℕ)
    (hy : ∀ i, y i - (f ^ 2) (y i) = z i)
    (hnil : ∀ i, ((f ^ 2) ^ N) (y i) = 0)
    (hm : ∀ e, e < 2 * N → Odd e → moment f w z e = 0) :
    (∑ i, w i * y i * f (y i)) = 0 := by
  have hyres (i : I) : y i = resolvent (f ^ 2) N (z i) :=
    nilpotent_solution_eq_resolvent (f ^ 2) N (hy i) (hnil i)
  simp_rw [hyres]
  exact inert_resolvent_pairing_zero f w z hw N hm

/-- If the formal parameter satisfies its ramified Artin--Schreier equation,
the corrected raw exponent `Y² - c*L²` sums to zero. This works for every `c`;
the application uses `c = 1/2` and includes the moment with gap zero. -/
theorem ramified_raw_exponent_zero (f : R →+* R) (w z y : I → R)
    (hw : ∀ i, f (w i) = w i) (N : ℕ) (c : R)
    (hy : ∀ i, y i - f (y i) = z i)
    (hnil : ∀ i, (f ^ N) (y i) = 0)
    (hm : ∀ e, e < N → moment f w z e = 0)
    (hzero : moment f w z 0 = 0) :
    (∑ i, w i * ((y i) ^ 2 - c * (z i) ^ 2)) = 0 := by
  have hyres (i : I) : y i = resolvent f N (z i) :=
    nilpotent_solution_eq_resolvent f N (hy i) (hnil i)
  have hyzero : (∑ i, w i * (y i) ^ 2) = 0 := by
    simp_rw [hyres]
    exact ramified_resolvent_square_zero f w z hw N hm
  have hzzero : (∑ i, w i * (z i) ^ 2) = 0 := by
    simpa only [moment, pow_zero, RingHom.coe_one, id_eq, pow_two, mul_assoc]
      using hzero
  calc
    _ = (∑ i, w i * (y i) ^ 2) - c * (∑ i, w i * (z i) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 0 := by rw [hyzero, hzzero]; ring

omit [Fintype I] in
/-- Natural-number multiplicities are fixed without any extra hypothesis.
Specializing to Frobenius therefore needs no coefficient-field assumption. -/
theorem natural_weights_fixed (f : R →+* R) (m : I → ℕ) :
    ∀ i, f (m i : R) = (m i : R) := by
  intro i
  exact map_natCast f (m i)

/-- The moment identity in the usual characteristic-p notation. -/
theorem frobenius_pairing_identity (p : ℕ) [ExpChar R p]
    (m : I → ℕ) (z : I → R) (a b : ℕ) :
    (∑ i, (m i : R) * (z i) ^ (p ^ a) * (z i) ^ (p ^ b)) =
    (∑ i, (m i : R) * z i * (z i) ^ (p ^ (gap a b))) ^
      (p ^ min a b) := by
  simpa only [pairing, moment, RingHom.coe_pow, iterate_frobenius]
    using pairing_eq_iterate_moment (frobenius R p) (fun i => (m i : R)) z
      (natural_weights_fixed (frobenius R p) m) a b

end FrobeniusJets

#print axioms FrobeniusJets.nilpotent_solution_unique
#print axioms FrobeniusJets.finite_pairing_identity
#print axioms FrobeniusJets.finite_pairing_zero
#print axioms FrobeniusJets.inert_raw_exponent_zero
#print axioms FrobeniusJets.ramified_raw_exponent_zero
#print axioms FrobeniusJets.frobenius_pairing_identity

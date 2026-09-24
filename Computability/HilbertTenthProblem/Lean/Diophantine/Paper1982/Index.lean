import Diophantine.Paper1982.Master1

/-!
# Jones 1982, (4.1): existence of admissible coding triples

Choose a power of two larger than the finitely many coefficient bounds, then evaluate
the two coding polynomials at `2z`. Their nonnegative coefficients ensure that these
integer evaluations are natural numbers. The choice of `z` can exceed any prescribed
bound. This supplies the `Index` hypothesis used by the master equivalence and Theorem 1;
it does not assert the separate universality of the pair `(58, 4)`.
-/

namespace Jones1982

open Polynomial Finset

/-- Every polynomial has admissible triples (4.1) with arbitrarily large first coordinate.
No degree or normalization hypothesis is needed to construct the triple itself. -/
theorem exists_index_above {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    ∃ z u y : ℕ, bound < z ∧ Index ν P z u y := by
  classical
  let s := bound + (∑ k ∈ star ν 4, (Pcoef ν P k).natAbs) + 2
  let z := 2 ^ s
  have hs : s < z := Nat.lt_two_pow_self
  have hbound : bound < z := by dsimp [s] at hs; omega
  have hbig : ∀ k ∈ star ν 4, |Pcoef ν P k| + 1 < (z : ℤ) := by
    intro k hk
    have hkbound : (Pcoef ν P k).natAbs ≤ ∑ j ∈ star ν 4, (Pcoef ν P j).natAbs :=
      Finset.single_le_sum (f := fun j => (Pcoef ν P j).natAbs)
        (fun _ _ => Nat.zero_le _) hk
    have hlt : (Pcoef ν P k).natAbs + 1 < z := by dsimp [s] at hs; omega
    rw [← Int.natCast_natAbs]
    exact_mod_cast hlt
  have hu : 0 ≤ (lpoly ν 4).eval (2 * z : ℤ) := by
    rw [eval_lpoly]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hy : 0 ≤ (epoly ν 4 P z).eval (2 * z : ℤ) := by
    rw [eval_epoly]
    apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg _ (by positivity)
    have := hbig k hk
    have := neg_abs_le (Pcoef ν P k)
    linarith
  refine ⟨z, ((lpoly ν 4).eval (2 * z : ℤ)).toNat,
    ((epoly ν 4 P z).eval (2 * z : ℤ)).toNat, hbound, ?_⟩
  exact ⟨⟨s, rfl⟩, hbig, Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hy⟩

/-- The second coordinate of (4.1) is positive when there is at least one witness variable. -/
theorem Index.u_pos {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}
    (hI : Index ν P z u y) (hν : 1 ≤ ν) : 0 < u := by
  have hz := hI.two_le
  have hterm : (0 : ℤ) < (2 * z : ℤ) ^ ((4 + 1) ^ (1 : ℕ)) := by positivity
  have hle : (2 * z : ℤ) ^ ((4 + 1) ^ (1 : ℕ)) ≤ (u : ℤ) := by
    rw [hI.hu, eval_lpoly]
    exact Finset.single_le_sum (f := fun i => (2 * z : ℤ) ^ ((4 + 1) ^ i))
      (fun _ _ => by positivity) (Finset.mem_Icc.2 ⟨le_rfl, hν⟩)
  exact_mod_cast (lt_of_lt_of_le hterm hle)

/-- Admissible coding triples exist with all three coordinates positive. -/
theorem exists_index {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ) (hν : 1 ≤ ν) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧ Index ν P z u y := by
  obtain ⟨z, u, y, hz, hI⟩ := exists_index_above P 0
  exact ⟨z, u, y, hz, hI.u_pos hν, hI.y_pos, hI⟩

end Jones1982

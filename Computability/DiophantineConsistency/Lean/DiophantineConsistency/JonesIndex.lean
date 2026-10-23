import Diophantine.Paper1982.Index

/-!
# An explicit finite recipe for Jones's coding index

The existence proof `Jones1982.exists_index_above` already displays every
coordinate of its index. This module exports those expressions as data,
without selecting a witness of an existence theorem and without
`Classical.choose`.

The definitions are marked noncomputable because the imported polynomial
operations and `Pcoef` are noncomputable library definitions. The recipe
itself consists of a finite coefficient sum, a power of two, and two
polynomial evaluations; it does not inspect the represented set or decide
consistency. An executable expression-to-coefficient implementation is a
separate matter from this choice-free mathematical specification.
-/

namespace DiophantineConsistency.JonesIndex

open Jones1982 Polynomial Finset

variable {ν : ℕ}

/-- A finite bound on all coefficients used in the Jones coding. -/
noncomputable def coefficientHeight (P : MvPolynomial (Fin (ν + 1)) ℤ) : ℕ :=
  ∑ k ∈ star ν 4, (Pcoef ν P k).natAbs

/-- The exact exponent used in the existing existence proof. -/
noncomputable def indexExponent (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) : ℕ :=
  bound + coefficientHeight P + 2

/-- The first index coordinate is this specified power of two. -/
noncomputable def indexZ (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) : ℕ :=
  2 ^ indexExponent P bound

/-- The second coordinate is the natural value of the literal coding polynomial. -/
noncomputable def indexU (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) : ℕ :=
  ((lpoly ν 4).eval (2 * indexZ P bound : ℤ)).toNat

/-- The third coordinate is the natural value of the coefficient-encoding polynomial. -/
noncomputable def indexY (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) : ℕ :=
  ((epoly ν 4 P (indexZ P bound)).eval (2 * indexZ P bound : ℤ)).toNat

theorem indexExponent_lt_indexZ (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    indexExponent P bound < indexZ P bound :=
  Nat.lt_two_pow_self

theorem bound_lt_indexZ (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    bound < indexZ P bound := by
  have hs := indexExponent_lt_indexZ P bound
  dsimp only [indexExponent] at hs
  omega

theorem coefficient_lt_indexZ (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ)
    (k : Fin (ν + 2) → ℕ) (hk : k ∈ star ν 4) :
    |Pcoef ν P k| + 1 < (indexZ P bound : ℤ) := by
  classical
  have hkbound : (Pcoef ν P k).natAbs ≤ coefficientHeight P :=
    Finset.single_le_sum (f := fun j => (Pcoef ν P j).natAbs)
      (fun _ _ => Nat.zero_le _) hk
  have hs := indexExponent_lt_indexZ P bound
  have hlt : (Pcoef ν P k).natAbs + 1 < indexZ P bound := by
    dsimp only [indexExponent] at hs
    omega
  rw [← Int.natCast_natAbs]
  exact_mod_cast hlt

/-- The three explicitly specified numbers satisfy the entire Jones index interface.
No degree, normalization, or semantic hypothesis on `P` is required. -/
theorem index_correct (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    Index ν P (indexZ P bound) (indexU P bound) (indexY P bound) := by
  classical
  have hu : 0 ≤ (lpoly ν 4).eval (2 * indexZ P bound : ℤ) := by
    rw [eval_lpoly]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hy : 0 ≤ (epoly ν 4 P (indexZ P bound)).eval (2 * indexZ P bound : ℤ) := by
    rw [eval_epoly]
    apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg _ (by positivity)
    have := coefficient_lt_indexZ P bound k hk
    have := neg_abs_le (Pcoef ν P k)
    linarith
  exact ⟨⟨indexExponent P bound, rfl⟩,
    coefficient_lt_indexZ P bound,
    Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hy⟩

/-- Type-valued index data, keeping the literal numerical fields and their certificate together. -/
structure Parameters (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) where
  z : ℕ
  u : ℕ
  y : ℕ
  valid : Index ν P z u y

/-- Construct the index record by the finite recipe, rather than extracting
it with choice from a proposition-valued existence theorem. -/
noncomputable def parameters (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ := 0) :
    Parameters ν P :=
  ⟨indexZ P bound, indexU P bound, indexY P bound, index_correct P bound⟩

@[simp] theorem parameters_z (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    (parameters P bound).z = indexZ P bound := rfl

@[simp] theorem parameters_u (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    (parameters P bound).u = indexU P bound := rfl

@[simp] theorem parameters_y (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    (parameters P bound).y = indexY P bound := rfl

theorem indexU_pos (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) (hν : 1 ≤ ν) :
    0 < indexU P bound :=
  (index_correct P bound).u_pos hν

theorem indexY_pos (P : MvPolynomial (Fin (ν + 1)) ℤ) (bound : ℕ) :
    0 < indexY P bound :=
  (index_correct P bound).y_pos

#print axioms index_correct

end DiophantineConsistency.JonesIndex

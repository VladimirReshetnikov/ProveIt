import Surreal.Algebra.ModuleKernelBasis

/-!
# Nonzero kernel directions with vector-space coefficients

The linear-algebra prerequisite for `odg:dec:cor:converse`. A scalar matrix
has a nonzero vector-space-valued kernel vector precisely when its scalar
kernel is nonzero, provided a nonzero vector in the coefficient space is given.
-/

namespace Surreal.ModuleKernelBasis

variable {K V m n : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Scaling a scalar kernel vector by any vector gives a vector-valued kernel vector. -/
theorem kernel_smul_vector (A : Matrix m n K) (v : n → K)
    (hv : v ∈ LinearMap.ker A.mulVecLin) (t : V) :
    ∀ j, ∑ k, A j k • (v k • t) = 0 := by
  intro j
  simp_rw [smul_smul]
  rw [← Finset.sum_smul]
  have h : ∑ k, A j k * v k = 0 := congrFun hv j
  rw [h, zero_smul]

omit [Fintype n] [DecidableEq n] in
/-- Nonzero scalar directions remain nonzero when multiplied by a nonzero vector. -/
theorem kernel_direction_ne_zero (v : n → K) (hv : v ≠ 0) (t : V) (ht : t ≠ 0) :
    (fun k => v k • t) ≠ 0 := by
  intro h
  apply hv
  funext k
  have hk : v k • t = 0 := congrFun h k
  exact (smul_eq_zero.mp hk).resolve_right ht

/-- Nonzero coefficient-space kernel vectors exist exactly for nonzero scalar kernels. -/
theorem exists_nonzero_kernel_iff (A : Matrix m n K) (t : V) (ht : t ≠ 0) :
    (∃ x : n → V, x ≠ 0 ∧ ∀ j, ∑ k, A j k • x k = 0) ↔
      LinearMap.ker A.mulVecLin ≠ ⊥ := by
  constructor
  · rintro ⟨x, hx, hAx⟩ hA
    exact hx (eq_zero_of_injective A (LinearMap.ker_eq_bot.mp hA) x hAx)
  · intro hA
    obtain ⟨v, hv, hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
    exact ⟨fun k => v k • t, kernel_direction_ne_zero v hvn t ht, kernel_smul_vector A v hv t⟩

end Surreal.ModuleKernelBasis

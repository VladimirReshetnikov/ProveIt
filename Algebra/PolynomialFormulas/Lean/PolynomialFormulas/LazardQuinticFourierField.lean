import PolynomialFormulas.LazardQuinticFourier

/-!
# Fourier soundness with the exact characteristic hypothesis

The characteristic-zero API in `LazardQuinticFourier` is convenient for the
rational solver.  The algebraic endgame in Lazard's paper needs only that
five be invertible.  These theorems expose that sharper hypothesis: the four
cyclic Fourier identities imply that every displayed inverse-Fourier value is
a root without assuming characteristic zero.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

section Field

variable {K : Type*} [Field K]

/-- The inverse-Fourier value at `1` is a root whenever `5 ≠ 0`. -/
theorem FourierRelations.base_root_of_five_ne_zero
    {c : DepressedQuintic K} {a b c' d : K}
    (h : FourierRelations c a b c' d) (h5 : (5 : K) ≠ 0) :
    c.eval ((a + b + c' + d) / 5) = 0 := by
  have h25eq : (25 : K) = 5 ^ 2 := by ring
  have h125eq : (125 : K) = 5 ^ 3 := by ring
  have h3125eq : (3125 : K) = 5 ^ 5 := by ring
  have h25 : (25 : K) ≠ 0 := by
    rw [h25eq]
    exact pow_ne_zero _ h5
  have h125 : (125 : K) ≠ 0 := by
    rw [h125eq]
    exact pow_ne_zero _ h5
  have h3125 : (3125 : K) ≠ 0 := by
    rw [h3125eq]
    exact pow_ne_zero _ h5
  have hp : c.p = -fourierCyclic2 a b c' d / 5 := by
    field_simp [h5]
    linear_combination h.cyclic2
  have hq : c.q = -fourierCyclic3 a b c' d / 25 := by
    field_simp [h25]
    linear_combination h.cyclic3
  have hr : c.r = fourierCyclic4 a b c' d / 125 := by
    apply (eq_div_iff h125).2
    simpa [mul_comm] using h.cyclic4.symm
  have hs : c.s = -fourierCyclic5 a b c' d / 3125 := by
    field_simp [h3125]
    linear_combination h.cyclic5
  unfold DepressedQuintic.eval
  rw [hp, hq, hr, hs]
  simp only [fourierCyclic2, fourierCyclic3, fourierCyclic4, fourierCyclic5]
  field_simp [h5, h25, h125, h3125]
  ring

/-- Twisting by any fifth root of unity preserves the relations, so every
corresponding inverse-Fourier value is a root under `5 ≠ 0`. -/
theorem FourierRelations.root_of_five_ne_zero
    {c : DepressedQuintic K} {a b c' d z : K}
    (h : FourierRelations c a b c' d) (h5 : (5 : K) ≠ 0)
    (hz : z ^ 5 = 1) :
    c.eval (inverseFourierAt z a b c' d) = 0 := by
  have ht := h.twist hz
  simpa [inverseFourierAt, mul_assoc] using
    ht.base_root_of_five_ne_zero h5

/-- Indexed pointwise soundness at a packaged primitive fifth root. -/
theorem FourierRelations.inverseFourier_root_of_five_ne_zero
    {c : DepressedQuintic K} {a b c' d : K}
    (h : FourierRelations c a b c' d) (h5 : (5 : K) ≠ 0)
    (omega : FifthRootOfUnity K) (k : Fin 5) :
    c.eval (inverseFourier omega.value a b c' d k) = 0 := by
  rw [inverseFourier_eq_at]
  apply h.root_of_five_ne_zero h5
  calc
    (omega.value ^ (k : ℕ)) ^ 5 = omega.value ^ ((k : ℕ) * 5) := by
      rw [pow_mul]
    _ = omega.value ^ (5 * (k : ℕ)) := by rw [Nat.mul_comm]
    _ = (omega.value ^ 5) ^ (k : ℕ) := by rw [pow_mul]
    _ = 1 := by rw [omega.primitive.pow_eq_one, one_pow]

end Field

end LeanProofs.PolynomialFormulas.LazardQuintic

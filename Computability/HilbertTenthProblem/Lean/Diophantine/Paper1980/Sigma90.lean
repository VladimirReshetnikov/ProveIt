import Diophantine.Paper1980.Mask90
import Diophantine.Paper1980.Sigma93

/-!
# The decomposition of `σ` for the 90-operation system

With the canonical codes `e = e₀(B)`, `l = ℓ₀(B)` one has `e − l = D(B)`, so the
positive product `σ = (e − l) C(B)²` is exactly `(D · C²)(B)`; its coefficient
sum below `K` is the tested part (`sigma_decomp`).  The coefficients of
`D · C_main²` are bounded by `D₁ · C(1)²` (`abs_coeff_le`).
-/

namespace Jones1980

namespace L90

open Polynomial Finset
open Layout (Row)
open Iso (eval_eq_sum_split absSum abs_coeff_mul_le)

noncomputable section

variable {m s : ℕ} (rows : Fin s → Row m) (hel : Fin s → Fin 3 → Fin m) (PX : Finset (Fin m))

/-- `σ = Σ_{p<K} [X^p](D · C²) B^p + B^K · High`. -/
theorem sigma_decomp (hL : LayoutOk s rows hel) {B L e l x g σ : ℕ} (hKL : K m s ≤ L)
    (he : e = Nat.ofDigits B (e0d rows hel PX)) (hl : l = Nat.ofDigits B (ell0d rows L))
    (Cf : ℤ[X]) (hC : ((x + g : ℕ) : ℤ) = Cf.eval (B : ℤ))
    (hσ : (σ : ℤ) = ((e : ℤ) - l) * ((x : ℤ) + g) ^ 2) :
    ∃ High : ℤ, (σ : ℤ) =
      ∑ p ∈ range (K m s), (D s rows hel PX * Cf ^ 2).coeff p * (B : ℤ) ^ p +
        (B : ℤ) ^ (K m s) * High := by
  have hD : ((e : ℤ) - l) = (D s rows hel PX).eval (B : ℤ) := by
    rw [he, hl]; exact e0_sub_ell0 rows hel PX hL B hKL
  have hC' : (x : ℤ) + g = Cf.eval (B : ℤ) := by exact_mod_cast hC
  obtain ⟨High, hH⟩ := eval_eq_sum_split (D s rows hel PX * Cf ^ 2) (B : ℤ) (K m s)
  refine ⟨High, ?_⟩
  rw [hσ, hD, hC', ← eval_pow, ← eval_mul, hH]

/-- `|[X^p](D · C_main²)| ≤ D₁ · (x + Σ zᵢ)²`. -/
theorem abs_coeff_le (x : ℤ) (z : Fin m → ℤ) (hx : 0 ≤ x) (hz : ∀ i, 0 ≤ z i) (p : ℕ) :
    |(D s rows hel PX * Cmain x z ^ 2).coeff p| ≤
      absSum (D s rows hel PX) * (x + ∑ i, z i) ^ 2 := by
  have := abs_coeff_mul_le (D s rows hel PX) (Cmain x z ^ 2)
    (coeff_Cmain_sq_nonneg x z hx hz) p
  rwa [eval_pow, eval_one_Cmain] at this

end

end L90

end Jones1980

import IPRADerivations.DiophantineNumberTheory.KroneckerBinomialLower
import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.Core.Header

/-!
# The constant Fourier coefficient of the Kronecker kernel

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:kronecker`, `eq:constant`: the kernel
`F(x) = ∏_j cos^{2r}(π x_j)` has coefficients `c_h = 4^{−rd} ∏_j C(2r, r + h_j)`, and "Since their sum is `4^r`,
the constant coefficient obeys `c₀ ≥ (2r+1)^{−d} = A^{−1}`". Cleared of denominators:

* `central_lower`: `4^r ≤ (2r + 1) C(2r, r)`, by induction on `r` with `(r+1) C(2r+2, r+1) = 2(2r+1) C(2r, r)`
  (`Catalan.cb_rec`): the step needs `2(2r + 3) ≥ 4(r + 1)`, then cancels `r + 1`;
* `constant_coeff`: `(4^r)^d ≤ (2r+1)^d C(2r, r)^d`, i.e. `c₀ = (C(2r, r)/4^r)^d ≥ (2r+1)^{−d} = 1/A`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.KroneckerCentral

open_ipra
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_zero cb_rec)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem central_base : Γ ⊢[PRAAx] le (pw (num 4) zero) (succ (two * zero) * cb (zero : PTm n)) := by
  have e1 := natEq (pw_zero (Γ := Γ) (num 4))
  have e2 := natEq (cb_zero (Γ := Γ) (n := n))
  refine le_of_eq_add (d := zero) ?_
  apply deriveNat; ipra_simps
  rw [e1, e2]; ring

theorem central_step {r : PTm n} (ih : Γ ⊢[PRAAx] le (pw (num 4) r) (succ (two * r) * cb r)) :
    Γ ⊢[PRAAx] le (pw (num 4) (succ r)) (succ (two * succ r) * cb (succ r)) := by
  have ecb := natEq (cb_rec (Γ := Γ) r)
  have p4 := natEq (pw_succ (Γ := Γ) (num 4) r)
  refine mul_le_cancel (d' := r) ?_
  ipra_le 2 * (2 * 𝔟 r + 3) * sl ih + 2 * 𝔟 (pw (num 4) r) using
    simp only [p4]
    linear_combination (2 * 𝔟 r + 3) * ecb

/-- Variable `0 = r`. -/
private abbrev cF : Fm PTm 1 := le (pw (num 4) (var 0)) (succ (two * var 0) * cb (var 0))

private theorem c₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] cF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp
    exact central_base
  · simp
    exact central_step Prf.hyp0

/-- `eq:constant`: `4^r ≤ (2r + 1) C(2r, r)`. -/
theorem central_lower (r : PTm n) : Γ ⊢[PRAAx] le (pw (num 4) r) (succ (two * r) * cb r) := by
  have h := inst (Γ := Γ) c₀ (![r] : Fin 1 → PTm n)
  simpa using h

/-- `c₀ ≥ 1/A`: `(4^r)^d ≤ (2r+1)^d C(2r, r)^d`. -/
theorem constant_coeff (r d : PTm n) :
    Γ ⊢[PRAAx] le (pw (pw (num 4) r) d) (pw (succ (two * r)) d * pw (cb r) d) :=
  le_congr (.eqRefl _) (mul_pw _ _ d) (pw_le_pw d (central_lower r))

end LeanProofs.IPRA.DiophantineNumberTheory.KroneckerCentral

import IPRADerivations.Combinatorics.CatalanNarayana
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.LinearCombination

/-!
# The square sum of the Catalan numbers

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (theorem "Square sum", (2.20)). The packet's
proof puts `d_k = C(n, k) − C(n, k − 1)` and shows `∑_{k=0}^{n+1} d_k² = 2 Cat_n` by expanding the
square and applying Vandermonde twice; the sum in (2.20) is half of it by the symmetry
`d_{n+1−k} = −d_k`. Here `d_k²` is the natural number `abs(C(n, k) − C(n, k − 1))²`, written with the
absolute difference `ad a b = (a ∸ b) + (b ∸ a)` of `Probability/Variance`, and the `k = 0` term
`d_0² = 1` is separated:

* `square_pt`: `abs(a − b)² + 2ab = a² + b²` at `a = C(n, j + 1)`, `b = C(n, j)`;
* `shift_squares`: `1 + ∑_{j ≤ n} C(n, j + 1)² = C(2n, n)`;
* `signed_square`: `1 + ∑_{j ≤ n} abs(C(n, j + 1) − C(n, j))² = 2 Cat_n` for `n ≥ 1`, from
  `∑ C(n, j)² = C(2n, n)`, `∑ C(n, j) C(n, j + 1) = n Cat_n` and `(n + 1) Cat_n = C(2n, n)`;
* `signed_square_zero`: the case `n = 0`.

The halving by symmetry, which gives the sum over `k ≤ n/2`, is `Combinatorics/CatalanHalving`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanSquares

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self gb_above)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (sqB nB inst2_sq inst2_n central_squares narayana_catalan)
open LeanProofs.IPRA.Combinatorics.Catalan (cat cat_zero cat_spec)
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies; variables `0 = j`, `1 = n` -/

/-- `abs(C(n, j + 1) − C(n, j))²`. -/
abbrev dB : PTm 2 :=
  ad (gb (var 1) (succ (var 0))) (gb (var 1) (var 0)) * ad (gb (var 1) (succ (var 0))) (gb (var 1) (var 0))
/-- `2 C(n, j) C(n, j + 1)`. -/
abbrev twoNB : PTm 2 := two * nB

theorem inst2_d (j N : PTm n) :
    inst2 dB j N = ad (gb N (succ j)) (gb N j) * ad (gb N (succ j)) (gb N j) := by simp [inst2]
theorem inst2_twoN (j N : PTm n) : inst2 twoNB j N = two * inst2 nB j N := by simp [inst2]

theorem square_pt (j N : PTm n) :
    Γ ⊢[PRAAx] inst2 (addBody dB twoNB) j N ≐ inst2 (addBody (shiftBody sqB) sqB) j N := by
  rw [inst2_addBody, inst2_addBody, inst2_d, inst2_twoN, inst2_n, inst2_shiftBody, inst2_sq, inst2_sq]
  ipra_lc natEq (ad_sq (Γ := Γ) (gb N (succ j)) (gb N j))

/-- `1 + ∑_{j ≤ n} C(n, j + 1)² = C(2n, n)`. -/
theorem shift_squares (N : PTm n) :
    Γ ⊢[PRAAx] one + ap2 (sumF (shiftBody sqB)) (succ N) N ≐ binom (N + N) N := by
  have z₀ : Γ ⊢[PRAAx] inst2 sqB zero N ≐ one := by
    rw [inst2_sq]; exact (congrMul (gb_zero N) (gb_zero N)).eqTrans (one_mul one)
  have zt : Γ ⊢[PRAAx] inst2 sqB (succ N) N ≐ zero := by
    rw [inst2_sq]; exact (congrMul (gb_above (le_refl _)) (.eqRefl _)).eqTrans (zero_mul _)
  ipra_lc -natEq (sum_shift (Γ := Γ) sqB (succ N) N) + natEq (sum_succ' (Γ := Γ) sqB (succ N) N) - natEq z₀ +
    natEq zt + natEq (central_squares (Γ := Γ) N)

/-- (2.20), cleared: `1 + ∑_{j ≤ n} abs(C(n, j + 1) − C(n, j))² = 2 Cat_n` for `n = m + 1`. -/
theorem signed_square (m : PTm n) :
    Γ ⊢[PRAAx] one + ap2 (sumF dB) (succ (succ m)) (succ m) ≐ two * cat (succ m) := by
  have P := natEq (sum_congr_bounded (Γ := Γ) (addBody dB twoNB) (addBody (shiftBody sqB) sqB)
    (succ m) (succ m) (succ (succ m)) (.allI (.impI (square_pt _ _))))
  have AL := natEq (sum_add (Γ := Γ) dB twoNB (succ (succ m)) (succ m))
  have AR := natEq (sum_add (Γ := Γ) (shiftBody sqB) sqB (succ (succ m)) (succ m))
  have Ts' : Γ ⊢[PRAAx] ap2 (sumF twoNB) (succ (succ m)) (succ m) ≐ two * ap2 (sumF nB) (succ (succ m)) (succ m) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    rw [inst2_twoN]
    exact .eqRefl _
  have Ts := natEq Ts'
  have Ns := natEq (sum_succ' (Γ := Γ) nB (succ m) (succ m))
  have nM' : Γ ⊢[PRAAx] inst2 nB (succ m) (succ m) ≐ zero := by
    rw [inst2_n]; exact (congrMul (gb_self _) (gb_above (le_refl _))).eqTrans (mul_zero _)
  have nM := natEq nM'
  have narr := natEq (narayana_catalan (Γ := Γ) m)
  have Sh := natEq (shift_squares (Γ := Γ) (succ m))
  have Cq := natEq (central_squares (Γ := Γ) (succ m))
  have cs := natEq (cat_spec (Γ := Γ) (succ m))
  have bc := natEq (congrBinom (Γ := Γ) (by ipra_ring :
    Γ ⊢[PRAAx] succ m + succ m ≐ two * succ m) (.eqRefl (succ m)))
  apply deriveNat; ipra_simps
  linear_combination -AL + P + AR + Sh + Cq + 2 * bc - 2 * cs - Ts - 2 * Ns - 2 * nM - 2 * narr

/-- (2.20), cleared, for `n = 0`: `1 + abs(C(0, 1) − C(0, 0))² = 2 Cat_0`. -/
theorem signed_square_zero : Γ ⊢[PRAAx] one + ap2 (sumF dB) (succ zero) (zero : PTm n) ≐ two * cat zero := by
  have a := natEq (sum_succ' (Γ := Γ) dB zero (zero : PTm n))
  have z := natEq (sum_zero (Γ := Γ) dB (zero : PTm n))
  have h₁ : Γ ⊢[PRAAx] gb (zero : PTm n) (succ zero) ≐ zero := gb_above (le_refl _)
  have h₂ : Γ ⊢[PRAAx] gb (zero : PTm n) zero ≐ one := gb_zero _
  have d : Γ ⊢[PRAAx] ad (gb (zero : PTm n) (succ zero)) (gb zero zero) ≐ one :=
    (congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)).eqTrans
      ((congrAdd (zero_monus _) (monus_zero _)).eqTrans (zero_add _))
  have t' : Γ ⊢[PRAAx] inst2 dB zero (zero : PTm n) ≐ one := by
    rw [inst2_d]; exact (congrMul d d).eqTrans (one_mul one)
  have t := natEq t'; have c := natEq (cat_zero (Γ := Γ) (n := n))
  apply deriveNat; ipra_simps
  linear_combination a + z + t - 2 * c

end LeanProofs.IPRA.Combinatorics.CatalanSquares

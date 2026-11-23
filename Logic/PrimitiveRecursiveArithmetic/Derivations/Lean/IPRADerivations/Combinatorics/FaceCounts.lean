import IPRADerivations.Combinatorics.BinomialSigned

/-!
# Alternating face counts of the simplex, the cube and the cross-polytope

Packet: `combinatorics/Combinatorics-iPRA`, `geometry.tex`, result 57 ("Simplex, cube, and cross-polytope"):
"In dimension `d`, the standard simplex has `C(d + 1, j + 1)` faces of dimension `j`; the cube has
`2^{d−j} C(d, j)`. For `d ≥ 1` the cross-polytope has `2^{j+1} C(d, j + 1)` faces of dimension `j < d` ...
Each of these polytopes ... has `∑_j (−1)^j f_j = 1`", by "`(1 − 1)^{d+1} = 0`", "`(2 − 1)^d = 1`" and
"`1 − (1 − 2)^d`; add `(−1)^d`".

With the even and odd parts `E m z = ∑_{k even} C(m, k) z^k`, `O m z = ∑_{k odd} C(m, k) z^k` of
`Combinatorics/BinomialSigned` (so `E − O = (1 − z)^m`), uniformly in the term for the dimension:

* `simplex_euler`: `E (d + 1) 1 = O (d + 1) 1`: the faces of the simplex, with the empty face, have alternating
  sum `0`, that is `∑_{j ≥ 0} (−1)^j C(d + 1, j + 1) = 1`;
* `alt_zero`, `alt_one`, `alt_step_two`: `E_0(2) = O_0(2) + 1`, `O_1(2) = E_1(2) + 1` and
  `E_{m+2}(2) − O_{m+2}(2) = E_m(2) − O_m(2)`: the value `∑_i (−1)^i 2^i C(d, i) = (−1)^d`, from which the
  alternating sums of the cube (`∑_j (−1)^j 2^{d−j} C(d, j) = (−1)^d ∑_i (−1)^i 2^i C(d, i) = 1`) and of the
  cross-polytope (`1 − (−1)^d + (−1)^d = 1`) follow.

Not derived: the face enumerations themselves, and the permutohedron.
-/

namespace LeanProofs.IPRA.Combinatorics.FaceCounts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialSigned (E O E_succ O_succ E_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The simplex: the even and the odd binomial sums of a row `d + 1` agree. -/
theorem simplex_euler (d : PTm n) : Γ ⊢[PRAAx] E (succ d) one ≐ O (succ d) one := by
  have e1 := natEq (E_succ (Γ := Γ) d one)
  have e2 := natEq (O_succ (Γ := Γ) d one)
  apply deriveNat; ipra_simps
  linear_combination e1 - e2

/-- `E_0(2) = O_0(2) + 1`. -/
theorem alt_zero : Γ ⊢[PRAAx] E (zero : PTm n) two ≐ O zero two + one := by
  have a := natEq (Prf.andE₁ (E_zero (Γ := Γ) two))
  have b := natEq (Prf.andE₂ (E_zero (Γ := Γ) two))
  apply deriveNat; ipra_simps
  linear_combination a - b

/-- `O_1(2) = E_1(2) + 1`. -/
theorem alt_one : Γ ⊢[PRAAx] O (succ (zero : PTm n)) two ≐ E (succ zero) two + one := by
  have a := natEq (Prf.andE₁ (E_zero (Γ := Γ) two))
  have b := natEq (Prf.andE₂ (E_zero (Γ := Γ) two))
  have e1 := natEq (E_succ (Γ := Γ) zero two)
  have e2 := natEq (O_succ (Γ := Γ) zero two)
  apply deriveNat; ipra_simps
  linear_combination e2 - e1 + a - b

/-- `E_{m+2}(2) + O_m(2) = O_{m+2}(2) + E_m(2)`. -/
theorem alt_step_two (m : PTm n) :
    Γ ⊢[PRAAx] E (succ (succ m)) two + O m two ≐ O (succ (succ m)) two + E m two := by
  have e1 := natEq (E_succ (Γ := Γ) (succ m) two)
  have e2 := natEq (O_succ (Γ := Γ) (succ m) two)
  have e3 := natEq (E_succ (Γ := Γ) m two)
  have e4 := natEq (O_succ (Γ := Γ) m two)
  apply deriveNat; ipra_simps
  linear_combination e1 - e2 - e3 + e4

end LeanProofs.IPRA.Combinatorics.FaceCounts

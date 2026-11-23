import IPRADerivations.Combinatorics.Turan

/-!
# The middle third of the residues modulo `3q + 2` is sum-free

Packet: `combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 34 ("Erdős's sum-free subset bound"): "Write
`p = 3q + 2`. The `q + 1` residues `I = {q + 1, …, 2q + 1}` are sum-free modulo `p`. Before reduction their pair
sums lie from `2q + 2` to `4q + 2`. After reduction they lie either above `2q + 1` or at most `q` ... Additivity
modulo `p` makes `B_t` sum-free in the integers."

For integer terms `x, y, z` in the interval `[q + 1, 2q + 1]`, as iPRA derivations:

* `middle_no_sum`: `x + y = z` is contradictory (the pair sums are at least `2q + 2`);
* `middle_no_wrap`: `x + y = z + (3q + 2)` is contradictory (the pair sums are at most `4q + 2`);
* `middle_sum_free`: `x + y = z + (3q + 2) m` is contradictory for every integer term `m` (with `q ≥ 0`): no
  solution of `x + y ≡ z` modulo `p` in the middle third. So if `t a, t b, t c` have residues in `I` and
  `a + b = c`, a contradiction follows: the sets `B_t` are sum-free in the integers.

Not derived: the choice of the prime `p ≡ 2 (mod 3)` exceeding the elements of `A`, the permutation of the
residues by a multiplier, and the averaging over the multipliers (its counting step is in
`Combinatorics/Averaging`).
-/

namespace LeanProofs.IPRA.Combinatorics.SumFreeResidues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Turan (zlt_or_zle)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local macro "ssimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [zsl_def, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] $[$loc]?)

/-- `x, y ≥ q + 1` and `z ≤ 2q + 1` exclude `x + y = z`. -/
theorem middle_no_sum {x y z q : ZT n}
    (hx : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) x) (hy : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) y)
    (hz : Γ ⊢[PRAAx] zle z (ZT.natLit 2 * q + ZT.natLit 1))
    (h : Γ ⊢[PRAAx] ZT.eq (x + y) z) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have e := ZT.toZ_eq h
  refine false_of_comb (zsl hx + zsl hy + zsl hz) ?_ (nn_add (nn_add (nn_zsl _) (nn_zsl _)) (nn_zsl _)) φ
  ssimp at e ⊢
  linear_combination e

/-- `x, y ≤ 2q + 1` and `z ≥ q + 1` exclude `x + y = z + (3q + 2)`. -/
theorem middle_no_wrap {x y z q : ZT n}
    (hx : Γ ⊢[PRAAx] zle x (ZT.natLit 2 * q + ZT.natLit 1))
    (hy : Γ ⊢[PRAAx] zle y (ZT.natLit 2 * q + ZT.natLit 1))
    (hz : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) z)
    (h : Γ ⊢[PRAAx] ZT.eq (x + y) (z + (ZT.natLit 3 * q + ZT.natLit 2))) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  have e := ZT.toZ_eq h
  refine false_of_comb (zsl hx + zsl hy + zsl hz) ?_ (nn_add (nn_add (nn_zsl _) (nn_zsl _)) (nn_zsl _)) φ
  ssimp at e ⊢
  linear_combination (-1 : Groth (Q Γ)) * e

/-- The middle third is sum-free modulo `3q + 2`: `x + y = z + (3q + 2) m` is contradictory. -/
theorem middle_sum_free {x y z q m : ZT n} (hq : Γ ⊢[PRAAx] zle (ZT.natLit 0) q)
    (hx1 : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) x) (hx2 : Γ ⊢[PRAAx] zle x (ZT.natLit 2 * q + ZT.natLit 1))
    (hy1 : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) y) (hy2 : Γ ⊢[PRAAx] zle y (ZT.natLit 2 * q + ZT.natLit 1))
    (hz1 : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) z) (hz2 : Γ ⊢[PRAAx] zle z (ZT.natLit 2 * q + ZT.natLit 1))
    (h : Γ ⊢[PRAAx] ZT.eq (x + y) (z + (ZT.natLit 3 * q + ZT.natLit 2) * m)) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  refine .orE (zlt_or_zle (Γ := Γ) m (ZT.natLit 0)) ?_ ?_
  · -- `m ≥ 1`: the sum would be at least `z + p`
    have hm : (zle (ZT.natLit 0 + ZT.natLit 1) m :: Γ) ⊢[PRAAx] zle (ZT.natLit 0 + ZT.natLit 1) m := Prf.hyp0
    have e := ZT.toZ_eq (h.wk (ψ := zle (ZT.natLit 0 + ZT.natLit 1) m))
    have kq := hq.wk (ψ := zle (ZT.natLit 0 + ZT.natLit 1) m)
    have kx := hx2.wk (ψ := zle (ZT.natLit 0 + ZT.natLit 1) m)
    have ky := hy2.wk (ψ := zle (ZT.natLit 0 + ZT.natLit 1) m)
    have kz := hz1.wk (ψ := zle (ZT.natLit 0 + ZT.natLit 1) m)
    refine false_of_comb (zsl kx + zsl ky + zsl kz + (3 * zsl kq + 2) * zsl hm) ?_
      (nn_add (nn_add (nn_add (nn_zsl _) (nn_zsl _)) (nn_zsl _))
        (nn_mul (nn_add (nn_mul (nn_ofNat 3) (nn_zsl _)) (nn_ofNat 2)) (nn_zsl _))) φ
    ssimp at e ⊢
    linear_combination (-1 : Groth (Q _)) * e
  · -- `m ≤ 0`: the sum would be at most `z`
    have hm : (zle m (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle m (ZT.natLit 0) := Prf.hyp0
    have e := ZT.toZ_eq (h.wk (ψ := zle m (ZT.natLit 0)))
    have kq := hq.wk (ψ := zle m (ZT.natLit 0))
    have kx := hx1.wk (ψ := zle m (ZT.natLit 0))
    have ky := hy1.wk (ψ := zle m (ZT.natLit 0))
    have kz := hz2.wk (ψ := zle m (ZT.natLit 0))
    refine false_of_comb (zsl kx + zsl ky + zsl kz + (3 * zsl kq + 2) * zsl hm) ?_
      (nn_add (nn_add (nn_add (nn_zsl _) (nn_zsl _)) (nn_zsl _))
        (nn_mul (nn_add (nn_mul (nn_ofNat 3) (nn_zsl _)) (nn_ofNat 2)) (nn_zsl _))) φ
    ssimp at e ⊢
    linear_combination e

end LeanProofs.IPRA.Combinatorics.SumFreeResidues

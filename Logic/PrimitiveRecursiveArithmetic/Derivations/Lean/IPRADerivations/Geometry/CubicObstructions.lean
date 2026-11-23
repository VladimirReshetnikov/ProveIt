import IPRADerivations.Core.Parity
import IPRADerivations.Geometry.ConwayAlgebra

/-!
# The cubics of the three classical impossibility results have no rational root

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/obstructions.tex`, Theorems `obs:cube`,
`obs:trisection` and `obs:heptagon`: "The only possible rational roots of `T³ − 2` are `±1, ±2`, and none is a
root", "`t³ − 3t − 1 = 0`. Its only possible rational roots are `1, −1`" and "`t³ + t² − 2t − 1 = 0`. The values
at the only possible rational roots `1, −1` are `−1, 1`". A rational `± p / q` is a pair of natural-number terms
of which at least one is odd (`par p = 1 ∨ par q = 1`, which holds for a fraction in lowest terms), and a root
is the cleared equation between two terms without subtraction. As iPRA derivations, each of the following
equations is contradictory:

* `cube_root_two`: `p³ = 2 q³` (a root `p / q` of `T³ − 2`; a negative root is excluded by its sign);
* `trisection_root_pos`, `trisection_root_neg`: `p³ = 3 p q² + q³` and `3 p q² = p³ + q³` (roots `p / q` and
  `−p / q` of `t³ − 3t − 1`);
* `heptagon_root_pos`, `heptagon_root_neg`: `p³ + p² q = 2 p q² + q³` and `p² q + 2 p q² = p³ + q³` (roots
  `p / q` and `−p / q` of `t³ + t² − 2t − 1`).

The proof is the parity calculation of Theorem `obs:diagonal` ("a finite parity calculation, not an infinite
descent"): with `p = 2a + α`, `q = 2b + β` the two sides have different parities in the three cases where
`α, β` are not both zero (after one cancellation of `2` in one case of the first equation), and
`Core/Parity.even_ne_odd` applies to explicit half-terms.

Not derived: the degree theorem `obs:degree` for towers of quadratic extensions, which turns the absence of a
rational root into the impossibility of the construction.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CubicObstructions

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Parity cases -/

/-- The second hypothesis of a context. -/
theorem hyp1 {α β : Fm PTm n} : (α :: β :: Γ) ⊢[PRAAx] β := (Prf.hyp0 : (β :: Γ) ⊢[PRAAx] β).wk

/-- Weakening by two hypotheses. -/
theorem wk2 {α β ψ : Fm PTm n} (h : Γ ⊢[PRAAx] ψ) : (α :: β :: Γ) ⊢[PRAAx] ψ := h.wk.wk

/-- An even term has parity zero. -/
theorem even_not_odd {x : PTm n} (φ : Fm PTm n) (he : Γ ⊢[PRAAx] x ≐ two * half x)
    (ho : Γ ⊢[PRAAx] par x ≐ one) : Γ ⊢[PRAAx] φ :=
  succ_ne_zero' φ (a := zero) (ho.eqSymm.eqTrans ((congrAp1 parF he).eqTrans (par_double _)))

/-- Two even terms are excluded when one of them is odd. -/
theorem both_even {p q : PTm n} (φ : Fm PTm n) (hp : Γ ⊢[PRAAx] p ≐ two * half p)
    (hq : Γ ⊢[PRAAx] q ≐ two * half q) (hc : Γ ⊢[PRAAx] (par p ≐ one) ⋎ (par q ≐ one)) : Γ ⊢[PRAAx] φ :=
  .orE hc (even_not_odd φ hp.wk Prf.hyp0) (even_not_odd φ hq.wk Prf.hyp0)

/-- The four parity cases of two terms. -/
theorem parity_split (p q : PTm n) {φ : Fm PTm n}
    (c00 : ((q ≐ two * half q) :: (p ≐ two * half p) :: Γ) ⊢[PRAAx] φ)
    (c01 : ((q ≐ two * half q + one) :: (p ≐ two * half p) :: Γ) ⊢[PRAAx] φ)
    (c10 : ((q ≐ two * half q) :: (p ≐ two * half p + one) :: Γ) ⊢[PRAAx] φ)
    (c11 : ((q ≐ two * half q + one) :: (p ≐ two * half p + one) :: Γ) ⊢[PRAAx] φ) : Γ ⊢[PRAAx] φ :=
  .orE (even_or_odd p) (.orE (even_or_odd q) c00 c01) (.orE (even_or_odd q) c10 c11)

/-! ## The three cubics -/

/-- `T³ − 2` has no rational root: `p³ = 2 q³` is contradictory. -/
theorem cube_root_two {p q : PTm n} (h : Γ ⊢[PRAAx] p * p * p ≐ num 2 * (q * q * q))
    (hc : Γ ⊢[PRAAx] (par p ≐ one) ⋎ (par q ≐ one)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  refine parity_split p q ?_ ?_ ?_ ?_
  · exact both_even φ hyp1 Prf.hyp0 (wk2 hc)
  · refine even_ne_odd (k := num 2 * (half p * half p * half p))
      (m := num 4 * (half q * half q * half q) + num 6 * (half q * half q) + num 3 * (half q)) φ ?_
    refine ConwayAlgebra.cancel_two_nat ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 8 * (half q * half q * half q))
      (m := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁
  · refine even_ne_odd (k := num 8 * (half q * half q * half q) + num 12 * (half q * half q) + num 6 * (half q) +
        num 1)
      (m := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁

/-- `t³ − 3t − 1` has no root `p / q`. -/
theorem trisection_root_pos {p q : PTm n} (h : Γ ⊢[PRAAx] p * p * p ≐ num 3 * (p * q * q) + q * q * q)
    (hc : Γ ⊢[PRAAx] (par p ≐ one) ⋎ (par q ≐ one)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  refine parity_split p q ?_ ?_ ?_ ?_
  · exact both_even φ hyp1 Prf.hyp0 (wk2 hc)
  · refine even_ne_odd (k := num 4 * (half p * half p * half p))
      (m := num 12 * (half p * half q * half q) + num 12 * (half p * half q) + num 3 * (half p) +
        num 4 * (half q * half q * half q) + num 6 * (half q * half q) + num 3 * (half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 12 * (half p * half q * half q) + num 4 * (half q * half q * half q) +
        num 6 * (half q * half q))
      (m := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁
  · refine even_ne_odd (k := num 12 * (half p * half q * half q) + num 12 * (half p * half q) + num 3 * (half p) +
        num 4 * (half q * half q * half q) + num 12 * (half q * half q) + num 9 * (half q) + num 2)
      (m := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁

/-- `t³ − 3t − 1` has no root `−p / q`. -/
theorem trisection_root_neg {p q : PTm n} (h : Γ ⊢[PRAAx] num 3 * (p * q * q) ≐ p * p * p + q * q * q)
    (hc : Γ ⊢[PRAAx] (par p ≐ one) ⋎ (par q ≐ one)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  refine parity_split p q ?_ ?_ ?_ ?_
  · exact both_even φ hyp1 Prf.hyp0 (wk2 hc)
  · refine even_ne_odd (k := num 12 * (half p * half q * half q) + num 12 * (half p * half q) +
        num 3 * (half p))
      (m := num 4 * (half p * half p * half p) + num 4 * (half q * half q * half q) + num 6 * (half q * half q) +
        num 3 * (half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 12 * (half p * half q * half q) + num 6 * (half q * half q))
      (m := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p) +
        num 4 * (half q * half q * half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p) +
        num 4 * (half q * half q * half q) + num 6 * (half q * half q) + num 3 * (half q) + num 1)
      (m := num 12 * (half p * half q * half q) + num 12 * (half p * half q) + num 3 * (half p) +
        num 6 * (half q * half q) + num 6 * (half q) + num 1) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁

/-- `t³ + t² − 2t − 1` has no root `p / q`. -/
theorem heptagon_root_pos {p q : PTm n} (h : Γ ⊢[PRAAx] p * p * p + p * p * q ≐ num 2 * (p * q * q) + q * q * q)
    (hc : Γ ⊢[PRAAx] (par p ≐ one) ⋎ (par q ≐ one)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  refine parity_split p q ?_ ?_ ?_ ?_
  · exact both_even φ hyp1 Prf.hyp0 (wk2 hc)
  · refine even_ne_odd (k := num 4 * (half p * half p * half p) + num 4 * (half p * half p * half q) +
        num 2 * (half p * half p))
      (m := num 8 * (half p * half q * half q) + num 8 * (half p * half q) + num 2 * (half p) +
        num 4 * (half q * half q * half q) + num 6 * (half q * half q) + num 3 * (half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 8 * (half p * half q * half q) + num 4 * (half q * half q * half q) +
        num 4 * (half q * half q))
      (m := num 4 * (half p * half p * half p) + num 4 * (half p * half p * half q) + num 6 * (half p * half p) +
        num 4 * (half p * half q) + num 3 * (half p) + num 1 * (half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁
  · refine even_ne_odd (k := num 4 * (half p * half p * half p) + num 4 * (half p * half p * half q) +
        num 8 * (half p * half p) + num 4 * (half p * half q) + num 5 * (half p) + num 1 * (half q) + num 1)
      (m := num 8 * (half p * half q * half q) + num 8 * (half p * half q) + num 2 * (half p) +
        num 4 * (half q * half q * half q) + num 10 * (half q * half q) + num 7 * (half q) + num 1) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁

/-- `t³ + t² − 2t − 1` has no root `−p / q`. -/
theorem heptagon_root_neg {p q : PTm n} (h : Γ ⊢[PRAAx] p * p * q + num 2 * (p * q * q) ≐ p * p * p + q * q * q)
    (hc : Γ ⊢[PRAAx] (par p ≐ one) ⋎ (par q ≐ one)) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  refine parity_split p q ?_ ?_ ?_ ?_
  · exact both_even φ hyp1 Prf.hyp0 (wk2 hc)
  · refine even_ne_odd (k := num 4 * (half p * half p * half q) + num 2 * (half p * half p) +
        num 8 * (half p * half q * half q) + num 8 * (half p * half q) + num 2 * (half p))
      (m := num 4 * (half p * half p * half p) + num 4 * (half q * half q * half q) + num 6 * (half q * half q) +
        num 3 * (half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 4 * (half p * half p * half q) + num 8 * (half p * half q * half q) +
        num 4 * (half p * half q) + num 4 * (half q * half q) + num 1 * (half q))
      (m := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p) +
        num 4 * (half q * half q * half q)) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination h₁
  · refine even_ne_odd (k := num 4 * (half p * half p * half p) + num 6 * (half p * half p) + num 3 * (half p) +
        num 4 * (half q * half q * half q) + num 6 * (half q * half q) + num 3 * (half q) + num 1)
      (m := num 4 * (half p * half p * half q) + num 2 * (half p * half p) + num 8 * (half p * half q * half q) +
        num 12 * (half p * half q) + num 4 * (half p) + num 4 * (half q * half q) + num 5 * (half q) +
        num 1) φ ?_
    refine withEq (wk2 h) fun h₁ => withEq hyp1 fun h₂ => withEq Prf.hyp0 fun h₃ => ?_
    apply deriveNat; ipra_simps; rw [h₂, h₃] at h₁; push_cast at h₁ ⊢
    linear_combination -h₁

end LeanProofs.IPRA.Geometry.CubicObstructions

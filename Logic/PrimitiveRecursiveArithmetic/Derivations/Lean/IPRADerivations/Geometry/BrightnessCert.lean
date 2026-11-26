import IPRADerivations.Geometry.CubeShadow

/-!
# The upper certificate for polyhedral brightness

Packet: `geometry/platonic_projection_extrema_2026-11-19`, Theorem `thm:finite` ("Signed sums and cross products"),
the upper half: for `F(x) = ∑ |g_i · x|`, if `Q(∑ ε_i g_i) ≤ U` for every sign vector `ε`, then `F(x)² ≤ U Q(x)`.
For a given `x`, `F(x) = w · x` with `w = ∑ ε_i g_i` for the signs `ε_i` of `g_i · x`; so the step is the
three-dimensional Cauchy–Schwarz inequality `(w · x)² ≤ Q(w) Q(x)`, followed by `Q(w) ≤ U`.

Over integer coordinates (homogeneous, so rational data are covered):

* `lagrange3`: `Q(w) Q(x) − (w · x)² = |w × x|²`;
* `cs3`: `(w · x)² ≤ Q(w) Q(x)` (the three squares of `w × x` are natural numbers, `IntOrder.sq_nat`);
* `finite_upper`: `F = w · x` and `Q(w) ≤ U` (with `U ≥ 0` implicit in the certificate) give `F² ≤ U Q(x)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.BrightnessCert

open_ipra
open LeanProofs.IPRA.Geometry.CuboidAlgebra (zle_mul_nonneg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section
variable (w1 w2 w3 x1 x2 x3 : ZT n)
/-- `w · x`. -/
abbrev Dot : ZT n := w1 * x1 + w2 * x2 + w3 * x3
/-- `Q(w)`. -/
abbrev Qd : ZT n := w1 * w1 + w2 * w2 + w3 * w3
end

/-- The Lagrange identity in three dimensions. -/
theorem lagrange3 (w1 w2 w3 x1 x2 x3 : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Qd w1 w2 w3 * Qd x1 x2 x3 - Dot w1 w2 w3 x1 x2 x3 * Dot w1 w2 w3 x1 x2 x3)
      ((w2 * x3 - w3 * x2) * (w2 * x3 - w3 * x2) + (w3 * x1 - w1 * x3) * (w3 * x1 - w1 * x3) +
        (w1 * x2 - w2 * x1) * (w1 * x2 - w2 * x1)) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]
  ring

/-- `(w · x)² ≤ Q(w) Q(x)`. -/
theorem cs3 (w1 w2 w3 x1 x2 x3 : ZT n) :
    Γ ⊢[PRAAx] zle (Dot w1 w2 w3 x1 x2 x3 * Dot w1 w2 w3 x1 x2 x3) (Qd w1 w2 w3 * Qd x1 x2 x3) := by
  have L := ZT.toZ_eq (lagrange3 (Γ := Γ) w1 w2 w3 x1 x2 x3)
  have c1 := sq_nat (Γ := Γ) (w2 * x3 - w3 * x2)
  have c2 := sq_nat (Γ := Γ) (w3 * x1 - w1 * x3)
  have c3 := sq_nat (Γ := Γ) (w1 * x2 - w2 * x1)
  refine zle_of_toZ ((monus (w2 * x3 - w3 * x2).pos (w2 * x3 - w3 * x2).neg +
      monus (w2 * x3 - w3 * x2).neg (w2 * x3 - w3 * x2).pos) *
      (monus (w2 * x3 - w3 * x2).pos (w2 * x3 - w3 * x2).neg +
      monus (w2 * x3 - w3 * x2).neg (w2 * x3 - w3 * x2).pos) +
    (monus (w3 * x1 - w1 * x3).pos (w3 * x1 - w1 * x3).neg +
      monus (w3 * x1 - w1 * x3).neg (w3 * x1 - w1 * x3).pos) *
      (monus (w3 * x1 - w1 * x3).pos (w3 * x1 - w1 * x3).neg +
      monus (w3 * x1 - w1 * x3).neg (w3 * x1 - w1 * x3).pos) +
    (monus (w1 * x2 - w2 * x1).pos (w1 * x2 - w2 * x1).neg +
      monus (w1 * x2 - w2 * x1).neg (w1 * x2 - w2 * x1).pos) *
      (monus (w1 * x2 - w2 * x1).pos (w1 * x2 - w2 * x1).neg +
      monus (w1 * x2 - w2 * x1).neg (w1 * x2 - w2 * x1).pos)) ?_
  simp only [ZT.toZ_sq, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul] at L c1 c2 c3 ⊢
  ipra_simps
  linear_combination -L - c1 - c2 - c3

/-- `thm:finite`, upper half: `F = w · x` and `Q(w) ≤ U` give `F² ≤ U Q(x)`. -/
theorem finite_upper {w1 w2 w3 x1 x2 x3 F U : ZT n} (hF : Γ ⊢[PRAAx] ZT.eq F (Dot w1 w2 w3 x1 x2 x3))
    (hU : Γ ⊢[PRAAx] zle (Qd w1 w2 w3) U) : Γ ⊢[PRAAx] zle (F * F) (U * Qd x1 x2 x3) := by
  have c := zle_toZ (cs3 (Γ := Γ) w1 w2 w3 x1 x2 x3)
  have hQ : Γ ⊢[PRAAx] zle (ZT.natLit 0) (Qd x1 x2 x3) := by
    refine zle_of_toZ ((monus x1.pos x1.neg + monus x1.neg x1.pos) * (monus x1.pos x1.neg + monus x1.neg x1.pos) +
      (monus x2.pos x2.neg + monus x2.neg x2.pos) * (monus x2.pos x2.neg + monus x2.neg x2.pos) +
      (monus x3.pos x3.neg + monus x3.neg x3.pos) * (monus x3.pos x3.neg + monus x3.neg x3.pos)) ?_
    have s1 := sq_nat (Γ := Γ) x1
    have s2 := sq_nat (Γ := Γ) x2
    have s3 := sq_nat (Γ := Γ) x3
    simp only [ZT.toZ_sq, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit] at s1 s2 s3 ⊢
    ipra_simps
    push_cast
    linear_combination -(s1 + s2 + s3)
  have hd : Γ ⊢[PRAAx] zle (ZT.natLit 0) (U - Qd w1 w2 w3) := by
    have e := zle_toZ hU
    refine zle_of_toZ (monus (U.pos + (Qd w1 w2 w3).neg) ((Qd w1 w2 w3).pos + U.neg)) ?_
    simp only [ZT.toZ_sub, ZT.toZ_natLit] at e ⊢
    push_cast
    linear_combination e
  have p := zle_toZ (zle_mul_nonneg hd hQ)
  have eF := ZT.toZ_eq hF
  refine zle_of_toZ (monus ((Qd w1 w2 w3 * Qd x1 x2 x3).pos + (Dot w1 w2 w3 x1 x2 x3 * Dot w1 w2 w3 x1 x2 x3).neg) ((Dot w1 w2 w3 x1 x2 x3 * Dot w1 w2 w3 x1 x2 x3).pos + (Qd w1 w2 w3 * Qd x1 x2 x3).neg) +
    monus (((U - Qd w1 w2 w3) * Qd x1 x2 x3).pos + (ZT.natLit 0 : ZT n).neg) ((ZT.natLit 0 : ZT n).pos + ((U - Qd w1 w2 w3) * Qd x1 x2 x3).neg)) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Q.mk_add, map_add] at c p eF ⊢
  push_cast at c p eF ⊢
  linear_combination c + p + (ZT.toZ Γ F + ZT.toZ Γ w1 * ZT.toZ Γ x1 + ZT.toZ Γ w2 * ZT.toZ Γ x2 +
    ZT.toZ Γ w3 * ZT.toZ Γ x3) * eF

end LeanProofs.IPRA.Geometry.BrightnessCert

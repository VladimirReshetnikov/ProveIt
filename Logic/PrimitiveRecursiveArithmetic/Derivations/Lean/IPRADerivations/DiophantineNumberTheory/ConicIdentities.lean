import IPRADerivations.Algebra.AdjugateInverse
import IPRADerivations.Core.Header

/-!
# The integer identities of a pointed conic

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Section `sec:conics` ("Conics: complete
parametrization and explicit height growth"), the identities behind Theorem `thm:conic-param`: for
`q = ∑ a_{ij} X_i X_j` and a point `p` with `q(p) = 0`, `M = [[p_0,0,0],[p_1,1,0],[p_2,0,1]]`:

* `conic_normal` (`eq:conic-normal`): `q(M(U, V, W)) = U L(V, W) + R(V, W)` with
  `L = ℓ V + m W`, `R = a V² + b V W + c W²` (`a = a_{11}`, `b = a_{12}`, `c = a_{22}`);
* `adj_inverse` (`eq:conic-adjugate`): `M (adj M x) = p_0 x` with `adj M x = (x_0, p_0 x_1 − p_1 x_0, p_0 x_2 − p_2 x_0)`;
* `identity_s`, `identity_t` (`eq:conic-identity-s`, `eq:conic-identity-t`):
  `r s² = m² R(s, t) − L(s, t)((b m − c ℓ) s + c m t)` and `r t² = ℓ² R(s, t) − L(s, t)(a ℓ s + (b ℓ − a m) t)`,
  `r = a m² − b ℓ m + c ℓ²`;
* `param_on_conic` (`thm:conic-param`, first step): `q(M F(s, t)) = 0` for `F = (−R, s L, t L)`;
* `param_tangent`: the parameter `[−m : ℓ]` has `L = 0` and `R = r`, so it maps to `[p]`.

All identities are equalities of integer terms (`ZT`), proved by expanding to the ring of differences.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicIdentities

open LeanProofs.ConciseIPRA LeanProofs.IPRA

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The six coefficients of a ternary quadratic form. -/
structure Form (n : ℕ) where
  a00 : ZT n
  a01 : ZT n
  a02 : ZT n
  a11 : ZT n
  a12 : ZT n
  a22 : ZT n

namespace Form

variable (Q : Form n)

/-- `q(x) = ∑_{i ≤ j} a_{ij} x_i x_j`. -/
def q (x0 x1 x2 : ZT n) : ZT n :=
  Q.a00 * x0 * x0 + Q.a01 * x0 * x1 + Q.a02 * x0 * x2 + Q.a11 * x1 * x1 + Q.a12 * x1 * x2 + Q.a22 * x2 * x2

/-- `ℓ = a_{01} p_0 + 2 a_{11} p_1 + a_{12} p_2`. -/
def ell (p0 p1 p2 : ZT n) : ZT n := Q.a01 * p0 + ZT.natLit 2 * Q.a11 * p1 + Q.a12 * p2
/-- `m = a_{02} p_0 + a_{12} p_1 + 2 a_{22} p_2`. -/
def emm (p0 p1 p2 : ZT n) : ZT n := Q.a02 * p0 + Q.a12 * p1 + ZT.natLit 2 * Q.a22 * p2
/-- `L(V, W) = ℓ V + m W`. -/
def L (p0 p1 p2 V W : ZT n) : ZT n := Q.ell p0 p1 p2 * V + Q.emm p0 p1 p2 * W
/-- `R(V, W) = a V² + b V W + c W²`. -/
def R (V W : ZT n) : ZT n := Q.a11 * V * V + Q.a12 * V * W + Q.a22 * W * W
/-- `r = a m² − b ℓ m + c ℓ²`. -/
def r (p0 p1 p2 : ZT n) : ZT n :=
  Q.a11 * Q.emm p0 p1 p2 * Q.emm p0 p1 p2 - Q.a12 * Q.ell p0 p1 p2 * Q.emm p0 p1 p2 +
    Q.a22 * Q.ell p0 p1 p2 * Q.ell p0 p1 p2

theorem toZ_q (x0 x1 x2 : ZT n) : ZT.toZ Γ (Q.q x0 x1 x2) =
    ZT.toZ Γ Q.a00 * ZT.toZ Γ x0 * ZT.toZ Γ x0 + ZT.toZ Γ Q.a01 * ZT.toZ Γ x0 * ZT.toZ Γ x1 +
      ZT.toZ Γ Q.a02 * ZT.toZ Γ x0 * ZT.toZ Γ x2 + ZT.toZ Γ Q.a11 * ZT.toZ Γ x1 * ZT.toZ Γ x1 +
      ZT.toZ Γ Q.a12 * ZT.toZ Γ x1 * ZT.toZ Γ x2 + ZT.toZ Γ Q.a22 * ZT.toZ Γ x2 * ZT.toZ Γ x2 := by
  simp [q]

theorem toZ_L (p0 p1 p2 V W : ZT n) : ZT.toZ Γ (Q.L p0 p1 p2 V W) =
    (ZT.toZ Γ Q.a01 * ZT.toZ Γ p0 + 2 * ZT.toZ Γ Q.a11 * ZT.toZ Γ p1 + ZT.toZ Γ Q.a12 * ZT.toZ Γ p2) * ZT.toZ Γ V +
      (ZT.toZ Γ Q.a02 * ZT.toZ Γ p0 + ZT.toZ Γ Q.a12 * ZT.toZ Γ p1 + 2 * ZT.toZ Γ Q.a22 * ZT.toZ Γ p2) * ZT.toZ Γ W := by
  simp [L, ell, emm]

theorem toZ_R (V W : ZT n) : ZT.toZ Γ (Q.R V W) =
    ZT.toZ Γ Q.a11 * ZT.toZ Γ V * ZT.toZ Γ V + ZT.toZ Γ Q.a12 * ZT.toZ Γ V * ZT.toZ Γ W +
      ZT.toZ Γ Q.a22 * ZT.toZ Γ W * ZT.toZ Γ W := by
  simp [R]

theorem toZ_r (p0 p1 p2 : ZT n) : ZT.toZ Γ (Q.r p0 p1 p2) =
    ZT.toZ Γ Q.a11 * ZT.toZ Γ (Q.emm p0 p1 p2) * ZT.toZ Γ (Q.emm p0 p1 p2) -
      ZT.toZ Γ Q.a12 * ZT.toZ Γ (Q.ell p0 p1 p2) * ZT.toZ Γ (Q.emm p0 p1 p2) +
      ZT.toZ Γ Q.a22 * ZT.toZ Γ (Q.ell p0 p1 p2) * ZT.toZ Γ (Q.ell p0 p1 p2) := by
  simp [r]

theorem toZ_ell (p0 p1 p2 : ZT n) : ZT.toZ Γ (Q.ell p0 p1 p2) =
    ZT.toZ Γ Q.a01 * ZT.toZ Γ p0 + 2 * ZT.toZ Γ Q.a11 * ZT.toZ Γ p1 + ZT.toZ Γ Q.a12 * ZT.toZ Γ p2 := by
  simp [ell]

theorem toZ_emm (p0 p1 p2 : ZT n) : ZT.toZ Γ (Q.emm p0 p1 p2) =
    ZT.toZ Γ Q.a02 * ZT.toZ Γ p0 + ZT.toZ Γ Q.a12 * ZT.toZ Γ p1 + 2 * ZT.toZ Γ Q.a22 * ZT.toZ Γ p2 := by
  simp [emm]

/-- `eq:conic-normal`: `q(M(U, V, W)) = U L(V, W) + R(V, W)` when `q(p) = 0`. -/
theorem conic_normal {p0 p1 p2 : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq (Q.q p0 p1 p2) (ZT.natLit 0)) (U V W : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Q.q (p0 * U) (p1 * U + V) (p2 * U + W)) (U * Q.L p0 p1 p2 V W + Q.R V W) := by
  have e := ZT.toZ_eq hp
  rw [toZ_q] at e
  refine ZT.derive ?_
  simp only [toZ_q, toZ_L, toZ_R, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit] at e ⊢
  linear_combination ZT.toZ Γ U * ZT.toZ Γ U * e

/-- `eq:conic-adjugate`: `M (adj M x) = p_0 x`. -/
theorem adj_inverse (p0 p1 p2 x0 x1 x2 : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (p0 * x0) (p0 * x0)) ∧
    (Γ ⊢[PRAAx] ZT.eq (p1 * x0 + (p0 * x1 - p1 * x0)) (p0 * x1)) ∧
    (Γ ⊢[PRAAx] ZT.eq (p2 * x0 + (p0 * x2 - p2 * x0)) (p0 * x2)) :=
  ⟨ZT.derive (by simp only [ZT.toZ_mul]), ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]; ring),
    ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]; ring)⟩

/-- `eq:conic-identity-s`. -/
theorem identity_s (p0 p1 p2 s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Q.r p0 p1 p2 * s * s)
      (Q.emm p0 p1 p2 * Q.emm p0 p1 p2 * Q.R s t -
        Q.L p0 p1 p2 s t * ((Q.a12 * Q.emm p0 p1 p2 - Q.a22 * Q.ell p0 p1 p2) * s + Q.a22 * Q.emm p0 p1 p2 * t)) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_add, toZ_r, toZ_R, toZ_L, toZ_ell, toZ_emm]
  ring

/-- `eq:conic-identity-t`. -/
theorem identity_t (p0 p1 p2 s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Q.r p0 p1 p2 * t * t)
      (Q.ell p0 p1 p2 * Q.ell p0 p1 p2 * Q.R s t -
        Q.L p0 p1 p2 s t * (Q.a11 * Q.ell p0 p1 p2 * s + (Q.a12 * Q.ell p0 p1 p2 - Q.a11 * Q.emm p0 p1 p2) * t)) := by
  refine ZT.derive ?_
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_add, toZ_r, toZ_R, toZ_L, toZ_ell, toZ_emm]
  ring

/-- `thm:conic-param`, the image lies on the conic: `q(M F(s, t)) = 0` for `F = (−R, s L, t L)`. -/
theorem param_on_conic {p0 p1 p2 : ZT n} (hp : Γ ⊢[PRAAx] ZT.eq (Q.q p0 p1 p2) (ZT.natLit 0)) (s t : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Q.q (p0 * -Q.R s t) (p1 * -Q.R s t + s * Q.L p0 p1 p2 s t)
      (p2 * -Q.R s t + t * Q.L p0 p1 p2 s t)) (ZT.natLit 0) := by
  have e := ZT.toZ_eq hp
  rw [toZ_q] at e
  refine ZT.derive ?_
  simp only [toZ_q, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_neg, ZT.toZ_natLit, toZ_R, toZ_L] at e ⊢
  linear_combination (ZT.toZ Γ Q.a11 * ZT.toZ Γ s * ZT.toZ Γ s + ZT.toZ Γ Q.a12 * ZT.toZ Γ s * ZT.toZ Γ t +
    ZT.toZ Γ Q.a22 * ZT.toZ Γ t * ZT.toZ Γ t) ^ 2 * e

/-- `thm:conic-param`, the tangent parameter: `L(−m, ℓ) = 0` and `R(−m, ℓ) = r`, so `[−m : ℓ]` maps to `[p]`. -/
theorem param_tangent (p0 p1 p2 : ZT n) :
    (Γ ⊢[PRAAx] ZT.eq (Q.L p0 p1 p2 (-Q.emm p0 p1 p2) (Q.ell p0 p1 p2)) (ZT.natLit 0)) ∧
    (Γ ⊢[PRAAx] ZT.eq (Q.R (-Q.emm p0 p1 p2) (Q.ell p0 p1 p2)) (Q.r p0 p1 p2)) := by
  refine ⟨ZT.derive ?_, ZT.derive ?_⟩
  · simp only [ZT.toZ_neg, ZT.toZ_natLit, toZ_L, toZ_ell, toZ_emm]; push_cast; ring
  · simp only [ZT.toZ_neg, toZ_R, toZ_r, toZ_ell, toZ_emm]; ring

end Form

end LeanProofs.IPRA.DiophantineNumberTheory.ConicIdentities


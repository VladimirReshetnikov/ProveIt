import IPRADerivations.Geometry.CircleChords

/-!
# Lagrange's identity in finite dimension, planes and the circumsphere

Packet: `geometry/euclidean_geometry_ipra_2026-11-22`, `chapters/solids.tex`, Theorems `sol:gram`,
`sol:projection` and `sol:circumsphere`. Vectors of dimension `d` are families `Fin d → ZT n` of integer terms,
with `N(u) = ∑ u_i²` and `u · v = ∑ u_i v_i`. As iPRA derivations:

* `lagrange_sum`, `lagrange`: "`N(u) N(v) − (u · v)² = ∑_{i<j<d} (u_i v_j − u_j v_i)²`", over ordered pairs:
  `∑_i ∑_j (u_i v_j − u_j v_i)² = 2 (N(u) N(v) − (u · v)²)`;
* `cauchy_schwarz`: `(u · v)² ≤ N(u) N(v)` in every dimension;
* `norm_triangle`: the triangle inequality, squared: for `s, t ≥ 0` with `s² = N(u)` and `t² = N(v)`,
  `N(u + v) ≤ (s + t)²`;
* `plane_foot`: "Substitution verifies `n · F = h`" for the foot `F = P + (h − n · P) n / N(n)` of `P` on the
  plane `n · X = h`, times `N(n)`;
* `plane_distance`: the distance `|n · P − h|/√N(n)` from `P` to the plane is a lower bound for the distance to
  its points ("It uniquely minimizes the distance to `P` among points of the plane"):
  `(n · P − h)² ≤ N(n) N(P − X)` when `n · X = h`;
* `circumsphere_u`, `circumsphere_v`, `circumsphere_w`: for the scaled centre
  `O' = N(u) (v × w) + N(v) (w × u) + N(w) (u × v)` of the sphere through `0, u, v, w`,
  `O' · u = N(u) D`, `O' · v = N(v) D`, `O' · w = N(w) D` with `D = [u, v, w]`: "`2 O · u = N(u)` and the
  corresponding equations for `v, w`".

Not derived: the uniqueness statements, the sphere sections, and the reflection in a plane.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.EuclideanSpace

open_ipra
open LeanProofs.IPRA.Geometry.CircleChords (zle_of_sq_le)

variable {n d : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

theorem sum_mul_sum_eq (f g : Fin d → R) : ∑ i, ∑ j, f i * g j = (∑ i, f i) * ∑ j, g j := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- Lagrange's identity over ordered pairs. -/
theorem lagrange_sum (u v : Fin d → R) :
    ∑ i, ∑ j, (u i * v j - u j * v i) ^ 2 =
      2 * ((∑ i, u i ^ 2) * (∑ i, v i ^ 2) - (∑ i, u i * v i) ^ 2) := by
  have e : ∀ i j, (u i * v j - u j * v i) ^ 2 =
      u i ^ 2 * v j ^ 2 + v i ^ 2 * u j ^ 2 - (u i * v i * (u j * v j) + u i * v i * (u j * v j)) := by
    intro i j
    ring
  have h : ∑ i, ∑ j, (u i * v j - u j * v i) ^ 2 =
      ∑ i, ∑ j, u i ^ 2 * v j ^ 2 + ∑ i, ∑ j, v i ^ 2 * u j ^ 2 -
        (∑ i, ∑ j, u i * v i * (u j * v j) + ∑ i, ∑ j, u i * v i * (u j * v j)) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j
  rw [h, sum_mul_sum_eq (fun i => u i ^ 2) (fun j => v j ^ 2),
    sum_mul_sum_eq (fun i => v i ^ 2) (fun j => u j ^ 2),
    sum_mul_sum_eq (fun i => u i * v i) (fun j => u j * v j)]
  ring

/-- `∑ (a_i + b_i)² = ∑ a_i² + 2 ∑ a_i b_i + ∑ b_i²`. -/
theorem sum_add_sq (a b : Fin d → R) :
    ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∑ n_i (N p_i + c n_i) = N ∑ n_i p_i + c ∑ n_i²`. -/
theorem foot_sum (ν p : Fin d → R) (N c : R) :
    ∑ i, ν i * (N * p i + c * ν i) = N * ∑ i, ν i * p i + c * ∑ i, ν i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∑ n_i (p_i − x_i) = ∑ n_i p_i − ∑ n_i x_i`. -/
theorem dot_sub (ν p x : Fin d → R) : ∑ i, ν i * (p i - x i) = ∑ i, ν i * p i - ∑ i, ν i * x i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Ring

/-! ## Lagrange and Cauchy–Schwarz -/

/-- Lagrange's identity: `∑_i ∑_j (u_i v_j − u_j v_i)² = 2 (N(u) N(v) − (u · v)²)`. -/
theorem lagrange (u v : Fin d → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ZT.sumFin fun j => ZT.sq (u i * v j - u j * v i))
      (ZT.natLit 2 * ((ZT.sumFin fun i => ZT.sq (u i)) * (ZT.sumFin fun i => ZT.sq (v i)) -
        ZT.sq (ZT.sumFin fun i => u i * v i))) := by
  have e := lagrange_sum (fun i => ZT.toZ Γ (u i)) (fun i => ZT.toZ Γ (v i))
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- Cauchy–Schwarz in dimension `d`: `(u · v)² ≤ N(u) N(v)`. -/
theorem cauchy_schwarz (u v : Fin d → ZT n) :
    Γ ⊢[PRAAx] zle (ZT.sq (ZT.sumFin fun i => u i * v i))
      ((ZT.sumFin fun i => ZT.sq (u i)) * (ZT.sumFin fun i => ZT.sq (v i))) := by
  have e := lagrange_sum (fun i => ZT.toZ Γ (u i)) (fun i => ZT.toZ Γ (v i))
  beta_reduce at e
  refine zle_of_comb_two (∑ i, ∑ j, ZT.toZ Γ (u i * v j - u j * v i) ^ 2) ?_
    (nn_sum _ _ fun i _ => nn_sum _ _ fun j _ => nn_zsq _)
  zsimp
  exact e.symm

/-- The triangle inequality, squared: `N(u + v) ≤ (s + t)²` for `s, t ≥ 0`, `s² = N(u)`, `t² = N(v)`. -/
theorem norm_triangle {u v : Fin d → ZT n} {s t : ZT n}
    (hs0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) s) (ht0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) t)
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sq s) (ZT.sumFin fun i => ZT.sq (u i)))
    (ht : Γ ⊢[PRAAx] ZT.eq (ZT.sq t) (ZT.sumFin fun i => ZT.sq (v i))) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun i => ZT.sq (u i + v i)) (ZT.sq (s + t)) := by
  have es := ZT.toZ_eq hs
  have et := ZT.toZ_eq ht
  simp only [ZT.toZ_sq, ZT.toZ_sumFin] at es et
  have hcs := cauchy_schwarz (Γ := Γ) u v
  have hst : Γ ⊢[PRAAx] zle (ZT.natLit 0) (s * t) := by
    ipra_zle (zsl hs0 * zsl ht0)
  have hsq : Γ ⊢[PRAAx] zle (ZT.sq (ZT.sumFin fun i => u i * v i)) (ZT.sq (s * t)) := by
    refine zle_of_comb (zsl hcs) ?_ (nn_zsl _)
    zsimp
    have eprod := congr (congrArg HMul.hMul es) et
    linear_combination eprod
  have hP := zle_of_sq_le hst hsq
  have ex := sum_add_sq (fun i => ZT.toZ Γ (u i)) (fun i => ZT.toZ Γ (v i))
  beta_reduce at ex
  refine zle_of_comb (2 * zsl hP) ?_ (nn_mul (nn_ofNat 2) (nn_zsl _))
  zsimp
  rw [ex]
  linear_combination es + et

/-! ## Planes -/

/-- The foot of `P` on the plane `n · X = h`, times `N(n)`, lies in the plane: `n · (N F) = N h`. -/
theorem plane_foot (ν p : Fin d → ZT n) (h : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.sumFin fun i => ν i * ((ZT.sumFin fun j => ZT.sq (ν j)) * p i +
        (h - ZT.sumFin fun j => ν j * p j) * ν i))
      ((ZT.sumFin fun j => ZT.sq (ν j)) * h) := by
  have e := foot_sum (fun i => ZT.toZ Γ (ν i)) (fun i => ZT.toZ Γ (p i))
    (∑ j, ZT.toZ Γ (ν j) ^ 2) (ZT.toZ Γ h - ∑ j, ZT.toZ Γ (ν j) * ZT.toZ Γ (p j))
  beta_reduce at e
  apply ZT.derive
  zsimp
  rw [e]
  ring

/-- The distance from `P` to the plane `n · X = h` is a lower bound for the distance to its points:
`(n · P − h)² ≤ N(n) N(P − X)` when `n · X = h`. -/
theorem plane_distance {ν p x : Fin d → ZT n} {h : ZT n}
    (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => ν i * x i) h) :
    Γ ⊢[PRAAx] zle (ZT.sq ((ZT.sumFin fun i => ν i * p i) - h))
      ((ZT.sumFin fun i => ZT.sq (ν i)) * (ZT.sumFin fun i => ZT.sq (p i - x i))) := by
  have ex := ZT.toZ_eq hx
  simp only [ZT.toZ_sumFin, ZT.toZ_mul] at ex
  have hcs := cauchy_schwarz (Γ := Γ) ν (fun i => p i - x i)
  have ed := dot_sub (fun i => ZT.toZ Γ (ν i)) (fun i => ZT.toZ Γ (p i)) (fun i => ZT.toZ Γ (x i))
  beta_reduce at ed
  refine zle_of_comb (zsl hcs) ?_ (nn_zsl _)
  zsimp
  rw [ed, ex]

/-! ## The circumsphere -/

/-- A coordinate of the cross product. -/
def cx (a₂ a₃ b₂ b₃ : ZT n) : ZT n := a₂ * b₃ - a₃ * b₂

/-- `N(a)` in dimension three. -/
def n3 (a₁ a₂ a₃ : ZT n) : ZT n := a₁ * a₁ + a₂ * a₂ + a₃ * a₃

/-- The triple product `[u, v, w]`. -/
def trip (u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ : ZT n) : ZT n :=
  u₁ * cx v₂ v₃ w₂ w₃ + u₂ * cx v₃ v₁ w₃ w₁ + u₃ * cx v₁ v₂ w₁ w₂

/-- A coordinate of `N(u) (v × w) + N(v) (w × u) + N(w) (u × v)`; the arguments `a₂ a₃` are the two
coordinates of each vector that enter the cross products. -/
def sc (U V W u₂ u₃ v₂ v₃ w₂ w₃ : ZT n) : ZT n :=
  U * cx v₂ v₃ w₂ w₃ + V * cx w₂ w₃ u₂ u₃ + W * cx u₂ u₃ v₂ v₃

attribute [local ipra_defs] cx n3 trip sc

/-- `O' · u = N(u) [u, v, w]`. -/
theorem circumsphere_u (u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₂ u₃ v₂ v₃ w₂ w₃ * u₁ +
        sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₃ u₁ v₃ v₁ w₃ w₁ * u₂ +
        sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₁ u₂ v₁ v₂ w₁ w₂ * u₃)
      (n3 u₁ u₂ u₃ * trip u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃) := by
  ipra_lc

/-- `O' · v = N(v) [u, v, w]`. -/
theorem circumsphere_v (u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₂ u₃ v₂ v₃ w₂ w₃ * v₁ +
        sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₃ u₁ v₃ v₁ w₃ w₁ * v₂ +
        sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₁ u₂ v₁ v₂ w₁ w₂ * v₃)
      (n3 v₁ v₂ v₃ * trip u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃) := by
  ipra_lc

/-- `O' · w = N(w) [u, v, w]`. -/
theorem circumsphere_w (u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₂ u₃ v₂ v₃ w₂ w₃ * w₁ +
        sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₃ u₁ v₃ v₁ w₃ w₁ * w₂ +
        sc (n3 u₁ u₂ u₃) (n3 v₁ v₂ v₃) (n3 w₁ w₂ w₃) u₁ u₂ v₁ v₂ w₁ w₂ * w₃)
      (n3 w₁ w₂ w₃ * trip u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃) := by
  ipra_lc

end LeanProofs.IPRA.Geometry.EuclideanSpace

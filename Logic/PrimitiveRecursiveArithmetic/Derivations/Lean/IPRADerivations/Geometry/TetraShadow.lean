import IPRADerivations.Geometry.CuboidAlgebra

/-!
# The shadows of a regular tetrahedron

Packets: `geometry/platonic_projection_extrema_2026-11-19` (`thm:answers`, the tetrahedron row: minimum `a²/(2√2)`,
maximum `a²/2`; `lem:brightness`) and `geometry/rigid_curve_convex_cover_2026-11-19` ("Smallest shadow of a regular
tetrahedron: every orthogonal planar projection has area at least `a²/(2√2)`").

For the tetrahedron with vertices `(1,1,1), (1,−1,−1), (−1,1,−1), (−1,−1,1)` (edge `2√2`), the face vectors are
proportional to `g_1 = (1,1,1)`, `g_2 = (1,−1,−1)`, `g_3 = (−1,1,−1)`, `g_4 = (−1,−1,1)`, and the brightness formula
gives `area(π_u T) = F(u)/|u|` with `F(u) = ∑ |g_i · u|`. The two bounds are `8Q ≤ F² ≤ 16Q` for `Q = |u|²`,
i.e. `2√2 ≤ area ≤ 4`, which is `a²/(2√2) ≤ area ≤ a²/2`. Over integer coordinates (the statement is homogeneous,
so rational directions are covered), with `a_i = g_i · u` and natural magnitudes `s_i`, `a_i = ±s_i`:

* `frame`: `∑ a_i² = 4Q` and `∑ a_i = 0`, hence `2 ∑_{i<j} a_i a_j = −4Q`;
* `pair_bound`: `a = ±s`, `b = ±t` give `−ab ≤ st`;
* `shadow_upper`: `F² ≤ 16Q` (Cauchy–Schwarz: `16Q − F² = ∑_{i<j} (s_i − s_j)²`);
* `shadow_lower`: `8Q ≤ F²` (`F² − 8Q = 2 ∑_{i<j} (s_i s_j + a_i a_j) ≥ 0`), with equality along an edge direction.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.TetraShadow

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `u = ±s`. -/
abbrev Sgn (u : ZT n) (s : PTm n) : Fm PTm n := ZT.eq u (ZT.ofNat s) ⋎ ZT.eq u (-(ZT.ofNat s))

/-- `u = ±s` gives `u² = s²` in the ring of differences. -/
theorem sgn_sq {u : ZT n} {s : PTm n} (h : Γ ⊢[PRAAx] Sgn u s) :
    Γ ⊢[PRAAx] ZT.eq (u * u) (ZT.ofNat (s * s)) := by
  refine .orE h ?_ ?_
  · have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq u (ZT.ofNat s) :: Γ) ⊢[PRAAx] _)
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at e ⊢
    rw [e]
  · have e := ZT.toZ_eq (Prf.hyp0 : (ZT.eq u (-(ZT.ofNat s)) :: Γ) ⊢[PRAAx] _)
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_neg, Q.mk_mul, map_mul] at e ⊢
    rw [e]; ring

theorem pair_pp {Δ : List (Fm PTm n)} {a b : ZT n} {s t : PTm n} (h1 : Δ ⊢[PRAAx] ZT.eq a (ZT.ofNat s))
    (h2 : Δ ⊢[PRAAx] ZT.eq b (ZT.ofNat t)) : Δ ⊢[PRAAx] zle (-(a * b)) (ZT.ofNat (s * t)) := by
  have e1 := ZT.toZ_eq h1
  have e2 := ZT.toZ_eq h2
  refine zle_of_toZ (num 2 * (s * t)) ?_
  simp only [ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_mul, Q.mk_num, map_mul, map_natCast] at e1 e2 ⊢
  rw [e1, e2]; push_cast; ring

theorem pair_pm {Δ : List (Fm PTm n)} {a b : ZT n} {s t : PTm n} (h1 : Δ ⊢[PRAAx] ZT.eq a (ZT.ofNat s))
    (h2 : Δ ⊢[PRAAx] ZT.eq b (-(ZT.ofNat t))) : Δ ⊢[PRAAx] zle (-(a * b)) (ZT.ofNat (s * t)) := by
  have e1 := ZT.toZ_eq h1
  have e2 := ZT.toZ_eq h2
  refine zle_of_toZ (zero) ?_
  simp only [ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_mul, Q.mk_zero, map_mul, map_zero] at e1 e2 ⊢
  rw [e1, e2]; ring

theorem pair_mp {Δ : List (Fm PTm n)} {a b : ZT n} {s t : PTm n} (h1 : Δ ⊢[PRAAx] ZT.eq a (-(ZT.ofNat s)))
    (h2 : Δ ⊢[PRAAx] ZT.eq b (ZT.ofNat t)) : Δ ⊢[PRAAx] zle (-(a * b)) (ZT.ofNat (s * t)) := by
  have e1 := ZT.toZ_eq h1
  have e2 := ZT.toZ_eq h2
  refine zle_of_toZ (zero) ?_
  simp only [ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_mul, Q.mk_zero, map_mul, map_zero] at e1 e2 ⊢
  rw [e1, e2]; ring

theorem pair_mm {Δ : List (Fm PTm n)} {a b : ZT n} {s t : PTm n} (h1 : Δ ⊢[PRAAx] ZT.eq a (-(ZT.ofNat s)))
    (h2 : Δ ⊢[PRAAx] ZT.eq b (-(ZT.ofNat t))) : Δ ⊢[PRAAx] zle (-(a * b)) (ZT.ofNat (s * t)) := by
  have e1 := ZT.toZ_eq h1
  have e2 := ZT.toZ_eq h2
  refine zle_of_toZ (num 2 * (s * t)) ?_
  simp only [ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_mul, Q.mk_num, map_mul, map_natCast] at e1 e2 ⊢
  rw [e1, e2]; push_cast; ring

/-- `a = ±s`, `b = ±t` give `−ab ≤ st`. -/
theorem pair_bound {a b : ZT n} {s t : PTm n} (ha : Γ ⊢[PRAAx] Sgn a s) (hb : Γ ⊢[PRAAx] Sgn b t) :
    Γ ⊢[PRAAx] zle (-(a * b)) (ZT.ofNat (s * t)) :=
  .orE ha (.orE hb.wk (pair_pp Prf.hyp1 Prf.hyp0) (pair_pm Prf.hyp1 Prf.hyp0))
    (.orE hb.wk (pair_mp Prf.hyp1 Prf.hyp0) (pair_mm Prf.hyp1 Prf.hyp0))

section
variable (x y z : ZT n)
/-- `a_i = g_i · u`. -/
abbrev A1 : ZT n := x + y + z
abbrev A2 : ZT n := x - y - z
abbrev A3 : ZT n := -x + y - z
abbrev A4 : ZT n := -x - y + z
/-- `Q = |u|²`. -/
abbrev QQ : ZT n := x * x + y * y + z * z
end

/-- The witness of `u ≤ v`. -/
abbrev wit (u v : ZT n) : PTm n := monus (v.pos + u.neg) (u.pos + v.neg)

/-- `thm:answers` (tetrahedron maximum): `F² ≤ 16Q`. -/
theorem shadow_upper {x y z : ZT n} {s1 s2 s3 s4 : PTm n} (h1 : Γ ⊢[PRAAx] Sgn (A1 x y z) s1)
    (h2 : Γ ⊢[PRAAx] Sgn (A2 x y z) s2) (h3 : Γ ⊢[PRAAx] Sgn (A3 x y z) s3) (h4 : Γ ⊢[PRAAx] Sgn (A4 x y z) s4) :
    Γ ⊢[PRAAx] zle (ZT.ofNat ((s1 + s2 + s3 + s4) * (s1 + s2 + s3 + s4))) (ZT.natLit 16 * QQ x y z) := by
  have q1 := ZT.toZ_eq (sgn_sq h1)
  have q2 := ZT.toZ_eq (sgn_sq h2)
  have q3 := ZT.toZ_eq (sgn_sq h3)
  have q4 := ZT.toZ_eq (sgn_sq h4)
  have d12 := natEq (ad_sq (Γ := Γ) s1 s2)
  have d13 := natEq (ad_sq (Γ := Γ) s1 s3)
  have d14 := natEq (ad_sq (Γ := Γ) s1 s4)
  have d23 := natEq (ad_sq (Γ := Γ) s2 s3)
  have d24 := natEq (ad_sq (Γ := Γ) s2 s4)
  have d34 := natEq (ad_sq (Γ := Γ) s3 s4)
  refine zle_of_toZ (ad s1 s2 * ad s1 s2 + ad s1 s3 * ad s1 s3 + ad s1 s4 * ad s1 s4 + ad s2 s3 * ad s2 s3 +
    ad s2 s4 * ad s2 s4 + ad s3 s4 * ad s3 s4) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, ZT.toZ_natLit] at q1 q2 q3 q4 ⊢
  ipra_simps
  push_cast at q1 q2 q3 q4 ⊢
  linear_combination d12 + d13 + d14 + d23 + d24 + d34 - 4 * (q1 + q2 + q3 + q4)

/-- `thm:answers` (tetrahedron minimum, the rigid-curve lemma): `8Q ≤ F²`. -/
theorem shadow_lower {x y z : ZT n} {s1 s2 s3 s4 : PTm n} (h1 : Γ ⊢[PRAAx] Sgn (A1 x y z) s1)
    (h2 : Γ ⊢[PRAAx] Sgn (A2 x y z) s2) (h3 : Γ ⊢[PRAAx] Sgn (A3 x y z) s3) (h4 : Γ ⊢[PRAAx] Sgn (A4 x y z) s4) :
    Γ ⊢[PRAAx] zle (ZT.natLit 8 * QQ x y z) (ZT.ofNat ((s1 + s2 + s3 + s4) * (s1 + s2 + s3 + s4))) := by
  have q1 := ZT.toZ_eq (sgn_sq h1)
  have q2 := ZT.toZ_eq (sgn_sq h2)
  have q3 := ZT.toZ_eq (sgn_sq h3)
  have q4 := ZT.toZ_eq (sgn_sq h4)
  have p12 := zle_toZ (pair_bound h1 h2)
  have p13 := zle_toZ (pair_bound h1 h3)
  have p14 := zle_toZ (pair_bound h1 h4)
  have p23 := zle_toZ (pair_bound h2 h3)
  have p24 := zle_toZ (pair_bound h2 h4)
  have p34 := zle_toZ (pair_bound h3 h4)
  refine zle_of_toZ (num 2 * (wit (-(A1 x y z * A2 x y z)) (ZT.ofNat (s1 * s2)) +
    wit (-(A1 x y z * A3 x y z)) (ZT.ofNat (s1 * s3)) + wit (-(A1 x y z * A4 x y z)) (ZT.ofNat (s1 * s4)) +
    wit (-(A2 x y z * A3 x y z)) (ZT.ofNat (s2 * s3)) + wit (-(A2 x y z * A4 x y z)) (ZT.ofNat (s2 * s4)) +
    wit (-(A3 x y z * A4 x y z)) (ZT.ofNat (s3 * s4)))) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, ZT.toZ_natLit] at q1 q2 q3 q4 p12 p13 p14 p23 p24 p34 ⊢
  ipra_simps
  push_cast at q1 q2 q3 q4 p12 p13 p14 p23 p24 p34 ⊢
  linear_combination 2 * (p12 + p13 + p14 + p23 + p24 + p34) + (q1 + q2 + q3 + q4)

end LeanProofs.IPRA.Geometry.TetraShadow

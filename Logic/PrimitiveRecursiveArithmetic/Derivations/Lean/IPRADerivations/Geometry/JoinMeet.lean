import IPRADerivations.Core.PolynomialImplications

/-!
# Join, meet and section lemmas of the projective plane (`eight_geometry_theorems_ipra`)

Packet: `geometry/eight_geometry_theorems_ipra`, the preparatory lemmas "Join-meet identities",
"Intersection parameter" and "Area principle", the theorem of Section 4 (Pappus's harmonic
theorem), and the skew-quadrilateral form of Carnot's polygon theorem (Section 7). All are
identities or implications between integer polynomial equations, universally closed over the
coordinates, derived through `Core/PolynomialImplications`.

Points and lines are integer triples; `×` is the cross product, `·` the dot product, and
`[U V W] = U · (V × W)`.

* `join_left`, `join_right`: `U · (U × V) = 0` and `V · (U × V) = 0`: the line `U × V` passes
  through `U` and `V`;
* `join_unique`: `(U × V) × L = (U · L) V − (V · L) U`, so a line `L` through `U` and `V` has
  `(U × V) × L = 0`: it is proportional to `U × V`;
* `section_parameter`: for affine points (third coordinate `1`),
  `[C D ((1 − t) A + t B)] = (1 − t) [C D A] + t [C D B]`;
* `area_principle`: if `P = (1 − t) A₁ + t A₂` lies on the line `B C`, then
  `t [A₂ C B] = (1 − t) [A₁ B C]`: the ratio in which `B C` cuts `A₁ A₂` is the ratio of the
  two areas;
* `pappus_harmonic`, `pappus_point_*`: with `A = (0,0)`, `B = (1,0)`, `Z = (0,1)`, `Y = (t,0)` on `A B` and
  `D = (0,d)` on `A Z`, the complete-quadrilateral point
  `W = (Z × ((A × C) × (D × B))) × (A × B)`, `C = (D × Y) × (Z × B)`, satisfies
  `[A,W][B,Y] + [A,Y][B,W] = 0`: the pair `W, Y` is harmonic with respect to `A, B`
  (`(A, B; W, Y) = −1`, division-free);
* `skew_quadrilateral`: if the four sides of a quadrilateral meet a plane with linear form
  values `L_A, …, L_D` at the vertices in the parameters `p, q, r, s`, then
  `p q r s · L_A L_B L_C L_D = (1 − p)(1 − q)(1 − r)(1 − s) · L_A L_B L_C L_D`.

The division by `L_A L_B L_C L_D ≠ 0` in the last statement, the certified side product for
`n` points on a side and Carnot's polygon theorem for general `m`, `n` are not derived here.
-/

namespace LeanProofs.IPRA.Geometry.JoinMeet

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## Join and meet: nine integer variables `U`, `V`, `L` -/

section Join

local notation "U" => (Vec3.mk (ZExp.var 0) (ZExp.var 1) (ZExp.var 2) : Vec3 9)
local notation "V" => (Vec3.mk (ZExp.var 3) (ZExp.var 4) (ZExp.var 5) : Vec3 9)
local notation "L" => (Vec3.mk (ZExp.var 6) (ZExp.var 7) (ZExp.var 8) : Vec3 9)

/-- `U · (U × V) = 0`. -/
theorem join_left :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9) (imp [] (dot U (cross U V), 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `V · (U × V) = 0`. -/
theorem join_right :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9) (imp [] (dot V (cross U V), 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `(U × V) × L = (U · L) V − (V · L) U`, first component. -/
theorem join_unique_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [] ((cross (cross U V) L).x, dot U L * (V).x - dot V L * (U).x)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `(U × V) × L = (U · L) V − (V · L) U`, second component. -/
theorem join_unique_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [] ((cross (cross U V) L).y, dot U L * (V).y - dot V L * (U).y)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

/-- `(U × V) × L = (U · L) V − (V · L) U`, third component. -/
theorem join_unique_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [] ((cross (cross U V) L).z, dot U L * (V).z - dot V L * (U).z)) :=
  derive_imp _ _ (by ipra_poly R ρ h; ring)

end Join

/-! ## Sections of a segment: affine points `A`, `B`, `C`, `D` and a parameter `t` -/

/-- The point `(1 − τ) X + τ Y`. -/
def between {k : ℕ} (τ : ZExp k) (X Y : Vec3 k) : Vec3 k :=
  ⟨(1 - τ) * X.x + τ * Y.x, (1 - τ) * X.y + τ * Y.y, (1 - τ) * X.z + τ * Y.z⟩

section Section

local notation "A" => (Vec3.mk (ZExp.var 0) (ZExp.var 1) (1) : Vec3 9)
local notation "B" => (Vec3.mk (ZExp.var 2) (ZExp.var 3) (1) : Vec3 9)
local notation "C" => (Vec3.mk (ZExp.var 4) (ZExp.var 5) (1) : Vec3 9)
local notation "D" => (Vec3.mk (ZExp.var 6) (ZExp.var 7) (1) : Vec3 9)
local notation "t" => (ZExp.var 8 : ZExp 9)

/-- `[C D ((1 − t) A + t B)] = (1 − t) [C D A] + t [C D B]`. -/
theorem section_parameter :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [] (det3 C D (between t A B), (1 - t) * det3 C D A + t * det3 C D B)) :=
  derive_imp _ _ (by ipra_poly R ρ h [between]; ring)

/-- The area principle: if `P = (1 − t) A + t B` lies on the line `C D`, then
`t [B D C] = (1 − t) [A C D]`. -/
theorem area_principle :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 9)
      (imp [(det3 C D (between t A B), 0)] (t * det3 B D C, (1 - t) * det3 A C D)) :=
  derive_imp _ _ (by ipra_poly R ρ h [between]; linear_combination (-1 : R) * h)

end Section

/-! ## Pappus's harmonic theorem: two integer variables `t`, `d` -/

section Harmonic

local notation "t" => (ZExp.var 0 : ZExp 2)
local notation "d" => (ZExp.var 1 : ZExp 2)

local notation "pA" => (Vec3.mk (0) (0) (1) : Vec3 2)
local notation "pB" => (Vec3.mk (1) (0) (1) : Vec3 2)
local notation "pZ" => (Vec3.mk (0) (1) (1) : Vec3 2)
local notation "pY" => (Vec3.mk (t) (0) (1) : Vec3 2)
local notation "pD" => (Vec3.mk (0) (d) (1) : Vec3 2)

/-- `C = D Y ∩ Z B`. -/
def pC : Vec3 2 := cross (cross pD pY) (cross pZ pB)
/-- `X = A C ∩ D B`. -/
def pX : Vec3 2 := cross (cross pA pC) (cross pD pB)
/-- `W = Z X ∩ A B`. -/
def pW : Vec3 2 := cross (cross pZ pX) (cross pA pB)

/-- The bracket `[P, Q] = P.x Q.z − P.z Q.x` of two points of the line `A B`. -/
def br (P Q : Vec3 2) : ZExp 2 := P.x * Q.z - P.z * Q.x

/-- `[A, W][B, Y] + [A, Y][B, W] = 0`: `W` and `Y` are harmonic conjugates with respect to
`A` and `B`. -/
theorem pappus_harmonic :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (br pA pW * br pB pY + br pA pY * br pB pW, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h [br, pW, pX, pC]; ring)

/-- The explicit harmonic conjugate: `W.x = −d (d − 1) t`. -/
theorem pappus_point_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2) (imp [] (pW.x, (0 - d * (d - 1)) * t)) :=
  derive_imp _ _ (by ipra_poly R ρ h [pW, pX, pC]; ring)

/-- The explicit harmonic conjugate: `W.y = 0`. -/
theorem pappus_point_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2) (imp [] (pW.y, 0)) :=
  derive_imp _ _ (by ipra_poly R ρ h [pW, pX, pC]; ring)

/-- The explicit harmonic conjugate: `W.z = −d (d − 1) (2t − 1)`. -/
theorem pappus_point_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 2)
      (imp [] (pW.z, (0 - d * (d - 1)) * (2 * t - 1))) :=
  derive_imp _ _ (by ipra_poly R ρ h [pW, pX, pC]; ring)

end Harmonic

/-! ## The skew quadrilateral: eight integer variables -/

section Skew

local notation "LA" => (ZExp.var 0 : ZExp 8)
local notation "LB" => (ZExp.var 1 : ZExp 8)
local notation "LC" => (ZExp.var 2 : ZExp 8)
local notation "LD" => (ZExp.var 3 : ZExp 8)
local notation "p" => (ZExp.var 4 : ZExp 8)
local notation "q" => (ZExp.var 5 : ZExp 8)
local notation "r" => (ZExp.var 6 : ZExp 8)
local notation "s" => (ZExp.var 7 : ZExp 8)

/-- If `(1 − p) L_A + p L_B = 0`, `(1 − q) L_B + q L_C = 0`, `(1 − r) L_C + r L_D = 0` and
`(1 − s) L_D + s L_A = 0`, then
`p q r s · L_A L_B L_C L_D = (1 − p)(1 − q)(1 − r)(1 − s) · L_A L_B L_C L_D`. -/
theorem skew_quadrilateral :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 8)
      (imp [((1 - p) * LA + p * LB, 0), ((1 - q) * LB + q * LC, 0), ((1 - r) * LC + r * LD, 0),
          ((1 - s) * LD + s * LA, 0)]
        (p * q * r * s * (LA * LB * LC * LD),
          (1 - p) * (1 - q) * (1 - r) * (1 - s) * (LA * LB * LC * LD))) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    linear_combination
      (ρ 5 * ρ 2 * (ρ 6 * ρ 3) * (ρ 7 * ρ 0)) * h₁ -
      ((1 - ρ 4) * ρ 0 * (ρ 6 * ρ 3) * (ρ 7 * ρ 0)) * h₂ +
      ((1 - ρ 4) * ρ 0 * ((1 - ρ 5) * ρ 1) * (ρ 7 * ρ 0)) * h₃ -
      ((1 - ρ 4) * ρ 0 * ((1 - ρ 5) * ρ 1) * ((1 - ρ 6) * ρ 2)) * h₄)

end Skew

end LeanProofs.IPRA.Geometry.JoinMeet

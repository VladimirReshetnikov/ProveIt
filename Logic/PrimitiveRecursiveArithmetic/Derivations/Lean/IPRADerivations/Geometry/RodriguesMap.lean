import IPRADerivations.Core.PolynomialImplications

/-!
# The Rodrigues map in axis form (`euler_rodrigues_ipra`, `thm:results` (i))

Packet: `geometry/euler_rodrigues_ipra`. `Geometry/EulerRodrigues` treats the quaternion form
and `Geometry/EulerRodriguesUniversal` the universal axis identities. This module derives
`thm:results` (i) for the axis form

  `R(u, c, s) = c I + (1 − c) u uᵀ + s [u]×`,

as implications between integer polynomial equations (`Core/PolynomialImplications`); `u` is an
integer vector, `c`, `s` are integers, `n = u · u`.

* `det_axis`: for arbitrary `c`, `h`, `s`, `u`:
  `det (c I + h u uᵀ + s [u]×) = (c + h n)(c² + s² n)`, with no hypothesis;
* `row_orth_ij` (`R Rᵀ = I`) and `col_orth_ij` (`Rᵀ R = I`), `i ≤ j`: under `n = 1` and
  `c² + s² = 1` the rows and the columns of `R(u, c, s)` are orthonormal;
* `axis_fixed_x`, `axis_fixed_y`, `axis_fixed_z`: under `n = 1`, `R u = u`;
* `det_one`: under `n = 1` and `c² + s² = 1`, `det R = 1`.

So `R(u, c, s)` is a proper orthogonal matrix that fixes `u`. Each certificate is explicit:
`R Rᵀ − I = (H₂ + s² H₁) I + ((1 − c)² H₁ − H₂) u uᵀ` with `H₁ = n − 1`, `H₂ = c² + s² − 1`.

The converse parts of `thm:results` (rational certificates, the gap hypothesis, approximate
axes) and the composition law are not derived here.
-/

namespace LeanProofs.IPRA.Geometry.RodriguesMap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-- The rows of `c I + h u uᵀ + s [u]×`. -/
def rowA {k : ℕ} (c h s : ZExp k) (u : Vec3 k) : Vec3 k :=
  ⟨c + h * u.x * u.x, h * u.x * u.y - s * u.z, h * u.x * u.z + s * u.y⟩
def rowB {k : ℕ} (c h s : ZExp k) (u : Vec3 k) : Vec3 k :=
  ⟨h * u.y * u.x + s * u.z, c + h * u.y * u.y, h * u.y * u.z - s * u.x⟩
def rowC {k : ℕ} (c h s : ZExp k) (u : Vec3 k) : Vec3 k :=
  ⟨h * u.z * u.x - s * u.y, h * u.z * u.y + s * u.x, c + h * u.z * u.z⟩

/-- The columns of `c I + h u uᵀ + s [u]×`. -/
def colA {k : ℕ} (c h s : ZExp k) (u : Vec3 k) : Vec3 k :=
  ⟨(rowA c h s u).x, (rowB c h s u).x, (rowC c h s u).x⟩
def colB {k : ℕ} (c h s : ZExp k) (u : Vec3 k) : Vec3 k :=
  ⟨(rowA c h s u).y, (rowB c h s u).y, (rowC c h s u).y⟩
def colC {k : ℕ} (c h s : ZExp k) (u : Vec3 k) : Vec3 k :=
  ⟨(rowA c h s u).z, (rowB c h s u).z, (rowC c h s u).z⟩

/-! ## The determinant: `c, h, s, u` -/

section Det

local notation "c" => (ZExp.var 0 : ZExp 6)
local notation "hh" => (ZExp.var 1 : ZExp 6)
local notation "s" => (ZExp.var 2 : ZExp 6)
local notation "u" => (Vec3.mk (ZExp.var 3) (ZExp.var 4) (ZExp.var 5) : Vec3 6)

/-- `det (c I + h u uᵀ + s [u]×) = (c + h n)(c² + s² n)`. -/
theorem det_axis :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp [] (det3 (rowA c hh s u) (rowB c hh s u) (rowC c hh s u),
        (c + hh * dot u u) * (c ^ 2 + s ^ 2 * dot u u))) :=
  derive_imp _ _ (by ipra_poly R ρ h [rowA, rowB, rowC]; ring)

end Det

/-! ## The rotation `R(u, c, s)`: `c, s, u` -/

section Rotation

local notation "c" => (ZExp.var 0 : ZExp 5)
local notation "s" => (ZExp.var 1 : ZExp 5)
local notation "u" => (Vec3.mk (ZExp.var 2) (ZExp.var 3) (ZExp.var 4) : Vec3 5)

/-- The hypotheses `u · u = 1` and `c² + s² = 1`. -/
abbrev unitHyps : List (ZExp 5 × ZExp 5) := [(dot u u, 1), (c ^ 2 + s ^ 2, 1)]

/-- `R Rᵀ = I`, entry `(1, 1)`. -/
theorem row_orth_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (rowA c (1 - c) s u) (rowA c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (1 * ρ 1 ^ 2 + ρ 2 * ρ 2 * (1 - ρ 0) ^ 2) * h₁ + (1 - ρ 2 * ρ 2) * h₂)

/-- `R Rᵀ = I`, entry `(1, 2)`. -/
theorem row_orth_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (rowA c (1 - c) s u) (rowB c (1 - c) s u), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0 * ρ 1 ^ 2 + ρ 2 * ρ 3 * (1 - ρ 0) ^ 2) * h₁ + (0 - ρ 2 * ρ 3) * h₂)

/-- `R Rᵀ = I`, entry `(1, 3)`. -/
theorem row_orth_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (rowA c (1 - c) s u) (rowC c (1 - c) s u), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0 * ρ 1 ^ 2 + ρ 2 * ρ 4 * (1 - ρ 0) ^ 2) * h₁ + (0 - ρ 2 * ρ 4) * h₂)

/-- `R Rᵀ = I`, entry `(2, 2)`. -/
theorem row_orth_22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (rowB c (1 - c) s u) (rowB c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (1 * ρ 1 ^ 2 + ρ 3 * ρ 3 * (1 - ρ 0) ^ 2) * h₁ + (1 - ρ 3 * ρ 3) * h₂)

/-- `R Rᵀ = I`, entry `(2, 3)`. -/
theorem row_orth_23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (rowB c (1 - c) s u) (rowC c (1 - c) s u), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0 * ρ 1 ^ 2 + ρ 3 * ρ 4 * (1 - ρ 0) ^ 2) * h₁ + (0 - ρ 3 * ρ 4) * h₂)

/-- `R Rᵀ = I`, entry `(3, 3)`. -/
theorem row_orth_33 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (rowC c (1 - c) s u) (rowC c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (1 * ρ 1 ^ 2 + ρ 4 * ρ 4 * (1 - ρ 0) ^ 2) * h₁ + (1 - ρ 4 * ρ 4) * h₂)

/-- `Rᵀ R = I`, entry `(1, 1)`. -/
theorem col_orth_11 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (colA c (1 - c) s u) (colA c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (1 * ρ 1 ^ 2 + ρ 2 * ρ 2 * (1 - ρ 0) ^ 2) * h₁ + (1 - ρ 2 * ρ 2) * h₂)

/-- `Rᵀ R = I`, entry `(1, 2)`. -/
theorem col_orth_12 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (colA c (1 - c) s u) (colB c (1 - c) s u), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0 * ρ 1 ^ 2 + ρ 2 * ρ 3 * (1 - ρ 0) ^ 2) * h₁ + (0 - ρ 2 * ρ 3) * h₂)

/-- `Rᵀ R = I`, entry `(1, 3)`. -/
theorem col_orth_13 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (colA c (1 - c) s u) (colC c (1 - c) s u), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0 * ρ 1 ^ 2 + ρ 2 * ρ 4 * (1 - ρ 0) ^ 2) * h₁ + (0 - ρ 2 * ρ 4) * h₂)

/-- `Rᵀ R = I`, entry `(2, 2)`. -/
theorem col_orth_22 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (colB c (1 - c) s u) (colB c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (1 * ρ 1 ^ 2 + ρ 3 * ρ 3 * (1 - ρ 0) ^ 2) * h₁ + (1 - ρ 3 * ρ 3) * h₂)

/-- `Rᵀ R = I`, entry `(2, 3)`. -/
theorem col_orth_23 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (colB c (1 - c) s u) (colC c (1 - c) s u), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (0 * ρ 1 ^ 2 + ρ 3 * ρ 4 * (1 - ρ 0) ^ 2) * h₁ + (0 - ρ 3 * ρ 4) * h₂)

/-- `Rᵀ R = I`, entry `(3, 3)`. -/
theorem col_orth_33 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (dot (colC c (1 - c) s u) (colC c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC, colA, colB, colC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination (1 * ρ 1 ^ 2 + ρ 4 * ρ 4 * (1 - ρ 0) ^ 2) * h₁ + (1 - ρ 4 * ρ 4) * h₂)

/-- `R u = u`, component `x`. -/
theorem axis_fixed_x :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1)] (dot (rowA c (1 - c) s u) u, (u).x)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    linear_combination ((1 - ρ 0) * ρ 2) * h)

/-- `R u = u`, component `y`. -/
theorem axis_fixed_y :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1)] (dot (rowB c (1 - c) s u) u, (u).y)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    linear_combination ((1 - ρ 0) * ρ 3) * h)

/-- `R u = u`, component `z`. -/
theorem axis_fixed_z :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp [(dot u u, 1)] (dot (rowC c (1 - c) s u) u, (u).z)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    linear_combination ((1 - ρ 0) * ρ 4) * h)

/-- `det R(u, c, s) = 1`. -/
theorem det_one :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 5)
      (imp unitHyps (det3 (rowA c (1 - c) s u) (rowB c (1 - c) s u) (rowC c (1 - c) s u), 1)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h [rowA, rowB, rowC]
    obtain ⟨h₁, h₂⟩ := h
    linear_combination
      ((1 - ρ 0) + ρ 1 ^ 2 + (1 - ρ 0) * ((ρ 0 ^ 2 + ρ 1 ^ 2 - 1) +
        ρ 1 ^ 2 * (ρ 2 * ρ 2 + ρ 3 * ρ 3 + ρ 4 * ρ 4 - 1))) * h₁ + h₂)

end Rotation

end LeanProofs.IPRA.Geometry.RodriguesMap

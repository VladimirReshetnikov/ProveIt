import IPRADerivations.Geometry.HellyPlane

/-!
# Helly's theorem in space: five points, the dependence by signed volumes

Packet: `geometry/helly-ipra`, `helly.tex`, Theorem `thm:main` for `d = 3`, `n = 5`, with the dependence of
"The independent minor construction": "Set `c_j = det B`, `c_{k_ℓ} = −det(B with column ℓ replaced by A_{I,j})`"
for the matrix with columns `(x_j, 1)`. For five points `p j : Fin 3 → ZT n` of space:

* `vol`, `spaceZ`: `z_j = (−1)^j` times the determinant of the other four points (the signed volume of their
  tetrahedron, six times);
* `spaceZ_mass`, `spaceZ_moment₀`, `spaceZ_moment₁`, `spaceZ_moment₂`, `spaceZ_moment`: `∑ z_j = 0` and
  `∑ z_j p_j = 0` in each coordinate: an affine dependence;
* `helly_space_five`: for every `i`, every half-space `∑_k α_k x_k + γ ≥ 0` that contains the four points `p_j`,
  `j ≠ i`, contains the Radon point `(∑_j z_j⁺ p_j, ∑_j z_j⁺)` in homogeneous coordinates
  (`Geometry/HellyPlane.radon_halfspace`). With `p_j ∈ ⋂_{i ≠ j} C_i` this is Helly's theorem for five convex
  sets in space, each an intersection of half-spaces.

Not derived: the positivity of the mass (it holds when the five points are not coplanar) and the division by
it.
-/

namespace LeanProofs.IPRA.Geometry.HellySpace

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.RadonPartition (pp)
open LeanProofs.IPRA.Geometry.HellyPlane (radon_halfspace)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The determinant of the rows `b − a`, `c − a`, `d − a`. -/
def vol (a b c d : Fin 3 → ZT n) : ZT n :=
  (b 0 - a 0) * ((c 1 - a 1) * (d 2 - a 2) - (c 2 - a 2) * (d 1 - a 1)) -
    (b 1 - a 1) * ((c 0 - a 0) * (d 2 - a 2) - (c 2 - a 2) * (d 0 - a 0)) +
    (b 2 - a 2) * ((c 0 - a 0) * (d 1 - a 1) - (c 1 - a 1) * (d 0 - a 0))

/-- The dependence of five points of space by signed volumes. -/
def spaceZ (p : Fin 5 → Fin 3 → ZT n) : Fin 5 → ZT n :=
  ![vol (p 1) (p 2) (p 3) (p 4), -vol (p 0) (p 2) (p 3) (p 4), vol (p 0) (p 1) (p 3) (p 4),
    -vol (p 0) (p 1) (p 2) (p 4), vol (p 0) (p 1) (p 2) (p 3)]

local macro "vsimp" : tactic =>
  `(tactic| simp only [vol, ZT.toZ_neg, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul])

theorem spaceZ_mass (p : Fin 5 → Fin 3 → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin (spaceZ p)) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_five, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (vol (p 1) (p 2) (p 3) (p 4)) + ZT.toZ Γ (-vol (p 0) (p 2) (p 3) (p 4)) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 3) (p 4)) + ZT.toZ Γ (-vol (p 0) (p 1) (p 2) (p 4)) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 2) (p 3)) = 0
  vsimp
  ring

theorem spaceZ_moment₀ (p : Fin 5 → Fin 3 → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => spaceZ p j * p j 0) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_five, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (vol (p 1) (p 2) (p 3) (p 4) * p 0 0) + ZT.toZ Γ (-vol (p 0) (p 2) (p 3) (p 4) * p 1 0) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 3) (p 4) * p 2 0) + ZT.toZ Γ (-vol (p 0) (p 1) (p 2) (p 4) * p 3 0) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 2) (p 3) * p 4 0) = 0
  vsimp
  ring

theorem spaceZ_moment₁ (p : Fin 5 → Fin 3 → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => spaceZ p j * p j 1) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_five, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (vol (p 1) (p 2) (p 3) (p 4) * p 0 1) + ZT.toZ Γ (-vol (p 0) (p 2) (p 3) (p 4) * p 1 1) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 3) (p 4) * p 2 1) + ZT.toZ Γ (-vol (p 0) (p 1) (p 2) (p 4) * p 3 1) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 2) (p 3) * p 4 1) = 0
  vsimp
  ring

theorem spaceZ_moment₂ (p : Fin 5 → Fin 3 → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => spaceZ p j * p j 2) (ZT.natLit 0) := by
  apply ZT.derive
  rw [ZT.toZ_sumFin, Fin.sum_univ_five, ZT.toZ_natLit, Nat.cast_zero]
  show ZT.toZ Γ (vol (p 1) (p 2) (p 3) (p 4) * p 0 2) + ZT.toZ Γ (-vol (p 0) (p 2) (p 3) (p 4) * p 1 2) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 3) (p 4) * p 2 2) + ZT.toZ Γ (-vol (p 0) (p 1) (p 2) (p 4) * p 3 2) +
    ZT.toZ Γ (vol (p 0) (p 1) (p 2) (p 3) * p 4 2) = 0
  vsimp
  ring

/-- The dependence has zero moment in each coordinate. -/
theorem spaceZ_moment (p : Fin 5 → Fin 3 → ZT n) :
    ∀ k : Fin 3, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => spaceZ p j * p j k) (ZT.natLit 0)
  | 0 => spaceZ_moment₀ p
  | 1 => spaceZ_moment₁ p
  | 2 => spaceZ_moment₂ p

/-- Helly in space for five sets: a half-space containing the four points `p_j`, `j ≠ i`, contains the Radon
point of the five points. -/
theorem helly_space_five (p : Fin 5 → Fin 3 → ZT n) (α : Fin 3 → ZT n) (γ : ZT n) (i : Fin 5)
    (hL : ∀ j, j ≠ i → (Γ ⊢[PRAAx] zle (ZT.natLit 0) ((ZT.sumFin fun k => α k * p j k) + γ))) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0)
      ((ZT.sumFin fun k => α k * ZT.sumFin fun j => pp (spaceZ p j) * p j k) +
        γ * ZT.sumFin fun j => pp (spaceZ p j)) :=
  radon_halfspace (spaceZ p) (fun k j => p j k) α γ i (spaceZ_mass p) (spaceZ_moment p) hL

end LeanProofs.IPRA.Geometry.HellySpace

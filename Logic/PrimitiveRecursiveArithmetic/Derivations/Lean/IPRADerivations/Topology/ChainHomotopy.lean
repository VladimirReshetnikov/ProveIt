import IPRADerivations.Algebra.AdjugateInverse

/-!
# Certified chain maps and chain homotopies

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Theorem A04
(`thm:chain-homotopy`, "certified chain-homotopy invariance"): "For a cycle `z`, the commuting-square identity
gives `D'Fz = FDz = 0`. For a boundary `Dw`, it gives `FDw = D'Fw`, a boundary … If `Dz = 0`, the homotopy
equation reduces to `(F − G)z = D'Sz`, proving equality of the induced maps."

The identities are proved for matrices over any commutative ring (`cycle_map`, `boundary_map`,
`homotopy_cycle`, `homotopy_identity`) and as iPRA derivations for integer-term matrices of a common padded
dimension `N` (every chain space embedded in `ℤ^N`, the unused coordinates carrying zero blocks), with all
hypotheses as derived matrix equations:

* `ipra_cycle_map`: a chain map `D' F = F D` sends cycles to cycles;
* `ipra_boundary_map`: it sends the boundary `D w` to the boundary `D' (F w)`;
* `ipra_homotopy_cycle`: if `F − G = D'_{+} S + S_{−} D`, then on a cycle `F z − G z = D'_{+} (S z)`, a
  boundary, so `F` and `G` induce the same map on homology;
* `ipra_homotopy_identity`: for supplied homotopies `G F ≃ 1`, `G (F z) − z` is a boundary on every cycle
  ("Applying this to the two supplied homotopies yields inverse homology matrices").
-/

namespace LeanProofs.IPRA.Topology.ChainHomotopy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.AdjugateInverse (toZ_of_eqFm conjFin_elim)
open Matrix
open scoped Fm

/-! ## Matrix identities over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {N : ℕ}

theorem cycle_map {D D' F : Matrix (Fin N) (Fin N) R} (hF : D' * F = F * D) {z : Fin N → R}
    (hz : D *ᵥ z = 0) : D' *ᵥ (F *ᵥ z) = 0 := by
  rw [mulVec_mulVec, hF, ← mulVec_mulVec, hz, mulVec_zero]

theorem boundary_map {D D' F : Matrix (Fin N) (Fin N) R} (hF : D' * F = F * D) (w : Fin N → R) :
    F *ᵥ (D *ᵥ w) = D' *ᵥ (F *ᵥ w) := by
  rw [mulVec_mulVec, mulVec_mulVec, hF]

theorem homotopy_cycle {D Dp F G S Sm : Matrix (Fin N) (Fin N) R} (hH : F - G = Dp * S + Sm * D)
    {z : Fin N → R} (hz : D *ᵥ z = 0) : F *ᵥ z - G *ᵥ z = Dp *ᵥ (S *ᵥ z) := by
  rw [← sub_mulVec, hH, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hz, mulVec_zero, _root_.add_zero]

theorem homotopy_identity {D Dp F G S Sm : Matrix (Fin N) (Fin N) R} (hH : G * F - 1 = Dp * S + Sm * D)
    {z : Fin N → R} (hz : D *ᵥ z = 0) : G *ᵥ (F *ᵥ z) - z = Dp *ᵥ (S *ᵥ z) := by
  have h := homotopy_cycle hH hz
  rwa [one_mulVec, ← mulVec_mulVec] at h

end Ring

/-! ## The iPRA statements -/

variable {n N : ℕ} {Γ : List (Fm PTm n)}

/-- The zero vector. -/
def zv : Vec N n := fun _ => ZT.natLit 0

theorem vec_toZ_of_eqFm {u v : Vec N n} (h : Γ ⊢[PRAAx] Vec.eqFm u v) : Vec.toZ Γ u = Vec.toZ Γ v :=
  funext fun i => ZT.toZ_eq (conjFin_elim h i)

@[simp] theorem toZ_zv : Vec.toZ Γ (zv : Vec N n) = 0 := by
  funext i; simp [zv, Vec.toZ, ZT.toZ_natLit]

theorem ipra_cycle_map {D D' F : Mat N n} {z : Vec N n}
    (hF : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul D' F) (Mat.mul F D))
    (hz : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec D z) zv) :
    Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec D' (Mat.mulVec F z)) zv := by
  apply Vec.derive
  have h1 := toZ_of_eqFm hF
  have h2 := vec_toZ_of_eqFm hz
  simp only [Mat.toZ_mul, Mat.toZ_mulVec, toZ_zv] at h1 h2 ⊢
  exact cycle_map h1 h2

theorem ipra_boundary_map {D D' F : Mat N n} (w : Vec N n)
    (hF : Γ ⊢[PRAAx] Mat.eqFm (Mat.mul D' F) (Mat.mul F D)) :
    Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec F (Mat.mulVec D w)) (Mat.mulVec D' (Mat.mulVec F w)) := by
  apply Vec.derive
  have h1 := toZ_of_eqFm hF
  simp only [Mat.toZ_mul, Mat.toZ_mulVec] at h1 ⊢
  exact boundary_map h1 _

theorem ipra_homotopy_cycle {D Dp F G S Sm : Mat N n} {z : Vec N n}
    (hH : Γ ⊢[PRAAx] Mat.eqFm (Mat.sub F G) (Mat.add (Mat.mul Dp S) (Mat.mul Sm D)))
    (hz : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec D z) zv) :
    Γ ⊢[PRAAx] Vec.eqFm (Vec.sub (Mat.mulVec F z) (Mat.mulVec G z)) (Mat.mulVec Dp (Mat.mulVec S z)) := by
  apply Vec.derive
  have h1 := toZ_of_eqFm hH
  have h2 := vec_toZ_of_eqFm hz
  simp only [Mat.toZ_mul, Mat.toZ_mulVec, Mat.toZ_sub, Mat.toZ_add, Vec.toZ_sub, toZ_zv] at h1 h2 ⊢
  exact homotopy_cycle h1 h2

theorem ipra_homotopy_identity {D Dp F G S Sm : Mat N n} {z : Vec N n}
    (hH : Γ ⊢[PRAAx] Mat.eqFm (Mat.sub (Mat.mul G F) Mat.one) (Mat.add (Mat.mul Dp S) (Mat.mul Sm D)))
    (hz : Γ ⊢[PRAAx] Vec.eqFm (Mat.mulVec D z) zv) :
    Γ ⊢[PRAAx] Vec.eqFm (Vec.sub (Mat.mulVec G (Mat.mulVec F z)) z) (Mat.mulVec Dp (Mat.mulVec S z)) := by
  apply Vec.derive
  have h1 := toZ_of_eqFm hH
  have h2 := vec_toZ_of_eqFm hz
  simp only [Mat.toZ_mul, Mat.toZ_mulVec, Mat.toZ_sub, Mat.toZ_add, Mat.toZ_one, Vec.toZ_sub, toZ_zv]
    at h1 h2 ⊢
  exact homotopy_identity h1 h2

end LeanProofs.IPRA.Topology.ChainHomotopy

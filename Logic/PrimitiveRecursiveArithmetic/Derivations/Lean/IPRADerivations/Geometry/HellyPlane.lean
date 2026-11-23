import IPRADerivations.Geometry.RadonPartition

/-!
# Helly's theorem in the plane: the Radon point lies in every set of the family

Packet: `geometry/helly-ipra`, `helly.tex`, Theorem `thm:main` for `d = 2`, `n = 4`, in the form of the
paragraph after it: "If `p_T` belongs to every convex set `C_i` with `i ∈ T`, row `i` places `y` in `C_i`. Thus
(H) yields a single exhibited point of the full intersection", and of the opening example ("Each description
avoids two of the given vertices, so one of them avoids any specified vertex").

A convex set is an intersection of half-planes `α x + β y + γ ≥ 0`, so membership is stated for one half-plane
at a time. For points `(x_j, y_j)`, `j : Fin s`, an affine dependence `Z` (`∑ Z_j = 0`, `∑ Z_j x_j = 0`,
`∑ Z_j y_j = 0`) and its positive parts `pp (Z j)` of `Geometry/RadonPartition`, the Radon point is written in
homogeneous coordinates `(X, Y, M) = (∑ Z_j⁺ x_j, ∑ Z_j⁺ y_j, ∑ Z_j⁺)`, that is `y = (X / M, Y / M)`. As iPRA
derivations:

* `lin_sum`: `∑ a_j (α x_j + β y_j + γ) = α ∑ a_j x_j + β ∑ a_j y_j + γ ∑ a_j`;
* `weighted_nonneg`: a combination with nonnegative weights, zero weight at `i`, of values that are
  nonnegative away from `i`, is nonnegative;
* `radon_halfplane`: if a half-plane contains every point `p_j` with `j ≠ i`, then
  `α X + β Y + γ M ≥ 0`: it contains the Radon point. The row is chosen by the object-level disjunction
  `Z_i⁺ = 0 ∨ Z_i⁻ = 0`: the positive parts if `Z_i⁺ = 0`, and otherwise the negative parts, which have the
  same mass and moments;
* `helly_plane_four`: for four points of the plane, with the dependence by signed areas (`planeZ`): for every
  `i`, every half-plane that contains the three points `p_j`, `j ≠ i`, contains the Radon point. With
  `p_j ∈ ⋂_{i ≠ j} C_i` this is Helly's theorem for four convex sets, each an intersection of half-planes.

* `lin_sum_dim`, `radon_halfspace`: the same statement in every dimension `d`, for points with coordinates
  `x k j`, `k : Fin d`, and a half-space `∑_k α_k x_k + γ ≥ 0`: the step of the gluing in which Radon's lemma
  is applied to `d + 2` points.

Not derived: the positivity of the mass `M` (it holds when the dependence is nonzero, by
`Geometry/HellyCertificates.part_zero`; four collinear points need the dependence of `line_dependence`
instead), the division by `M`, and the gluing over the levels for more than four sets.
-/

namespace LeanProofs.IPRA.Geometry.HellyPlane

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.RadonPartition
open Syn
open scoped Fm

variable {n s : ℕ} {Γ : List (Fm PTm n)}

/-- `∑ a_j (α x_j + β y_j + γ) = α ∑ a_j x_j + β ∑ a_j y_j + γ ∑ a_j`. -/
theorem lin_sum {R : Type*} [CommRing R] (a x y : Fin s → R) (α β γ : R) :
    ∑ j, a j * (α * x j + β * y j + γ) = α * ∑ j, a j * x j + β * ∑ j, a j * y j + γ * ∑ j, a j := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Nonnegative weights with weight zero at `i`, and values nonnegative away from `i`. -/
theorem weighted_nonneg (a L : Fin s → ZT n) (i : Fin s)
    (ha : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (a j)) (hi : Γ ⊢[PRAAx] ZT.eq (a i) (ZT.natLit 0))
    (hL : ∀ j, j ≠ i → (Γ ⊢[PRAAx] zle (ZT.natLit 0) (L j))) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.sumFin fun j => a j * L j) := by
  have ei := ZT.toZ_eq hi
  simp only [ZT.toZ_natLit, Nat.cast_zero] at ei
  refine zle_of_comb (∑ j, if h : j = i then 0 else zsl (ha j) * zsl (hL j h)) ?_
    (nn_sum _ _ fun j _ => ?_)
  · simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = i
    · subst h
      rw [dif_pos rfl, ei, MulZeroClass.zero_mul]
    · rw [dif_neg h]
      simp only [zsl_def, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
  · by_cases h : j = i
    · rw [dif_pos h]
      exact nn_zero
    · rw [dif_neg h]
      exact nn_mul (nn_zsl _) (nn_zsl _)

/-- A half-plane containing every point other than `p_i` contains the Radon point `(X, Y, M)`. -/
theorem radon_halfplane (Z x y : Fin s → ZT n) (α β γ : ZT n) (i : Fin s)
    (hZ : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin Z) (ZT.natLit 0))
    (hx : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => Z j * x j) (ZT.natLit 0))
    (hy : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => Z j * y j) (ZT.natLit 0))
    (hL : ∀ j, j ≠ i → (Γ ⊢[PRAAx] zle (ZT.natLit 0) (α * x j + β * y j + γ))) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0)
      (α * (ZT.sumFin fun j => pp (Z j) * x j) + β * (ZT.sumFin fun j => pp (Z j) * y j) +
        γ * (ZT.sumFin fun j => pp (Z j))) := by
  refine .orE (parts_disjoint (Γ := Γ) (Z i)) ?_ ?_
  · -- `Z_i⁺ = 0`: the row of positive parts
    have w := weighted_nonneg (fun j => pp (Z j)) (fun j => α * x j + β * y j + γ) i
      (fun j => pp_nonneg (Z j)) Prf.hyp0 (fun j h => (hL j h).wk)
    have S := lin_sum (fun j => ZT.toZ _ (pp (Z j))) (fun j => ZT.toZ _ (x j)) (fun j => ZT.toZ _ (y j))
      (ZT.toZ (ZT.eq (pp (Z i)) (ZT.natLit 0) :: Γ) α) (ZT.toZ _ β) (ZT.toZ _ γ)
    beta_reduce at S
    refine zle_of_comb (zsl w) ?_ (nn_zsl _)
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
    exact S.symm
  · -- `Z_i⁻ = 0`: the row of negative parts, with the same mass and moments
    have w := weighted_nonneg (fun j => np (Z j)) (fun j => α * x j + β * y j + γ) i
      (fun j => np_nonneg (Z j)) Prf.hyp0 (fun j h => (hL j h).wk)
    have S := lin_sum (fun j => ZT.toZ _ (np (Z j))) (fun j => ZT.toZ _ (x j)) (fun j => ZT.toZ _ (y j))
      (ZT.toZ (ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) α) (ZT.toZ _ β) (ZT.toZ _ γ)
    beta_reduce at S
    have em := ZT.toZ_eq (parts_mass (Γ := ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) Z hZ.wk)
    have ex := ZT.toZ_eq (parts_moment (Γ := ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) Z x hx.wk)
    have ey := ZT.toZ_eq (parts_moment (Γ := ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) Z y hy.wk)
    simp only [ZT.toZ_sumFin, ZT.toZ_mul] at em ex ey
    refine zle_of_comb (zsl w) ?_ (nn_zsl _)
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
    rw [S, em, ex, ey]

/-- Helly in the plane for four sets: a half-plane containing the three points `p_j`, `j ≠ i`, contains the
Radon point of the four points. -/
theorem helly_plane_four (x y : Fin 4 → ZT n) (α β γ : ZT n) (i : Fin 4)
    (hL : ∀ j, j ≠ i → (Γ ⊢[PRAAx] zle (ZT.natLit 0) (α * x j + β * y j + γ))) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0)
      (α * (ZT.sumFin fun j => pp (planeZ x y j) * x j) + β * (ZT.sumFin fun j => pp (planeZ x y j) * y j) +
        γ * (ZT.sumFin fun j => pp (planeZ x y j))) :=
  radon_halfplane (planeZ x y) x y α β γ i (planeZ_mass x y) (planeZ_moment_x x y) (planeZ_moment_y x y) hL

/-! ## Any dimension -/

/-- `∑_j a_j (∑_k α_k x_{k j} + γ) = ∑_k α_k ∑_j a_j x_{k j} + γ ∑_j a_j`. -/
theorem lin_sum_dim {R : Type*} [CommRing R] {d : ℕ} (a : Fin s → R) (x : Fin d → Fin s → R) (α : Fin d → R)
    (γ : R) :
    ∑ j, a j * ((∑ k, α k * x k j) + γ) = (∑ k, α k * ∑ j, a j * x k j) + γ * ∑ j, a j := by
  have h1 : ∀ j, a j * ((∑ k, α k * x k j) + γ) = (∑ k, α k * (a j * x k j)) + γ * a j := fun j => by
    rw [_root_.mul_add, Finset.mul_sum, _root_.mul_comm (a j) γ]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]

/-- In dimension `d`: a half-space `∑_k α_k x_k + γ ≥ 0` containing every point other than `p_i` contains the
Radon point `(∑_j Z_j⁺ x_{k j})_k` with mass `∑_j Z_j⁺` of an affine dependence `Z`. -/
theorem radon_halfspace {d : ℕ} (Z : Fin s → ZT n) (x : Fin d → Fin s → ZT n) (α : Fin d → ZT n) (γ : ZT n)
    (i : Fin s) (hZ : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin Z) (ZT.natLit 0))
    (hx : ∀ k, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => Z j * x k j) (ZT.natLit 0))
    (hL : ∀ j, j ≠ i → (Γ ⊢[PRAAx] zle (ZT.natLit 0) ((ZT.sumFin fun k => α k * x k j) + γ))) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0)
      ((ZT.sumFin fun k => α k * ZT.sumFin fun j => pp (Z j) * x k j) + γ * ZT.sumFin fun j => pp (Z j)) := by
  refine .orE (parts_disjoint (Γ := Γ) (Z i)) ?_ ?_
  · have w := weighted_nonneg (fun j => pp (Z j)) (fun j => (ZT.sumFin fun k => α k * x k j) + γ) i
      (fun j => pp_nonneg (Z j)) Prf.hyp0 (fun j h => (hL j h).wk)
    have S := lin_sum_dim (fun j => ZT.toZ _ (pp (Z j))) (fun k j => ZT.toZ _ (x k j))
      (fun k => ZT.toZ (ZT.eq (pp (Z i)) (ZT.natLit 0) :: Γ) (α k)) (ZT.toZ _ γ)
    beta_reduce at S
    refine zle_of_comb (zsl w) ?_ (nn_zsl _)
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
    exact S.symm
  · have w := weighted_nonneg (fun j => np (Z j)) (fun j => (ZT.sumFin fun k => α k * x k j) + γ) i
      (fun j => np_nonneg (Z j)) Prf.hyp0 (fun j h => (hL j h).wk)
    have S := lin_sum_dim (fun j => ZT.toZ _ (np (Z j))) (fun k j => ZT.toZ _ (x k j))
      (fun k => ZT.toZ (ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) (α k)) (ZT.toZ _ γ)
    beta_reduce at S
    have em := ZT.toZ_eq (parts_mass (Γ := ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) Z hZ.wk)
    have ex : ∀ k, _ := fun k =>
      ZT.toZ_eq (parts_moment (Γ := ZT.eq (np (Z i)) (ZT.natLit 0) :: Γ) Z (x k) (hx k).wk)
    simp only [ZT.toZ_sumFin, ZT.toZ_mul] at em ex
    refine zle_of_comb (zsl w) ?_ (nn_zsl _)
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_natLit, Nat.cast_zero, sub_zero]
    rw [S, em]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [ex k]

end LeanProofs.IPRA.Geometry.HellyPlane

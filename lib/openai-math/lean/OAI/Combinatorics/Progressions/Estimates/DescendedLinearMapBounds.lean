import OAI.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight

namespace OAI

section

namespace Erdos3

open Module

variable {L M Z ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [AddCommGroup Z] [Module ℚ Z]
  [Fintype ι] [Fintype κ]

theorem descended_linear_map_coordinate_height
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (b : Basis ν ℚ Z)
    (π : L →ₗ[ℚ] M) (hπ : Function.Surjective π) (φ : M →ₗ[ℚ] Z)
    {Q H : ℕ} (hQ : 1 ≤ Q)
    (hproj : ∀ i j, RationalHeightLE (f.repr (π (e j)) i) Q)
    (hcomp : ∀ i j, RationalHeightLE (b.repr (φ (π (e j))) i) H) (i : ν) (j : κ) :
    RationalHeightLE (b.repr (φ (f j)) i)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) Q * H) ^ Fintype.card ι) := by
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_section e f π hπ hQ hproj
  have h := linearMap_coordinate_height e b (φ.comp π) (fun j i => hcomp i j)
    (σ (f j)) (fun k => hσH k j) i
  simpa only [LinearMap.comp_apply, hσ (f j)] using h

theorem descended_linear_map_coordinate_logHeight
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (b : Basis ν ℚ Z)
    (π : L →ₗ[ℚ] M) (hπ : Function.Surjective π) (φ : M →ₗ[ℚ] Z)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p)
    (hproj : ∀ i j, rationalLogHeight (f.repr (π (e j)) i) ≤ p)
    (hcomp : ∀ i j, rationalLogHeight (b.repr (φ (π (e j))) i) ≤ p) (i : ν) (j : κ) :
    rationalLogHeight (b.repr (φ (f j)) i) ≤ (p + 3) ^ 8 := by
  have h := descended_linear_map_coordinate_height e f b π hπ φ (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hproj i j))
    (fun i j => rationalHeightLE_ceil_exp (hcomp i j)) i j
  apply rationalLogHeight_le_of_height h
  have hb := embedding_coordinate_height_budget (Fintype.card ι) (Fintype.card κ)
    ⌈Real.exp p⌉₊ ⌈Real.exp p⌉₊ (by linarith : 0 ≤ p + 1)
    (hn.trans (by linarith)) (hd.trans (by linarith))
    (ceil_exp_le_exp_add_one hp) (ceil_exp_le_exp_add_one hp)
  simpa only [show p + 1 + 2 = p + 3 by ring] using hb

end Erdos3

end

end OAI

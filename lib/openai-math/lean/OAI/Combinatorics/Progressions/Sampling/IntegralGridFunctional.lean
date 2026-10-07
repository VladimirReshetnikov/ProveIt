import OAI.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials

namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

def coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) : Submodule ℤ L where
  carrier := {x | e.equivFun x ∈ scaledIntegerGrid B}
  zero_mem' := ⟨fun _ => 0, by ext i; simp⟩
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨w, hw⟩
    refine ⟨fun i => z i + w i, ?_⟩
    rw [map_add, hz, hw]
    ext i
    simp [mul_add]
  smul_mem' := by
    rintro n x ⟨z, hz⟩
    refine ⟨fun i => n * z i, ?_⟩
    rw [map_zsmul, hz]
    ext i
    simp only [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_mul]
    ring

theorem mem_coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) (x : L) :
    x ∈ coordinateGridModule e B ↔ e.equivFun x ∈ scaledIntegerGrid B := Iff.rfl

theorem scaled_basis_mem_coordinateGridModule (e : Basis ι ℚ L) (B : ℕ) (i : ι) :
    (B : ℚ) • e i ∈ coordinateGridModule e B := by
  classical
  refine ⟨fun j => if i = j then 1 else 0, ?_⟩
  ext j
  simp only [map_smul, Pi.smul_apply, Basis.equivFun_self, Int.cast_ite, Int.cast_one,
    Int.cast_zero]

theorem coordinateGrid_bracket_divisible (e : Basis ι ℚ L) (B D : ℕ)
    (hc : ∀ i j k, ∃ n : ℤ, (B : ℚ) * lieStructureConstants e i j k = (D : ℚ) * n)
    {a b : L} (ha : a ∈ coordinateGridModule e B) (hb : b ∈ coordinateGridModule e B) :
    ∃ z ∈ coordinateGridModule e B, ⁅a, b⁆ = (D : ℚ) • z := by
  classical
  choose c hc using hc
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  let w : ι → ℤ := fun k => ∑ ij : ι × ι, c ij.1 ij.2 k * u ij.1 * v ij.2
  let z : L := e.equivFun.symm ((B : ℚ) • fun k => (w k : ℚ))
  have hz : e.equivFun z = (B : ℚ) • fun k => (w k : ℚ) := e.equivFun.apply_symm_apply _
  refine ⟨z, ⟨w, hz⟩, ?_⟩
  apply e.equivFun.injective
  ext k
  rw [map_smul, hz]
  change e.repr ⁅a, b⁆ k = (D : ℚ) * ((B : ℚ) * (w k : ℚ))
  rw [lie_coordinate_formula]
  have hu' (i : ι) : e.repr a i = (B : ℚ) * (u i : ℚ) := congrFun hu i
  have hv' (i : ι) : e.repr b i = (B : ℚ) * (v i : ℚ) := congrFun hv i
  simp only [w, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hu', hv']
  calc
    _ = (B : ℚ) * (((B : ℚ) * lieStructureConstants e ij.1 ij.2 k) * u ij.1 * v ij.2) := by ring
    _ = (D : ℚ) * ((B : ℚ) * ((c ij.1 ij.2 k : ℚ) * u ij.1 * v ij.2)) := by
      rw [hc]
      ring

end Erdos3

end

section

namespace Erdos3

open Module

theorem coordinateGridModule_map_of_basis {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M)
    (hφ : ∀ i, ∃ j, φ (b i) = c j) (B : ℕ) {x : L}
    (hx : x ∈ coordinateGridModule b B) : φ x ∈ coordinateGridModule c B := by
  classical
  obtain ⟨z, hz⟩ := hx
  rw [← b.sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro i _
  obtain ⟨j, hj⟩ := hφ i
  have hi : b.repr x i = (B : ℚ) * (z i : ℚ) := congrFun hz i
  rw [map_smul, hi, hj]
  have hm := (coordinateGridModule c B).smul_mem (z i) (scaled_basis_mem_coordinateGridModule c B j)
  simpa only [← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm] using hm

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem linearFunctional_coordinate_height {ι L : Type*} [Fintype ι]
    [AddCommGroup L] [Module ℚ L] (b : Basis ι ℚ L) (η : L →ₗ[ℚ] ℚ)
    {H K : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (x : L) (hx : ∀ i, RationalHeightLE (b.repr x i) K) :
    RationalHeightLE (η x) ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  classical
  have heq : η x = ∑ i, b.repr x i * η (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [heq]
  exact rationalHeightLE_sum _ (fun i => (hx i).mul (hη i))

theorem coordinateGrid_functional_integral {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] (b : Basis ι ℚ L) (η : L →ₗ[ℚ] ℚ)
    (l B : ℕ) (hdiv : l ∣ B)
    (hη : ∀ i, ∃ n : ℤ, (l : ℚ) * η (b i) = n)
    {x : L} (hx : x ∈ coordinateGridModule b B) : ∃ n : ℤ, η x = n := by
  classical
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨z, hz⟩ := hx
  choose n hn using hη
  refine ⟨∑ i, (k : ℤ) * z i * n i, ?_⟩
  rw [← b.sum_repr x, map_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : b.repr x i = (B : ℚ) * (z i : ℚ) := congrFun hz i
  rw [map_smul, smul_eq_mul, hi, hk, Nat.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    _ = (k : ℚ) * (z i : ℚ) * ((l : ℚ) * η (b i)) := by ring
    _ = _ := by rw [hn i]

end Erdos3

end

end OAI

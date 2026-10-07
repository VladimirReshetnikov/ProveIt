import OAI.Combinatorics.Progressions.Geometry.LinearMapCoordinateHeight

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem range_kernel_projection (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ)
    (hS : A * S = 1) :
    LinearMap.range (1 - S * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  have hzero : A * (1 - S * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hS, Matrix.one_mul, sub_self]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change A *ᵥ ((1 - S * A) *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  · intro hy
    change A *ᵥ y = 0 at hy
    refine ⟨y, ?_⟩
    change (1 - S * A) *ᵥ y = y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, sub_zero]

def rationalKernelHeight (r H : ℕ) : ℕ :=
  2 * (r + 1) * (rationalSolveHeight r H * H) ^ r

omit [DecidableEq ι] in
theorem exists_bounded_kernel_projection (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ P : Matrix κ κ ℚ,
      LinearMap.range P.mulVecLin = LinearMap.ker A.mulVecLin ∧
      ∀ i j, RationalHeightLE (P i j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, rows, _, hsurj, hker⟩ := exists_independent_defining_rows A
  let R := A.submatrix rows id
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section R hsurj hH
    (fun i j => hA (rows i) j)
  refine ⟨r, hr, 1 - S * R, (range_kernel_projection R S hS).trans hker, ?_⟩
  intro i j
  have hI : RationalHeightLE ((1 : Matrix κ κ ℚ) i j) 1 := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
    · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  have hprod := rationalHeightLE_matrix_mul S R hSH (fun i j => hA (rows i) j) i j
  have hout := hI.sub hprod
  simpa only [Matrix.sub_apply, Fintype.card_fin, rationalKernelHeight, mul_one,
    mul_assoc] using hout

omit [DecidableEq ι] in

theorem exists_bounded_rational_kernel_family (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ v : Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)) → (κ → ℚ),
        LinearIndependent ℚ v ∧ Submodule.span ℚ (Set.range v) = LinearMap.ker A.mulVecLin ∧
        ∀ i j, RationalHeightLE (v i j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, P, hP, hPH⟩ := exists_bounded_kernel_projection A hH hA
  have hspan : Submodule.span ℚ (Set.range P.col) = LinearMap.ker A.mulVecLin := by
    rw [← Matrix.range_mulVecLin, hP]
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range P.col)
  rw [hspan] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨r, hr, v, hli, hvspan, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := hv i
  rw [← hk]
  exact hPH j k

omit [DecidableEq ι] in

theorem exists_bounded_rational_kernel_basis (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)))
        ℚ (LinearMap.ker A.mulVecLin),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, v, hli, hspan, hv⟩ := exists_bounded_rational_kernel_family A hH hA
  refine ⟨r, hr, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), ?_⟩
  intro i j
  simpa only [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply] using hv i j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype κ]

noncomputable def finiteCombination (v : κ → V) : (κ → K) →ₗ[K] V :=
  (Pi.basisFun K κ).constr K v

theorem finiteCombination_apply (v : κ → V) (x : κ → K) :
    finiteCombination v x = ∑ i, x i • v i := by
  classical
  rw [finiteCombination, Basis.constr_apply_fintype]
  rfl

theorem finiteCombination_basis (v : κ → V) (i : κ) :
    finiteCombination v (Pi.basisFun K κ i) = v i :=
  Basis.constr_basis (Pi.basisFun K κ) K v i

theorem finiteCombination_range (v : κ → V) :
    LinearMap.range (finiteCombination (K := K) v) = Submodule.span K (Set.range v) :=
  Basis.constr_range (Pi.basisFun K κ) K

theorem finiteCombination_kernel_image (v : κ → V) (P : V →ₗ[K] W) :
    (LinearMap.ker (P.comp (finiteCombination v))).map (finiteCombination v) =
      Submodule.span K (Set.range v) ⊓ LinearMap.ker P := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(finiteCombination_range v).le ⟨x, rfl⟩, hx⟩
  · rintro ⟨hy, hP⟩
    obtain ⟨x, rfl⟩ := (finiteCombination_range v).ge hy
    exact ⟨x, hP, rfl⟩

section Rational

variable {V W ι η κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype κ] [Fintype η]

theorem finiteCombination_constraint_kernel (f : Basis η ℚ W) (P : V →ₗ[ℚ] W)
    (v : κ → V) :
    LinearMap.ker (Matrix.mulVecLin (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i)) =
      LinearMap.ker (P.comp (finiteCombination v)) := by
  classical
  ext x
  have he : (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i) *ᵥ x =
      f.equivFun (P (finiteCombination v x)) := by
    ext i
    simp only [finiteCombination_apply, map_sum, map_smul, Basis.equivFun_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  change (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i) *ᵥ x = 0 ↔
    P (finiteCombination v x) = 0
  rw [he, LinearEquiv.map_eq_zero_iff]

theorem exists_bounded_span_kernel_generators (e : Basis ι ℚ V) (f : Basis η ℚ W)
    (P : V →ₗ[ℚ] W) (v : κ → V) {H B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H)
    (hPv : ∀ i j, RationalHeightLE (f.repr (P (v i)) j) B) :
    ∃ r : ℕ, r ≤ Fintype.card η ∧ ∃ z : κ → V,
      Submodule.span ℚ (Set.range z) = Submodule.span ℚ (Set.range v) ⊓ LinearMap.ker P ∧
      ∀ i j, RationalHeightLE (e.repr (z i) j)
        ((Fintype.card κ + 1) * (rationalKernelHeight r B * H) ^ Fintype.card κ) := by
  classical
  let A : Matrix η κ ℚ := fun i j => f.repr (P (v j)) i
  obtain ⟨r, hr, Q, hQ, hQH⟩ := exists_bounded_kernel_projection A hB (fun i j => hPv j i)
  refine ⟨r, hr, fun i => finiteCombination v (Q.col i), ?_, ?_⟩
  · rw [← finiteCombination_kernel_image v P, ← finiteCombination_constraint_kernel f P v,
      ← hQ, Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro i j
    exact linearMap_coordinate_height (Pi.basisFun ℚ κ) e (finiteCombination v)
      (by intro a b; rw [finiteCombination_basis]; exact hv a b)
      (Q.col i) (fun a => hQH a i) j

end Rational
end Erdos3

end

end OAI

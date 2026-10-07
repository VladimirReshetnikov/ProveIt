import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Fourier.BohrNiltestBudget

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def shiftPolynomialLayer (k : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈
    F.layer ((k + Finsupp.weight (fun _ : σ => 1) α + 1) / 2)}
  zero_mem' := by intro α; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp α)

theorem shiftPolynomialLayer_antitone : Antitone (F.shiftPolynomialLayer (σ := σ)) := by
  intro i j hij p hp α
  exact F.antitone (by omega) (hp α)

theorem adapted_mem_shiftPolynomialLayer_one
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    p.val ∈ F.shiftPolynomialLayer 1 := by
  intro α
  by_cases hα : Finsupp.weight (fun _ : σ => 1) α = 0
  · simp only [hα, Nat.add_zero, Nat.reduceAdd, Nat.reduceDiv, F.one_eq_top,
      Submodule.mem_top]
  · exact F.antitone (by omega) (p.property α)

theorem monomial_mem_shiftPolynomialLayer (k : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ F.layer ((k + Finsupp.weight (fun _ : σ => 1) α + 1) / 2)) :
    monomial (R := ℚ) α x ∈ F.shiftPolynomialLayer k := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp only [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm h), Submodule.zero_mem]

theorem shiftPolynomialLayer_lie {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftPolynomialLayer i) (hq : q ∈ F.shiftPolynomialLayer j) :
    ⁅p, q⁆ ∈ F.shiftPolynomialLayer (i + j) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, sum_lie_sum]
  apply (F.shiftPolynomialLayer (i + j)).sum_mem
  intro α _
  apply (F.shiftPolynomialLayer (i + j)).sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_shiftPolynomialLayer
  apply F.antitone _ (F.lie_mem (hp α) (hq β))
  rw [map_add]
  omega

theorem directionalDerivative_mem_shiftPolynomialLayer [Fintype σ] (h : σ → ℚ)
    {k : ℕ} {p : VectorPolynomial σ ℚ L} (hp : p ∈ F.shiftPolynomialLayer k) :
    directionalDerivative h p ∈ F.shiftPolynomialLayer (k + 1) := by
  intro α
  rw [coefficients_directionalDerivative]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  have hi := hp (α + Finsupp.single i 1)
  simpa only [map_add, Finsupp.weight_single, one_smul, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using hi

theorem shiftPolynomialLayer_terminal :
    F.shiftPolynomialLayer (σ := σ) (2 * s + 1) = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply coefficients.injective
  ext α
  have h := F.antitone (show s + 1 ≤
    (2 * s + 1 + Finsupp.weight (fun _ : σ => 1) α + 1) / 2 by omega) (hp α)
  simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_commute (i j : σ) (p : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L
        ((MvPolynomial.pderiv j).toLinearMap.rTensor L p) =
      (MvPolynomial.pderiv j).toLinearMap.rTensor L
        ((MvPolynomial.pderiv i).toLinearMap.rTensor L p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  apply coefficients.injective
  ext α
  simp only [coefficients_pderiv, Finsupp.add_apply,
    Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne (Ne.symm hij),
    Nat.add_zero, smul_smul]
  congr 1
  · ring
  · congr 1
    abel

theorem directionalDerivative_commute [Fintype σ]
    (h k : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivative h (directionalDerivative k p) =
      directionalDerivative k (directionalDerivative h p) := by
  simp only [directionalDerivative, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_commute, mul_comm]

noncomputable def directionalLieDerivation [Fintype σ] (h : σ → ℚ) :
    LieDerivation ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) where
  toLinearMap := directionalDerivative h
  leibniz' p q := by
    rw [directionalDerivative_lie, sub_eq_add_neg, ← lie_skew]
    exact add_comm _ _

@[simp] theorem directionalLieDerivation_apply [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalLieDerivation h p = directionalDerivative h p := rfl

noncomputable def directionalDerivationLinear [Fintype σ] :
    (σ → ℚ) →ₗ[ℚ] LieDerivation ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) where
  toFun := directionalLieDerivation
  map_add' h k := by
    apply LieDerivation.ext
    intro p
    exact directionalDerivative_direction_add h k p
  map_smul' r h := by
    apply LieDerivation.ext
    intro p
    exact directionalDerivative_direction_smul r h p

@[simp] theorem directionalDerivationLinear_apply [Fintype σ]
    (h : σ → ℚ) (p : VectorPolynomial σ ℚ L) :
    directionalDerivationLinear h p = directionalDerivative h p := rfl

theorem directionalLieDerivation_lie_eq_zero [Fintype σ] (h k : σ → ℚ) :
    ⁅directionalLieDerivation (L := L) h, directionalLieDerivation (L := L) k⁆ = 0 := by
  apply LieDerivation.ext
  intro p
  simp only [LieDerivation.lie_apply, directionalLieDerivation_apply,
    directionalDerivative_commute h k p, sub_self, LieDerivation.zero_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedShiftDerivation (h : σ → ℚ) :
    LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))
      (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toLinearMap := F.adaptedDirectionalDerivative h
  leibniz' p q := by
    rw [F.adaptedDirectionalDerivative_lie, sub_eq_add_neg, ← lie_skew]
    exact add_comm _ _

@[simp] theorem adaptedShiftDerivation_coe (h : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    (F.adaptedShiftDerivation h p : VectorPolynomial σ ℚ L) =
      directionalDerivative h p.val := rfl

noncomputable def adaptedShiftDerivationLinear :
    (σ → ℚ) →ₗ[ℚ] LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : σ => 1))
      (F.adaptedLieSubalgebra (fun _ : σ => 1)) where
  toFun := F.adaptedShiftDerivation
  map_add' h k := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    exact directionalDerivative_direction_add h k p.val
  map_smul' r h := by
    apply LieDerivation.ext
    intro p
    apply Subtype.ext
    exact directionalDerivative_direction_smul r h p.val

theorem adaptedShiftDerivation_commute (h k : σ → ℚ)
    (p : F.adaptedLieSubalgebra (fun _ : σ => 1)) :
    F.adaptedShiftDerivation h (F.adaptedShiftDerivation k p) =
      F.adaptedShiftDerivation k (F.adaptedShiftDerivation h p) := by
  apply Subtype.ext
  exact directionalDerivative_commute h k p.val

omit [Fintype σ] in
noncomputable def adaptedShiftAction (d : ℕ) :
    RationalTorus.Algebra d →ₗ⁅ℚ⁆
      LieDerivation ℚ (F.adaptedLieSubalgebra (fun _ : Fin d => 1))
        (F.adaptedLieSubalgebra (fun _ : Fin d => 1)) where
  toLinearMap := F.adaptedShiftDerivationLinear
  map_lie' {h k} := by
    apply LieDerivation.ext
    intro p
    rw [RationalTorus.lie_eq_zero]
    change (F.adaptedShiftDerivationLinear (0 : Fin d → ℚ)) p = _
    rw [map_zero, LieDerivation.zero_apply, LieDerivation.lie_apply]
    exact (sub_eq_zero.mpr (F.adaptedShiftDerivation_commute h k p)).symm

omit [Fintype σ] in
@[simp] theorem adaptedShiftAction_coe (d : ℕ) (h : RationalTorus.Algebra d)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    (F.adaptedShiftAction d h p : VectorPolynomial (Fin d) ℚ L) =
      directionalDerivative h p.val := rfl

omit [Fintype σ] in

abbrev PolynomialShiftAlgebra (d : ℕ) :=
  LieAlgebra.SemiDirectSum (F.adaptedLieSubalgebra (fun _ : Fin d => 1))
    (RationalTorus.Algebra d) (F.adaptedShiftAction d)

omit [Fintype σ] in
theorem polynomialShift_bracket (d : ℕ) (x y : F.PolynomialShiftAlgebra d) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + F.adaptedDirectionalDerivative x.right y.left -
      F.adaptedDirectionalDerivative y.right x.left, 0⟩ := rfl

omit [Fintype σ] in
theorem polynomialShift_direction_bracket (d : ℕ) (h : RationalTorus.Algebra d)
    (p : F.adaptedLieSubalgebra (fun _ : Fin d => 1)) :
    ⁅(⟨0, h⟩ : F.PolynomialShiftAlgebra d), (⟨p, 0⟩ : F.PolynomialShiftAlgebra d)⁆ =
      ⟨F.adaptedDirectionalDerivative h p, 0⟩ := by
  rw [F.polynomialShift_bracket]
  simp only [zero_lie, zero_add, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s)

include b hF hω in
theorem polynomialShift_finiteDimensional (d : ℕ) :
    FiniteDimensional ℚ (F.PolynomialShiftAlgebra d) := by
  let w : Fin d → ℕ := fun _ => 1
  let : Finite (AdaptedBasisIndex w ω) := adaptedBasisIndex_finite w ω s (by simp [w]) hω
  let : FiniteDimensional ℚ (F.adaptedLieSubalgebra w) :=
    (F.adaptedMonomialBasis b ω hF w).finiteDimensional_of_finite
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).toLinearMap
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).injective

include b hF hω in
theorem polynomialShift_finrank_le (d : ℕ) :
    finrank ℚ (F.PolynomialShiftAlgebra d) ≤
      Fintype.card ι * (s + 1) * (d + 1) ^ s + d := by
  let w : Fin d → ℕ := fun _ => 1
  let : Fintype (AdaptedBasisIndex w ω) :=
    adaptedBasisIndexFintype w ω s (by simp [w]) hω
  let : FiniteDimensional ℚ (F.adaptedLieSubalgebra w) :=
    (F.adaptedMonomialBasis b ω hF w).finiteDimensional_of_finite
  let : FiniteDimensional ℚ (RationalTorus.Algebra d) :=
    (RationalTorus.basis d).finiteDimensional_of_finite
  rw [(LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction d)).finrank_eq,
    Module.finrank_prod, finrank_eq_card_basis (F.adaptedMonomialBasis b ω hF w),
    finrank_eq_card_basis (RationalTorus.basis d), Fintype.card_fin]
  exact Nat.add_le_add_right
    (by simpa only [Fintype.card_fin] using adaptedBasisIndex_card_le w ω s (by simp [w]) hω) d

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialShiftLayer (d k : ℕ) : Submodule ℚ (F.PolynomialShiftAlgebra d) where
  carrier := {x | x.left.val ∈ F.shiftPolynomialLayer k ∧
    x.right ∈ (RationalTorus.filtration d).layer k}
  zero_mem' := ⟨(F.shiftPolynomialLayer k).zero_mem, Submodule.zero_mem _⟩
  add_mem' hx hy := ⟨(F.shiftPolynomialLayer k).add_mem hx.1 hy.1,
    Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' c _ hx := ⟨(F.shiftPolynomialLayer k).smul_mem c hx.1,
    Submodule.smul_mem _ c hx.2⟩

theorem polynomialShiftLayer_antitone (d : ℕ) : Antitone (F.polynomialShiftLayer d) := by
  intro i j hij x hx
  exact ⟨F.shiftPolynomialLayer_antitone hij hx.1,
    (RationalTorus.filtration d).antitone hij hx.2⟩

theorem polynomialShiftLayer_one (d : ℕ) : F.polynomialShiftLayer d 1 = ⊤ := by
  apply top_unique
  intro x _
  exact ⟨F.adapted_mem_shiftPolynomialLayer_one x.left,
    by rw [(RationalTorus.filtration d).one_eq_top]; trivial⟩

theorem shift_directionalDerivative_mem (d : ℕ) {i j : ℕ}
    {h : RationalTorus.Algebra d} {p : VectorPolynomial (Fin d) ℚ L}
    (hh : h ∈ (RationalTorus.filtration d).layer i) (hp : p ∈ F.shiftPolynomialLayer j) :
    directionalDerivative h p ∈ F.shiftPolynomialLayer (i + j) := by
  by_cases hi : i ≤ 1
  · exact F.shiftPolynomialLayer_antitone (by omega)
      (F.directionalDerivative_mem_shiftPolynomialLayer h hp)
  · have hz : h = 0 := by
      simpa only [RationalTorus.filtration, hi, ite_false, Submodule.mem_bot] using hh
    rw [hz]
    change directionalDerivative (0 : Fin d → ℚ) p ∈ _
    simp only [directionalDerivative, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      LinearMap.zero_apply, Submodule.zero_mem]

theorem polynomialShiftLayer_lie (d : ℕ) {i j : ℕ} {x y : F.PolynomialShiftAlgebra d}
    (hx : x ∈ F.polynomialShiftLayer d i) (hy : y ∈ F.polynomialShiftLayer d j) :
    ⁅x, y⁆ ∈ F.polynomialShiftLayer d (i + j) := by
  constructor
  · change ⁅x.left.val, y.left.val⁆ + directionalDerivative x.right y.left.val -
      directionalDerivative y.right x.left.val ∈ F.shiftPolynomialLayer (i + j)
    apply (F.shiftPolynomialLayer (i + j)).sub_mem
    · exact (F.shiftPolynomialLayer (i + j)).add_mem
        (F.shiftPolynomialLayer_lie hx.1 hy.1) (F.shift_directionalDerivative_mem d hx.2 hy.1)
    · simpa only [Nat.add_comm] using F.shift_directionalDerivative_mem d hy.2 hx.1
  · exact Submodule.zero_mem _

theorem polynomialShiftLayer_terminal (d : ℕ) :
    F.polynomialShiftLayer d (max 1 (2 * s) + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply LieAlgebra.SemiDirectSum.ext
  · apply Subtype.ext
    change (x.left : VectorPolynomial (Fin d) ℚ L) = 0
    have h := F.shiftPolynomialLayer_antitone (show 2 * s + 1 ≤ max 1 (2 * s) + 1 by omega) hx.1
    simpa only [F.shiftPolynomialLayer_terminal, Submodule.mem_bot] using h
  · change x.right = 0
    have hi : ¬max 1 (2 * s) + 1 ≤ 1 := by omega
    simpa only [RationalTorus.filtration, hi, ite_false, Submodule.mem_bot] using hx.2

noncomputable def polynomialShiftFiltration (d : ℕ) :
    NilpotentLieFiltration (F.PolynomialShiftAlgebra d) (max 1 (2 * s)) where
  layer := F.polynomialShiftLayer d
  antitone := F.polynomialShiftLayer_antitone d
  one_eq_top := F.polynomialShiftLayer_one d
  lie_mem := F.polynomialShiftLayer_lie d
  terminal := F.polynomialShiftLayer_terminal d

theorem polynomialShift_lowerCentralSeries_eq_bot (d : ℕ) :
    LieModule.lowerCentralSeries ℚ (F.PolynomialShiftAlgebra d)
      (F.PolynomialShiftAlgebra d) (max 1 (2 * s)) = ⊥ :=
  (F.polynomialShiftFiltration d).lowerCentralSeries_eq_bot

abbrev PolynomialShiftGroup (d : ℕ) := (F.polynomialShiftFiltration d).Group

theorem polynomialShiftGroup_nilpotencyClass_le (d : ℕ) :
    _root_.Group.nilpotencyClass (F.PolynomialShiftGroup d) ≤ max 1 (2 * s) :=
  (F.polynomialShiftFiltration d).nilpotencyClass_le

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def polynomialShiftBasis (t : ℕ) :
    Basis (AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) ℚ (F.PolynomialShiftAlgebra t) :=
  ((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod (RationalTorus.basis t)).map
    (LieAlgebra.SemiDirectSum.toProdl (F.adaptedShiftAction t)).symm

theorem polynomialShiftBasis_repr_inl (t : ℕ) (x : F.PolynomialShiftAlgebra t)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    (F.polynomialShiftBasis b ω hF t).repr x (.inl z) =
      b.repr (coefficients x.left.val z.val.1) z.val.2 := by
  change (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).repr x.left z = _
  exact F.adaptedMonomialBasis_repr b ω hF (fun _ : Fin t => 1) x.left z

theorem polynomialShiftBasis_repr_inr (t : ℕ) (x : F.PolynomialShiftAlgebra t) (i : Fin t) :
    (F.polynomialShiftBasis b ω hF t).repr x (.inr i) = x.right i := by
  change (RationalTorus.basis t).repr x.right i = x.right i
  rfl

theorem polynomialShiftBasis_inl_left (t : ℕ)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    ((F.polynomialShiftBasis b ω hF t) (.inl z)).left =
      F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) z := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inl z)).1 = _
  exact Basis.prod_apply_inl_fst _ _ z

theorem polynomialShiftBasis_inl_right (t : ℕ)
    (z : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    ((F.polynomialShiftBasis b ω hF t) (.inl z)).right = 0 := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inl z)).2 = _
  exact Basis.prod_apply_inl_snd _ _ z

theorem polynomialShiftBasis_inr_left (t : ℕ) (i : Fin t) :
    ((F.polynomialShiftBasis b ω hF t) (.inr i)).left = 0 := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inr i)).1 = _
  exact Basis.prod_apply_inr_fst _ _ i

theorem polynomialShiftBasis_inr_right (t : ℕ) (i : Fin t) :
    ((F.polynomialShiftBasis b ω hF t) (.inr i)).right = RationalTorus.basis t i := by
  change (((F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1)).prod
    (RationalTorus.basis t)) (.inr i)).2 = _
  exact Basis.prod_apply_inr_snd _ _ i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficients_torusDerivative {t : ℕ} (i : Fin t)
    (p : VectorPolynomial (Fin t) ℚ L) (α : Fin t →₀ ℕ) :
    coefficients (directionalDerivative (RationalTorus.basis t i) p) α =
      (α i + 1 : ℚ) • coefficients p (α + Finsupp.single i 1) := by
  have hdir (j : Fin t) : (RationalTorus.basis t i) j = if i = j then 1 else 0 := by
    rw [← RationalTorus.basis_repr t (RationalTorus.basis t i) j,
      (RationalTorus.basis t).repr_self, Finsupp.single_apply]
  change coefficients (directionalDerivative (fun j : Fin t => (RationalTorus.basis t i) j) p) α = _
  rw [coefficients_directionalDerivative]
  simp_rw [hdir]
  simp

theorem torusDerivative_monomial_height {ι : Type*} (b : Basis ι ℚ L)
    {s t : ℕ} (β : Fin t →₀ ℕ) (hβ : Finsupp.weight (fun _ : Fin t => 1) β ≤ s)
    (i : Fin t) (j : ι) (α : Fin t →₀ ℕ) (k : ι) :
    RationalHeightLE (b.repr (coefficients
      (directionalDerivative (RationalTorus.basis t i) (monomial (R := ℚ) β (b j))) α) k) (s + 1) := by
  classical
  rw [coefficients_torusDerivative, coefficients_monomial]
  by_cases he : β = α + Finsupp.single i 1
  · rw [he, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply, b.repr_self]
    have hi := (Finsupp.le_weight (fun _ : Fin t => 1) (s := i) (by norm_num) β).trans hβ
    rw [he, Finsupp.add_apply, Finsupp.single_eq_same] at hi
    have hn : RationalHeightLE ((α i + 1 : ℕ) : ℚ) (s + 1) := by
      constructor
      · simpa only [Rat.num_natCast, Int.natAbs_natCast] using hi.trans (Nat.le_succ s)
      · simp only [Rat.den_natCast]
        omega
    by_cases hj : j = k
    · subst k
      simpa only [Finsupp.single_eq_same, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using hn
    · rw [Finsupp.single_eq_of_ne (Ne.symm hj), smul_zero]
      exact rationalHeightLE_zero (by omega)
  · rw [Finsupp.single_eq_of_ne (Ne.symm he), smul_zero, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (by omega)

end VectorPolynomial

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem polynomialShiftBasis_inl (t : ℕ) (i : AdaptedBasisIndex (fun _ : Fin t => 1) ω) :
    F.polynomialShiftBasis b ω hF t (.inl i) =
      LieAlgebra.SemiDirectSum.inl (F.adaptedShiftAction t)
        (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) i) := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact F.polynomialShiftBasis_inl_left b ω hF t i
  · exact F.polynomialShiftBasis_inl_right b ω hF t i

theorem polynomialShiftBasis_inr (t : ℕ) (i : Fin t) :
    F.polynomialShiftBasis b ω hF t (.inr i) =
      LieAlgebra.SemiDirectSum.inr (F.adaptedShiftAction t) (RationalTorus.basis t i) := by
  apply LieAlgebra.SemiDirectSum.ext
  · exact F.polynomialShiftBasis_inr_left b ω hF t i
  · exact F.polynomialShiftBasis_inr_right b ω hF t i

theorem polynomialShiftBasis_mixed_height (hω : ∀ i, ω i ≤ s) (t : ℕ) (i : Fin t)
    (j : AdaptedBasisIndex (fun _ : Fin t => 1) ω)
    (k : AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE ((F.polynomialShiftBasis b ω hF t).repr
      ⁅F.polynomialShiftBasis b ω hF t (.inr i), F.polynomialShiftBasis b ω hF t (.inl j)⁆ k) (s + 1) := by
  rw [F.polynomialShiftBasis_inr, F.polynomialShiftBasis_inl]
  rw [LieAlgebra.SemiDirectSum.inr_eq_mk, LieAlgebra.SemiDirectSum.inl_eq_mk,
    F.polynomialShift_direction_bracket]
  rcases k with k | k
  · rw [F.polynomialShiftBasis_repr_inl]
    change RationalHeightLE (b.repr (coefficients
      (directionalDerivative (RationalTorus.basis t i)
        (F.adaptedMonomialBasis b ω hF (fun _ : Fin t => 1) j).val) k.val.1) k.val.2) _
    rw [F.adaptedMonomialBasis_coe]
    exact torusDerivative_monomial_height b j.val.1 (j.property.trans (hω j.val.2)) i j.val.2 k.val.1 k.val.2
  · rw [F.polynomialShiftBasis_repr_inr]
    exact rationalHeightLE_zero (by omega)

theorem polynomialShiftBasis_structure_height (hω : ∀ i, ω i ≤ s) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) (t : ℕ)
    (i j k : AdaptedBasisIndex (fun _ : Fin t => 1) ω ⊕ Fin t) :
    RationalHeightLE (lieStructureConstants (F.polynomialShiftBasis b ω hF t) i j k) (max H (s + 1)) := by
  change RationalHeightLE ((F.polynomialShiftBasis b ω hF t).repr
    ⁅F.polynomialShiftBasis b ω hF t i, F.polynomialShiftBasis b ω hF t j⁆ k) _
  rcases i with i | i <;> rcases j with j | j
  · rw [F.polynomialShiftBasis_inl, F.polynomialShiftBasis_inl,
      ← (LieAlgebra.SemiDirectSum.inl (F.adaptedShiftAction t)).map_lie]
    rcases k with k | k
    · rw [F.polynomialShiftBasis_repr_inl]
      simp only [LieAlgebra.SemiDirectSum.inl_eq_mk]
      simpa only [F.adaptedMonomialBasis_repr] using
        (F.adaptedMonomialBasis_bracket_height b ω hF (fun _ : Fin t => 1) hH hc i j k).mono
          (Nat.le_max_left H (s + 1))
    · rw [F.polynomialShiftBasis_repr_inr]
      exact rationalHeightLE_zero (hH.trans (Nat.le_max_left _ _))
  · rw [← lie_skew, map_neg, Finsupp.neg_apply]
    exact ((F.polynomialShiftBasis_mixed_height b ω hF hω t j i k).mono (Nat.le_max_right _ _)).neg
  · exact (F.polynomialShiftBasis_mixed_height b ω hF hω t i j k).mono (Nat.le_max_right _ _)
  · rw [F.polynomialShiftBasis_inr, F.polynomialShiftBasis_inr,
      ← (LieAlgebra.SemiDirectSum.inr (F.adaptedShiftAction t)).map_lie,
      RationalTorus.lie_eq_zero, map_zero, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (hH.trans (Nat.le_max_left _ _))

end NilpotentLieFiltration
end Erdos3

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.RealOrderedChartPatch

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eval₂_substitute (f : σ → MvPolynomial τ R) (x : τ → S)
    (p : VectorPolynomial σ R V) :
    eval₂ x (substitute f p) = eval₂ (fun i => MvPolynomial.aeval x (f i)) p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
      simp only [substitute_tmul, eval₂_tmul]
      rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

theorem polynomialOrbitSubstitute_realEval {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) (x : τ → ℝ) :
    F.polynomialOrbitRealEval v x (F.polynomialOrbitSubstitute f hf p) =
      F.polynomialOrbitRealEval w (fun i => MvPolynomial.aeval x (f i)) p := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_substitute f x p.log

theorem polynomialOrbitRealEval_constant (w : σ → ℕ) (a : F.Group) (x : σ → ℝ) :
    F.polynomialOrbitRealEval w x (F.constantPolynomialOrbit w a) = a := by
  apply NilpotentLieBCHGroup.ext
  change eval₂ x (monomial 0 a.coord) = a.coord
  rw [eval₂_monomial, Finsupp.prod_zero_index, one_smul]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_adapted_coordinate_degree (e : Basis ι ℚ L) (omega : ι → ℕ)
    (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
    {w : σ → ℕ} (p : F.realification.PolynomialOrbit w) (j : ι) :
    coordinate ((e.baseChange ℝ).coord j).toAddMonoidHom p.log ∈
      weightedSupportLE w (omega j) := by
  rw [mem_weightedSupportLE_iff, scalar_weightedDegree_le_iff]
  intro α hα
  rw [coeff_coordinate]
  change (e.baseChange ℝ).repr (coefficients p.log α) j = 0
  have hm := (F.realification.adapted_iff_coefficients w p.log).mp p.adapted α
  change coefficients p.log α ∈ (F.realLayer (Finsupp.weight w α)).toSubmodule at hm
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _), (e.baseChange ℝ).mem_span_image] at hm
  by_contra h
  exact (not_le_of_gt hα) (hm (Finsupp.mem_support_iff.mpr h))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

include hlayer

theorem real_scaled_adapted_basis_mem (B : ℝ) (j : Fin d) :
    B • (e.baseChange ℝ) j ∈ F.realification.layer (omega j) := by
  change B • (e.baseChange ℝ) j ∈ (F.realLayer (omega j)).toSubmodule
  rw [F.realLayer_eq_span_basis e _ _ (hlayer _)]
  exact Submodule.smul_mem _ B (Submodule.subset_span ⟨j, by simp, rfl⟩)

noncomputable def orderedSlotFactor (B : ℝ) (i j : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) := by
  classical
  exact if h : j.val < i.val then
    polynomialOrbitOfLog
      (monomial (Finsupp.single (Sum.inr (⟨j.val, h⟩ : Fin i.val)) 1)
        (B • (e.baseChange ℝ) j)) (by
      apply (F.realification.mem_adaptedSubmodule _ _).mp
      apply F.realification.monomial_mem_adaptedSubmodule
      simpa only [Finsupp.weight_single, one_smul, patchVariableWeight,
        Sum.elim_inr, earlierSlot, Fin.eta] using
        F.real_scaled_adapted_basis_mem e omega hlayer B j)
  else 1

theorem orderedSlotFactor_realEval (B : ℝ) (i j : Fin d)
    (u : σ → ℝ) (v : Fin d → ℝ) :
    F.realification.polynomialOrbitRealEval (patchVariableWeight omega i)
      (Sum.elim u (fun k => v (earlierSlot i k)))
      (F.orderedSlotFactor e omega hlayer B i j) =
      (⟨(if j.val < i.val then B * v j else 0) • (e.baseChange ℝ) j⟩ :
        F.realification.Group) := by
  classical
  by_cases h : j.val < i.val
  · apply NilpotentLieBCHGroup.ext
    simp only [orderedSlotFactor, dite_eq_left h, polynomialOrbitRealEval_coord,
      polynomialOrbitOfLog_log, eval₂_monomial, pow_zero, Finsupp.prod_single_index,
      pow_one, Sum.elim_inr, earlierSlot, Fin.eta, ite_eq_left h, smul_smul]
    rw [mul_comm]
  · simp only [orderedSlotFactor, dite_eq_right h, map_one, ite_eq_right h, zero_smul]
    rfl

noncomputable def orderedSlotOrbit (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (i : Fin d) :
    F.realification.PolynomialOrbit (patchVariableWeight (σ := σ) omega i) :=
  F.realification.constantPolynomialOrbit _ a *
    F.realification.polynomialOrbitSubstitute
      (w := fun _ : σ => 1) (v := patchVariableWeight omega i)
      (fun x => (MvPolynomial.X (Sum.inl x) : MvPolynomial (σ ⊕ Fin i.val) ℚ))
      (by
        intro x
        simpa only [patchVariableWeight, Sum.elim_inl] using
          (weightedSupportLE_X (R := ℚ) (patchVariableWeight (σ := σ) omega i) (Sum.inl x))) p *
    ((List.finRange d).map (F.orderedSlotFactor e omega hlayer B i)).prod

theorem orderedSlotOrbit_realEval (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (i : Fin d)
    (u : σ → ℝ) (v : Fin d → ℝ) :
    F.realification.polynomialOrbitRealEval (patchVariableWeight omega i)
      (Sum.elim u (fun k => v (earlierSlot i k)))
      (F.orderedSlotOrbit e omega hlayer B a p i) =
      a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p *
        realOrderedBasisProduct (e.baseChange ℝ) F.realification.lowerCentralSeries_eq_bot
          (fun j => if j.val < i.val then B * v j else 0) := by
  classical
  simp only [orderedSlotOrbit, map_mul, polynomialOrbitRealEval_constant,
    map_list_prod, List.map_map, Function.comp_def, orderedSlotFactor_realEval]
  rw [F.realification.polynomialOrbitSubstitute_realEval]
  simp only [MvPolynomial.aeval_X, Sum.elim_inl]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

include hlayers hP

theorem real_ofCoordinates_adapted :
    F.realification.Adapted v (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) := by
  classical
  apply (F.realification.adapted_iff_coefficients v _).mpr
  intro α
  change coefficients (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) α ∈
    (F.realLayer (Finsupp.weight v α)).toSubmodule
  rw [coefficients_ofCoordinates, F.realLayer_eq_span_basis b _ _ (hlayers _)]
  apply Submodule.sum_mem
  intro i _
  by_cases hα : Finsupp.weight v α ≤ ω i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hα, rfl⟩)
  · have hc : (P i).coeff α = 0 := by
      by_contra hne
      exact hα (hP i (MvPolynomial.mem_support_iff.mpr hne))
    rw [hc, zero_smul]
    exact Submodule.zero_mem _

noncomputable def realCoordinatePolynomialOrbit : F.realification.PolynomialOrbit v :=
  polynomialOrbitOfLog (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)
    (F.real_ofCoordinates_adapted b ω hlayers v P hP)

@[simp] theorem realCoordinatePolynomialOrbit_log :
    (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log =
      ofCoordinates (R := ℚ) (b.baseChange ℝ) P := rfl

theorem realCoordinatePolynomialOrbit_coefficients (α : σ →₀ ℕ) :
    coefficients (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log α =
      ∑ i, (P i).coeff α • (b.baseChange ℝ) i :=
  coefficients_ofCoordinates (b.baseChange ℝ) P α

@[simp] theorem realCoordinatePolynomialOrbit_coordinate (i : ι) :
    coordinate ((b.baseChange ℝ).coord i).toAddMonoidHom
      (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log = P i :=
  coordinate_ofCoordinates (b.baseChange ℝ) P i

theorem realCoordinatePolynomialOrbit_eval_coordinates (u : σ → ℝ) (i : ι) :
    (b.baseChange ℝ).repr
      (F.realification.polynomialOrbitRealEval v u
        (F.realCoordinatePolynomialOrbit b ω hlayers v P hP)).coord i =
      MvPolynomial.eval u (P i) := by
  change (b.baseChange ℝ).coord i
    (eval₂ u (F.realCoordinatePolynomialOrbit b ω hlayers v P hP).log) = _
  rw [coordinate_eval₂, realCoordinatePolynomialOrbit_coordinate]

theorem exists_real_coordinate_polynomialOrbit :
    ∃ p : F.realification.PolynomialOrbit v,
      p.log = ofCoordinates (R := ℚ) (b.baseChange ℝ) P ∧
      ∀ u : σ → ℝ, ∀ i, (b.baseChange ℝ).repr
        (F.realification.polynomialOrbitRealEval v u p).coord i =
          MvPolynomial.eval u (P i) :=
  ⟨F.realCoordinatePolynomialOrbit b ω hlayers v P hP, rfl,
    F.realCoordinatePolynomialOrbit_eval_coordinates b ω hlayers v P hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))

theorem orderedSlotOrbit_coordinate (he : IsCentralLieBasis e) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (i : Fin d) (u : σ → ℝ) (v : Fin d → ℝ) :
    MvPolynomial.eval (Sum.elim u (fun k => v (earlierSlot i k)))
      (coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
        (F.orderedSlotOrbit e omega hlayer B a p i).log) =
      (e.baseChange ℝ).repr
        ((a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p) *
          realOrderedBasisPrefixProduct (e.baseChange ℝ)
            F.realification.lowerCentralSeries_eq_bot i.val (fun j => B * v j)).coord i := by
  rw [← coordinate_eval₂]
  change (e.baseChange ℝ).repr
    (F.realification.polynomialOrbitRealEval _ _
      (F.orderedSlotOrbit e omega hlayer B a p i)).coord i = _
  rw [F.orderedSlotOrbit_realEval,
    he.real_baseChange.mul_realOrderedBasisProduct_coordinate,
    ite_eq_right (lt_irrefl i.val), add_zero]
  have hp : realOrderedBasisPrefixProduct (e.baseChange ℝ)
      F.realification.lowerCentralSeries_eq_bot i.val
      (fun j => if j.val < i.val then B * v j else 0) =
      realOrderedBasisPrefixProduct (e.baseChange ℝ)
        F.realification.lowerCentralSeries_eq_bot i.val (fun j => B * v j) := by
    apply realOrderedBasisPrefixProduct_congr
    intro j hj
    exact ite_eq_left hj
  rw [hp]

noncomputable def orderedPolynomialSlots (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) : PolynomialSlots σ d omega where
  center i := MvPolynomial.C (-1 / B) *
    coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
      (F.orderedSlotOrbit e omega hlayer B a p i).log
  degree i := by
    simpa only [zero_add] using weightedSupportLE_mul
      (weightedSupportLE_C (patchVariableWeight omega i) 0 (-1 / B))
      (F.real_adapted_coordinate_degree e omega hlayer
        (F.orderedSlotOrbit e omega hlayer B a p i) i)

theorem orderedPolynomialSlots_slots (he : IsCentralLieBasis e) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (u : σ → ℝ) :
    (F.orderedPolynomialSlots e omega hlayer B a p).slots u =
      realOrderedSlots (e.baseChange ℝ) F.realification.lowerCentralSeries_eq_bot B
        (a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p) := by
  apply TriangularSlots.ext
  intro v i
  change MvPolynomial.aeval (Sum.elim u (fun k => v (earlierSlot i k)))
    (MvPolynomial.C (-1 / B) * coordinate ((e.baseChange ℝ).coord i).toAddMonoidHom
      (F.orderedSlotOrbit e omega hlayer B a p i).log) = _
  rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_eq_eval,
    F.orderedSlotOrbit_coordinate e omega hlayer he]
  dsimp only [realOrderedSlots]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, div_eq_mul_inv]
  ring

noncomputable def orderedPolynomialPatch (hpos : ∀ i, 1 ≤ omega i)
    (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega) (B : ℝ)
    (a : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (Phi : PatchKernel d) : PolynomialPatch σ s d where
  weight := omega
  weight_pos := hpos
  weight_le := hmax
  weight_mono := hmono
  form := F.orderedPolynomialSlots e omega hlayer B a p
  kernel := Phi

theorem orderedPolynomialPatch_value (he : IsCentralLieBasis e)
    (hpos : ∀ i, 1 ≤ omega i) (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega)
    (B : ℝ) (a : F.realification.Group)
    (p : F.realification.PolynomialOrbit (fun _ : σ => 1)) (Phi : PatchKernel d)
    (u : σ → ℝ) :
    (F.orderedPolynomialPatch e omega hlayer hpos hmax hmono B a p Phi).value u =
      (realOrderedSlots (e.baseChange ℝ) F.realification.lowerCentralSeries_eq_bot B
        (a * F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p)).patchValue Phi := by
  change ((F.orderedPolynomialSlots e omega hlayer B a p).slots u).patchValue Phi = _
  rw [F.orderedPolynomialSlots_slots e omega hlayer he]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realExtendedSymbolMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolMap w)

theorem realSymbolOfPolynomial_realAdaptedPolynomialMap
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realAdaptedPolynomialMap w x) =
      F.realExtendedSymbolMap w x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
    ext z
    rw [F.realSymbolOfPolynomial_coordinate, F.realAdaptedPolynomialMap_coefficient_tmul]
    change (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
        (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p) z
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul, F.polynomialSymbolBasis_repr_map]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolMap :
    F.realification.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w where
  toLinearMap := (F.realSymbolOfPolynomial b ω hlayers w).comp
    (F.realification.adaptedLieSubalgebra w).incl.toLinearMap
  map_lie' {p q} := by
    change F.realSymbolOfPolynomial b ω hlayers w (↑⁅p, q⁆) =
      ⁅F.realSymbolOfPolynomial b ω hlayers w p, F.realSymbolOfPolynomial b ω hlayers w q⁆
    obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers p
    obtain ⟨y, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hlayers q
    rw [← (F.realAdaptedPolynomialTensor w).map_lie x y]
    simp only [F.realAdaptedPolynomialTensor_coe, F.realSymbolOfPolynomial_realAdaptedPolynomialMap]
    exact (F.realExtendedSymbolMap w).map_lie x y

@[simp] theorem realPolynomialSymbolMap_apply (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = F.realSymbolOfPolynomial b ω hlayers w p := rfl

@[simp] theorem realPolynomialSymbolMap_representative (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolMap b ω hlayers w (F.realAdaptedSymbolRepresentative b ω hlayers w x) = x := by
  rw [F.realPolynomialSymbolMap_apply, F.realAdaptedSymbolRepresentative_coe,
    F.realSymbolOfPolynomial_representative]

theorem realPolynomialSymbolMap_surjective :
    Function.Surjective (F.realPolynomialSymbolMap b ω hlayers w) :=
  fun x => ⟨F.realAdaptedSymbolRepresentative b ω hlayers w x,
    F.realPolynomialSymbolMap_representative b ω hlayers w x⟩

theorem realPolynomialSymbolMap_eq_zero_iff (p : F.realification.adaptedLieSubalgebra w) :
    F.realPolynomialSymbolMap b ω hlayers w p = 0 ↔
      F.realification.polynomialSymbolMap w p = 0 := by
  rw [F.realPolynomialSymbolMap_apply, F.realSymbolOfPolynomial_eq_zero_iff,
    F.realification.polynomialSymbolMap_eq_zero_iff]

noncomputable def realPolynomialSymbolHom :
    (F.realification.adaptedPolynomialFiltration w).Group →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolMap b ω hlayers w)

@[simp] theorem realPolynomialSymbolHom_coord
    (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    (F.realPolynomialSymbolHom b ω hlayers w g).coord =
      F.realPolynomialSymbolMap b ω hlayers w g.coord := rfl

noncomputable def realPolynomialSymbolLift (g : F.RealPolynomialSymbolGroup w) :
    (F.realification.adaptedPolynomialFiltration w).Group :=
  ⟨F.realAdaptedSymbolRepresentative b ω hlayers w g.coord⟩

@[simp] theorem realPolynomialSymbolHom_lift (g : F.RealPolynomialSymbolGroup w) :
    F.realPolynomialSymbolHom b ω hlayers w (F.realPolynomialSymbolLift b ω hlayers w g) = g := by
  apply NilpotentLieBCHGroup.ext
  simp only [F.realPolynomialSymbolHom_coord, realPolynomialSymbolLift,
    F.realPolynomialSymbolMap_representative]

theorem realPolynomialSymbolHom_surjective :
    Function.Surjective (F.realPolynomialSymbolHom b ω hlayers w) :=
  fun g => ⟨F.realPolynomialSymbolLift b ω hlayers w g,
    F.realPolynomialSymbolHom_lift b ω hlayers w g⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis (Fin d) ℚ L) (omega : Fin d → ℕ)
  (hlayer : ∀ k, F.layer k = Submodule.span ℚ (e '' {j | k ≤ omega j}))
  (Λ : Subgroup F.Group) [MetricSpace (F.realification.Group ⧸ Λ.map realificationHom)]

theorem orderedPolynomialPatch_chart_value (he : IsCentralLieBasis e)
    (hpos : ∀ i, 1 ≤ omega i) (hmax : ∀ i, omega i ≤ s) (hmono : Monotone omega)
    (B : ℕ) (hB : 0 < B) (hgrid : bchSubgroupCoordinates e Λ = scaledIntegerGrid B)
    (z : F.realification.Group) (p : F.realification.PolynomialOrbit (fun _ : σ => 1))
    (phi : OpenPartialHomeomorph (Fin d → ℝ) (F.realification.Group ⧸ Λ.map realificationHom))
    (hphi : ∀ v, phi v = QuotientGroup.mk
      (z * (⟨(e.baseChange ℝ).equivFun.symm v⟩ : F.realification.Group)))
    (f : (F.realification.Group ⧸ Λ.map realificationHom) → ℝ)
    (hf : Function.support f ⊆ phi.target) (Phi : PatchKernel d)
    (hPhi : ∀ v, Phi.value v = chartCoordinateKernel phi f ((B : ℝ) • v)) (u : σ → ℝ) :
    (F.orderedPolynomialPatch e omega hlayer hpos hmax hmono (B : ℝ) z⁻¹ p Phi).value u =
      f (QuotientGroup.mk (F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p)) := by
  rw [F.orderedPolynomialPatch_value e omega hlayer he]
  exact he.realOrderedSlots_patchValue F.lowerCentralSeries_eq_bot Λ B hB hgrid z
    (F.realification.polynomialOrbitRealEval (fun _ : σ => 1) u p) phi hphi f hf Phi hPhi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open MvPolynomial

theorem weightedHomogeneousComponent_mem_weightedSupportLE
    {σ R : Type*} [CommRing R] (v : σ → ℕ) (d : ℕ) (P : MvPolynomial σ R) :
    weightedHomogeneousComponent v d P ∈ weightedSupportLE v d := by
  intro α hα
  exact (weightedHomogeneousComponent_isWeightedHomogeneous d P
    (MvPolynomial.mem_support_iff.mp hα)).le

namespace NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ k, F.layer k = Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (v : σ → ℕ) (P : ι → MvPolynomial σ ℝ)

private theorem repr_coefficients_ofCoordinates (α : σ →₀ ℕ) (i : ι) :
    (b.baseChange ℝ).repr (coefficients
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) α) i = (P i).coeff α := by
  exact congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := ℚ) (b.baseChange ℝ) P i)

theorem realSymbolRepresentative_ofCoordinates :
    F.realSymbolRepresentative b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v
        (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)) =
      ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i)) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply (b.baseChange ℝ).repr.injective
  ext i
  by_cases h : Finsupp.weight v α = ω i
  · have hc := F.realSymbolRepresentative_coefficient b ω hlayers v
      (F.realSymbolOfPolynomial b ω hlayers v
        (ofCoordinates (R := ℚ) (b.baseChange ℝ) P)) ⟨(α, i), h⟩
    have hs := F.realSymbolOfPolynomial_coordinate b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) ⟨(α, i), h⟩
    rw [hc, hs, repr_coefficients_ofCoordinates, repr_coefficients_ofCoordinates,
      coeff_weightedHomogeneousComponent, ite_eq_left h]
  · rw [F.realSymbolRepresentative_coefficient_of_ne b ω hlayers v _ α i h,
      repr_coefficients_ofCoordinates, coeff_weightedHomogeneousComponent, ite_eq_right h]

theorem realSymbolOfPolynomial_ofCoordinates_top :
    F.realSymbolOfPolynomial b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ) P) =
    F.realSymbolOfPolynomial b ω hlayers v
      (ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i))) := by
  rw [← F.realSymbolRepresentative_ofCoordinates b ω hlayers v P]
  exact (F.realSymbolOfPolynomial_representative b ω hlayers v _).symm

variable (hP : ∀ i, P i ∈ weightedSupportLE v (ω i))

theorem realCoordinatePolynomialOrbit_symbol_top :
    F.realPolynomialSymbolHom b ω hlayers v
      (F.realification.polynomialOrbitCoordinates v
        (F.realCoordinatePolynomialOrbit b ω hlayers v P hP)) =
    F.realPolynomialSymbolHom b ω hlayers v
      (F.realification.polynomialOrbitCoordinates v
        (F.realCoordinatePolynomialOrbit b ω hlayers v
          (fun i => weightedHomogeneousComponent v (ω i) (P i))
          (fun i => weightedHomogeneousComponent_mem_weightedSupportLE v (ω i) (P i)))) := by
  apply NilpotentLieBCHGroup.ext
  simp only [realPolynomialSymbolHom_coord, realPolynomialSymbolMap_apply,
    polynomialOrbitCoordinates_log, realCoordinatePolynomialOrbit_log]
  exact F.realSymbolOfPolynomial_ofCoordinates_top b ω hlayers v P

theorem realCoordinatePolynomialOrbit_symbol_eq_of_top
    (Q : ι → MvPolynomial σ ℝ)
    (hQ : ∀ i, Q i ∈ weightedSupportLE v (ω i))
    (hPQ : ∀ i, weightedHomogeneousComponent v (ω i) (P i) = Q i) :
    F.realPolynomialSymbolHom b ω hlayers v
      (F.realification.polynomialOrbitCoordinates v
        (F.realCoordinatePolynomialOrbit b ω hlayers v P hP)) =
    F.realPolynomialSymbolHom b ω hlayers v
      (F.realification.polynomialOrbitCoordinates v
        (F.realCoordinatePolynomialOrbit b ω hlayers v Q hQ)) := by
  apply NilpotentLieBCHGroup.ext
  simp only [realPolynomialSymbolHom_coord, realPolynomialSymbolMap_apply,
    polynomialOrbitCoordinates_log, realCoordinatePolynomialOrbit_log]
  rw [F.realSymbolOfPolynomial_ofCoordinates_top b ω hlayers v P, funext hPQ]

theorem realCoordinatePolynomialOrbit_symbol_representative :
    F.realSymbolRepresentative b ω hlayers v
      (F.realPolynomialSymbolHom b ω hlayers v
        (F.realification.polynomialOrbitCoordinates v
          (F.realCoordinatePolynomialOrbit b ω hlayers v P hP))).coord =
      ofCoordinates (R := ℚ) (b.baseChange ℝ)
        (fun i => weightedHomogeneousComponent v (ω i) (P i)) := by
  simp only [realPolynomialSymbolHom_coord, realPolynomialSymbolMap_apply,
    polynomialOrbitCoordinates_log, realCoordinatePolynomialOrbit_log]
  rw [realSymbolRepresentative_ofCoordinates]

end NilpotentLieFiltration

end Erdos3

end

end OAI

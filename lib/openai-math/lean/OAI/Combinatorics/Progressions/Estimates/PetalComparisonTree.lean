/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Equalizer
import OAI.Combinatorics.Progressions.Estimates.FourBalancedRelations
import OAI.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
import OAI.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates
import OAI.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realificationLieSubalgebra (K : LieSubalgebra ℚ L) :
    LieSubalgebra ℝ (ℝ ⊗[ℚ] L) := (realificationLieHom K.incl).range

theorem realificationLieSubalgebra_toSubmodule (K : LieSubalgebra ℚ L) :
    (realificationLieSubalgebra K).toSubmodule = K.toSubmodule.baseChange ℝ := rfl

theorem realificationLieHom_incl_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationLieHom K.incl) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) K.incl.toLinearMap
    (fun _ _ h => Subtype.ext h)

theorem rational_inclusion_mem_realificationLieSubalgebra_iff (K : LieSubalgebra ℚ L) (a : L) :
    rationalLieInclusion a ∈ realificationLieSubalgebra K ↔ a ∈ K :=
  one_tmul_mem_real_baseChange_iff K.toSubmodule a

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationSubgroup (K : LieSubalgebra ℚ L) :
    Subgroup (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :=
  realLieSubgroup (realificationLieSubalgebra K)

theorem realificationMap_incl_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl) := by
  intro x y hxy
  apply ext
  apply realificationLieHom_incl_injective K
  exact congrArg coord hxy

theorem realificationMap_incl_mem (K : LieSubalgebra ℚ L)
    (x : NilpotentLieBCHGroup (ℝ ⊗[ℚ] K) s
      (realification_lowerCentralSeries_eq_bot (lie_subalgebra_lowerCentralSeries_eq_bot hnil K))) :
    realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl x ∈
      realificationSubgroup (hnil := hnil) K :=
  ⟨x.coord, rfl⟩

theorem realificationMap_incl_range (K : LieSubalgebra ℚ L) :
    (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl).range =
      realificationSubgroup (hnil := hnil) K := by
  ext g
  change (∃ x, realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
    (hM := hnil) K.incl x = g) ↔ ∃ y, realificationLieHom K.incl y = g.coord
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.coord, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y⟩, ext hy⟩

theorem realification_subgroup_comap_incl (K : LieSubalgebra ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) :
    (Γ.map realificationHom).comap
      (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl) =
      (Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)).map
        (realificationHom (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hx
    have hgK : g.coord ∈ K := by
      apply (rational_inclusion_mem_realificationLieSubalgebra_iff K g.coord).mp
      have hm := realificationMap_incl_mem (hnil := hnil) K x
      rw [← heq] at hm
      exact hm
    let a : NilpotentLieBCHGroup K s (lie_subalgebra_lowerCentralSeries_eq_bot hnil K) :=
      ⟨⟨g.coord, hgK⟩⟩
    have hag : map K.incl a = g := ext rfl
    refine Subgroup.mem_map.mpr ⟨a, ?_, ?_⟩
    · change map K.incl a ∈ Γ
      rwa [hag]
    · apply realificationMap_incl_injective (hnil := hnil) K
      rw [realificationMap_realificationHom, hag]
      exact heq
  · rintro ⟨a, ha, rfl⟩
    change realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl (realificationHom a) ∈ Γ.map realificationHom
    rw [realificationMap_realificationHom]
    exact Subgroup.mem_map.mpr ⟨map K.incl a, ha, rfl⟩

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem lieSubalgebra_mem_iInf {η R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (U : η → LieSubalgebra R L) (x : L) : x ∈ (⨅ j, U j) ↔ ∀ j, x ∈ U j := by
  change x ∈ ((sInf (Set.range U) : LieSubalgebra R L) : Set L) ↔ _
  rw [LieSubalgebra.coe_sInf]
  simp

theorem real_baseChange_ker {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℚ V] [Module ℚ W] (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact (Module.Flat.ker_lTensor_eq ℝ ℝ f).symm

theorem real_baseChange_pi {η V : Type*} {W : η → Type*}
    [AddCommGroup V] [Module ℚ V] [∀ j, AddCommGroup (W j)] [∀ j, Module ℚ (W j)]
    (f : ∀ j, V →ₗ[ℚ] W j) :
    (TensorProduct.piRightHom ℚ ℝ ℝ W).comp ((LinearMap.pi f).baseChange ℝ) =
      LinearMap.pi (fun j => (f j).baseChange ℝ) := by
  ext a v
  rfl

theorem real_baseChange_iInf {η V : Type*} [Fintype η] [AddCommGroup V] [Module ℚ V]
    (U : η → Submodule ℚ V) :
    (⨅ j, U j).baseChange ℝ = ⨅ j, (U j).baseChange ℝ := by
  classical
  let f := LinearMap.pi (fun j => (U j).mkQ)
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun j => V ⧸ U j)
  have hker : LinearMap.ker f = ⨅ j, U j := by
    simp only [f, LinearMap.ker_pi, Submodule.ker_mkQ]
  have hsingle (j : η) : (U j).baseChange ℝ = LinearMap.ker ((U j).mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker (U j).mkQ
  rw [← hker, real_baseChange_ker]
  simp_rw [hsingle]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf]
  have heq : e (f.baseChange ℝ x) = fun j => (U j).mkQ.baseChange ℝ x :=
    congrArg (fun g => g x) (real_baseChange_pi (fun j => (U j).mkQ))
  constructor
  · intro hx
    have hz : e (f.baseChange ℝ x) = 0 := by rw [hx, map_zero]
    rw [heq] at hz
    exact fun j => congrFun hz j
  · intro hx
    apply e.injective
    rw [map_zero, heq]
    funext j
    exact hx j

theorem realificationLieSubalgebra_iInf {η L : Type*} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] (U : η → LieSubalgebra ℚ L) :
    realificationLieSubalgebra (⨅ j, U j) = ⨅ j, realificationLieSubalgebra (U j) := by
  have hsub : (⨅ j, U j).toSubmodule = ⨅ j, (U j).toSubmodule := by
    ext x
    change x ∈ (⨅ j, U j) ↔ x ∈ (⨅ j, (U j).toSubmodule)
    rw [Submodule.mem_iInf]
    exact lieSubalgebra_mem_iInf U x
  ext x
  change x ∈ (⨅ j, U j).toSubmodule.baseChange ℝ ↔ _
  rw [hsub, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, lieSubalgebra_mem_iInf]
  rfl

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realWeightedGroupInclusion (c : σ → ℕ) :
    (F.weightedFiltration c).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.weightedFiltration c).lowerCentralSeries_eq_bot)
    (hM := F.ordinary.lowerCentralSeries_eq_bot) (F.weightedSubalgebra c).incl

theorem realWeightedGroupInclusion_injective (c : σ → ℕ) :
    Function.Injective (F.realWeightedGroupInclusion c) := by
  intro x y hxy
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_incl_injective (F.weightedSubalgebra c)
    (congrArg NilpotentLieBCHGroup.coord hxy)

noncomputable def realifiedWeightedOrbit {τ : Type*} (c : σ → ℕ) {v : τ → ℕ}
    (q : (F.realification.weightedFiltration c).PolynomialOrbit v) :
    (F.weightedFiltration c).realification.PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (VectorPolynomial.map (F.realifiedWeightedEquiv c).symm.toLinearMap q.log)
    ((F.realification.weightedFiltration c).adapted_map (F.weightedFiltration c).realification
      (F.realifiedWeightedEquiv c).symm.toLinearMap
      (fun n x hx => (F.realifiedWeightedEquiv_symm_mem_layer c n x).mpr hx) v q.adapted)

theorem realifiedWeightedOrbit_eval {τ : Type*} (c : σ → ℕ) {v : τ → ℕ}
    (q : (F.realification.weightedFiltration c).PolynomialOrbit v) (x : τ → ℤ) :
    F.realWeightedGroupInclusion c
      ((F.weightedFiltration c).realification.polynomialOrbitEval v x (F.realifiedWeightedOrbit c q)) =
        F.realification.weightedGroupInclusion c
          ((F.realification.weightedFiltration c).polynomialOrbitEval v x q) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.weightedSubalgebra c).incl
    (eval (fun i => (x i : ℚ))
      (VectorPolynomial.map (F.realifiedWeightedEquiv c).symm.toLinearMap q.log)) = _
  rw [eval_map, ← F.realifiedWeightedEquiv_coe]
  exact congrArg (fun z : F.realification.weightedSubalgebra c => (z : ℝ ⊗[ℚ] L))
    ((F.realifiedWeightedEquiv c).apply_symm_apply _)

theorem exists_real_normalized_frozen_orbit [DecidableEq σ] (S : Finset σ) (b : σ → ℤ)
    (p : F.realification.PolynomialOrbit) (a γ : F.realification.Group)
    (hzero : F.realification.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).realification.PolynomialOrbit
        (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).realification.polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.realWeightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).realification.polynomialOrbitEval _ x q) =
          a⁻¹ * F.realification.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
  obtain ⟨q, hq, hval⟩ := F.realification.exists_normalized_frozen_orbit S b p a γ hzero
  refine ⟨F.realifiedWeightedOrbit _ q, ?_, ?_⟩
  · apply F.realWeightedGroupInclusion_injective (retainedCoordinateWeight S)
    rw [F.realifiedWeightedOrbit_eval, hq, map_one, map_one]
  · intro x
    rw [F.realifiedWeightedOrbit_eval, hval]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_sup (P Q : Submodule ℚ V) :
    (P ⊔ Q).baseChange ℝ = P.baseChange ℝ ⊔ Q.baseChange ℝ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    change (1 : ℝ) ⊗ₜ[ℚ] (a + b) ∈ _
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem_sup (Submodule.tmul_mem_baseChange_of_mem _ ha)
      (Submodule.tmul_mem_baseChange_of_mem _ hb)
  · exact sup_le (Submodule.baseChange_mono ℝ le_sup_left)
      (Submodule.baseChange_mono ℝ le_sup_right)

theorem real_four_projection (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ x =
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x k := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem real_four_single (k : Fin 4) (x : ℝ ⊗[ℚ] V) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V))
        ((LinearMap.single ℚ (fun _ : Fin 4 => V) k).baseChange ℝ x) =
      LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) k x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    ext j
    change a ⊗ₜ[ℚ] ((Pi.single k x : Fin 4 → V) j) =
      (Pi.single k (a ⊗ₜ[ℚ] x) : Fin 4 → ℝ ⊗[ℚ] V) j
    rw [TensorProduct.tmul_single]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem real_four_alternating (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
    (fourAlternatingMap (R := ℚ)).baseChange ℝ x =
      fourAlternatingMap (R := ℝ) ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x) := by
  simp only [fourAlternatingMap, LinearMap.baseChange_sub, LinearMap.baseChange_add,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.proj_apply, real_four_projection]

theorem mem_realified_four_product_iff (D : Submodule ℚ V)
    (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
    x ∈ (Submodule.pi Set.univ (fun _ : Fin 4 => D)).baseChange ℝ ↔
      ∀ k, (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)) x k ∈ D.baseChange ℝ := by
  have heq : Submodule.pi Set.univ (fun _ : Fin 4 => D) =
      ⨅ k : Fin 4, D.comap (LinearMap.proj k) := by
    ext v
    simp [Submodule.mem_pi]
  rw [heq, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, realification_comap, Submodule.mem_comap, real_four_projection]

theorem realification_fourCommonModulo (C D : Submodule ℚ V) :
    ((fourCommonModulo C D).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
      x ∈ (fourCommonModulo C D).baseChange ℝ ↔
        e x ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
    rw [fourCommonModulo, realification_inf, Submodule.mem_inf,
      mem_realified_four_product_iff, real_baseChange_iInf, mem_fourCommonModulo]
    simp only [e, Submodule.mem_iInf, realification_comap, Submodule.mem_comap,
      LinearMap.baseChange_sub, LinearMap.sub_apply, real_four_projection]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

theorem realification_fourBalancedDependent (D : Submodule ℚ V) :
    ((fourBalancedDependent D).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourBalancedDependent (D.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 4 → V)) :
      x ∈ (fourBalancedDependent D).baseChange ℝ ↔
        e x ∈ fourBalancedDependent (D.baseChange ℝ) := by
    rw [fourBalancedDependent, realification_inf, realification_ker, Submodule.mem_inf,
      mem_realified_four_product_iff, LinearMap.mem_ker, real_four_alternating,
      mem_fourBalancedDependent, fourAlternatingMap_apply]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

theorem realification_fourRefinedRelation (C D : Submodule ℚ V)
    (K : Submodule ℚ (Fin 4 → V)) :
    ((fourRefinedRelation C D K).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap =
      fourRefinedRelation (C.baseChange ℝ) (D.baseChange ℝ)
        ((K.baseChange ℝ).map (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap) := by
  rw [fourRefinedRelation, realification_sup, realification_inf, Submodule.map_sup,
    Submodule.map_inf _ (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).injective,
    realification_fourCommonModulo, realification_fourBalancedDependent]
  rfl

theorem realification_fourPetalSpace (D : Submodule ℚ V)
    (K : Submodule ℚ (Fin 4 → V)) :
    (fourPetalSpace D K).baseChange ℝ =
      fourPetalSpace (D.baseChange ℝ)
        ((K.baseChange ℝ).map (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap) := by
  rw [fourPetalSpace, realification_inf, realification_comap]
  ext x
  change (x ∈ D.baseChange ℝ ∧
      (LinearMap.single ℚ (fun _ : Fin 4 => V) 0).baseChange ℝ x ∈ K.baseChange ℝ) ↔
    (x ∈ D.baseChange ℝ ∧ LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) 0 x ∈
      (K.baseChange ℝ).map (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).toLinearMap)
  apply and_congr_right
  intro _
  rw [← real_four_single]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    have h := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).injective he
    rwa [← h]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def symbolPointwiseSubalgebra (U : LieSubalgebra ℚ F.AssociatedGraded) :
    LieSubalgebra ℚ (F.PolynomialSymbol w) :=
  (coefficientLieSubalgebra U).comap (F.gradedSymbolPolynomialLie b ω hlayers w)

theorem mem_symbolPointwiseSubalgebra_iff (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) :
    x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
      ∀ α, coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α ∈ U := Iff.rfl

theorem mem_symbolPointwiseSubalgebra_iff_values (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) :
    x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
      ∀ t : σ → ℚ, eval t (F.gradedSymbolPolynomial b ω hlayers w x) ∈ U := by
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  exact (eval_mem_iff_coefficients U.toSubmodule _).symm

theorem gradedSymbolPolynomial_block_coefficient [DecidableEq σ]
    (α β : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    coefficients (F.gradedSymbolPolynomial b ω hlayers w
      (basisCoordinateProjection (F.polynomialSymbolBasis b ω hlayers w)
        {z | z.val.1 = α} x)) β =
      if β = α then coefficients (F.gradedSymbolPolynomial b ω hlayers w x) β else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  by_cases hβ : β = α
  · rw [ite_eq_left hβ]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        F.gradedSymbolPolynomial_coefficient b ω hlayers w x ⟨(β, i), hd⟩,
        basisCoordinateProjection_repr]
      exact ite_eq_left hβ
    · rw [F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd,
        F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w x β i hd]
  · rw [ite_eq_right hβ, map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w β = ω i
    · rw [F.gradedSymbolPolynomial_coefficient b ω hlayers w _ ⟨(β, i), hd⟩,
        basisCoordinateProjection_repr]
      exact ite_eq_right hβ
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ β i hd

theorem symbolPointwiseSubalgebra_blockInvariant (U : LieSubalgebra ℚ F.AssociatedGraded) :
    BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1)
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  intro α x hx
  apply (F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U _).mpr
  intro β
  rw [F.gradedSymbolPolynomial_block_coefficient]
  split_ifs
  · exact (F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx β
  · exact U.zero_mem

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

section Algebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def petalComparisonSpace (C P K : Submodule R V) : Submodule R (Fin 2 → V) :=
  (C ⊔ K).comap (LinearMap.proj (1 : Fin 2) : (Fin 2 → V) →ₗ[R] V) ⊓
    (P ⊔ K).comap ((LinearMap.proj (0 : Fin 2) : (Fin 2 → V) →ₗ[R] V) -
      (LinearMap.proj (1 : Fin 2) : (Fin 2 → V) →ₗ[R] V))

theorem mem_petalComparisonSpace (C P K : Submodule R V) (x : Fin 2 → V) :
    x ∈ petalComparisonSpace C P K ↔ x 1 ∈ C ⊔ K ∧ x 0 - x 1 ∈ P ⊔ K := Iff.rfl

theorem petalComparisonSpace_decompose (C P K : Submodule R V) (x : Fin 2 → V)
    (hx : x ∈ petalComparisonSpace C P K) :
    ∃ c ∈ C, ∃ p ∈ P, ∃ k₀ ∈ K, ∃ k₁ ∈ K,
      x 0 = c + p + k₀ ∧ x 1 = c + k₁ := by
  obtain ⟨c, hc, k₁, hk₁, h₁⟩ := Submodule.mem_sup.mp hx.1
  obtain ⟨p, hp, k₀, hk₀, h₀⟩ := Submodule.mem_sup.mp hx.2
  change c + k₁ = x 1 at h₁
  change p + k₀ = x 0 - x 1 at h₀
  refine ⟨c, hc, p, hp, k₁ + k₀, K.add_mem hk₁ hk₀, k₁, hk₁, ?_, h₁.symm⟩
  calc
    x 0 = (x 0 - x 1) + x 1 := (sub_add_cancel _ _).symm
    _ = (p + k₀) + (c + k₁) := by rw [← h₀, ← h₁]
    _ = c + p + (k₁ + k₀) := by abel

theorem petalComparisonSpace_le_pi (C P K U : Submodule R V)
    (hC : C ≤ U) (hP : P ≤ U) (hK : K ≤ U) :
    petalComparisonSpace C P K ≤ Submodule.pi Set.univ (fun _ : Fin 2 => U) := by
  intro x hx
  obtain ⟨c, hc, p, hp, k₀, hk₀, k₁, hk₁, h₀, h₁⟩ := petalComparisonSpace_decompose C P K x hx
  apply Submodule.mem_pi.mpr
  intro i _
  fin_cases i
  · change x 0 ∈ U
    rw [h₀]
    exact U.add_mem (U.add_mem (hC hc) (hP hp)) (hK hk₀)
  · change x 1 ∈ U
    rw [h₁]
    exact U.add_mem (hC hc) (hK hk₁)

end Algebra

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem real_pair_projection (x : ℝ ⊗[ℚ] (Fin 2 → V)) (k : Fin 2) :
    (LinearMap.proj k).baseChange ℝ x =
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)) x k := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realification_petalComparisonSpace (C P K : Submodule ℚ V) :
    ((petalComparisonSpace C P K).baseChange ℝ).map
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)).toLinearMap =
      petalComparisonSpace (C.baseChange ℝ) (P.baseChange ℝ) (K.baseChange ℝ) := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => V)
  have hmem (x : ℝ ⊗[ℚ] (Fin 2 → V)) :
      x ∈ (petalComparisonSpace C P K).baseChange ℝ ↔
        e x ∈ petalComparisonSpace (C.baseChange ℝ) (P.baseChange ℝ) (K.baseChange ℝ) := by
    simp only [petalComparisonSpace, realification_inf, realification_comap, realification_sup,
      Submodule.mem_inf, Submodule.mem_comap, LinearMap.baseChange_sub, LinearMap.sub_apply,
      LinearMap.proj_apply, real_pair_projection, e]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mp hx
  · intro hv
    refine ⟨e.symm v, (hmem _).mpr ?_, e.apply_symm_apply v⟩
    simpa only [e.apply_symm_apply] using hv

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem realification_map {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (U : Submodule ℚ V) (f : V →ₗ[ℚ] W) :
    (U.map f).baseChange ℝ = (U.baseChange ℝ).map (f.baseChange ℝ) := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span ℝ)
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ[ℚ] x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

theorem realificationLieSubalgebra_map {L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (U : LieSubalgebra ℚ L) (f : L →ₗ⁅ℚ⁆ M) :
    realificationLieSubalgebra (U.map f) =
      (realificationLieSubalgebra U).map (realificationLieHom f) := by
  apply LieSubalgebra.toSubmodule_injective
  exact realification_map U.toSubmodule f.toLinearMap

theorem toLin_baseChange_coordinates {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (T : Matrix ι κ ℚ) (y : ℝ ⊗[ℚ] M) :
    (e.baseChange ℝ).equivFun ((Matrix.toLin f e T).baseChange ℝ y) =
      (fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y := by
  classical
  simpa only [LinearMap.toMatrix_toLin] using
    (baseChange_matrix_apply f e (Matrix.toLin f e T) y).symm

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def symbolSubalgebraQuotientMap (U : LieSubalgebra ℚ F.AssociatedGraded) :
    F.PolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ (F.AssociatedGraded ⧸ U.toSubmodule) :=
  (VectorPolynomial.map U.toSubmodule.mkQ).comp (F.gradedSymbolPolynomial b ω hlayers w)

theorem symbolPointwiseSubalgebra_eq_ker (U : LieSubalgebra ℚ F.AssociatedGraded) :
    (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule =
      LinearMap.ker (F.symbolSubalgebraQuotientMap b ω hlayers w U) := by
  ext x
  change x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
    F.symbolSubalgebraQuotientMap b ω hlayers w U x = 0
  rw [F.mem_symbolPointwiseSubalgebra_iff]
  constructor
  · intro hx
    apply coefficients.injective
    ext α
    change coefficients (VectorPolynomial.map U.toSubmodule.mkQ
      (F.gradedSymbolPolynomial b ω hlayers w x)) α = _
    rw [coefficients_map, map_zero, Finsupp.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr (hx α)
  · intro hx α
    have hc := congrArg (fun p => coefficients p α) hx
    change coefficients (VectorPolynomial.map U.toSubmodule.mkQ
      (F.gradedSymbolPolynomial b ω hlayers w x)) α = _ at hc
    rw [coefficients_map, map_zero, Finsupp.zero_apply] at hc
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp hc

theorem symbolSubalgebraQuotientMap_real_coefficient
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (VectorPolynomial.realificationLinearEquiv
      ((F.symbolSubalgebraQuotientMap b ω hlayers w U).baseChange ℝ x)) α =
      U.toSubmodule.mkQ.baseChange ℝ
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  unfold symbolSubalgebraQuotientMap
  exact F.realGradedSymbolPolynomial_map_coefficient b ω hlayers w U.toSubmodule.mkQ x α

theorem mem_real_symbolPointwiseSubalgebra_iff_coefficients
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) :
    x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hlayers w U) ↔
      ∀ α, coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈
        realificationLieSubalgebra U := by
  change x ∈ (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule.baseChange ℝ ↔ _
  rw [F.symbolPointwiseSubalgebra_eq_ker, real_baseChange_ker]
  change (F.symbolSubalgebraQuotientMap b ω hlayers w U).baseChange ℝ x = 0 ↔ _
  rw [VectorPolynomial.realificationLinearEquiv_eq_zero_iff]
  have hker : U.toSubmodule.baseChange ℝ = LinearMap.ker (U.toSubmodule.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker U.toSubmodule.mkQ
  constructor
  · intro hx α
    change coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈ U.toSubmodule.baseChange ℝ
    rw [hker]
    change U.toSubmodule.mkQ.baseChange ℝ
      (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) = 0
    exact (F.symbolSubalgebraQuotientMap_real_coefficient b ω hlayers w U x α).symm.trans (hx α)
  · intro hx α
    have h := hx α
    change coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α ∈ U.toSubmodule.baseChange ℝ at h
    rw [hker] at h
    exact (F.symbolSubalgebraQuotientMap_real_coefficient b ω hlayers w U x α).trans h

theorem mem_real_symbolPointwiseSubalgebra_iff_values
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) :
    x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hlayers w U) ↔
      ∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x) ∈
        realificationLieSubalgebra U := by
  rw [F.mem_real_symbolPointwiseSubalgebra_iff_coefficients]
  exact (eval₂_mem_iff_coefficients (realificationLieSubalgebra U).toSubmodule _).symm

theorem symbolPointwiseSubalgebra_iInf {η : Type*} (U : η → LieSubalgebra ℚ F.AssociatedGraded) :
    F.symbolPointwiseSubalgebra b ω hlayers w (⨅ j, U j) =
      ⨅ j, F.symbolPointwiseSubalgebra b ω hlayers w (U j) := by
  ext x
  rw [lieSubalgebra_mem_iInf, F.mem_symbolPointwiseSubalgebra_iff]
  simp only [F.mem_symbolPointwiseSubalgebra_iff, lieSubalgebra_mem_iInf]
  exact forall_comm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

section Functional

variable {R L M : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M]

def pairDifferenceFunctional (η : L →ₗ[R] M) : (Fin 2 → L) →ₗ[R] M :=
  η.comp (LinearMap.proj (0 : Fin 2)) - η.comp (LinearMap.proj (1 : Fin 2))

theorem pairDifferenceFunctional_apply (η : L →ₗ[R] M) (z : Fin 2 → L) :
    pairDifferenceFunctional η z = η (z 0) - η (z 1) := rfl

end Functional

theorem petalComparisonSpace_top_tree
    {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup M] [Module ℚ M]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r) (d : I → ℕ)
    (C P : I → Submodule ℚ L) (hC : ∀ i, C i ≤ F.layer (d i) 1)
    (hP : ∀ i, P i ≤ F.layer (d i) 1)
    (η : L →ₗ[ℚ] M) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hinvariant : ∀ c p : I → L, (∀ i, c i ∈ C i) → (∀ i, p i ∈ P i) →
      η (lieTreeEval (c + p) a) = η (lieTreeEval c a))
    (z : I → Fin 2 → L)
    (hz : ∀ i, z i ∈ petalComparisonSpace (C i) (P i) (F.layer (d i) 2)) :
    pairDifferenceFunctional η (lieTreeEval z a) = 0 := by
  classical
  choose c hc p hp k₀ hk₀ k₁ hk₁ h₀ h₁ using
    (fun i => petalComparisonSpace_decompose (C i) (P i) (F.layer (d i) 2) (z i) (hz i))
  have hle (i : I) : F.layer (d i) 2 ≤ F.layer (d i) 1 :=
    F.lex_antitone (Or.inr ⟨rfl, by omega⟩)
  have hz₀ (i : I) : z i 0 ∈ F.layer (d i) 1 := by
    rw [h₀]
    exact (F.layer (d i) 1).add_mem ((F.layer (d i) 1).add_mem (hC i (hc i)) (hP i (hp i)))
      (hle i (hk₀ i))
  have hz₁ (i : I) : z i 1 ∈ F.layer (d i) 1 := by
    rw [h₁]
    exact (F.layer (d i) 1).add_mem (hC i (hc i)) (hle i (hk₁ i))
  have hdiff₀ (i : I) : z i 0 - (c i + p i) ∈ F.layer (d i) 2 := by
    rw [h₀]
    simpa only [add_sub_cancel_left] using hk₀ i
  have hdiff₁ (i : I) : z i 1 - c i ∈ F.layer (d i) 2 := by
    rw [h₁]
    simpa only [add_sub_cancel_left] using hk₁ i
  have heq₀ := F.top_lieTreeEval_congr (fun i => z i 0) (c + p) d hz₀
    (fun i => (F.layer (d i) 1).add_mem (hC i (hc i)) (hP i (hp i))) hdiff₀ a hd hr
  have heq₁ := F.top_lieTreeEval_congr (fun i => z i 1) c d hz₁
    (fun i => hC i (hc i)) hdiff₁ a hd hr
  change η ((liePiEval (0 : Fin 2)) (lieTreeEval z a)) -
    η ((liePiEval (1 : Fin 2)) (lieTreeEval z a)) = 0
  rw [map_lieTreeEval, map_lieTreeEval]
  change η (lieTreeEval (fun i => z i 0) a) - η (lieTreeEval (fun i => z i 1) a) = 0
  rw [heq₀, heq₁, hinvariant c p hc hp, sub_self]

end Erdos3

end

end OAI

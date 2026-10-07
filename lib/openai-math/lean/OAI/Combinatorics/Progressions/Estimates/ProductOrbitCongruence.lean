/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem baseChange_mem_of_mapsTo {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (P : Submodule ℚ V) (Q : Submodule ℚ W)
    (f : V →ₗ[ℚ] W) (hf : ∀ x ∈ P, f x ∈ Q) {x : ℝ ⊗[ℚ] V}
    (hx : x ∈ P.baseChange ℝ) : f.baseChange ℝ x ∈ Q.baseChange ℝ := by
  have hm : P.baseChange ℝ ≤ (Q.baseChange ℝ).comap (f.baseChange ℝ) := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hf a ha)
  exact hm hx

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def realProductSingle (i : ι) :
    (ℝ ⊗[ℚ] L i) →ₗ[ℝ] (ℝ ⊗[ℚ] (∀ j, L j)) := by
  classical
  exact (LinearMap.single ℚ L i).baseChange ℝ

theorem realProductSingle_projection (i : ι) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval i) (realProductSingle i x) = x := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x i) = r ⊗ₜ[ℚ] x
    rw [Pi.single_eq_same]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realProductSingle_projection_ne {i j : ι} (hij : j ≠ i) (x : ℝ ⊗[ℚ] L i) :
    realificationLieHom (liePiEval j) (realProductSingle i x) = 0 := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    change r ⊗ₜ[ℚ] (Pi.single i x j) = 0
    rw [Pi.single_eq_of_ne hij, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem realProductSingle_mem_layer {s : ℕ} (F : ∀ i, NilpotentLieFiltration (L i) s)
    (i : ι) (n : ℕ) {x : ℝ ⊗[ℚ] L i} (hx : x ∈ (F i).realification.layer n) :
    realProductSingle i x ∈ (NilpotentLieFiltration.pi F).realification.layer n := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer n) ((NilpotentLieFiltration.pi F).layer n)
    (LinearMap.single ℚ L i) _ hx
  intro a ha
  apply (NilpotentLieFiltration.mem_pi_layer F n _).mpr
  intro j
  change Pi.single i a j ∈ (F j).layer n
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using ha
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}
  (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)

theorem realProductSingle_mem_layer (i : ι) (a : σ → ℕ) {x : ℝ ⊗[ℚ] L i}
    (hx : x ∈ (F i).realification.layer a) :
    realProductSingle i x ∈ (pi F).realification.layer a := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer a) ((pi F).layer a)
    (LinearMap.single ℚ L i) _ hx
  intro y hy
  apply (mem_pi_layer F a _).mpr
  intro j
  change Pi.single i y j ∈ (F j).layer a
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using hy
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

noncomputable def piRealOrbit (g : ∀ i, (F i).realification.PolynomialOrbit) :
    (pi F).realification.PolynomialOrbit :=
  (pi F).realification.polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
      ((g i).log (F i).realification)) (by
      intro a
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _ ((g i).adapted (F i).realification a))

theorem piRealOrbit_eval (g : ∀ i, (F i).realification.PolynomialOrbit) (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).ordinary.lowerCentralSeries_eq_bot)
      (hM := (F i).ordinary.lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval x (piRealOrbit F g)) =
        (F i).realification.polynomialOrbitEval x (g i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog, PolynomialOrbit.log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.MultidegreeLieFiltration

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

noncomputable def piRealOrbit (p : ∀ i, (F i).realification.PolynomialOrbit w) :
    (pi F).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ) (p i).log) (by
      apply ((pi F).realification.adapted_iff_coefficients w _).mpr
      intro α
      simp only [map_sum, Finsupp.finsetSum_apply, VectorPolynomial.coefficients_map]
      apply Submodule.sum_mem
      intro i _
      exact realProductSingle_mem_layer F i _
        (((F i).realification.adapted_iff_coefficients w _).mp (p i).adapted α))

theorem piRealOrbit_eval (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (x : σ → ℤ) (i : ι) :
    NilpotentLieBCHGroup.realificationMap
      (hnil := (pi F).lowerCentralSeries_eq_bot) (hM := (F i).lowerCentralSeries_eq_bot) (liePiEval i)
      ((pi F).realification.polynomialOrbitEval w x (piRealOrbit F p)) =
        (F i).realification.polynomialOrbitEval w x (p i) := by
  classical
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieBCHGroup.realificationMap_coord, polynomialOrbitEval_coord,
    piRealOrbit, polynomialOrbitOfLog_log, map_sum, VectorPolynomial.eval_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

theorem piRealOrbit_coefficient (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (α : σ →₀ ℕ) (i : ι) :
    realificationLieHom (liePiEval i) (coefficients (piRealOrbit F p).log α) =
      coefficients (p i).log α := by
  classical
  simp only [piRealOrbit, polynomialOrbitOfLog_log, map_sum,
    Finsupp.finsetSum_apply, coefficients_map]
  rw [Finset.sum_eq_single i]
  · exact realProductSingle_projection i _
  · intro j _ hji
    exact realProductSingle_projection_ne (Ne.symm hji) _
  · simp

theorem piRealOrbit_project_log (p : ∀ i, (F i).realification.PolynomialOrbit w) (i : ι) :
    VectorPolynomial.map ((realificationLieHom (liePiEval i)).toLinearMap.restrictScalars ℚ)
      (piRealOrbit F p).log = (p i).log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact piRealOrbit_coefficient F p α i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

theorem exists_real_firstProjection_lift {V : Type*} [AddCommGroup V] [Module ℚ V]
    (J : Submodule ℚ (Fin 4 → V)) (x : ℝ ⊗[ℚ] V)
    (hx : x ∈ (fourFirstProjection J).baseChange ℝ) :
    ∃ z ∈ J.baseChange ℝ, (LinearMap.proj (0 : Fin 4)).baseChange ℝ z = x := by
  rwa [fourFirstProjection, realification_map] at hx

theorem exists_real_sparseProjection_lift {V : Type*} [AddCommGroup V] [Module ℚ V]
    (J : Submodule ℚ (Fin 4 → V)) (S : Finset (Fin 4)) (x : ℝ ⊗[ℚ] V)
    (hx : x ∈ (fourSparseFirstProjection J S).baseChange ℝ) :
    ∃ z ∈ J.baseChange ℝ, (LinearMap.proj (0 : Fin 4)).baseChange ℝ z = x ∧
      ∀ k ∈ S, (LinearMap.proj k).baseChange ℝ z = 0 := by
  rw [fourSparseFirstProjection, realification_map, realification_inf] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨z, hz.1, hzx, ?_⟩
  intro k hk
  have h := baseChange_mem_of_mapsTo (fourCoordinateKernel (V := V) S)
    (⊥ : Submodule ℚ V) (LinearMap.proj k)
    (fun v hv => (mem_fourCoordinateKernel S v).mp hv k hk) hz.2
  simpa only [Submodule.baseChange_bot, Submodule.mem_bot] using h

theorem real_four_sparse_lifts_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, ℝ ⊗[ℚ] V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, ℝ ⊗[ℚ] (Fin 4 → V i), (∀ i, v i ∈ (J i).baseChange ℝ) →
      η (B (fun i => (LinearMap.proj (0 : Fin 4)).baseChange ℝ (v i))) +
      η (B (fun i => (LinearMap.proj (1 : Fin 4)).baseChange ℝ (v i))) -
      η (B (fun i => (LinearMap.proj (2 : Fin 4)).baseChange ℝ (v i))) -
      η (B (fun i => (LinearMap.proj (3 : Fin 4)).baseChange ℝ (v i))) = 0)
    (v : ∀ i, ℝ ⊗[ℚ] V i) (hv : ∀ i, v i ∈ (fourFirstProjection (J i)).baseChange ℝ)
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ (fourSparseFirstProjection (J a) {1, 2}).baseChange ℝ)
    (hvb : v b ∈ (fourSparseFirstProjection (J b) {1, 3}).baseChange ℝ) : η (B v) = 0 := by
  classical
  choose w hwJ hw0 using (fun i => exists_real_firstProjection_lift (J i) (v i) (hv i))
  obtain ⟨xa, hxa, hxa0, hxaz⟩ := exists_real_sparseProjection_lift (J a) {1, 2} (v a) hva
  obtain ⟨xb, hxb, hxb0, hxbz⟩ := exists_real_sparseProjection_lift (J b) {1, 3} (v b) hvb
  let z := Function.update (Function.update w a xa) b xb
  have hza : z a = xa := by simp [z, hab]
  have hzb : z b = xb := by simp [z]
  have hzJ (i : I) : z i ∈ (J i).baseChange ℝ := by
    by_cases hib : i = b
    · subst i; rw [hzb]; exact hxb
    by_cases hia : i = a
    · subst i; rw [hza]; exact hxa
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hwJ i
  have hzfirst : (fun i => (LinearMap.proj (0 : Fin 4)).baseChange ℝ (z i)) = v := by
    funext i
    by_cases hib : i = b
    · subst i; rw [hzb]; exact hxb0
    by_cases hia : i = a
    · subst i; rw [hza]; exact hxa0
    simpa only [z, Function.update_of_ne hib, Function.update_of_ne hia] using hw0 i
  have hz1 : B (fun i => (LinearMap.proj (1 : Fin 4)).baseChange ℝ (z i)) = 0 :=
    hzero _ a ha (by rw [hza]; exact hxaz 1 (by simp))
  have hz2 : B (fun i => (LinearMap.proj (2 : Fin 4)).baseChange ℝ (z i)) = 0 :=
    hzero _ a ha (by rw [hza]; exact hxaz 2 (by simp))
  have hz3 : B (fun i => (LinearMap.proj (3 : Fin 4)).baseChange ℝ (z i)) = 0 :=
    hzero _ b hb (by rw [hzb]; exact hxbz 3 (by simp))
  have h := hJ z hzJ
  simpa only [hzfirst, hz1, hz2, hz3, hη, add_zero, sub_zero] using h

theorem real_four_dependent_inputs_vanish {I : Type*} {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ (V i)]
    {M A : Type*} [Zero M] [AddCommGroup A]
    (S : Set I) (B : (∀ i, ℝ ⊗[ℚ] V i) → M)
    (hzero : ∀ v i, i ∈ S → v i = 0 → B v = 0)
    (η : M → A) (hη : η 0 = 0) (J : ∀ i, Submodule ℚ (Fin 4 → V i))
    (hJ : ∀ v : ∀ i, ℝ ⊗[ℚ] (Fin 4 → V i), (∀ i, v i ∈ (J i).baseChange ℝ) →
      η (B (fun i => (LinearMap.proj (0 : Fin 4)).baseChange ℝ (v i))) +
      η (B (fun i => (LinearMap.proj (1 : Fin 4)).baseChange ℝ (v i))) -
      η (B (fun i => (LinearMap.proj (2 : Fin 4)).baseChange ℝ (v i))) -
      η (B (fun i => (LinearMap.proj (3 : Fin 4)).baseChange ℝ (v i))) = 0)
    (v : ∀ i, ℝ ⊗[ℚ] V i) (hv : ∀ i, v i ∈ (fourFirstProjection (J i)).baseChange ℝ)
    (a b : I) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hva : v a ∈ (fourDependentProjection (J a)).baseChange ℝ)
    (hvb : v b ∈ (fourDependentProjection (J b)).baseChange ℝ) : η (B v) = 0 := by
  rw [fourDependentProjection, realification_inf] at hva hvb
  exact real_four_sparse_lifts_vanish S B hzero η hη J hJ v hv a b hab ha hb hva.1 hvb.2

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

theorem piRealOrbit_eval_eq_of_log_eq
    {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F G : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (q : ∀ i, (G i).realification.PolynomialOrbit w)
    (hlog : ∀ i, (p i).log = (q i).log) (x : σ → ℤ) :
    (pi F).realification.polynomialOrbitEval w x (piRealOrbit F p) =
      (pi G).realification.polynomialOrbitEval w x (piRealOrbit G q) := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitEval_coord, piRealOrbit, polynomialOrbitOfLog_log]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg _ (hlog i))

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

theorem pi_basis_eq_of_basis_eq {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D E : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (h : ∀ i, (D i).basis = (E i).basis) : (pi D).basis = (pi E).basis := by
  change (Pi.basis (fun i => (D i).basis)).reindex (Fintype.equivFin _) =
    (Pi.basis (fun i => (E i).basis)).reindex (Fintype.equivFin _)
  rw [show (fun i => (D i).basis) = (fun i => (E i).basis) from funext h]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

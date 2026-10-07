/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.CoveredQuotientCorrelation

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem realify_pairDifferenceFunctional {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (η : L →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] (Fin 2 → L)) :
    realifyFunctional (pairDifferenceFunctional η) x =
      realifyFunctional η (realificationLieHom (liePiEval (0 : Fin 2)) x) -
        realifyFunctional η (realificationLieHom (liePiEval (1 : Fin 2)) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [realifyFunctional_tmul, pairDifferenceFunctional_apply,
      realificationLieHom_tmul, liePiEval_apply, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

theorem pairDifferenceFunctional_eq_piFrequency {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (η : L →ₗ[ℚ] ℚ) :
    pairDifferenceFunctional η = piFrequency (fun i : Fin 2 => if i = 0 then η else -η) := by
  ext x
  simp [piFrequency_apply, Fin.sum_univ_two, pairDifferenceFunctional_apply, sub_eq_add_neg]

namespace RationalFilteredNilmanifold.UnitVerticalObservable

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))]
  {D : RationalFilteredNilmanifold L s d} (T : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)

noncomputable def pairedObservable (a : I × I) (x : (pi (fun _ : Fin 2 => D)).Space) : ℂ :=
  V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x) *
    star (V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x))

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_unit (x : (pi (fun _ : Fin 2 => D)).Space) :
    ∑ a, ‖V.pairedObservable T a x‖ ^ 2 = 1 := by
  simp only [pairedObservable, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, V.unit, mul_one]

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_norm (a : I × I) (x : (pi (fun _ : Fin 2 => D)).Space) :
    ‖V.pairedObservable T a x‖ ≤ 1 := by
  simpa only [pairedObservable, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm a.1 _) (V.norm a.2 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem pairedObservable_lipschitz (a : I × I) :
    letI := (pi (fun _ : Fin 2 => D)).metricSpace
    LipschitzWith
      (2 * (V.lipBound * coordinateLipschitzBound d (Fintype.card (Σ _ : Fin 2, Fin d)) 1))
      (V.pairedObservable T a) := by
  let := D.metricSpace
  let := (pi (fun _ : Fin 2 => D)).metricSpace
  have h₀ := (V.lipschitz a.1).comp (productProjection_lipschitz (fun _ : Fin 2 => D) 0)
  have h₁ := (V.lipschitz a.2).comp (productProjection_lipschitz (fun _ : Fin 2 => D) 1)
  change LipschitzWith _ (fun x : (pi (fun _ : Fin 2 => D)).Space =>
    V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x) *
      star (V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x)))
  exact (lipschitz_mul_star_of_bounds
    (fun x : (pi (fun _ : Fin 2 => D)).Space => V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x))
    (fun x : (pi (fun _ : Fin 2 => D)).Space => V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x))
    (Bf := 1) (Bg := 1) h₀ h₁ (fun x => V.norm a.1 _) (fun x => V.norm a.2 _)).weaken
      (by simp only [one_mul, two_mul, le_refl])

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_vertical (a : I × I) (z : (pi (fun _ : Fin 2 => D)).RealGroup)
    (hz : z ∈ (piRank (fun _ : Fin 2 => D) (fun _ => T)).realSubgroup s r)
    (x : (pi (fun _ : Fin 2 => D)).Space) :
    V.pairedObservable T a (z • x) =
      CircleFourier.character
        ((realifyFunctional (pairDifferenceFunctional V.frequency) z.coord : ℝ) : CircleFourier.Circle) *
        V.pairedObservable T a x := by
  simp only [pairedObservable, productProjection_smul]
  rw [V.vertical a.1 _ (productProjectionHom_mem_rank (fun _ : Fin 2 => D)
    (fun _ => T) 0 s r z hz), V.vertical a.2 _
    (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 1 s r z hz)]
  rw [star_mul, realify_pairDifferenceFunctional, AddCircle.coe_sub,
    sub_eq_add_neg, CircleFourier.character_add, CircleFourier.character_neg]
  simp only [productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  ring

noncomputable def paired (hp : 2 ≤ p) (hD : D.GeometryComplexityLE p) :
    (pi (fun _ : Fin 2 => D)).UnitVerticalObservable
      ((piRank (fun _ : Fin 2 => D) (fun _ => T)).realSubgroup s r) (I × I)
      (p + (p ^ 2 + p + 3) ^ 2 + 2) where
  observable := V.pairedObservable T
  unit := V.pairedObservable_unit T
  norm := V.pairedObservable_norm T
  lipBound := 2 * (V.lipBound * coordinateLipschitzBound d (Fintype.card (Σ _ : Fin 2, Fin d)) 1)
  lip_bound := by
    have hp₀ : 0 ≤ p := by linarith
    have hproj := productProjection_lipschitz_bound (fun _ : Fin 2 => D) hp₀
      (by simpa using hp) (fun _ => hD) 0
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    calc
      _ ≤ Real.exp 2 * (Real.exp p * Real.exp ((p ^ 2 + p + 3) ^ 2)) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (2 : ℝ)])
          (mul_le_mul V.lip_bound hproj (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  lipschitz := V.pairedObservable_lipschitz T
  frequency := pairDifferenceFunctional V.frequency
  height i := by
    have hsmall : p ≤ p + (p ^ 2 + p + 3) ^ 2 + 2 := by nlinarith [sq_nonneg (p ^ 2 + p + 3)]
    apply le_trans _ hsmall
    rw [pairDifferenceFunctional_eq_piFrequency]
    apply piFrequency_logHeight
    intro j k
    split_ifs
    · exact V.height k
    · simpa [rationalLogHeight] using V.height k
  vertical := V.pairedObservable_vertical T
  integral z hz hL := by
    have hmem (i : Fin 2) : productProjectionHom (fun _ : Fin 2 => D) i z ∈ D.realLattice :=
      NilpotentLieBCHGroup.realificationMap_subgroup (liePiEval i) _ _
        (productProjection_lattice (fun _ : Fin 2 => D) i) hL
    obtain ⟨m, hm⟩ := V.integral _
      (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 0 s r z hz) (hmem 0)
    obtain ⟨n, hn⟩ := V.integral _
      (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 1 s r z hz) (hmem 1)
    refine ⟨m - n, ?_⟩
    rw [realify_pairDifferenceFunctional]
    change realifyFunctional V.frequency (productProjectionHom (fun _ : Fin 2 => D) 0 z).coord -
      realifyFunctional V.frequency (productProjectionHom (fun _ : Fin 2 => D) 1 z).coord = _
    rw [hm, hn, Int.cast_sub]

end RationalFilteredNilmanifold.UnitVerticalObservable
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] {s : ℕ}

theorem map_positiveUnivariate (f : V →ₗ[ℚ] W) (v : Fin s → V) :
    map f (positiveUnivariate v) = positiveUnivariate (fun d => f (v d)) := by
  simp only [positiveUnivariate, map_sum, map_monomial]

theorem positiveUnivariate_reconstruct (p : VectorPolynomial Unit ℚ V)
    (hp : DegreeLE (fun _ : Unit => 1) s p) (hzero : coefficients p 0 = 0) :
    positiveUnivariate (fun d : Fin s => coefficients p (Finsupp.single () (d.val + 1))) = p := by
  apply coefficients.injective
  ext α
  have hα : Finsupp.single () (α ()) = α := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  have hweight : Finsupp.weight (fun _ : Unit => 1) α = α () := by
    rw [← hα]
    simp [Finsupp.weight_single]
  by_cases h0 : α () = 0
  · have hz : α = 0 := by simpa only [h0, Finsupp.single_zero] using hα.symm
    rw [hz, positiveUnivariate_zero, hzero]
  · by_cases hle : α () ≤ s
    · let d : Fin s := ⟨α () - 1, by omega⟩
      have hd : d.val + 1 = α () := by dsimp only [d]; omega
      have he : Finsupp.single () (d.val + 1) = α := by rw [hd]; exact hα
      rw [← he, positiveUnivariate_coefficient]
    · have hhigh : s < Finsupp.weight (fun _ : Unit => 1) α := by rw [hweight]; omega
      rw [hp α hhigh]
      apply positiveUnivariate_coefficient_eq_zero
      intro d he
      have hv := congrArg (fun β : Unit →₀ ℕ => β ()) he
      simp only [Finsupp.single_eq_same] at hv
      omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

theorem exists_positiveUnivariate_orbit_lift
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (π : L →ₗ[ℚ] M) (g : G.PolynomialOrbit (fun _ : Unit => 1))
    (hg : G.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (v : Fin s → L) (hv : ∀ d, v d ∈ F.layer (d.val + 1))
    (hπ : ∀ d, π (v d) = coefficients g.log (Finsupp.single () (d.val + 1))) :
    ∃ q : F.PolynomialOrbit (fun _ : Unit => 1),
      q.log = positiveUnivariate v ∧ F.polynomialOrbitEval (fun _ : Unit => 1) 0 q = 1 ∧
      VectorPolynomial.map π q.log = g.log ∧
      ∀ x : Unit → ℤ, π (F.polynomialOrbitEval (fun _ : Unit => 1) x q).coord =
        (G.polynomialOrbitEval (fun _ : Unit => 1) x g).coord := by
  have hadapt : F.Adapted (fun _ : Unit => 1) (positiveUnivariate v) := by
    apply (F.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hv d
  let q := polynomialOrbitOfLog (positiveUnivariate v) hadapt
  have hzero : coefficients g.log 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hg
    simpa only [G.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using h
  have hmap : VectorPolynomial.map π q.log = g.log := by
    change VectorPolynomial.map π (positiveUnivariate v) = g.log
    rw [map_positiveUnivariate, show (fun d => π (v d)) =
      (fun d : Fin s => coefficients g.log (Finsupp.single () (d.val + 1))) from funext hπ]
    exact positiveUnivariate_reconstruct g.log g.degreeLE hzero
  refine ⟨q, rfl, ?_, hmap, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
    rw [eval_zero_eq_coefficient, positiveUnivariate_zero]
  · intro x
    rw [F.polynomialOrbitEval_coord, G.polynomialOrbitEval_coord, ← eval_map, hmap]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

abbrev Alphabet := Σ d : Fin s, Fin (finrank ℚ (S d))

def weight (x : Alphabet S) : ℕ := x.1.val + 1

theorem weight_pos (x : Alphabet S) : 0 < weight S x := Nat.succ_pos _

abbrev Algebra (r : ℕ) := FreeDegreeRankLieAlgebra (Alphabet S) s r (weight S) (weight_pos S)

noncomputable def filtration (hr : r ≤ s) : DegreeRankLieFiltration (Algebra S r) s r :=
  FreeDegreeRankLieAlgebra.filtration (Alphabet S) s r (weight S) (weight_pos S) hr

noncomputable def generator (r : ℕ) (x : Alphabet S) : Algebra S r :=
  FreeDegreeRankLieAlgebra.of (Alphabet S) s r (weight S) (weight_pos S) x

noncomputable def generatorSpan (r : ℕ) (d : Fin s) : Submodule ℚ (Algebra S r) :=
  Submodule.span ℚ (Set.range (fun i => generator S r ⟨d, i⟩))

theorem generatorSpan_le_layer (hr : r ≤ s) (d : Fin s) :
    generatorSpan S r d ≤ (filtration S hr).layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact FreeDegreeRankLieAlgebra.of_mem_layer (Alphabet S) s r (weight S) (weight_pos S) hr ⟨d, i⟩

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

noncomputable def coefficientLift (r : ℕ) (d : Fin s) : S d →ₗ[ℚ] Algebra S r :=
  (B d).constr ℚ (fun i => generator S r ⟨d, i⟩)

theorem coefficientLift_range (r : ℕ) (d : Fin s) :
    LinearMap.range (coefficientLift S B r d) = generatorSpan S r d :=
  (B d).constr_range ℚ

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

noncomputable def evaluation : Algebra S r →ₗ⁅ℚ⁆ L :=
  FreeDegreeRankLieAlgebra.lift F (weight S) (weight_pos S)
    (fun x => (B x.1 x.2).val) (fun x => hS x.1 (B x.1 x.2).property)

theorem evaluation_generator (x : Alphabet S) :
    evaluation S B F hS (generator S r x) = (B x.1 x.2).val :=
  FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x

theorem evaluation_coefficientLift (d : Fin s) (x : S d) :
    evaluation S B F hS (coefficientLift S B r d x) = x.val := by
  have heq : (evaluation S B F hS).toLinearMap.comp (coefficientLift S B r d) =
      (S d).subtype := by
    apply (B d).ext
    intro i
    change evaluation S B F hS ((B d).constr ℚ _ (B d i)) = _
    rw [Basis.constr_basis]
    exact evaluation_generator S B F hS ⟨d, i⟩
  exact LinearMap.congr_fun heq x

noncomputable def realCoefficientLift (d : Fin s) :
    (S d).baseChange ℝ →ₗ[ℝ] ℝ ⊗[ℚ] Algebra S r :=
  ((coefficientLift S B r d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (S d)).symm.toLinearMap

theorem realCoefficientLift_baseChange (d : Fin s) (x : ℝ ⊗[ℚ] S d) :
    realCoefficientLift S B (r := r) d (realificationSubmoduleEquiv _ x) =
      (coefficientLift S B r d).baseChange ℝ x :=
  congrArg ((coefficientLift S B r d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem realCoefficientLift_mem (d : Fin s) (x : (S d).baseChange ℝ) :
    realCoefficientLift S B (r := r) d x ∈ (generatorSpan S r d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [realCoefficientLift_baseChange]
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((coefficientLift_range S B r d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem realEvaluation_coefficientLift (d : Fin s) (x : (S d).baseChange ℝ) :
    realificationLieHom (evaluation S B F hS) (realCoefficientLift S B d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [realCoefficientLift_baseChange, realificationSubmoduleEquiv_coe]
  change (evaluation S B F hS).toLinearMap.baseChange ℝ
    ((coefficientLift S B r d).baseChange ℝ v) = _
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    change a ⊗ₜ[ℚ] evaluation S B F hS (coefficientLift S B r d v) = a ⊗ₜ[ℚ] v.val
    rw [evaluation_coefficientLift]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem exists_polynomialOrbit
    (g : F.associatedDegree.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : F.associatedDegree.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (S d).baseChange ℝ) :
    let G := (filtration S F.rank_le_degree).associatedDegree.realification
    ∃ u : G.PolynomialOrbit (fun _ : Unit => 1),
      G.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (generatorSpan S r d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (evaluation S B F hS)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := (filtration S F.rank_le_degree).associatedDegree.lowerCentralSeries_eq_bot)
        (hM := F.associatedDegree.lowerCentralSeries_eq_bot) (evaluation S B F hS)
        (G.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          F.associatedDegree.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  intro G
  let v (d : Fin s) := realCoefficientLift S B (r := r) d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (generatorSpan S r d).baseChange ℝ :=
    realCoefficientLift_mem S B d _
  have hv (d : Fin s) : v d ∈ G.layer (d.val + 1) := by
    change v d ∈ ((filtration S F.rank_le_degree).layer (d.val + 1) 0).baseChange ℝ
    rw [(filtration S F.rank_le_degree).rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (generatorSpan_le_layer S F.rank_le_degree d) (hvspan d)
  let π := (realificationLieHom (evaluation S B F hS)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    realEvaluation_coefficientLift S B F hS d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ := G.exists_positiveUnivariate_orbit_lift
    F.associatedDegree.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e : ℕ}
  (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
  (S : Fin s → Submodule ℚ L)
  (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
  (hS : ∀ j, S j ≤ T.filtration.layer (j.val + 1) 0)
  (E : RationalFilteredNilmanifold (Algebra S r) s e) (Q : E.DegreeRankStructure r)
  (hQ : Q.filtration = filtration S T.filtration.rank_le_degree)

include Q hQ

theorem exists_native_polynomialOrbit
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ j : Fin s, coefficients g.log (Finsupp.single () (j.val + 1)) ∈
      (S j).baseChange ℝ) :
    ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
        (generatorSpan S r j).baseChange ℝ) ∧
      VectorPolynomial.map
        ((realificationLieHom (evaluation S B T.filtration hS)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS)
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let hD := congrArg NilpotentLieFiltration.realification T.associated.symm
  let g' := D.filtration.realification.orbitEquivOfEq hD (fun _ : Unit => 1) g
  have hg' : T.filtration.associatedDegree.realification.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g' = 1 :=
    (D.filtration.realification.orbitEquivOfEq_eval hD _ g 0).trans hg
  have hlog' : g'.log = g.log := D.filtration.realification.orbitEquivOfEq_log hD _ g
  obtain ⟨u, hu0, huc, humap, hueval⟩ := exists_polynomialOrbit S B T.filtration hS g' hg'
    (fun j => by rw [hlog']; exact hcoeff j)
  let G := (filtration S T.filtration.rank_le_degree).associatedDegree.realification
  have hE : G = E.filtration.realification :=
    congrArg NilpotentLieFiltration.realification
      ((congrArg DegreeRankLieFiltration.associatedDegree hQ).symm.trans Q.associated)
  let u' := G.orbitEquivOfEq hE (fun _ : Unit => 1) u
  have hulog : u'.log = u.log := G.orbitEquivOfEq_log hE _ u
  have hueq (x : Unit → ℤ) :
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        G.polynomialOrbitEval (fun _ : Unit => 1) x u := G.orbitEquivOfEq_eval hE _ u x
  refine ⟨u', (hueq 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hulog] using huc
  · exact (congrArg _ hulog).trans (humap.trans hlog')
  · intro x
    rw [hueq]
    exact (hueval x).trans (D.filtration.realification.orbitEquivOfEq_eval hD _ g x)

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e : ℕ}
  (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
  (S : Fin s → Submodule ℚ (Fin 2 → L))
  (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
  (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
  (M : RationalFilteredNilmanifold (Algebra S r) s e) (Q : M.DegreeRankStructure r)
  (hQ : Q.filtration = filtration S T.filtration.rank_le_degree)

include Q hQ in
theorem exists_native_pair_orbit
    (a : Fin 2 → D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (ha : ∀ i, D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (a i) = 1)
    (hc : ∀ j : Fin s,
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => L)).symm
        (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) ∈ (S j).baseChange ℝ) :
    let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
    ∃ u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
        (generatorSpan S r j).baseChange ℝ) ∧
      ∀ i x, productProjectionHom (fun _ : Fin 2 => D) i
        (realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ
          (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
        D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i) := by
  intro φ
  let g := NilpotentLieFiltration.piRealOrbit (fun _ : Fin 2 => D.filtration) a
  have hg : (pi (fun _ : Fin 2 => D)).filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g = 1 := by
    apply (realBCHPiEquiv (fun _ : Fin 2 => D.filtration)).injective
    funext i
    change realificationMap
      (hnil := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (liePiEval i) _ = (1 : D.RealGroup)
    exact (NilpotentLieFiltration.piRealOrbit_eval (fun _ : Fin 2 => D.filtration) a 0 i).trans (ha i)
  have hcoeff (j : Fin s) : coefficients g.log (Finsupp.single () (j.val + 1)) ∈
      (S j).baseChange ℝ := by
    have heq : coefficients g.log (Finsupp.single () (j.val + 1)) =
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => L)).symm
          (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) := by
      apply (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => L)).injective
      rw [LinearEquiv.apply_symm_apply]
      funext i
      rw [realification_piRight_apply]
      exact NilpotentLieFiltration.piRealOrbit_coefficient (fun _ : Fin 2 => D.filtration) a _ i
    rw [heq]
    exact hc j
  obtain ⟨u, hu0, huc, _, hueval⟩ := exists_native_polynomialOrbit
    (pi (fun _ : Fin 2 => D)) (piRank (fun _ : Fin 2 => D) (fun _ => T))
    S B hS M Q hQ g hg hcoeff
  refine ⟨u, hu0, huc, ?_⟩
  intro i x
  rw [hueval]
  exact NilpotentLieFiltration.piRealOrbit_eval (fun _ : Fin 2 => D.filtration) a x i

variable {I : Type*} [Fintype I] {p q : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] Algebra S r)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra S r)] [T2Space (ℝ ⊗[ℚ] Algebra S r)]
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)
  (Z : M.UnitVerticalObservable (Q.realSubgroup s r) (I × I) q)

theorem native_pair_observable_eval
    (hobs : ∀ i z, Z.observable i (QuotientGroup.mk z) =
      V.pairedObservable T i (QuotientGroup.mk (realificationMap
        (hnil := M.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot)
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS) z)))
    (a : Fin 2 → D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hlift : ∀ i x, productProjectionHom (fun _ : Fin 2 => D) i
      (realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot)
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS)
        (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i))
    (i : I × I) (x : Unit → ℤ) :
    Z.observable i (QuotientGroup.mk
      (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
      V.observable i.1 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a 0))) *
      star (V.observable i.2 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a 1)))) := by
  rw [hobs]
  simp only [RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable,
    productProjection_mk, hlift]

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem alphabet_card_le {L : Type*} [LieRing L] [LieAlgebra ℚ L] [Module.Finite ℚ L]
    {s : ℕ} (S : Fin s → Submodule ℚ L) :
    Fintype.card (Alphabet S) ≤ s * finrank ℚ L := by
  change Fintype.card (Σ d : Fin s, Fin (finrank ℚ (S d))) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _d : Fin s, finrank ℚ L := Finset.sum_le_sum
      (fun d _ => by simpa only [Fintype.card_fin] using Submodule.finrank_le (S d))
    _ = _ := by simp

theorem exists_native_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L I : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (r d : ℕ) (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ L)
      (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (hS : ∀ j, S j ≤ T.filtration.layer (j.val + 1) 0)
      (p : ℝ), 0 ≤ p → T.ComplexityLE p →
      (∀ j a i, rationalLogHeight (D.basis.repr (B j a : L) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (T.realSubgroup s r) I p,
      ∃ E : RationalFilteredNilmanifold (Algebra S r) s (finrank ℚ (Algebra S r)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = filtration S T.filtration.rank_le_degree ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr
            (evaluation S B T.filtration hS (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS)) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) :=
             IsModuleTopology.isTopologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) I ((p + C) ^ C),
             V.frequency = U.frequency.comp (evaluation S B T.filtration hS).toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS) x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_unit_observable s
  let K₀ : Polynomial ℕ := Polynomial.C (s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ r d D T S B hS p hp hT hB U
  let : Module.Finite ℚ L := D.basis.finiteDimensional_of_finite
  let K := ((s + 1 : ℕ) : ℝ) * p + 1
  have hpK : p ≤ K := by dsimp only [K]; push_cast; nlinarith [show (0 : ℝ) ≤ s from Nat.cast_nonneg s]
  have hK : 0 ≤ K := hp.trans hpK
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hT.1.1
  have hcard : (Fintype.card (Alphabet S) : ℝ) ≤ K := by
    calc
      _ ≤ (s : ℝ) * finrank ℚ L := by exact_mod_cast alphabet_card_le S
      _ ≤ (s : ℝ) * p := mul_le_mul_of_nonneg_left hdim (Nat.cast_nonneg _)
      _ ≤ K := by dsimp only [K]; push_cast; nlinarith
  have hbound : (K + a) ^ a ≤ (p + C) ^ C := by
    simpa [K₀, K, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨E, Q, hQ, hQc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree (Alphabet S) L I r d T.filtration.rank_le_degree D T (weight S) (weight_pos S)
      (fun x => (B x.1 x.2).val) (fun x => hS x.1 (B x.1 x.2).property) K hK hcard
      (hT.mono T hpK) (fun x i => (hB x.1 x.2 i).trans hpK) (U.mono hpK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  exact ⟨E, Q, hQ, hQc.mono Q hbound, hcentral, ⟨frame.mono hbound⟩,
    (fun i j => (hmatrix i j).trans hbound), hlattice, V.mono hbound, hfreq, hobs⟩

end Erdos3.SubspaceFreeLift

end

end OAI

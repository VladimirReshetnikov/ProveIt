import OAI.Combinatorics.Progressions.Estimates.ControlledSingleRefilteredReconstruction

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem scalarAffinePolynomial_integer {σ : Type*} (a : ℤ) (shift : σ → ℤ) (i : σ) :
    scalarAffinePolynomial (a : ℚ) (fun j => (shift j : ℚ)) i ∈ integerCoefficientPolynomials σ := by
  exact (integerCoefficientPolynomials σ).add_mem (integerCoefficientPolynomials_C (shift i))
    ((integerCoefficientPolynomials σ).mul_mem (integerCoefficientPolynomials_C a)
      (integerCoefficientPolynomials_X i))

theorem scalarAffine_monomial_integer_coefficients {σ : Type*}
    (a : ℤ) (shift : σ → ℤ) (α β : σ →₀ ℕ) :
    ∃ z : ℤ, (MvPolynomial.aeval (R := ℚ)
      (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ))) (monomial β 1)).coeff α =
        (z : ℚ) := by
  apply (mem_integerCoefficientPolynomials_iff _).mp ?_ α
  apply integerPolynomialHom_preserves
    (MvPolynomial.aeval (R := ℚ) (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ))))
  · intro i
    simpa only [aeval_X] using scalarAffinePolynomial_integer a shift i
  · refine ⟨monomial β (1 : ℤ), ?_⟩
    simp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

noncomputable def scalarAffineAdaptedHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) :
    (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
  (F.polynomialOrbitCoordinates (fun _ => 1)).toMonoidHom.comp
    ((F.polynomialOrbitSubstitute (scalarAffinePolynomial r h) (scalarAffinePolynomial_support r h)).comp
      (F.polynomialOrbitCoordinates (fun _ => 1)).symm.toMonoidHom)

theorem scalarAffineAdaptedHom_coord {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ)
    (g : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.scalarAffineAdaptedHom r h g).coord : VectorPolynomial σ ℚ L) =
      weightedDilation (fun _ : σ => 1) r (translate h (g.coord : VectorPolynomial σ ℚ L)) := by
  change substitute (scalarAffinePolynomial r h) (g.coord : VectorPolynomial σ ℚ L) = _
  exact substitute_scalarAffinePolynomial r h _

theorem PolynomialSlowBound.scalarAffine {σ ι L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (T A : σ → ℝ)
    (hT : ∀ i, 0 < T i) (hA : ∀ i, 0 < A i) {M B : ℝ}
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ => 1) T M g) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (r : ℚ) (h : σ → ℚ)
    (hphysical : ∀ i, |(h i : ℝ)| + |(r : ℝ)| * A i ≤ B * T i) :
    F.PolynomialSlowBound b (fun _ => 1) A
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * B ^ s)
      (F.realification.scalarAffineAdaptedHom r h g) := by
  have hdegree : DegreeLE (fun _ : σ => 1) s (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :=
    (F.realification.adaptedBCHToOrbit (fun _ => 1) g).degreeLE
  change CoefficientBound (b.baseChange ℝ) A _
    ((F.realification.scalarAffineAdaptedHom r h g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  rw [scalarAffineAdaptedHom_coord]
  exact CoefficientBound.scalarAffine (b.baseChange ℝ) T A hT hA hg hM hB hdegree r h hphysical

theorem exists_scalarAffine_slow_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (p : ℝ),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      ∀ T A : σ → ℝ, (∀ i, 0 < T i) → (∀ i, 0 < A i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g →
      ∀ (r : ℚ) (h : σ → ℚ), (∀ i, |(h i : ℝ)| ≤ T i) →
      (∀ i, |(r : ℝ)| * A i ≤ T i) →
      F.PolynomialSlowBound b (fun _ => 1) A (Real.exp ((p + C) ^ C))
        (F.realification.scalarAffineAdaptedHom r h g) := by
  let P : Polynomial ℕ := Polynomial.C ((s + 1) * 2 ^ s) * (Polynomial.X + 1) ^ s +
    (Polynomial.X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ F b p hp hσ T A hT hA g hg r h hh hr
  have hbound := PolynomialSlowBound.scalarAffine F b T A hT hA g hg
    (Real.exp_nonneg _) (by norm_num : (1 : ℝ) ≤ 2) r h (fun i => by linarith [hh i, hr i])
  let K := ((s : ℝ) + 1) * (p + 1) ^ s * 2 ^ s
  have hK : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * 2 ^ s ≤ K := by
    dsimp [K]
    gcongr
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hcost : K + (p + 2) ^ a ≤ (p + C) ^ C := by
    simpa [P, K, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_assoc,
      mul_left_comm, mul_comm] using hbudget p hp
  apply F.polynomialSlowBound_mono b (fun _ => 1) A hA _ _ hbound
  calc
    ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp ((p + 2) ^ a) * 2 ^ s =
        (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * 2 ^ s) * Real.exp ((p + 2) ^ a) := by ring
    _ ≤ K * Real.exp ((p + 2) ^ a) := mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ ≤ Real.exp K * Real.exp ((p + 2) ^ a) := mul_le_mul_of_nonneg_right hKe (Real.exp_nonneg _)
    _ = Real.exp (K + (p + 2) ^ a) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hcost

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem polynomialRationalGrid_scalarAffine_integer {σ ι L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialRationalGrid b (fun _ : σ => 1) q g)
    (a : ℤ) (shift : σ → ℤ) :
    F.PolynomialRationalGrid b (fun _ : σ => 1) q
      (F.realification.scalarAffineAdaptedHom (a : ℚ) (fun i => (shift i : ℚ)) g) := by
  classical
  obtain ⟨u, hu⟩ := hg
  choose c hc using fun α β => scalarAffine_monomial_integer_coefficients a shift α β
  refine ⟨fun z => ∑ β ∈ (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).support,
    c z.1 β * u (β, z.2), ?_⟩
  funext z
  change ((∑ β ∈ (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).support,
    c z.1 β * u (β, z.2) : ℤ) : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.scalarAffineAdaptedHom (a : ℚ)
        (fun i => (shift i : ℚ)) g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [scalarAffineAdaptedHom_coord, ← substitute_scalarAffinePolynomial, coefficients_substitute]
  simp only [Int.cast_sum, Int.cast_mul, map_sum, Finsupp.finsetSum_apply,
    map_rat_smul, Finsupp.smul_apply, Rat.smul_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [hc z.1 β]
  have hβ := congrFun hu (β, z.2)
  change (u (β, z.2) : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) β) z.2 at hβ
  rw [hβ]
  push_cast
  ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem scalarAffineAdaptedHom_constant {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) (κ : F.Group) :
    F.scalarAffineAdaptedHom r h (F.adaptedConstantGroupHom (fun _ : σ => 1) κ) =
      F.adaptedConstantGroupHom (fun _ : σ => 1) κ := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change substitute (scalarAffinePolynomial r h) (monomial 0 κ.coord) = monomial 0 κ.coord
  simp [monomial]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_normalized_factorization (S : D.Niltest (fun _ : σ => 1))
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (κ : D.RealGroup)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
      ⟨⟨S.orbit.log, S.orbit.property⟩⟩)
    (r : ℚ) (h : σ → ℚ) :
    D.filtration.realification.scalarAffineAdaptedHom r h E *
      D.filtration.realification.scalarAffineAdaptedHom r h b *
      D.filtration.realification.scalarAffineAdaptedHom r h R *
      D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨(S.scalarAffinePullback r h).orbit.log, (S.scalarAffinePullback r h).orbit.property⟩⟩ := by
  have heq := congrArg (D.filtration.realification.scalarAffineAdaptedHom r h) hprod
  simp only [map_mul, NilpotentLieFiltration.scalarAffineAdaptedHom_constant] at heq
  refine heq.trans ?_
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [NilpotentLieFiltration.scalarAffineAdaptedHom_coord]
  exact (S.scalarAffinePullback_log r h).symm

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem scalarAffineAdaptedHom_value (r : ℚ) (h : σ → ℚ) (x : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialRealValueHom (fun _ : σ => 1) x
        (F.realification.scalarAffineAdaptedHom r h g) =
      F.adaptedPolynomialRealValueHom (fun _ : σ => 1)
        (fun i => (h i : ℝ) + (r : ℝ) * x i) g := by
  apply NilpotentLieBCHGroup.ext
  rw [adaptedPolynomialRealValueHom_coord, adaptedPolynomialRealValueHom_coord,
    scalarAffineAdaptedHom_coord, ← substitute_scalarAffinePolynomial, eval₂_substitute]
  apply congrArg (fun y : σ → ℝ => eval₂ y (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)))
  funext i
  simp [scalarAffinePolynomial]

theorem scalarAffineAdaptedHom_value_integer (r : ℚ) (h : σ → ℚ) (x y : σ → ℤ)
    (hxy : ∀ i, h i + r * (x i : ℚ) = (y i : ℚ))
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    F.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ))
        (F.realification.scalarAffineAdaptedHom r h g) =
      F.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (y i : ℝ)) g := by
  rw [scalarAffineAdaptedHom_value]
  have heq : (fun i => (h i : ℝ) + (r : ℝ) * (x i : ℝ)) = (fun i => (y i : ℝ)) := by
    funext i
    exact_mod_cast hxy i
  rw [heq]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_scalarAffine_factor_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      ∀ S : D.Niltest (fun _ : σ => 1), S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        ∀ T A : σ → ℝ, (∀ i, 0 < T i) → (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) T
            (Real.exp ((p + 2) ^ a)) E →
          ∀ (r : ℚ) (h : σ → ℚ), (∀ i, |(h i : ℝ)| ≤ T i) →
            (∀ i, |(r : ℝ)| * A i ≤ T i) →
            ∀ (x : σ → ℤ) (z : σ → ℝ) (r₀ : D.RealGroup) (δ : ℝ), 0 ≤ δ →
              (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, |z i| ≤ A i) →
              (∀ i, |(x i : ℝ) - z i| ≤ A i * δ) →
              (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
                (fun i => (x i : ℝ)) (D.filtration.realification.scalarAffineAdaptedHom r h R)) :
                  D.Space) = QuotientGroup.mk r₀ →
              ‖(S.scalarAffinePullback r h).eval x - S.observable (QuotientGroup.mk
                (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) z
                    (D.filtration.realification.scalarAffineAdaptedHom r h E) *
                  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ))
                    (D.filtration.realification.scalarAffineAdaptedHom r h b) * r₀))‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨u, _, hslow⟩ := NilpotentLieFiltration.exists_scalarAffine_slow_bound s a
  obtain ⟨v, _, hfreeze⟩ := exists_slow_factor_freezing s 1
  let P : Polynomial ℕ := (Polynomial.X + (Polynomial.X + Polynomial.C u) ^ u + Polynomial.C v) ^ v
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D p hp hσ S hS E b R κ hκ hprod T A hT hA hE r h hh hr x z r₀ δ hδ hx hz hxz hR
  let q := p + (p + u) ^ u
  have hpq : p ≤ q := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hq : 0 ≤ q := hp.trans hpq
  have hE' := hslow D.filtration D.basis p hp hσ T A hT hA E hE r h hh hr
  have hcost : (p + u) ^ u ≤ (q + 2) ^ (1 : ℕ) := by
    dsimp [q]
    rw [pow_one]
    linarith
  have hE'' := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
    (Real.exp_le_exp.mpr hcost) _ hE'
  have hS' : (S.scalarAffinePullback r h).ComplexityLE q :=
    (S.scalarAffinePullback_complexityLE r h q).mpr (hS.mono hpq)
  have hprod' := S.scalarAffinePullback_normalized_factorization E b R κ hprod r h
  have hbound := hfreeze D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) q hq (hσ.trans hpq)
    (S.scalarAffinePullback r h) hS'
    (D.filtration.realification.scalarAffineAdaptedHom r h E)
    (D.filtration.realification.scalarAffineAdaptedHom r h b)
    (D.filtration.realification.scalarAffineAdaptedHom r h R) κ hκ hprod' A hA hE''
    x z r₀ δ hδ hx hz hxz hR
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hδ
  simpa [P, q, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_periodic_scalarAffine_freezing (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∀ S : D.Niltest (fun _ : σ => 1), S.ComplexityLE p →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
          ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q R →
        ∀ T A : σ → ℝ, (∀ i, 0 < T i) → (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) T
            (Real.exp ((p + 2) ^ a)) E →
          ∀ (r : ℚ) (h : σ → ℚ), (∀ i, |(h i : ℝ)| ≤ T i) →
            (∀ i, |(r : ℝ)| * A i ≤ T i) →
            ∀ (x : σ → ℤ) (z : σ → ℝ) (y t : σ → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ i, h i + r * (x i : ℚ) = (y i : ℚ)) →
              (∀ i, (M : ℤ) ∣ y i - t i) →
              (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, |z i| ≤ A i) →
              (∀ i, |(x i : ℝ) - z i| ≤ A i * δ) →
              let r₀ := D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
                (fun i => (t i : ℝ)) R
              (D.basis.baseChange ℝ).equivFun r₀.coord ∈ realDenominatorGrid q ∧
              ‖(S.scalarAffinePullback r h).eval x - S.observable (QuotientGroup.mk
                (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) z
                    (D.filtration.realification.scalarAffineAdaptedHom r h E) *
                  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ))
                    (D.filtration.realification.scalarAffineAdaptedHom r h b) * r₀))‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨u, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨v, _, hfreeze⟩ := exists_scalarAffine_factor_freezing s a
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C u) ^ u +
    (Polynomial.X + Polynomial.C v) ^ v
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D p hp hD hσ q hq hqp
  have hcost : (p + u) ^ u + (p + v) ^ v ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hucost : (p + u) ^ u ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hcost
  have hvcost : (p + v) ^ v ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hcost
  obtain ⟨M, hM, hMb, hcoset⟩ := hperiod D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    p hp hD hσ q hq hqp
  refine ⟨M, hM, hMb.trans (Real.exp_le_exp.mpr hucost), ?_⟩
  intro S hS E b R κ hκ hprod hgrid T A hT hA hE r h hh hr x z y t δ hδ hxy hcongr hx hz hxz r₀
  have hR : (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1)
      (fun i => (x i : ℝ)) (D.filtration.realification.scalarAffineAdaptedHom r h R)) : D.Space) =
      QuotientGroup.mk r₀ := by
    rw [D.filtration.scalarAffineAdaptedHom_value_integer r h x y hxy]
    exact (hcoset R hgrid y t hcongr).1
  refine ⟨D.filtration.polynomialRationalGrid_value D.basis (fun _ : σ => 1) q R hgrid t, ?_⟩
  have hb := hfreeze D p hp hσ S hS E b R κ hκ hprod T A hT hA hE r h hh hr x z r₀ δ hδ hx hz hxz hR
  exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hvcost) hδ)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open scoped TensorProduct

namespace NilpotentLieFiltration

noncomputable def scalarAffineOrbitHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) :
    F.PolynomialOrbit (fun _ : σ => 1) →* F.PolynomialOrbit (fun _ : σ => 1) :=
  F.polynomialOrbitSubstitute (scalarAffinePolynomial r h) (scalarAffinePolynomial_support r h)

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

theorem FixedPositiveNiltestRealization.scalarAffine
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {child : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1)}
    {cost : ℝ} {f : (σ → ℤ) → ℂ}
    (h : D.FixedPositiveNiltestRealization child cost f) (a : ℤ) (shift : σ → ℤ) :
    D.FixedPositiveNiltestRealization
      (D.filtration.realification.scalarAffineOrbitHom (a : ℚ) (fun i => (shift i : ℚ)) child)
      cost (fun x => f (fun i => a * x i + shift i)) := by
  obtain ⟨U, hU, hunit, hcost, heval⟩ := h
  refine ⟨U.scalarAffinePullback (a : ℚ) (fun i => (shift i : ℚ)), ?_, hunit, hcost, ?_⟩
  · change D.filtration.realification.scalarAffineOrbitHom (a : ℚ) (fun i => (shift i : ℚ)) U.orbit = _
    rw [hU]
  · intro x
    rw [U.scalarAffinePullback_eval_integer]
    exact heval _

end RationalFilteredNilmanifold

end Erdos3

end

section

namespace Erdos3

namespace NilpotentLieFiltration

theorem scalarAffineOrbitHom_comp {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) :
    F.scalarAffineOrbitHom r₁ h₁ (F.scalarAffineOrbitHom r₀ h₀ g) =
      F.scalarAffineOrbitHom (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i) g := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial r₁ h₁)
      (VectorPolynomial.substitute (scalarAffinePolynomial r₀ h₀) g.log) =
    VectorPolynomial.substitute (scalarAffinePolynomial (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i)) g.log
  rw [VectorPolynomial.substitute_comp]
  simp only [scalarAffinePolynomial_comp]

end NilpotentLieFiltration

theorem commonStrideIndex_refinement_tower {σ : Type*} (u v w : σ → ℤ)
    {A B : ℕ} (hA : 0 < A) (hAB : A ∣ B)
    (huv : ∀ i, v i ≡ u i [ZMOD (A : ℤ)])
    (hvw : ∀ i, w i ≡ v i [ZMOD (B : ℤ)]) :
    commonStrideIndex u A w = fun i =>
      ((B / A : ℕ) : ℤ) * commonStrideIndex v B w i + commonStrideIndex u A v i := by
  have h := commonStrideIndex_of_refinement u v hA hAB huv (commonStrideIndex v B w)
  simpa only [commonStridePoint_index_of_modEq v B w hvw] using h

theorem residue_refinement_scale_tower {A B C : ℕ} (hAB : A ∣ B) (hBC : B ∣ C) :
    ((B / A : ℕ) : ℚ) * (C / B : ℕ) = (C / A : ℕ) := by
  exact_mod_cast (show B / A * (C / B) = C / A by
    rw [mul_comm]
    exact Nat.div_mul_div hBC hAB)

namespace NilpotentLieFiltration

theorem scalarAffineOrbitHom_refinement_tower {σ L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1))
    (u v w : σ → ℤ) {A B C : ℕ} (hA : 0 < A) (hAB : A ∣ B) (hBC : B ∣ C)
    (huv : ∀ i, v i ≡ u i [ZMOD (A : ℤ)])
    (hvw : ∀ i, w i ≡ v i [ZMOD (B : ℤ)]) :
    F.scalarAffineOrbitHom (C / B : ℕ) (fun i => (commonStrideIndex v B w i : ℚ))
      (F.scalarAffineOrbitHom (B / A : ℕ) (fun i => (commonStrideIndex u A v i : ℚ)) g) =
      F.scalarAffineOrbitHom (C / A : ℕ) (fun i => (commonStrideIndex u A w i : ℚ)) g := by
  rw [scalarAffineOrbitHom_comp, residue_refinement_scale_tower hAB hBC]
  have hshift : (fun i => ((B / A : ℕ) : ℚ) * (commonStrideIndex v B w i : ℚ) +
      (commonStrideIndex u A v i : ℚ)) = (fun i => (commonStrideIndex u A w i : ℚ)) := by
    funext i
    have h := congrFun (commonStrideIndex_refinement_tower u v w hA hAB huv hvw) i
    have hc := congrArg (fun z : ℤ => (z : ℚ)) h.symm
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hc
  rw [hshift]

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def FixedResidueDescent {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (V : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (b : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (child : V.filtration.realification.PolynomialOrbit w)
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∀ S : D.Niltest w, S.ComplexityLE p → S.UnitIntervalValued →
    (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
      ∀ x, S.observable (z • x) = S.observable x) →
    ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
      (κ : D.RealGroup), κ ∈ D.realLattice →
      E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ →
      D.filtration.PolynomialRationalGrid D.basis w q R →
      ∀ A : σ → ℝ, (∀ i, 0 < A i) →
        D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E →
        ∀ (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N H : σ → ℕ)
          (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]),
          (∀ i, (M * (M * P)).Coprime (J i)) →
          ∀ (δ ε : ℝ), 0 ≤ δ → ε < 1 / 2 →
          (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (H i : ℝ)) ≤ ε →
          let Q := comparableBoxPartitions N H hH hHN
          let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
            (fun _ => Nat.mul_pos hM hP) u
          let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
            (fun _ => Nat.mul_pos hM hP) u v hv
          let F : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u → ℂ :=
            residueBoxStrideValue S.eval u M
          let G : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v → ℂ :=
            residueBoxStrideValue S.eval u M
          ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
            0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
            ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
              ‖(𝔼 x, F x) - (𝔼 x, G x)‖ - 8 * ε - 2 * (Real.exp ((p + 2) ^ C) * δ) ≤
                ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue U.eval u M x) -
                  (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue U.eval u M x)‖

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

noncomputable def FixedAffineResidueDescent {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (V : RationalFilteredNilmanifold K t e)
    (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (p : ℝ) (q P : ℕ) (hP : 0 < P) (C a : ℕ) (cost : ℝ) : Prop :=
  ∀ (scale : ℤ) (shift : σ → ℤ),
    FixedResidueDescent D W V (fun _ : σ => 1)
      (D.filtration.realification.scalarAffineAdaptedHom (scale : ℚ) (fun i => (shift i : ℚ)) b)
      (V.filtration.realification.scalarAffineOrbitHom (scale : ℚ) (fun i => (shift i : ℚ)) child)
      p q P hP C a cost

end Erdos3.RationalFilteredNilmanifold

end

end OAI

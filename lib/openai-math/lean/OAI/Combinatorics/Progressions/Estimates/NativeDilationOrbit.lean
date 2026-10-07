import OAI.Combinatorics.Progressions.Linear.NativeDilationPairProjections

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realifiedDilationPairPolynomial_adapted (q : ℚ)
    (p : VectorPolynomial σ ℚ (F.ordinary.realification.dilationPairSubalgebra q))
    (hp : (F.realification.dilationPairMultidegree q).Adapted p) :
    (F.dilationPairMultidegree q).realification.Adapted
      (VectorPolynomial.map (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap p) := by
  intro a
  rw [coefficients_map]
  exact (F.realifiedDilationPairEquiv_symm_mem_multidegree q _ _).mpr (hp a)

noncomputable def realifiedDilationPairOrbit (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit) :
    (F.dilationPairMultidegree q).realification.PolynomialOrbit :=
  (F.dilationPairMultidegree q).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap
      (p.log (F.realification.dilationPairMultidegree q)))
    (F.realifiedDilationPairPolynomial_adapted q _ (p.adapted _))

theorem realifiedDilationPairOrbit_eval (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit) (x : σ → ℤ) :
    F.ordinary.realifiedDilationPairEquiv q
      (((F.dilationPairMultidegree q).realification.polynomialOrbitEval x
        (F.realifiedDilationPairOrbit q p)).coord) =
      ((F.realification.dilationPairMultidegree q).polynomialOrbitEval x p).coord := by
  change F.ordinary.realifiedDilationPairEquiv q
    (eval (fun j => (x j : ℚ)) (VectorPolynomial.map
      (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap
        (p.log (F.realification.dilationPairMultidegree q)))) = _
  rw [eval_map]
  exact (F.ordinary.realifiedDilationPairEquiv q).apply_symm_apply _

theorem realifiedDilationPairOrbit_zero (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit)
    (hp : (F.realification.dilationPairMultidegree q).polynomialOrbitEval 0 p = 1) :
    (F.dilationPairMultidegree q).realification.polynomialOrbitEval 0
      (F.realifiedDilationPairOrbit q p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (F.ordinary.realifiedDilationPairEquiv q).injective
  rw [F.realifiedDilationPairOrbit_eval, hp]
  exact (map_zero _).symm

theorem exists_real_normalized_dilationPair_orbit (q : ℤ)
    (p : F.realification.PolynomialOrbit) (a b : F.realification.Group)
    (hp0 : F.realification.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).realification.PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        let h := (F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x g
        F.ordinary.realDilationPairProjection (q : ℚ) 0 h =
          a⁻¹ * F.realification.polynomialOrbitEval (fun i => q * x i) p * b⁻¹ ∧
        F.ordinary.realDilationPairProjection (q : ℚ) 1 h =
          a⁻¹ * F.realification.polynomialOrbitEval x p * b⁻¹ := by
  obtain ⟨g, hg0, hg⟩ := F.realification.exists_normalized_dilationPair_orbit q p a b hp0
  refine ⟨F.realifiedDilationPairOrbit (q : ℚ) g,
    F.realifiedDilationPairOrbit_zero (q : ℚ) g hg0, ?_⟩
  intro x
  dsimp only
  have he (j : Fin 2) := F.ordinary.realDilationPairProjection_coord (q : ℚ) j
    ((F.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x
      (F.realifiedDilationPairOrbit (q : ℚ) g))
  simp only [F.realifiedDilationPairOrbit_eval, hg x] at he
  exact ⟨NilpotentLieBCHGroup.ext (he 0), NilpotentLieBCHGroup.ext (he 1)⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_native_dilation_orbit (q : ℤ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) s r)
    (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 h = 1 ∧
      ∀ x : σ → ℤ,
        (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection (q : ℚ) 0
          (E.filtration.realification.polynomialOrbitEval _ x h)) : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (fun i => q * x i) g) ∧
        (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection (q : ℚ) 1
          (E.filtration.realification.polynomialOrbitEval _ x h)) : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) := by
  let F := M.filtration.ordinary.dilationPairFiltration (q : ℚ)
  obtain ⟨h, hh0, hh⟩ := M.filtration.exists_real_normalized_dilationPair_orbit q g ε γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let hE := F.realification.orbitEquivOfEq hF (fun _ : σ => 1)
    ((M.filtration.dilationPairMultidegree (q : ℚ)).realification.toOrdinaryOrbit h)
  have hhE (x : σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x hE =
      (M.filtration.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x h :=
    F.realification.orbitEquivOfEq_eval hF _ _ x
  refine ⟨hE, (hhE 0).trans hh0, fun x => ?_⟩
  rw [hhE]
  constructor
  · rw [(hh x).1]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)
  · rw [(hh x).2]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

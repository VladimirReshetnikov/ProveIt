import OAI.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct NNReal

variable {L M σ X Ω J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [Fintype Ω] [Fintype J]
  {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

omit [Fintype Ω] in

theorem exists_marked_diagram_external_score_lift
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace E.Space]
    (K : ℝ≥0) (observable : X → D.RealGroup → ℂ)
    (hrecovery : ∀ x source, positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K
      (observable x) (D.markedTopQuotientDiagram E φ Q source).2
        (D.markedTopQuotientDiagram E φ Q source).1 = observable x source)
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked)
    (H : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ) (weight : X → ℂ)
    (externalAt : X → E.Space)
    (hexternal : ∀ a ∈ H, ∀ j, externalAt (physical a j) = QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval w (point a j) marked))
    {δ : ℝ}
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K (observable (physical a j))
        (externalAt (physical a j)) (QuotientGroup.mk
          (Q.filtration.realification.polynomialOrbitEval w (point a j) q)))).re) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
        observable (physical a j)
          (D.filtration.realification.polynomialOrbitEval w (point a j) g))).re := by
  obtain ⟨g, hg, hm, heval⟩ :=
    D.exists_marked_topQuotientOrbit_lift_externalFamily E φ hφ Q hQ QF hQF
      K observable hrecovery hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro a ha
  have hpoint (j : J) :
      positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K (observable (physical a j))
        (externalAt (physical a j)) (QuotientGroup.mk
          (Q.filtration.realification.polynomialOrbitEval w (point a j) q)) =
        observable (physical a j)
          (D.filtration.realification.polynomialOrbitEval w (point a j) g) := by
    rw [hexternal a ha j]
    simpa only [polynomialOrbitRealEval_integer] using
      heval (physical a j) (fun i => (point a j i : ℝ))
  simpa only [hpoint] using hscore a ha

theorem exists_marked_diagram_kernel_restored_score
    [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (L ⧸ D.filtration.layerIdeal (s + 1)))]
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace E.Space]
    (Lip : ℝ≥0) (observable : X → D.RealGroup → ℂ)
    (hrecovery : ∀ x source, positiveImageSlice (D.markedTopQuotientDiagram E φ Q) Lip
      (observable x) (D.markedTopQuotientDiagram E φ Q source).2
        (D.markedTopQuotientDiagram E φ Q source).1 = observable x source)
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked)
    (externalAt : X → E.Space) (T : X → Q.Niltest w)
    (hT : ∀ x, (T x).UnitIntervalValued)
    (hobs : ∀ x, (T x).observable = positiveImageSlice
      (D.markedTopQuotientDiagram E φ Q) Lip (observable x) (externalAt x))
    (K : Submodule ℚ (L ⧸ D.filtration.layerIdeal (s + 1)))
    (hK : K ≤ Q.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker (D.topQuotientMarkedMap E φ hφ).toLinearMap)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ) (weight : X → ℂ)
    (hexternal : ∀ a ∈ H, ∀ j, externalAt (physical a j) = QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval w (point a j) marked))
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight (physical a j)‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      (((T (physical a j)).kernelProjection K hK).withOrbit q).eval (point a j))).re) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
          observable (physical a j)
            (D.filtration.realification.polynomialOrbitEval w (point a j) g))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    Niltest.exists_external_kernelProjection_restored_orbit T hT K hK q
      outer H hH localLaw physical point (fun a j => weight (physical a j))
      hB hδ hweight hscore
  have hzk : z.coord ∈
      (LinearMap.ker (D.topQuotientMarkedMap E φ hφ).toLinearMap).baseChange ℝ :=
    Submodule.baseChange_mono ℝ hkernel hz
  have hzmark := (NilpotentLieBCHGroup.coord_mem_realificationKernel_iff
    (hnil := Q.filtration.lowerCentralSeries_eq_bot)
    (hM := QF.filtration.lowerCentralSeries_eq_bot)
    (D.topQuotientMarkedMap E φ hφ) z).mp hzk
  let q' := Q.filtration.realification.constantGroupOrbit w z * q
  have hmark' : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q' =
      E.topQuotientOrbit QF hQF marked :=
    (D.topQuotientMarkedOrbit_left_mul_of_map_eq_one E φ hφ Q hQ QF hQF q z hzmark).trans heq
  have hs' : ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      positiveImageSlice (D.markedTopQuotientDiagram E φ Q) Lip (observable (physical a j))
        (externalAt (physical a j)) (QuotientGroup.mk
          (Q.filtration.realification.polynomialOrbitEval w (point a j) q')))).re := by
    intro a ha
    simpa only [Niltest.withLeftTranslatedOrbit, Niltest.withOrbit_eval, hobs] using hs a ha
  obtain ⟨g, _, hgmark, hgscore⟩ :=
    D.exists_marked_diagram_external_score_lift E φ hφ Q hQ QF hQF
      Lip observable hrecovery hsurj q' marked hmark' H' localLaw physical point weight
      externalAt (fun a ha => hexternal a (hsub ha)) hs'
  exact ⟨g, hgmark, H', hsub, hpos, hmass, hgscore⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

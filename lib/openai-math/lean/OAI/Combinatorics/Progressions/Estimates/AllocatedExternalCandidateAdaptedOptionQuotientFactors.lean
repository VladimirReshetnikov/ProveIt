import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateFrozenNativeFactors
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
import OAI.Combinatorics.Progressions.Sampling.MarkedExternalKernelProjectionScoreRestoration

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t u : ℕ}
    (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0) {w : σ → ℕ}

theorem realQuotientPolynomialOrbit_mark
    (g : F.realification.PolynomialOrbit w) :
    map ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      (F.realQuotientPolynomialOrbit I hI g).log =
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log := by
  change map ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
    (map ((realificationLieHom (lieQuotientMap I)).toLinearMap.restrictScalars ℚ) g.log) = _
  apply coefficients.injective
  ext a
  simp only [coefficients_map]
  exact quotientInducedMark_real_mk I π hker (coefficients g.log a)

theorem exists_marked_quotient_orbit_lift
    (q : (F.quotientLie I hI).realification.PolynomialOrbit w) :
    ∃ g : F.realification.PolynomialOrbit w,
      F.realQuotientPolynomialOrbit I hI g = q ∧
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log =
        map ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
          q.log := by
  obtain ⟨g, hg⟩ := F.realQuotientPolynomialOrbit_surjective I hI q
  refine ⟨g, hg, ?_⟩
  rw [← hg]
  exact (F.realQuotientPolynomialOrbit_mark I hI π hker g).symm

theorem exists_prescribed_marked_quotient_orbit_lift
    (G : NilpotentLieFiltration M u)
    (q : (F.quotientLie I hI).realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmarked : map
      ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      q.log = marked.log) :
    ∃ g : F.realification.PolynomialOrbit w,
      F.realQuotientPolynomialOrbit I hI g = q ∧
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log = marked.log ∧
      (∀ z : σ → ℝ, F.realQuotientStepHom I hI
        (F.realification.polynomialOrbitRealEval w z g) =
          (F.quotientLie I hI).realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) π
          (F.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z marked := by
  obtain ⟨g, hq, hm⟩ := F.exists_marked_quotient_orbit_lift I hI π hker q
  have hformal := hm.trans hmarked
  refine ⟨g, hq, hformal, ?_, ?_⟩
  · intro z
    rw [← hq]
    exact (F.realQuotientPolynomialOrbit_realEval I hI g z).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom π (eval₂ z g.log) = eval₂ z marked.log
    rw [← hformal]
    exact (eval₂_map (realificationLieHom π).toLinearMap z g.log).symm

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQ : Q.filtration = D.filtration.quotientLie I hI) {w : σ → ℕ}

noncomputable def quotientOrbit (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit I hI g
  polynomialOrbitOfLog q.log (by rw [hQ]; exact q.adapted)

@[simp] theorem quotientOrbit_log (g : D.filtration.realification.PolynomialOrbit w) :
    (D.quotientOrbit I hI Q hQ g).log =
      VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
        g.log := rfl

theorem quotientOrbit_surjective :
    Function.Surjective (D.quotientOrbit I hI Q hQ (w := w)) := by
  intro q
  let q₀ : (D.filtration.quotientLie I hI).realification.PolynomialOrbit w :=
    polynomialOrbitOfLog q.log (by rw [← hQ]; exact q.adapted)
  obtain ⟨g, hg⟩ := D.filtration.realQuotientPolynomialOrbit_surjective I hI q₀
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  exact congrArg (fun p => p.log) hg

theorem quotientOrbit_eval (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.quotientOrbit I hI Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitEval w x g) := by
  exact D.filtration.realQuotientPolynomialOrbit_eval I hI g x

theorem quotientOrbit_realEval (g : D.filtration.realification.PolynomialOrbit w) (z : σ → ℝ) :
    Q.filtration.realification.polynomialOrbitRealEval w z (D.quotientOrbit I hI Q hQ g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitRealEval w z g) := by
  exact D.filtration.realQuotientPolynomialOrbit_realEval I hI g z

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t u d n : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (I : LieIdeal ℚ L) (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
    (hQ : Q.filtration = D.filtration.quotientLie I hI)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0) {w : σ → ℕ}

theorem quotientOrbit_mark (g : D.filtration.realification.PolynomialOrbit w) :
    map ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      (D.quotientOrbit I hI Q hQ g).log =
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log := by
  rw [D.quotientOrbit_log I hI Q hQ]
  apply coefficients.injective
  ext a
  simp only [coefficients_map]
  exact quotientInducedMark_real_mk I π hker (coefficients g.log a)

theorem exists_prescribed_marked_quotientOrbit_lift
    (G : NilpotentLieFiltration M u)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmarked : map
      ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      q.log = marked.log) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.quotientOrbit I hI Q hQ g = q ∧
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) π
          (D.filtration.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z marked := by
  obtain ⟨g, hq⟩ := D.quotientOrbit_surjective I hI Q hQ q
  have hformal : map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log =
      marked.log := by
    rw [← D.quotientOrbit_mark I hI Q hQ π hker g, hq]
    exact hmarked
  refine ⟨g, hq, hformal, ?_, ?_⟩
  · intro z
    rw [← hq]
    exact (D.quotientOrbit_realEval I hI Q hQ g z).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom π (eval₂ z g.log) = eval₂ z marked.log
    rw [← hformal]
    exact (eval₂_map (realificationLieHom π).toLinearMap z g.log).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ X Ω J : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] [Fintype Ω] [Fintype J]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {s t u d n : ℕ} (D : RationalFilteredNilmanifold L s d)
  (I : LieIdeal ℚ L) (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQ : Q.filtration = D.filtration.quotientLie I hI)

include hQ in

theorem exists_external_marked_quotient_restoration
    (G : NilpotentLieFiltration M u) (φ : L →ₗ⁅ℚ⁆ M)
    (hker : ∀ x ∈ I, φ x = 0) (htop : I.toSubmodule ≤ D.filtration.layer s)
    {w : σ → ℕ} (tests : X → D.Niltest w)
    (htests : ∀ x, (tests x).UnitIntervalValued)
    (quotientObservable : X → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup), quotientObservable x (QuotientGroup.mk
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g)) =
      ((tests x).kernelProjection I.toSubmodule htop).observable (QuotientGroup.mk g))
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmark : map ((realificationLieHom (quotientInducedMark I φ hker)).toLinearMap.restrictScalars ℚ)
      q.log = marked.log)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ) (weight : X → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight (physical a j)‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      quotientObservable (physical a j) (QuotientGroup.mk
        (Q.filtration.realification.polynomialOrbitEval w (point a j) q)))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
      (∀ x, ((tests x).withOrbit restored).observable = (tests x).observable ∧
        ((tests x).withOrbit restored).UnitIntervalValued ∧
        ∀ p, ((tests x).withOrbit restored).ComplexityLE p ↔ (tests x).ComplexityLE p) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
          ((tests (physical a j)).withOrbit restored).eval (point a j))).re := by
  obtain ⟨g, hg, hm, _, _⟩ :=
    D.exists_prescribed_marked_quotientOrbit_lift I hI Q hQ φ hker G q marked hmark
  have hpoint (x : X) (z : σ → ℤ) :
      quotientObservable x (QuotientGroup.mk
        (Q.filtration.realification.polynomialOrbitEval w z q)) =
      (((tests x).kernelProjection I.toSubmodule htop).withOrbit g).eval z := by
    rw [← hg, D.quotientOrbit_eval I hI Q hQ]
    exact hrecovery x _
  have hs : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      (((tests (physical a j)).kernelProjection I.toSubmodule htop).withOrbit g).eval
        (point a j))).re := by
    intro a ha
    simpa only [hpoint] using hscore a ha
  have hkernel : I.toSubmodule ≤ LinearMap.ker φ.toLinearMap := fun x hx => hker x hx
  obtain ⟨restored, hmarked, z, hz, hzmem, hzmap, htests', H', hsub, hpos, hmass, hfinal⟩ :=
    Niltest.exists_external_kernelProjection_prescribed_marked_orbit tests htests G φ
      I.toSubmodule htop hkernel g marked hm outer H hH localLaw physical point
      (fun a j => weight (physical a j)) hB hδ hweight hs
  refine ⟨restored, hmarked, ?_, H', hsub, hpos, hmass, hfinal⟩
  intro x
  exact ⟨(htests' x).1, (htests' x).2.2.2.1, (htests' x).2.2.2.2⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t dQ : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

def lieQuotient :
    AllocatedExternalLocalCandidate C Q Fmark (quotientInducedMark ideal φ hker) marked where
  orbit := D.quotientOrbit ideal hI Q hQ candidate.orbit
  mark_on_slice u hu := by
    rw [D.quotientOrbit_eval ideal hI Q hQ]
    have hcompose :
        realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.lowerCentralSeries_eq_bot) (quotientInducedMark ideal φ hker)
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal)
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) =
        realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit) := by
      apply NilpotentLieBCHGroup.ext
      exact quotientInducedMark_real_mk ideal φ hker _
    exact hcompose.trans (candidate.mark_on_slice u hu)

@[simp] theorem lieQuotient_orbit :
    (candidate.lieQuotient ideal hI Q hQ hker).orbit =
      D.quotientOrbit ideal hI Q hQ candidate.orbit := rfl

theorem lieQuotient_value (u : C.Variables → ℤ) :
    (candidate.lieQuotient ideal hI Q hQ hker).value u =
      (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal)
        (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) : Q.Space) := by
  unfold value
  rw [lieQuotient_orbit, D.quotientOrbit_eval ideal hI Q hQ]

theorem lieQuotient_score_eq
    (observable : (X → ℤ) → D.Space → ℂ) (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))
    (weight : (X → ℤ) → ℂ) :
    (candidate.lieQuotient ideal hI Q hQ hker).score descended weight =
      candidate.score observable weight := by
  unfold score
  simp only [value, lieQuotient_orbit, D.quotientOrbit_eval, hrecovery]

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold scoreThreshold)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

def lieQuotientProblem :
    AllocatedExternalCandidateProblem (E := Deck) A Q Fmark
      (quotientInducedMark ideal φ hker) marked
      descended weight cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).lieQuotient ideal hI Q hQ hker
  score z := by
    rw [(P.candidate z).lieQuotient_score_eq ideal hI Q hQ hker
      observable descended hrecovery weight]
    exact P.score z

@[simp] theorem lieQuotientProblem_productive :
    (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).productive = P.productive := rfl

theorem lieQuotientProblem_ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).ambientScore
      (D.quotientOrbit ideal hI Q hQ ambient) z points = P.ambientScore ambient z points := by
  unfold ambientScore
  simp only [lieQuotientProblem, D.quotientOrbit_eval, hrecovery]

theorem conclusion_of_lieQuotient
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨ambient, hquotient, hmark, _, _⟩ :=
    D.exists_prescribed_marked_quotientOrbit_lift ideal hI Q hQ φ hker
      Fmark lower.ambient marked lower.marked
  refine ⟨{
    ambient := ambient
    marked := hmark
    retained := lower.retained
    subset := lower.subset
    mass := lower.mass
    step := lower.step
    step_pos := lower.step_pos
    slice := lower.slice
    dense := lower.dense
    inside := lower.inside
    score := ?_
  }⟩
  intro z
  have he := P.lieQuotientProblem_ambientScore ideal hI Q hQ hker descended hrecovery
    ambient ⟨z.val, lower.subset z.property⟩ (lower.slice z).integerPoints
  rw [hquotient] at he
  exact (lower.score z).trans_eq he

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d dQ : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)

include hQ in

theorem quotientMap_mem_layer (j : ℕ) (x : L) (hx : x ∈ D.filtration.layer j) :
    lieQuotientMap ideal x ∈ Q.filtration.layer j := by
  rw [hQ]
  exact D.filtration.quotientLie_mem ideal hI hx

theorem quotientOrbit_polynomialCoordinates {σ : Type*} (w : σ → ℕ)
    (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.polynomialOrbitCoordinates w (D.quotientOrbit ideal hI Q hQ g) =
      D.filtration.realPolynomialGroupMap Q.filtration (lieQuotientMap ideal)
        (D.quotientMap_mem_layer ideal hI Q hQ) w
        (D.filtration.realification.polynomialOrbitCoordinates w g) := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [polynomialOrbitCoordinates_log, D.quotientOrbit_log,
    D.filtration.realPolynomialGroupMap_log, polynomialOrbitCoordinates_log]
  rfl

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t dQ : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)

namespace AllocatedExternalCandidateProblem

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked
      observable weight cost massThreshold scoreThreshold)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

theorem exists_withKeep_lieQuotientProblem_common_factors
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {α : Type*} [Fintype α] (e : Basis α ℚ L) (ω : α → ℕ)
    (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (ν : Fin dQ → ℕ)
    (hG : ∀ k, Q.filtration.layer k = Submodule.span ℚ (Q.basis '' {i | k ≤ ν i}))
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE (Q.basis.repr (lieQuotientMap ideal (e j)) i) H)
    {pProj q : ℝ} (hpProj : 0 ≤ pProj)
    (hsource : (Fintype.card α : ℝ) ≤ pProj) (htarget : (dQ : ℝ) ≤ pProj)
    (hH : (H : ℝ) ≤ Real.exp pProj)
    (den : ℕ) (hden : 0 < den) (hdenBound : (den : ℝ) ≤ Real.exp pProj)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hfactor : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors e ω hF
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ : {i // keep i} => 1)
          ((P.withKeep keep hkeep).candidate z).orbit)) :
    ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
      ∀ z : P.productive,
        Q.filtration.HasCommonRefilteredOrbitFactors Q.basis ν hG
          (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + q) denQ
          (W.map (D.filtration.associatedGradedMap Q.filtration (lieQuotientMap ideal)
            (D.quotientMap_mem_layer ideal hI Q hQ)))
          (Q.filtration.realification.polynomialOrbitCoordinates (fun _ : {i // keep i} => 1)
            (((P.withKeep keep hkeep).lieQuotientProblem ideal hI Q hQ hker
              descended hrecovery).candidate z).orbit) := by
  obtain ⟨denQ, hpositive, hbound, hdiv, htransport⟩ :=
    D.filtration.exists_common_refiltered_mapped_orbit_factors
      (σ := {i // keep i}) Q.filtration e ω hF Q.basis ν hG
      (lieQuotientMap ideal) (D.quotientMap_mem_layer ideal hI Q hQ)
      hentries hpProj hsource (by simpa only [Fintype.card_fin] using htarget)
      hH den hden hdenBound
  refine ⟨denQ, hpositive, hbound, hdiv, ?_⟩
  intro z
  change Q.filtration.HasCommonRefilteredOrbitFactors Q.basis ν hG
    (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + q) denQ
    (W.map (D.filtration.associatedGradedMap Q.filtration (lieQuotientMap ideal)
      (D.quotientMap_mem_layer ideal hI Q hQ)))
    (Q.filtration.realification.polynomialOrbitCoordinates (fun _ : {i // keep i} => 1)
      (D.quotientOrbit ideal hI Q hQ ((P.withKeep keep hkeep).candidate z).orbit))
  have ht := htransport _ (fun i => by exact_mod_cast A.sides_pos i.val) q W _ (hfactor z)
  exact Eq.mpr (congrArg
    (Q.filtration.HasCommonRefilteredOrbitFactors Q.basis ν hG
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + q) denQ
      (W.map (D.filtration.associatedGradedMap Q.filtration (lieQuotientMap ideal)
        (D.quotientMap_mem_layer ideal hI Q hQ))))
    (D.quotientOrbit_polynomialCoordinates ideal hI Q hQ
      (fun _ : {i // keep i} => 1) ((P.withKeep keep hkeep).candidate z).orbit)) ht

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))

include hQ in

theorem optionQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option Pivot, optionLieSpace L P i)
    (hx : x ∈ (optionProduct D partners).filtration.layer k) :
    optionMarkedLieMap (lieQuotientMap ideal) x ∈
      (optionProduct Q partners).filtration.layer k := by
  apply (mem_pi_layer (fun i => (optionFactors Q partners i).filtration) k _).mpr
  intro i
  cases i with
  | none =>
    exact D.quotientMap_mem_layer ideal hI Q hQ k (x none)
      ((mem_pi_layer (fun i => (optionFactors D partners i).filtration) k x).mp hx none)
  | some i =>
    exact (mem_pi_layer (fun i => (optionFactors D partners i).filtration) k x).mp hx (some i)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

theorem optionJoint_lieQuotient_log :
    ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.log =
      VectorPolynomial.map
        ((realificationLieHom (optionMarkedLieMap (L := P)
          (lieQuotientMap ideal))).toLinearMap.restrictScalars ℚ)
        (candidate.optionJoint partners partnerOrbit).orbit.log := by
  exact (optionMarkedLieMap_piRealOrbit_log D Q partners (lieQuotientMap ideal)
    (candidate.optionJointLocalOrbits partners partnerOrbit)
    ((candidate.lieQuotient ideal hI Q hQ hker).optionJointLocalOrbits partners partnerOrbit)
    (D.quotientOrbit_log ideal hI Q hQ candidate.orbit).symm (fun _ => rfl)).symm

attribute [local irreducible] NilpotentLieFiltration.realPolynomialGroupMap

theorem optionJoint_lieQuotient_polynomialCoordinates :
    (⟨⟨((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.log,
        ((candidate.lieQuotient ideal hI Q hQ hker).optionJoint partners partnerOrbit).orbit.property⟩⟩ :
      ((optionProduct Q partners).filtration.realification.adaptedPolynomialFiltration
        (fun _ : C.Variables => 1)).Group) =
      (optionProduct D partners).filtration.realPolynomialGroupMap
        (optionProduct Q partners).filtration
        (optionMarkedLieMap (L := P) (lieQuotientMap ideal))
        (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
        (fun _ : C.Variables => 1)
        ⟨⟨(candidate.optionJoint partners partnerOrbit).orbit.log,
          (candidate.optionJoint partners partnerOrbit).orbit.property⟩⟩ := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [realPolynomialGroupMap_log]
  exact candidate.optionJoint_lieQuotient_log ideal hI Q hQ hker partners partnerOrbit

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {Pivot : Type v} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    {s d : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold LG s d}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (partners : ∀ j, RationalFilteredNilmanifold (MG j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

variable (ideal : LieIdeal ℚ LG)
    (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (LG ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

def optionQuotient :=
  (P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).optionJoint
    partners partnerOrbit

@[simp] theorem optionQuotient_productive :
    (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).productive =
      P.productive := rfl

@[simp] theorem optionQuotient_chart (z : P.productive) :
    (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).chart z =
      P.chart z := rfl

theorem conclusion_of_optionQuotient {outputCost outputMass outputScore : ℝ}
    (result : (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  exact P.conclusion_of_lieQuotient ideal hI Q hQ hker descended hrecovery
    ((P.lieQuotientProblem ideal hI Q hQ hker descended hrecovery).conclusion_of_optionJoint
      partners partnerOrbit result)

theorem exists_withKeep_optionQuotient_common_factors
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {α κ γ : Type*} [Fintype α] [Fintype κ]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D partners).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (c : Basis κ ℚ (∀ i : Option Pivot, optionLieSpace (LG ⧸ ideal) MG i)) (ν : κ → ℕ)
    (hG : ∀ k, (optionProduct Q partners).filtration.layer k =
      Submodule.span ℚ (c '' {i | k ≤ ν i}))
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE
      (c.repr (optionMarkedLieMap (L := MG) (lieQuotientMap ideal) (e j)) i) H)
    {pProj q : ℝ} (hpProj : 0 ≤ pProj)
    (hsource : (Fintype.card α : ℝ) ≤ pProj)
    (htarget : (Fintype.card κ : ℝ) ≤ pProj)
    (hH : (H : ℝ) ≤ Real.exp pProj)
    (den : ℕ) (hden : 0 < den) (hdenBound : (den : ℝ) ≤ Real.exp pProj)
    (W : LieSubalgebra ℚ (optionProduct D partners).filtration.AssociatedGraded)
    (v : γ → (optionProduct D partners).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule
      ((optionProduct D partners).filtration.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hvH : ∀ a i, rationalLogHeight
      (((optionProduct D partners).filtration.associatedGradedBasis e ω hF).repr (v a) i) ≤ pProj)
    (hfactor : ∀ z : P.productive,
      (optionProduct D partners).filtration.HasCommonRefilteredOrbitFactors e ω hF
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
        ⟨⟨(((P.withKeep keep hkeep).optionJoint partners partnerOrbit).candidate z).orbit.log,
          (((P.withKeep keep hkeep).optionJoint partners partnerOrbit).candidate z).orbit.property⟩⟩) :
    let F₀ := (optionProduct D partners).filtration
    let FQ := (optionProduct Q partners).filtration
    let ψ := optionMarkedLieMap (L := MG) (lieQuotientMap ideal)
    let hψ := D.optionQuotientMap_mem_layer ideal hI Q hQ partners
    let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
    let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
    ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
      Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
      BasisGradedSubmodule (FQ.associatedGradedBasis c ν hG) ν V.toSubmodule ∧
      (∀ a i, rationalLogHeight ((FQ.associatedGradedBasis c ν hG).repr (vQ a) i) ≤
        (pProj + 2) ^ 4) ∧
      ∀ z : P.productive,
        FQ.HasCommonRefilteredOrbitFactors c ν hG
          (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + q) denQ V
          ⟨⟨(((P.withKeep keep hkeep).optionQuotient partners partnerOrbit ideal hI Q hQ hker
              descended hrecovery).candidate z).orbit.log,
            (((P.withKeep keep hkeep).optionQuotient partners partnerOrbit ideal hI Q hQ hker
              descended hrecovery).candidate z).orbit.property⟩⟩ := by
  dsimp only
  obtain ⟨denQ, hpositive, hbound, hdiv, htransport⟩ :=
    (optionProduct D partners).filtration.exists_common_refiltered_mapped_orbit_factors
      (σ := {i // keep i}) (optionProduct Q partners).filtration e ω hF c ν hG
      (optionMarkedLieMap (L := MG) (lieQuotientMap ideal))
      (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
      hentries hpProj hsource htarget hH den hden hdenBound
  obtain ⟨hspan, hgraded, hheight⟩ :=
    (optionProduct D partners).filtration.gradedImage_bounded_spanning
      (optionProduct Q partners).filtration
      (optionMarkedLieMap (L := MG) (lieQuotientMap ideal))
      (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)
      e ω hF c ν hG W v hv hW hpProj hsource hvH
      (fun i j => rationalLogHeight_le_of_height (hentries j i) hH)
  refine ⟨denQ, hpositive, hbound, hdiv, hspan, hgraded, hheight, ?_⟩
  intro z
  have ht := htransport _ (fun i => by exact_mod_cast A.sides_pos i.val) q W _ (hfactor z)
  have he := ((P.withKeep keep hkeep).candidate z).optionJoint_lieQuotient_polynomialCoordinates
    ideal hI Q hQ hker partners partnerOrbit
  exact Eq.mpr (congrArg
    ((optionProduct Q partners).filtration.HasCommonRefilteredOrbitFactors c ν hG
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + q) denQ
      (W.map ((optionProduct D partners).filtration.associatedGradedMap
        (optionProduct Q partners).filtration
        (optionMarkedLieMap (L := MG) (lieQuotientMap ideal))
        (D.optionQuotientMap_mem_layer ideal hI Q hQ partners)))) he) ht

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {Pivot : Type v} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    {s d : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold LG s d}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (partners : ∀ j, RationalFilteredNilmanifold (MG j) s (dp j))
    (partnerOrbit : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

variable (ideal : LieIdeal ℚ LG)
    (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    {dQ : ℕ} (Q : RationalFilteredNilmanifold (LG ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (hker : ∀ x ∈ ideal, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap ideal) g)) =
        observable x (QuotientGroup.mk g))

variable (adapted : (optionProduct Q partners).AdaptedModelData)

def adaptedOptionQuotient :=
  (P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).adaptedRebase adapted

theorem conclusion_of_adaptedOptionQuotient {outputCost outputMass outputScore : ℝ}
    (result : (P.adaptedOptionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery
      adapted).Conclusion outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) :=
  P.conclusion_of_optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery
    ((P.optionQuotient partners partnerOrbit ideal hI Q hQ hker descended hrecovery).conclusion_of_adaptedRebase adapted result)

theorem exists_withKeep_adaptedOptionQuotient_common_factors
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {α γ : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D partners).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    {H : ℕ} (hentries : ∀ i j, RationalHeightLE
      (adapted.basis.repr (optionMarkedLieMap (L := MG) (lieQuotientMap ideal) (e j)) i) H)
    {pProj q : ℝ} (hpProj : 0 ≤ pProj)
    (hsource : (Fintype.card α : ℝ) ≤ pProj)
    (htarget : (finrank ℚ (∀ i : Option Pivot, optionLieSpace (LG ⧸ ideal) MG i) : ℝ) ≤ pProj)
    (hH : (H : ℝ) ≤ Real.exp pProj)
    (den : ℕ) (hden : 0 < den) (hdenBound : (den : ℝ) ≤ Real.exp pProj)
    (W : LieSubalgebra ℚ (optionProduct D partners).filtration.AssociatedGraded)
    (v : γ → (optionProduct D partners).filtration.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule
      ((optionProduct D partners).filtration.associatedGradedBasis e ω hF) ω W.toSubmodule)
    (hvH : ∀ a i, rationalLogHeight
      (((optionProduct D partners).filtration.associatedGradedBasis e ω hF).repr (v a) i) ≤ pProj)
    (hfactor : ∀ z : P.productive,
      (optionProduct D partners).filtration.HasCommonRefilteredOrbitFactors e ω hF
        (fun i : {i // keep i} => (A.sides i.val : ℝ)) q den W
        ⟨⟨(((P.withKeep keep hkeep).optionJoint partners partnerOrbit).candidate z).orbit.log,
          (((P.withKeep keep hkeep).optionJoint partners partnerOrbit).candidate z).orbit.property⟩⟩) :
    let F₀ := (optionProduct D partners).filtration
    let FQ := adapted.model.filtration
    let ψ := optionMarkedLieMap (L := MG) (lieQuotientMap ideal)
    let hψ := D.optionQuotientMap_mem_layer ideal hI Q hQ partners
    let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
    let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
    ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
      Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
      BasisGradedSubmodule (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers) adapted.weight V.toSubmodule ∧
      (∀ a i, rationalLogHeight ((FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers).repr (vQ a) i) ≤
        (pProj + 2) ^ 4) ∧
      ∀ z : P.productive,
        FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
          (fun i : {i // keep i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + q) denQ V
          ⟨⟨(((P.withKeep keep hkeep).adaptedOptionQuotient partners partnerOrbit ideal hI Q hQ hker
              descended hrecovery adapted).candidate z).orbit.log,
            (((P.withKeep keep hkeep).adaptedOptionQuotient partners partnerOrbit ideal hI Q hQ hker
              descended hrecovery adapted).candidate z).orbit.property⟩⟩ := by
  exact P.exists_withKeep_optionQuotient_common_factors partners partnerOrbit ideal hI Q hQ hker
    descended hrecovery keep hkeep e ω hF adapted.basis adapted.weight adapted.layers hentries
    hpProj hsource (by simpa only [Fintype.card_fin] using htarget) hH den hden hdenBound
    W v hv hW hvH hfactor

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI

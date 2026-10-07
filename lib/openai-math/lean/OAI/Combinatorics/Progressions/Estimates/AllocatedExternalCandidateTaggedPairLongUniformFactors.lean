import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateAxisChartOrbit

namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem retainedLength_of_densityBudget {densityBudget p : ℝ}
    (hdense : IsDenseCommonStrideBox
      (fun i : C.Variables => A.sides i.val) densityBudget C.slice.integerPoints)
    (hbudget : densityBudget ≤ p) (i : C.Variables) :
    Real.exp (-p) * (A.sides i.val : ℝ) ≤ C.slice.length i :=
  (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbudget))
    (Nat.cast_nonneg (A.sides i.val))).trans
      (C.slice.length_lower_of_dense C.step_pos hdense i)

end AllocatedExternalLocalChart

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hretained : ∀ i : C.Variables,
      Real.exp (-p) * (A.sides i.val : ℝ) ≤ C.slice.length i)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

def ofCandidate_of_retainedLength
    (hcorr : Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (C.physical t.val)) *
          (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p where
  twist := twist
  c := C.centerLift
  a := C.path.1.val
  v := C.path.2.val
  hv := by
    change C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  sample := C.sample
  read := C.read
  hread := C.recovered
  fixed := C.fixed
  hfixed := C.fixed_in_box
  q := C.step
  Q := C.slice
  hq := C.step_pos
  hlen := C.slice.length_pos_of_dense C.dense
  hQ := hretained
  V := reference.withOrbit candidate.orbit
  W := partner.integerChartPullback (fun _ : C.Variables => 1) C.integerChart C.integerChart_support
  hp := hp
  hperiod := hperiod
  hvariationBound := hvariation
  hV := hV
  hW := hW
  hWnorm := hWnorm
  η := η
  θ := θ
  hηheight := hηheight
  hθheight := hθheight
  hη := hη
  hθ := hθ
  hK := hK
  hbias := by
    change Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (integerSampledSpatial C.integerChart t.val)) *
          ((reference.withOrbit candidate.orbit).eval t.val *
            (partner.integerChartPullback (fun _ : C.Variables => 1)
              C.integerChart C.integerChart_support).eval t.val))‖
    simp only [C.integerChart_spatial, Niltest.integerChartPullback_eval,
      Niltest.withOrbit_eval]
    exact hcorr

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

local notation "candidateInput" => ofCandidate_of_retainedLength A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  C candidate reference partner twist hp hretained hperiod hvariation hV hW hWnorm
  η θ hηheight hθheight hη hθ hK hcorr

@[simp] theorem ofCandidate_of_retainedLength_V_orbit :
    (candidateInput).V.orbit = candidate.orbit := rfl

@[simp] theorem ofCandidate_of_retainedLength_W_orbit :
    (candidateInput).W.orbit =
      (partner.integerChartPullback (fun _ : C.Variables => 1)
        C.integerChart C.integerChart_support).orbit := rfl

def ofCandidate_of_retainedLength_of_localLaw
    (hcorr : Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
      star (twist.eval N poly (A.physical C.path site)) *
        (reference.observable (candidate.value (C.retainedParameter site.val)) *
          partner.eval (fullTaggedPhysicalIntegerPoint J poly
            (fun j => (C.centerLift j).val) (A.physical C.path site))))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p := by
  apply ofCandidate_of_retainedLength A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall C candidate
    reference partner twist hp hretained hperiod hvariation hV hW hWnorm
    η θ hηheight hθheight hη hθ hK
  have he := C.localLaw_complexMean_eq_fullSliceLaw (fun x =>
    star (twist.eval N poly (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter x)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))))
  change Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
    star (twist.eval N poly (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter site.val)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val)))))‖ at hcorr
  rw [he] at hcorr
  have hf : (fun t : integerBox (fun i : C.Variables => A.sides i.val) =>
      star (twist.eval N poly (C.physical t.val)) *
        (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val))) =
      (fun t => star (twist.eval N poly
        (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))) *
          (reference.observable (candidate.value (C.retainedParameter (C.parameter t.val))) *
            partner.eval (fullTaggedPhysicalIntegerPoint J poly
              (fun j => (C.centerLift j).val)
              (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))))) := by
    funext t
    rw [C.retainedParameter_parameter,
      C.chartValues_eq_physicalIntegerPoint hσ1 Cgeo hCgeo hchart hsmall hpoly t.val t.property]
    rfl
  rw [hf]
  exact hcorr

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

theorem exists_long_pair_inputs
    (keepLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, keepLong i → keep i) :
    ∃ input : ∀ _a : Ω, ∀ j : Pivot,
        AllocatedFrozenTaggedPairInput F.context Deck keepLong D (E j) p,
      ∀ a j, (input a j).η = F.η j ∧ (input a j).θ = F.θ j ∧
        ∀ (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ
            (PairAlgebra LG (MG j)))
          (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
          (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
            Submodule.span ℚ (c '' {i | k ≤ w i})),
          pairOrbitSymbol D (E j) (input a j).V.orbit (input a j).W.orbit c w hc =
            pairOrbitSymbol D (E j)
              ((F.candidate a).axisOrbit keepLong (fun _ => 0))
              ((E j).filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
                ((F.chart a).axisPolynomial keepLong (fun _ => 0))
                ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))
                (F.jointOrbit a (some j))) c w hc := by
  classical
  have hKlong : (Fintype.card {i // keepLong i} : ℝ) ≤ p := by
    have hcard : Fintype.card {i // keepLong i} ≤ Fintype.card {i // keep i} :=
      Fintype.card_le_of_injective
        (fun i : {i // keepLong i} => (⟨i.val, hsub i.val i.property⟩ : {i // keep i}))
        (fun i j h => Subtype.ext
          (congrArg (fun k : {i // keep i} => k.val) h))
    exact (Nat.cast_le.mpr hcard).trans F.hK
  suffices hsingle : ∀ a : Ω, ∀ j : Pivot,
      ∃ input : AllocatedFrozenTaggedPairInput F.context Deck keepLong D (E j) p,
        input.η = F.η j ∧ input.θ = F.θ j ∧
          ∀ (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ
              (PairAlgebra LG (MG j)))
            (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
            (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
              Submodule.span ℚ (c '' {i | k ≤ w i})),
            pairOrbitSymbol D (E j) input.V.orbit input.W.orbit c w hc =
              pairOrbitSymbol D (E j)
                ((F.candidate a).axisOrbit keepLong (fun _ => 0))
                ((E j).filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
                  ((F.chart a).axisPolynomial keepLong (fun _ => 0))
                  ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))
                  (F.jointOrbit a (some j))) c w hc by
    choose input hinput using hsingle
    exact ⟨input, hinput⟩
  intro a j
  let C := F.chart a
  let candidate := F.candidate a
  have hkeep : ∀ i, keepLong i → C.keep i := hsub
  let test : A.Site → D.Space → ℂ := fun site x =>
    star ((F.twist a j).eval N poly (A.physical C.path site)) *
      ((F.reference a j).observable x *
        (F.selected j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => (C.centerLift k).val) (A.physical C.path site)))
  have hstart : Real.exp (-p) ≤
      ‖C.localLaw.complexMean (fun site => test site (candidate.siteValue site))‖ := by
    change Real.exp (-p) ≤ ‖(F.chart a).localLaw.complexMean _‖
    rw [F.chart_localLaw]
    exact F.hcorr a j
  obtain ⟨fixed, hfixed, hfiber⟩ :=
    candidate.exists_restrictAxes_site_norm keepLong hkeep test
  let C' := C.restrictAxes keepLong hkeep fixed hfixed
  let candidate' := candidate.restrictAxes keepLong hkeep fixed hfixed
  have hcorr : Real.exp (-p) ≤ ‖C'.localLaw.complexMean (fun site =>
      star ((F.twist a j).eval N poly (A.physical C'.path site)) *
        ((F.reference a j).observable (candidate'.value (C'.retainedParameter site.val)) *
          (F.selected j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => (C'.centerLift k).val) (A.physical C'.path site))))‖ :=
    hstart.trans hfiber
  let input := AllocatedFrozenTaggedPairInput.ofCandidate_of_retainedLength_of_localLaw A
    F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    C' candidate' (F.reference a j) (F.selected j) (F.twist a j)
    F.hp (C'.retainedLength_of_densityBudget C'.dense F.hcost)
    (F.hperiod a j) F.hvariation (F.hV a j) (F.hW j) (F.hWnorm j)
    (F.η j) (F.θ j) (F.hηheight j) (F.hθheight j) (F.hη a j) (F.hθ j) hKlong hcorr
  refine ⟨input, rfl, rfl, ?_⟩
  intro c w hc
  change pairOrbitSymbol D (E j) (candidate.axisOrbit keepLong fixed)
    ((F.selected j).integerChartPullback (fun _ => 1)
      C'.integerChart C'.integerChart_support).orbit c w hc = _
  rw [(F.selected j).integerChartPullback_orbit_eq_of_orbit_eq (fun _ => 1)
    C'.integerChart C'.integerChart_support (F.ambient j) (F.selected_orbit j)]
  simp only [Niltest.integerChartPullback_orbit]
  rw [C.restrictAxes_polynomialOrbitRealChart keepLong hkeep fixed hfixed
    (E j).filtration (F.ambient j).orbit]
  exact candidate.pairOrbitSymbol_axisOrbit_independent (E j) keepLong fixed (fun _ => 0)
    (F.jointOrbit a (some j)) c w hc

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω}

def LongCommonFactors
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
    (keepLong : LayerSamplerVariables G I n B → Prop)
    (outer : FiniteProbabilityWeights Ω)
    {α : Type*} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D E).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i})) (q : ℝ) : Prop :=
  ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
    (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
    (den : ℕ) (H' : Finset Ω),
    H' ⊆ H ∧ 0 < outer.mass H' ∧
    Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
      ω W.toSubmodule ∧
    (∀ i k, rationalLogHeight
      (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
    (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional ((pairFrequency (F.η j) (F.θ j)).comp
        (optionPairProjection j).toLinearMap) x = 0) ∧
    0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
    ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
      e ω hF (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) q den W
      ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration)
          (F.extendedLongJointOrbit keepLong a)).log,
        (piRealOrbit (fun i => (optionFactors D E i).filtration)
          (F.extendedLongJointOrbit keepLong a)).property⟩⟩

theorem exists_long_common_factors (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ (outer : FiniteProbabilityWeights Ω), 0 < outer.mass H →
    ∀ (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
      (keepLong : LayerSamplerVariables G I n B → Prop)
      (_hsub : ∀ i, keepLong i → keep i)
      [Nonempty {i // keepLong i}], (Fintype.card {i // keepLong i} : ℝ) ≤ bnd →
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.LongCommonFactors keepLong outer e ω hF q := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedFrozenTaggedFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he localCost r P outer hH F keepLong hsub _ hkeep hlong hcommonLong
  obtain ⟨input, hinput⟩ := F.exists_long_pair_inputs keepLong hsub
  have hresult := hcommon D E hpGeo F.hp hbnd hGeo hpGeoB hInvB hα hPivot
    e ω hF hstructure he B F.context Deck keepLong hkeep
    hlong hcommonLong outer H hH (F.extendedLongJointOrbit keepLong) F.η F.θ input
    (fun a j c w hc => by
      rw [F.extendedLongJointOrbit_mem keepLong a.val a.property]
      exact (hinput a j).2.2 c w hc)
    (fun a j => (hinput a j).1) (fun a j => (hinput a j).2.1)
  exact hresult

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

theorem exists_allocatedExternalCandidateTaggedPairFamily_long_common_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C Cbasis K T : ℕ, 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

    {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Ω] [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    {H : Finset Ω},
    ∀ {α : Type*} [Fintype α] {pGeo bnd : ℝ},
      0 ≤ pGeo → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ (outer : FiniteProbabilityWeights Ω), 0 < outer.mass H →
    ∀ (F : AllocatedExternalCandidateTaggedPairFamily A Deck {a // a ∈ H} Pivot
      D E Fmark φ marked keep cost p periodCap coverCap Lip)
      (keepLong : LayerSamplerVariables G I n B → Prop)
      (_hsub : ∀ i, keepLong i → keep i)
      [Nonempty {i // keepLong i}], (Fintype.card {i // keepLong i} : ℝ) ≤ bnd →
      (∀ i : {i // keepLong i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keepLong i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      F.LongCommonFactors keepLong outer e ω hF q := by
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hcommon⟩ :=
    exists_allocatedFrozenTaggedFamily_common_factors s hs
  refine ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Ω Pivot _ _ LG LM MG _ _ _ _ _ _ _ _ _ _ _ _ _ _ d₀ t d D E Fmark φ marked
    keep cost p periodCap coverCap Lip H
    α _ pGeo bnd hpGeo hbnd hGeo hpGeoB hInvB hα hPivot e ω hF
    hstructure he localCost r P outer hH F keepLong hsub _ hkeep hlong hcommonLong
  obtain ⟨input, hinput⟩ := F.exists_long_pair_inputs keepLong hsub
  have hresult := hcommon D E hpGeo F.hp hbnd hGeo hpGeoB hInvB hα hPivot
    e ω hF hstructure he B F.context Deck keepLong hkeep
    hlong hcommonLong outer H hH (F.extendedLongJointOrbit keepLong) F.η F.θ input
    (fun a j c w hc => by
      rw [F.extendedLongJointOrbit_mem keepLong a.val a.property]
      exact (hinput a j).2.2 c w hc)
    (fun a j => (hinput a j).1) (fun a j => (hinput a j).2.1)
  exact hresult

end Erdos3.VectorPolynomial

end

end OAI

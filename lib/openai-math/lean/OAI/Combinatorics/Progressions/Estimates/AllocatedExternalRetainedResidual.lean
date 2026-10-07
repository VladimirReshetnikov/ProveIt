/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw

namespace OAI


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

noncomputable def sliceTest : D.Niltest (fun _ : C.Variables => 1) :=
  (reference.withOrbit candidate.orbit).scalarAffinePullback
    (C.step : ℚ) (fun i => (C.slice.start i : ℚ))

@[simp] theorem sliceTest_normBound :
    (candidate.sliceTest reference).normBound = reference.normBound := rfl

@[simp] theorem sliceTest_lipBound :
    (candidate.sliceTest reference).lipBound = reference.lipBound := rfl

@[simp] theorem sliceTest_observable :
    (candidate.sliceTest reference).observable = reference.observable := rfl

@[simp] theorem sliceTest_complexity (p : ℝ) :
    (candidate.sliceTest reference).ComplexityLE p ↔ reference.ComplexityLE p := Iff.rfl

theorem sliceTest_eval (j : C.Variables → ℤ) :
    (candidate.sliceTest reference).eval j =
      reference.observable (candidate.value
        (commonStridePoint (fun i => (C.slice.start i : ℤ)) C.step j)) := by
  have h := (reference.withOrbit candidate.orbit).scalarAffinePullback_eval_integer
    (C.step : ℤ) (fun i => (C.slice.start i : ℤ)) j
  have hpoint : (fun i => (C.step : ℤ) * j i + (C.slice.start i : ℤ)) =
      commonStridePoint (fun i => (C.slice.start i : ℤ)) C.step j := by
    funext i
    exact add_comm _ _
  rw [hpoint] at h
  simpa only [sliceTest, Int.cast_natCast, RationalFilteredNilmanifold.Niltest.withOrbit_eval,
    value] using h

theorem sliceTest_eval_on_slice (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    (candidate.sliceTest reference).eval
      (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u) =
      reference.observable (candidate.value u) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
  rw [C.slice_index, candidate.sliceTest_eval, ← C.slice.integerPoint_eq]

theorem sliceTest_correlation (signal : (X → ℤ) → ℂ) :
    (𝔼 u ∈ C.slice.integerPoints, signal (C.physical u) *
      star ((candidate.sliceTest reference).eval
        (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u))) =
    𝔼 u ∈ C.slice.integerPoints, signal (C.physical u) *
      star (reference.observable (candidate.value u)) := by
  apply Finset.expect_congr rfl
  intro u hu
  rw [candidate.sliceTest_eval_on_slice reference u hu]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

local instance candidateVariableDecidableEq : DecidableEq C.Variables := Subtype.instDecidableEq

noncomputable def normalizedSlicePacket {p : ℝ} (hreference : reference.ComplexityLE p) :
    LocalMajorSliceTest D (fun i : C.Variables => A.sides i.val) cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice
  dense := by
    have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
      Subsingleton.elim _ _
    rw [he]
    exact C.dense
  test := (candidate.sliceTest reference).conjugate.expNormalize p
  norm := by
    exact_mod_cast ((candidate.sliceTest reference).conjugate.expNormalize_norm hreference)
  complexity := (candidate.sliceTest reference).conjugate.expNormalize_complexity hreference

theorem normalizedSlicePacket_weight {p : ℝ} (hreference : reference.ComplexityLE p)
    (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    (candidate.normalizedSlicePacket reference hreference).weight u =
      (Real.exp (-p) : ℂ) * reference.observable (candidate.value u) := by
  have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hu' : u ∈ @ResidueBoxSlice.integerPoints C.Variables _ _ _ (Classical.decEq _) C.slice := by
    rw [← he]
    exact hu
  change star (((candidate.sliceTest reference).conjugate.expNormalize p).eval
    (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u)) = _
  rw [RationalFilteredNilmanifold.Niltest.expNormalize_eval,
    RationalFilteredNilmanifold.Niltest.eval_conjugate,
    candidate.sliceTest_eval_on_slice reference u hu', star_mul, star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

end AllocatedExternalLocalCandidate

namespace AllocatedExternalLocalChart
variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

noncomputable def fixedNatural (i : LayerSamplerVariables G I n B) : ℕ :=
  if hi : C.keep i then 0 else (C.fixed ⟨i, hi⟩).toNat

theorem fixedNatural_lt (i : LayerSamplerVariables G I n B) (hi : ¬C.keep i) :
    C.fixedNatural i < A.sides i := by
  simp only [fixedNatural, dite_eq_right hi]
  have h := C.fixed_in_box ⟨i, hi⟩
  have he : ((C.fixed ⟨i, hi⟩).toNat : ℤ) = C.fixed ⟨i, hi⟩ :=
    Int.toNat_of_nonneg h.1
  exact_mod_cast (show ((C.fixed ⟨i, hi⟩).toNat : ℤ) < (A.sides i : ℤ) by
    rw [he]
    exact h.2)

theorem frozenLongExtension_fixedNatural (u : C.Variables → ℤ) :
    frozenLongExtension C.keep C.fixedNatural u = C.parameter u := by
  funext i
  by_cases hi : C.keep i
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, dite_eq_left hi]
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, fixedNatural, dite_eq_right hi]
    exact Int.toNat_of_nonneg (C.fixed_in_box ⟨i, hi⟩).1

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

attribute [local instance] candidateVariableDecidableEq

noncomputable def admissibleFullPacket {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost) :
    LocalMajorSliceTest D A.sides cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
  dense := by
    have h := (candidate.normalizedSlicePacket reference hreference).slice.freezeShort_dense
      C.keep C.fixedNatural C.fixedNatural_lt C.step_pos
      (candidate.normalizedSlicePacket reference hreference).dense
      (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
    simpa only [Real.log_exp, max_self, normalizedSlicePacket] using h
  test := (candidate.normalizedSlicePacket reference hreference).test.liftLong C.keep
  norm := (candidate.normalizedSlicePacket reference hreference).norm
  complexity := (candidate.normalizedSlicePacket reference hreference).complexity

theorem admissibleFullPacket_expect {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (signal : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
      signal site.val * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      (Real.exp (-p) : ℂ) * C.localLaw.complexMean
        (fun site => signal site.val * reference.observable (candidate.siteValue site)) := by
  let short := candidate.normalizedSlicePacket reference hreference
  let full := short.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
  have hmean := short.expect_freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩) signal
  have hleft :
      (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
        signal site.val * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      𝔼 u ∈ C.slice.integerPoints,
        signal (C.parameter u) * short.weight u := by
    rw [(candidate.admissibleFullPacket reference hreference hcost hshort).slice.expect_subtypeSites
      (fun x => signal x * (candidate.admissibleFullPacket reference hreference hcost hshort).weight x)]
    simpa only [admissibleFullPacket, full, short, Real.log_exp, max_self,
      C.frozenLongExtension_fixedNatural, normalizedSlicePacket,
      LocalMajorSliceTest.freezeShort, LocalMajorSliceTest.weight] using hmean
  rw [hleft]
  change _ = (Real.exp (-p) : ℂ) * C.localLaw.complexMean
    (fun site => signal site.val * reference.observable (candidate.value (C.retainedParameter site.val)))
  rw [C.localLaw_complexMean_parameter
    (fun x => signal x * reference.observable (candidate.value (C.retainedParameter x)))]
  rw [Finset.mul_expect]
  have he : candidateVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hpoints := congrArg
    (fun dec : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables _ _ _ dec C.slice) he
  rw [hpoints]
  apply Finset.expect_congr rfl
  intro u hu
  have hu' : u ∈ C.slice.integerPoints := by
    rw [hpoints]
    exact hu
  rw [candidate.normalizedSlicePacket_weight reference hreference u hu']
  change signal (C.parameter u) * ((Real.exp (-p) : ℂ) * reference.observable (candidate.value u)) =
    (Real.exp (-p) : ℂ) * (signal (C.parameter u) *
      reference.observable (candidate.value (C.retainedParameter (C.parameter u))))
  rw [C.retainedParameter_parameter]
  ring

theorem admissibleFullPacket_site_expect {p : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ) :
    (𝔼 site ∈ (candidate.admissibleFullPacket reference hreference hcost hshort).slice.subtypeSites,
      err site * (candidate.admissibleFullPacket reference hreference hcost hshort).weight site.val) =
      (Real.exp (-p) : ℂ) * C.localLaw.complexMean
        (fun site => err site * reference.observable (candidate.siteValue site)) := by
  let signal : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    Function.extend Subtype.val err (fun _ => 0)
  have heval (site : A.Site) : signal site.val = err site :=
    Subtype.val_injective.extend_apply _ _ site
  have h := candidate.admissibleFullPacket_expect reference hreference hcost hshort signal
  simpa only [heval] using h

theorem localLaw_residual_le_of_uniform {p ε : ℝ} (hreference : reference.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides cost p,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤ ε) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp p * ε := by
  have h := hUniform (candidate.admissibleFullPacket reference hreference hcost hshort)
  rw [candidate.admissibleFullPacket_site_expect reference hreference hcost hshort err,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))] at h
  calc
    _ = Real.exp p * (Real.exp (-p) * ‖C.localLaw.complexMean
        (fun site => err site * reference.observable (candidate.siteValue site))‖) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp p * ε := mul_le_mul_of_nonneg_left h (Real.exp_nonneg p)

theorem localLaw_residual_le_exp_of_uniform {p Eres : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides cost p,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  simpa only [← Real.exp_add, sub_eq_add_neg] using
    candidate.localLaw_residual_le_of_uniform reference hreference hcost hshort err hUniform

theorem localLaw_residual_le_exp_of_uniform_budget
    {p Eres sliceBudget testBudget : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : LocalMajorSliceTest D A.sides sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  apply candidate.localLaw_residual_le_exp_of_uniform reference hreference hcost hshort err
  intro packet
  exact hUniform (packet.mono hSliceBudget hTestBudget)

end AllocatedExternalLocalCandidate
end
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

noncomputable def fullFixed (i : LayerSamplerVariables G I n B) : ℕ :=
  if hi : C.keep i then 0 else (C.fixed ⟨i, hi⟩).toNat

theorem fullFixed_lt (i : LayerSamplerVariables G I n B) (hi : ¬C.keep i) :
    C.fullFixed i < A.sides i := by
  rw [fullFixed, dite_eq_right hi]
  exact Int.toNat_lt (C.fixed_in_box ⟨i, hi⟩).1 |>.mpr (C.fixed_in_box ⟨i, hi⟩).2

theorem frozenLongExtension_eq (u : C.Variables → ℤ) :
    frozenLongExtension C.keep C.fullFixed u = C.parameter u := by
  funext i
  by_cases hi : C.keep i
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, dite_eq_left hi]
  · simp only [frozenLongExtension, AllocatedExternalLocalChart.parameter,
      finiteSplitPoint, fullFixed, dite_eq_right hi,
      Int.toNat_of_nonneg (C.fixed_in_box ⟨i, hi⟩).1]

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate
variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)
    {budget : ℝ} (hnorm : (reference.normBound : ℝ) ≤ 1)
    (hcomplex : reference.ComplexityLE budget)

noncomputable local instance : DecidableEq C.Variables :=
  @Subtype.instDecidableEq (LayerSamplerVariables G I n B) C.keep inferInstance

noncomputable def retainedSliceTest : LocalMajorSliceTest D
    (fun i : C.Variables => A.sides i.val) cost budget where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice
  dense := by
    convert C.dense using 1
    exact congrArg (fun d : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables
        (fun i => A.sides i.val) C.step inferInstance d C.slice) (Subsingleton.elim _ _)
  test := candidate.sliceTest reference
  norm := hnorm
  complexity := hcomplex

noncomputable def fullSliceTest (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost) :
    LocalMajorSliceTest D A.sides cost budget := by
  let T := LocalMajorSliceTest.freezeShort (D := D) (cost := cost) (budget := budget)
    C.keep (candidate.retainedSliceTest reference hnorm hcomplex)
    C.fullFixed C.fullFixed_lt (Real.one_le_exp hcost)
    (fun i hi => hshort ⟨i, hi⟩)
  exact { T with dense := by simpa only [Real.log_exp, max_self] using T.dense }

theorem fullSliceTest_correlation (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (signal : (X → ℤ) → ℂ) :
    (𝔼 x ∈ (candidate.fullSliceTest reference hnorm hcomplex hcost hshort).slice.integerPoints,
      signal (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)) *
        (candidate.fullSliceTest reference hnorm hcomplex hcost hshort).weight x) =
    𝔼 u ∈ C.slice.integerPoints, signal (C.physical u) *
      star (reference.observable (candidate.value u)) := by
  change (𝔼 x ∈ ((candidate.retainedSliceTest reference hnorm hcomplex).freezeShort
    C.keep C.fullFixed C.fullFixed_lt (Real.one_le_exp hcost)
    (fun i hi => hshort ⟨i, hi⟩)).slice.integerPoints,
    signal (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)) *
      ((candidate.retainedSliceTest reference hnorm hcomplex).freezeShort
        C.keep C.fullFixed C.fullFixed_lt (Real.one_le_exp hcost)
        (fun i hi => hshort ⟨i, hi⟩)).weight x) = _
  rw [LocalMajorSliceTest.expect_freezeShort]
  simp only [C.frozenLongExtension_eq]
  dsimp only [retainedSliceTest, LocalMajorSliceTest.weight]
  have hpoints : C.slice.integerPoints =
      @ResidueBoxSlice.integerPoints C.Variables
        (fun coordinate => A.sides coordinate.val) C.step inferInstance
        (fun left right => Classical.propDecidable (left = right)) C.slice :=
    congrArg (fun decidableEq : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables
        (fun coordinate => A.sides coordinate.val) C.step inferInstance decidableEq C.slice)
      (Subsingleton.elim _ _)
  rw [hpoints]
  exact candidate.sliceTest_correlation reference signal

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

local instance chartNativeVariableDecidableEq : DecidableEq C.Variables := Subtype.instDecidableEq

variable {L : Type} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

def nativeSlicePacket (V : D.Niltest (fun _ : C.Variables => 1))
    {p : ℝ} (hV : (V.normBound : ℝ) ≤ 1) (hcomplex : V.ComplexityLE p) :
    LocalMajorSliceTest D (fun i : C.Variables => A.sides i.val) cost p where
  stride := C.step
  stride_pos := C.step_pos
  slice := C.slice
  dense := by
    have he : chartNativeVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
      Subsingleton.elim _ _
    rw [he]
    exact C.dense
  test := V
  norm := hV
  complexity := hcomplex

theorem localLaw_residual_le_of_universal_niltest
    (V : D.Niltest (fun _ : C.Variables => 1))
    {p ε sliceBudget testBudget : ℝ}
    (hV : (V.normBound : ℝ) ≤ 1) (hcomplex : V.ComplexityLE p)
    (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤ ε) :
    ‖C.localLaw.complexMean (fun site => err site * star (V.eval
      (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step
        (C.retainedParameter site.val))))‖ ≤ ε := by
  let packet := C.nativeSlicePacket V hV hcomplex
  let full := packet.freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩)
  have hcostFull : max cost (Real.log (Real.exp cost)) ≤ sliceBudget := by
    simpa only [Real.log_exp, max_self] using hSliceBudget
  have h := hUniform (UniversalLocalMajorSliceTest.ofLocalMajorSliceTest
    (full.mono hcostFull hTestBudget))
  change ‖𝔼 site ∈ full.slice.subtypeSites, err site * full.weight site.val‖ ≤ ε at h
  let signal : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    Function.extend Subtype.val err (fun _ => 0)
  have heval (site : A.Site) : signal site.val = err site :=
    Subtype.val_injective.extend_apply _ _ site
  have hmean := packet.expect_freezeShort C.keep C.fixedNatural C.fixedNatural_lt
    (Real.one_le_exp hcost) (fun i hi => hshort ⟨i, hi⟩) signal
  have hleft : (𝔼 site ∈ full.slice.subtypeSites, err site * full.weight site.val) =
      𝔼 u ∈ C.slice.integerPoints, signal (C.parameter u) * packet.weight u := by
    rw [← show (𝔼 site ∈ full.slice.subtypeSites, signal site.val * full.weight site.val) =
      (𝔼 site ∈ full.slice.subtypeSites, err site * full.weight site.val) by simp only [heval]]
    rw [full.slice.expect_subtypeSites (fun x => signal x * full.weight x)]
    simpa only [full, packet, nativeSlicePacket, C.frozenLongExtension_fixedNatural] using hmean
  rw [hleft] at h
  have hlaw := C.localLaw_complexMean_parameter (fun x => signal x * star (V.eval
    (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step (C.retainedParameter x))))
  simp only [C.retainedParameter_parameter] at hlaw
  change ‖𝔼 u ∈ C.slice.integerPoints, signal (C.parameter u) * star (V.eval
    (commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u))‖ ≤ ε at h
  have he : chartNativeVariableDecidableEq (C := C) = Classical.decEq C.Variables :=
    Subsingleton.elim _ _
  have hpoints := congrArg
    (fun dec : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables _ _ _ dec C.slice) he
  rw [hpoints] at h
  rw [← hlaw] at h
  simpa only [heval] using h

end AllocatedExternalLocalChart
end
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalCandidate

variable {A} {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L : Type} {M V : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    {w : V → ℕ} (reference : D.Niltest w)

theorem localLaw_residual_le_exp_of_universal_native_budget
    {p Eres sliceBudget testBudget : ℝ}
    (hreference : reference.ComplexityLE p) (hcost : 0 ≤ cost)
    (hshort : ∀ i : {i // ¬C.keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : p ≤ testBudget)
    (err : A.Site → ℂ)
    (hUniform : ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
      ‖𝔼 site ∈ packet.slice.subtypeSites, err site * packet.weight site.val‖ ≤
        Real.exp (-Eres)) :
    ‖C.localLaw.complexMean
      (fun site => err site * reference.observable (candidate.siteValue site))‖ ≤
        Real.exp (p - Eres) := by
  apply candidate.localLaw_residual_le_exp_of_uniform_budget reference hreference hcost hshort
    hSliceBudget hTestBudget err
  intro packet
  exact hUniform (UniversalLocalMajorSliceTest.ofLocalMajorSliceTest packet)

end AllocatedExternalLocalCandidate
end
end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)
    {sliceBudget testBudget : ℝ}
    (hbudget : 0 ≤ sliceBudget) (hcost : outputCost ≤ sliceBudget)
    (htest : 2 ≤ testBudget)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp sliceBudget)

noncomputable def retainedResidualPacket (z : out.retained) :
    LocalMajorSliceTest (RationalTorus.trivialNilmanifold 0) A.sides sliceBudget testBudget where
  stride := out.step z
  stride_pos := out.step_pos z
  slice := (out.slice z).freezeShort (P.chart ⟨z.val, out.subset z.property⟩).keep
    (P.chart ⟨z.val, out.subset z.property⟩).fixedNatural
    (P.chart ⟨z.val, out.subset z.property⟩).fixedNatural_lt
  dense := by
    let C := P.chart ⟨z.val, out.subset z.property⟩
    have he : Classical.decEq C.Variables = Subtype.instDecidableEq :=
      Subsingleton.elim _ _
    have hd : @IsDenseCommonStrideBox C.Variables _ Subtype.instDecidableEq
        (fun i => A.sides i.val) outputCost
        (@ResidueBoxSlice.integerPoints C.Variables _ _ _ Subtype.instDecidableEq (out.slice z)) := by
      rw [← he]
      exact out.dense z
    have h : IsDenseCommonStrideBox A.sides (max outputCost (Real.log (Real.exp sliceBudget)))
        ((out.slice z).freezeShort C.keep C.fixedNatural C.fixedNatural_lt).integerPoints := by
      exact (out.slice z).freezeShort_dense C.keep C.fixedNatural C.fixedNatural_lt
        (out.step_pos z) hd (Real.one_le_exp hbudget) (fun i hi => hshort z ⟨i, hi⟩)
    simpa only [Real.log_exp, max_eq_right hcost] using h
  test := RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) _ 1
  norm := by change ‖(1 : ℂ)‖ ≤ 1; exact le_of_eq norm_one
  complexity := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ htest

@[simp] theorem retainedResidualPacket_weight (z : out.retained)
    (x : LayerSamplerVariables G I n B → ℤ) :
    (out.retainedResidualPacket hbudget hcost htest hshort z).weight x = 1 := by
  simp [LocalMajorSliceTest.weight, retainedResidualPacket]

theorem retainedResidualPacket_expect (z : out.retained) (err : A.Site → ℂ) :
    (𝔼 site ∈ (out.retainedResidualPacket hbudget hcost htest hshort z).slice.subtypeSites,
      err site) = (out.siteLaw z).complexMean err := by
  let C := P.chart ⟨z.val, out.subset z.property⟩
  have he : (Subtype.instDecidableEq : DecidableEq C.Variables) = Classical.decEq _ :=
    Subsingleton.elim _ _
  let signal : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    Function.extend Subtype.val err (fun _ => 0)
  have heval (site : A.Site) : signal site.val = err site :=
    Subtype.val_injective.extend_apply _ _ site
  have hleft :
      (𝔼 site ∈ (out.retainedResidualPacket hbudget hcost htest hshort z).slice.subtypeSites,
        signal site.val) =
      𝔼 u ∈ (out.slice z).integerPoints, signal (C.parameter u) := by
    rw [ResidueBoxSlice.expect_subtypeSites]
    change (𝔼 x ∈ ((out.slice z).freezeShort C.keep C.fixedNatural C.fixedNatural_lt).integerPoints,
      signal x) = _
    rw [ResidueBoxSlice.expect_freezeShort]
    simp only [C.frozenLongExtension_fixedNatural]
    congr 1
    exact congrArg (fun dec : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables _ _ _ dec (out.slice z)) he
  have hright := C.retainedLaw_complexMean_parameter (out.slice z).integerPoints
    (out.dense z).nonempty (out.slice z).integerPoints_subset_integerBox signal
  have hright' : (out.siteLaw z).complexMean (fun site => signal site.val) =
      𝔼 u ∈ (out.slice z).integerPoints, signal (C.parameter u) := by
    change (C.retainedLaw (out.slice z).integerPoints (out.dense z).nonempty
      (out.slice z).integerPoints_subset_integerBox).complexMean _ = _
    exact hright
  simpa only [heval] using hleft.trans hright'.symm

noncomputable def residualPacket (z : A.Path) :
    LocalMajorSliceTest (RationalTorus.trivialNilmanifold 0) A.sides sliceBudget testBudget :=
  if hz : z ∈ out.retained then out.retainedResidualPacket hbudget hcost htest hshort ⟨z, hz⟩
  else LocalMajorSliceTest.full A.sides A.sides_pos sliceBudget testBudget hbudget
    (RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold 0) _ 1)
    (by simp [RationalFilteredNilmanifold.Niltest.const])
    (RationalTorus.trivialNilmanifold_const_one_complexity 0 _ htest)

@[simp] theorem residualPacket_weight (z : A.Path)
    (x : LayerSamplerVariables G I n B → ℤ) :
    (out.residualPacket hbudget hcost htest hshort z).weight x = 1 := by
  unfold residualPacket
  split_ifs
  · exact out.retainedResidualPacket_weight hbudget hcost htest hshort _ x
  · simp [LocalMajorSliceTest.weight, LocalMajorSliceTest.full]

@[simp] theorem residualPacket_retained (z : out.retained) :
    out.residualPacket hbudget hcost htest hshort z.val =
      out.retainedResidualPacket hbudget hcost htest hshort z := by
  simp only [residualPacket, dite_eq_left z.property]

theorem retained_residual_mean_le_sampledSliceSeminorm
    {Ω : Type*} (physical : A.Path → A.Site → Ω) (err : Ω → ℂ) :
    A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean (fun t => err (physical z t))‖ else 0) ≤
    sampledSliceSeminorm A.law physical
      (fun z (_ : Unit) => (out.residualPacket hbudget hcost htest hshort z).slice.subtypeSites)
      (fun z (_ : Unit) t => (out.residualPacket hbudget hcost htest hshort z).weight t.val) err := by
  classical
  let : Nonempty A.Site := ⟨⟨fun _ => 0,
    (mem_integerBox A.sides _).mpr (fun i => ⟨le_rfl, by exact_mod_cast A.sides_pos i⟩)⟩⟩
  let packet := out.residualPacket hbudget hcost htest hshort
  have hnonempty (z : A.Path) : (packet z).slice.subtypeSites.Nonempty :=
    (packet z).slice.subtypeSites_nonempty_of_integerPoints (packet z).dense.nonempty
  have hsize (z : A.Path) : (Fintype.card A.Site : ℝ) / (packet z).slice.subtypeSites.card ≤
      Fintype.card A.Site := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hnonempty z).card_pos)).mpr
    have hcard : (1 : ℝ) ≤ (packet z).slice.subtypeSites.card := by
      exact_mod_cast (hnonempty z).card_pos
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card A.Site)]
  rw [sampledSliceSeminorm_apply A.law physical _ _ (fun z _ => hnonempty z)
    (fun z _ => hsize z) (fun z _ t => (packet z).weight_norm t.val)]
  simp only [packet, residualPacket_weight, mul_one, ciSup_unique]
  apply A.law.mean_mono
  intro z
  split_ifs with hz
  · rw [out.residualPacket_retained hbudget hcost htest hshort ⟨z, hz⟩,
      out.retainedResidualPacket_expect hbudget hcost htest hshort]
  · exact norm_nonneg _

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end OAI

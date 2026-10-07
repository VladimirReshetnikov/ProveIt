import OAI.Combinatorics.Progressions.Estimates.NativeMajorCorrelationFamily
import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredModelMarginalData
import OAI.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

attribute [local instance] NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

theorem exists_full_chart_major_correlation_witness_of_native_detections
    {m k t : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hβ : ∀ u ∈ integerBox N, ∀ i,
      |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
        c i - (β u i : ℝ)| ≤ 1 / 2)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hperiod : periodCap ≤ Real.exp pMajor) (hcover : coverCap ≤ Real.exp pMajor)
    (hLip : (Lip : ℝ) ≤ Real.exp pMajor) (hΨ : (Ψ.lip : ℝ) ≤ Real.exp pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hdetected : ∀ j,
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (g : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) t pNative
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-pNative) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun u => majorPhaseSample J k poly Ψ c
              (coordinate (basis.coord j).toAddMonoidHom
                (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                  (fullTaggedVariableWeight (X := X) J) fast k
                    (left⁻¹ * Z * right⁻¹).coord))) β (fun _ => 1) u.val)
            (fun u => star (W.eval N poly u.val) * g u)‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  obtain ⟨W, g, common, hcorr⟩ := exists_native_major_correlation_family_of_detections
    J N hbox poly Ψ c
    (fun j => coordinate (basis.coord j).toAddMonoidHom
      (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
    β pNative hpNative hη hdetected
  refine ⟨{
    L := common.L
    step := t
    dim := common.dim
    model := common.model
    lower := htk
    correlation := ?_ }⟩
  unfold FullChartMajorCorrelation
  refine ⟨periodCap, coverCap, Lip, W, (fun j => (common.test j).conjugate),
    Ψ, c, β, hpoly, hcoeff, hβ, ?_, ?_, ?_, hdim, ?_, ?_, hLip, hΨ,
    hN, hRrank, hrank, ?_⟩
  · linarith
  · intro j
    exact ((common.test j).conjugate_complexityLE pMajor).mpr
      ((common.complexity j).mono hproduct)
  · intro j
    exact_mod_cast common.norm j
  · exact fun j => (W j).modulus_bound.trans hperiod
  · exact fun j => (W j).cover_bound.trans hcover
  · intro j
    exact (Real.exp_le_exp.mpr (neg_le_neg hNativeMajor)).trans (hcorr j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct NNReal

def SampledSliceNativeDetection
    {m : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (pathLaw : FiniteProbabilityWeights Ω) (physical : Ω → T → X → ℤ)
    (slices : ∀ z, Tests z → Finset T) (weight : ∀ z, Tests z → T → ℂ)
    (degree : ℕ) (pNative α : ℝ) : Prop :=
  ∀ signal : (X → ℤ) → ℂ,
    (∀ u, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    α ≤ sampledSliceSeminorm pathLaw physical slices weight signal →
    ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩)
      (g : integerBox N → ℂ),
      Nonempty (NativeSampleModel (fun _ : X => 1) degree pNative
        (fun u : integerBox N => u.val) g) ∧
      Real.exp (-pNative) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
          (fun u => signal u.val) (fun u => star (W.eval N poly u.val) * g u)‖

noncomputable def majorPhasePlateauBoxSignal
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) :
    (X → ℤ) → ℂ :=
  (integerBox N : Set (X → ℤ)).indicator (majorPhasePlateauSignal J k poly c P)

theorem majorPhasePlateauBoxSignal_inside
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (hu : u ∈ integerBox N) :
    majorPhasePlateauBoxSignal J k N poly c P u = majorPhasePlateauSignal J k poly c P u :=
  Set.indicator_of_mem hu _

theorem majorPhasePlateauBoxSignal_outside
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (hu : u ∉ integerBox N) :
    majorPhasePlateauBoxSignal J k N poly c P u = 0 :=
  Set.indicator_of_notMem hu _

theorem majorPhasePlateauBoxSignal_norm_le_one
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) : ‖majorPhasePlateauBoxSignal J k N poly c P u‖ ≤ 1 := by
  classical
  by_cases hu : u ∈ integerBox N
  · rw [majorPhasePlateauBoxSignal_inside J k N poly c P u hu]
    exact majorPhasePlateauSignal_norm_le_one J k poly c P u
  · rw [majorPhasePlateauBoxSignal_outside J k N poly c P u hu, norm_zero]
    exact zero_le_one

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal

theorem exists_full_chart_major_correlation_witness_of_prepared_detection
    {m k t : ℕ} {X L ι η Ω T : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype T]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    {Tests : Ω → Type} (pathLaw : FiniteProbabilityWeights Ω)
    (physical : Ω → T → X → ℤ) (slices : ∀ z, Tests z → Finset T)
    (weight : ∀ z, Tests z → T → ℂ) (α : ℝ)
    (hdirect : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight t pNative α)
    (hlarge : ∀ j, α ≤ sampledSliceSeminorm pathLaw physical slices weight
      (majorPhasePlateauBoxSignal J k N poly c
        (coordinate (basis.coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))))) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  have hNative0 : 0 ≤ pNative := by linarith
  have hseven : 7 ≤ pMajor := by
    have h := (productNiltestBudget_geometry hNative0).trans hproduct
    nlinarith
  have hkernel : ((majorPhasePlateauKernel (Fintype.card (LowTaggedIndex J k))).lip : ℝ) ≤
      Real.exp pMajor := by
    change (8 : ℝ) ≤ Real.exp pMajor
    linarith [Real.add_one_le_exp pMajor]
  have hexp := Real.exp_le_exp.mpr hNativeMajor
  apply exists_full_chart_major_correlation_witness_of_native_detections
    (Lip := ⟨Real.exp pNative, Real.exp_nonneg _⟩)
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff
    (majorPhasePlateauKernel _) c (majorPhaseNearestLift J k poly c)
    (fun u _ i => majorPhaseNearestLift_close J k poly c u i)
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim
    hexp hexp hexp hkernel hN hRrank hrank
  intro j
  let P := coordinate (basis.coord j).toAddMonoidHom
    (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
      (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))
  obtain ⟨W, g, hmodel, hcorr⟩ := hdirect (majorPhasePlateauBoxSignal J k N poly c P)
    (majorPhasePlateauBoxSignal_norm_le_one J k N poly c P)
    (majorPhasePlateauBoxSignal_outside J k N poly c P) (hlarge j)
  refine ⟨W, g, hmodel, ?_⟩
  have heq : (fun u : integerBox N => majorPhasePlateauBoxSignal J k N poly c P u.val) =
      fun u : integerBox N => majorPhasePlateauSignal J k poly c P u.val := by
    funext u
    exact majorPhasePlateauBoxSignal_inside J k N poly c P u.val u.property
  rw [heq] at hcorr
  exact hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_chart_major_correlation_witness_of_productive_local_tests
    {m k t : ℕ} {X L ι η Ω I : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (pathLaw : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (localN : I → ℕ) (hlocalN : ∀ i, 0 < localN i)
    (cost : ℝ) (hcost : 0 ≤ cost)
    (physical : Ω → (I → ℤ) → X → ℤ)
    (hphysical : ∀ j z, z ∈ good j → ∀ x,
      x ∈ integerBox localN → physical z x ∈ integerBox N)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * pathLaw.mass (good j))
    (hdirect : ∀ chosen : Ω → Option η →
      LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : integerBox localN) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox localN) => (chosen z a).weight x.val) t pNative α)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (physical z x) * A.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  let phase := fun j => coordinate (basis.coord j).toAddMonoidHom
    (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
      (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))
  let signal := fun j => majorPhasePlateauBoxSignal J k N poly c (phase j)
  have hlocalBox : ∀ j z, z ∈ good j →
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          signal j (physical z x) * A.weight x‖ := by
    intro j z hz
    obtain ⟨A, hA⟩ := hlocal j z hz
    refine ⟨A, ?_⟩
    have heq : (𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x) =
        𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c (phase j) (physical z x) * A.weight x := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [show signal j (physical z x) =
          majorPhasePlateauSignal J k poly c (phase j) (physical z x) from
        majorPhasePlateauBoxSignal_inside J k N poly c (phase j) (physical z x)
          (hphysical j z hz x (A.slice.integerPoints_subset_integerBox hx))]
    rw [heq]
    exact hA
  obtain ⟨chosen, _, hlarge⟩ := exists_productive_localMajorSlice_coordinate_family
    (OrdinaryPolynomialPhase.nilmanifold t) pathLaw good localN hlocalN cost
    (OrdinaryPolynomialPhase.budget t) (9 / 10)
    (OrdinaryPolynomialPhase.zeroLocalMajorSlice localN hlocalN cost hcost)
    physical signal hlocalBox
  apply exists_full_chart_major_correlation_witness_of_prepared_detection
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff c
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim hN hRrank hrank
    pathLaw (fun z (x : integerBox localN) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox localN) => (chosen z a).weight x.val)
    α (hdirect chosen)
  intro j
  exact (hmass j).trans (hlarge j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators Classical

theorem exists_full_chart_major_correlation_witness_of_frozen_productive_local_tests
    {m k t : ℕ} {X L ι η Ω I : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (pathLaw : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (localN : I → ℕ) (hlocalN : ∀ i, 0 < localN i)
    (keep : I → Prop) (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (localN i : ℝ) ≤ Bshort)
    (physical : Ω → (I → ℤ) → X → ℤ)
    (hphysical : ∀ j z, z ∈ good j → ∀ x,
      x ∈ integerBox localN → physical z x ∈ integerBox N)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * pathLaw.mass (good j))
    (hdirect : ∀ chosen : Ω → Option η →
      LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN (max cost (Real.log Bshort))
        (OrdinaryPolynomialPhase.budget t),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : integerBox localN) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox localN) => (chosen z a).weight x.val) t pNative α)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < localN i.val) ∧
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
        (fun i : {i // keep i} => localN i.val) cost (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (physical z (finiteSplitPoint keep x fixed)) * A.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_full_chart_major_correlation_witness_of_productive_local_tests
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff c
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim hN hRrank hrank
    pathLaw good localN hlocalN (max cost (Real.log Bshort))
    (hcost.trans (le_max_left _ _)) physical hphysical α hmass hdirect
  intro j z hz
  obtain ⟨fixed, hfixed, A, hA⟩ := hlocal j z hz
  let starts := frozenShortStarts keep fixed
  have hstarts := frozenShortStarts_inside keep fixed hfixed
  refine ⟨A.freezeShort keep starts hstarts hBshort hshort, ?_⟩
  rw [A.expect_freezeShort keep starts hstarts hBshort hshort
    (fun x => majorPhasePlateauSignal J k poly c
      (coordinate (basis.coord j).toAddMonoidHom
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
      (physical z x))]
  simpa only [starts, frozenLongExtension_shortStarts keep fixed (fun i => (hfixed i).1)] using hA

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

section Consumer

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (selection : Fin (s + 1) ↪ G) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (u pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog u pModel
local notation "qDetect" => allocatedModelTestLog u pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (α τ : ℝ)
variable {P : ℝ}

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]
variable [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]
variable [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]
variable [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
  OrdinaryPolynomialPhase.weight s)]

include μ hR hσ hb o in

theorem preparedFullChartNativeDetection
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (hDirect : PreparedModularGeneralDirectDetectionFreeTrimPreparedInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (α := α / 2) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget)
    (hα : 0 < α)
    (hcount : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect)
    (hbudget : OrdinaryPolynomialPhase.budget s ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) qDetect) :
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ (hτSpatial : 0 < τ), τ⁻¹ ≤ Real.exp Pphysical →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s) (s + 1) Pmaster Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    let ξn := normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2))
      Pphysical coarseTarget
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp r.required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp r.required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let hξn := normalizedTupleNarrowWidth_pos (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect pDetect qDetect (α / 2)) Pphysical coarseTarget
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-r.E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    ∃ hcenter : ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      0 < selectedJointDensityMass bases stride cells V
        (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center),
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hcenter center)
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    ∀ {η : Type},
      ∀ chosen : Path → Option η → LocalMajorSliceTest
        (OrdinaryPolynomialPhase.nilmanifold s) sides pSlice
        (OrdinaryPolynomialPhase.budget s),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : Sites) => jointIntegerPhysicalSite x.val (z.1.val, z.2.val))
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : Sites) => (chosen z a).weight x.val) s r.nativeBudget α := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
    r W ξn hW cells poly hp hmem Rrank hsize hrank hRank V hCells bases hξn Z
  have hcentered := preparedModularGeneralCenteredDetectionFreeTrim_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := u) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (α := α) (τ := τ) (hb := hb) (o := o) (μ := μ)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, htail⟩ :=
    hcentered hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτSpatial hτInv hτHalf hτDim
      cells poly hp hmem hsize hrank hRank hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path
  obtain ⟨hcenter, hweight, hdetect⟩ := htail
  refine ⟨hcenter, hweight, ?_⟩
  intro pathLaw sides Sites η chosen
  have hfamily := hdetect (fun _ _ => OrdinaryPolynomialPhase.nilmanifold s)
    (fun z a => (chosen z a).test)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a i => ((chosen z a).slice.start i : ℤ))
    (fun z a => (chosen z a).stride)
    (fun z a => (chosen z a).slice.length)
    (fun z a => (chosen z a).stride_pos)
    (fun z a => ((chosen z a).slice.subtypeSites_image_val).trans
      (chosen z a).slice.integerPoints_eq_commonStrideBox)
    (fun z a => (chosen z a).slice.subtypeSites_dense (chosen z a).dense)
    hcount
    (fun z a => (chosen z a).complexity.mono hbudget)
    (fun z a => (chosen z a).norm)
  intro signal hsignal hsupp hlarge
  exact hfamily signal hα hsignal hsupp hlarge

end Consumer
end Erdos3.VectorPolynomial

end

end OAI

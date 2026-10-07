/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Fourier.CommonMarkedFrequencyModel

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_controlled_dependentQuotient_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure r), T.filtration = D.coefficientFreeFiltration →
      0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      (∀ i, rationalLogHeight (B.freeFrequency D (E.basis i)) ≤ v) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
      ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE ((v + C) ^ C) ∧
          l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤
            (v + C) ^ C) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, rationalLogHeight (ξ (G.basis i)) ≤ (v + C) ^ C) ∧
            ∀ z : G.RealGroup, z ∈ G.realLattice → ∃ a : ℤ, realifyFunctional ξ z.coord = a := by
  let k := (6 * s + 4) * 424
  let a := bchIntegralDenominatorBound s + 5
  let P₀ : Polynomial ℕ := (Polynomial.X + 3) ^ k
  let R₀ := ((P₀ + 2) ^ 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P₀ + R₀)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P Q v W out H R D B n E T hT hv hcomplex hgen hfreq l hl hlv
  let H₁ := ⌈Real.exp v⌉₊
  obtain ⟨m, hm, d, hd, u, hu, G, S, hSF, hdiv, hgrid, hcoords, hproj,
      ξ, hξ, hξH, hint, hSc⟩ :=
    B.exists_dependentQuotient_integral_model D E T hT (one_le_ceil_exp v)
      (fun i j k => rationalHeightLE_ceil_exp (hcomplex.1.2.2.1 i j k))
      (fun i a j => rationalHeightLE_ceil_exp (hcomplex.1.2.2.2 i a j))
      (fun i j a k => rationalHeightLE_ceil_exp (hcomplex.2 i j a k))
      (fun i j => rationalHeightLE_ceil_exp (hgen i j))
      (fun i => rationalHeightLE_ceil_exp (hfreq i)) l hl
  let K := rankQuotientHeight n m d u (lieTreeHeight n H₁ s)
  let P₁ := (v + 3) ^ k
  let R₁ := ((P₁ + 2) ^ 2 + a) ^ a
  have hv1 : 0 ≤ v + 1 := by linarith
  have hn : (n : ℝ) ≤ v + 1 := hcomplex.1.1.trans (by linarith)
  have hm' : (m : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hm).trans hn
  have hd' : (d : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hd).trans hn
  have hu' : (u : ℝ) ≤ v + 1 := (Nat.cast_le.mpr hu).trans hd'
  have hK : (K : ℝ) ≤ Real.exp P₁ := by
    have h := dependentQuotientHeight_le_exp s n m d u H₁ hv1 hn hm' hd' hu'
      (ceil_exp_le_exp_add_one hv)
    simpa only [show v + 1 + 2 = v + 3 by ring] using h
  have hvP : v ≤ P₁ := by
    have h := le_power_budget hv1 (show 1 ≤ k by dsimp [k]; omega)
    exact (show v ≤ v + 1 by linarith).trans (by
      simpa only [show v + 1 + 2 = v + 3 by ring] using h)
  have hP : 0 ≤ P₁ := hv.trans hvP
  have hdP : (d : ℝ) ≤ P₁ := (Nat.cast_le.mpr hd).trans (hcomplex.1.1.trans hvP)
  have hgrid' : (G.grid : ℝ) ≤ Real.exp R₁ :=
    (Nat.cast_le.mpr hgrid).trans (integral_frequency_grid_allowance_le_exp
      (bchIntegralDenominatorBound s) d K l hP hdP hK
      (hlv.trans (Real.exp_le_exp.mpr hvP)))
  have htotal : P₁ + R₁ ≤ (v + C) ^ C := by
    simpa [P₀, R₀, P₁, R₁, Polynomial.eval₂_pow] using hbudget v hv
  have hPC : P₁ ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by dsimp [R₁]; positivity)).trans htotal
  have hRC : R₁ ≤ (v + C) ^ C := (le_add_of_nonneg_left hP).trans htotal
  refine ⟨d, hd, G, S, hSF, hSc _ (hdP.trans hPC)
    (hgrid'.trans (Real.exp_le_exp.mpr hRC)) (hK.trans (Real.exp_le_exp.mpr hPC)),
    hdiv, hcoords, ?_, ξ, hξ, ?_, G.realLattice_functional_integral ξ hint⟩
  · intro i j
    exact (rationalLogHeight_le_of_height (hproj i j) hK).trans hPC
  · intro i
    exact (rationalLogHeight_le_of_height (hξH i) hK).trans hPC

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

noncomputable def restrictVertical {L I : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype I] [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
    (V : D.UnitVerticalObservable T I p) (S : Subgroup D.RealGroup) (hS : S ≤ T) :
    D.UnitVerticalObservable S I p where
  observable := V.observable
  unit := V.unit
  norm := V.norm
  lipBound := V.lipBound
  lip_bound := V.lip_bound
  lipschitz := V.lipschitz
  frequency := V.frequency
  height := V.height
  vertical i z hz := V.vertical i z (hS hz)
  integral z hz := V.integral z (hS hz)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependentQuotient_unit_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure r), T.filtration = D.coefficientFreeFiltration →
      0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      (∀ i, rationalLogHeight (B.freeFrequency D (E.basis i)) ≤ v) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
      ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
        ∃ S : G.DegreeRankStructure r,
          S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE ((v + C) ^ C) ∧
          l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
          (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤
            (v + C) ^ C) ∧
          ∃ ξ : D.DependentQuotient →ₗ[ℚ] ℚ,
            (∀ x ∈ D.coefficientFreeFiltration.layer s r,
              ξ (D.dependentQuotientMap x) = B.freeFrequency D x) ∧
            (∀ i, rationalLogHeight (ξ (G.basis i)) ≤ (v + C) ^ C) ∧
            (∀ z : G.RealGroup, z ∈ G.realLattice → ∃ a : ℤ, realifyFunctional ξ z.coord = a) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 G.basis
             ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp ((v + C) ^ C) ∧
               ∃ U : G.UnitVerticalObservable (S.realSubgroup s r) (Fin k) ((v + C) ^ C),
                 U.frequency = ξ) := by
  obtain ⟨a, _, hmodel⟩ := exists_controlled_dependentQuotient_model s
  obtain ⟨c, _, hunit⟩ := RationalFilteredNilmanifold.exists_native_prescribed_unit s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A₀ + (A₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P Q v W out H R D B n E T hT hv hcomplex hgen hfreq l hl hlv
  obtain ⟨d, hd, G, S, hSF, hSc, hdiv, hcoords, hproj, ξ, hξ, hξH, hint⟩ :=
    hmodel D B E T hT hv hcomplex hgen hfreq l hl hlv
  let A := (v + a) ^ a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have htotal : A + (A + c) ^ c ≤ (v + C) ^ C := by
    simpa [A₀, A, Polynomial.eval₂_pow] using hbudget v hv
  have hAC : A ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (A + c) ^ c)).trans htotal
  have hUC : (A + c) ^ c ≤ (v + C) ^ C := (le_add_of_nonneg_left hA).trans htotal
  refine ⟨d, hd, G, S, hSF, hSc.mono S hAC, hdiv, hcoords,
    (fun i j => (hproj i j).trans hAC), ξ, hξ, (fun i => (hξH i).trans hAC), hint, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 G.basis
  obtain ⟨k, hk, hkbound, U, hU⟩ := hunit G hA hSc.1 ξ hξH hint
  refine ⟨k, hk, hkbound.trans (Real.exp_le_exp.mpr hUC),
    (U.restrictVertical (S.realSubgroup s r) (S.realSubgroup_le_degree s r)).mono hUC, ?_⟩
  exact hU

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasCoveredDependentComparison {s r N : ℕ} [NeZero N] {b p q P v : ℝ}
    {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) {n : ℕ}
    (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    (T : E.DegreeRankStructure (r + 1)) {I : Type} [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I v) (l : ℕ) (Q : ℝ) : Prop :=
  ∃ d : ℕ, d ≤ n ∧ ∃ G : RationalFilteredNilmanifold D.DependentQuotient s d,
    ∃ S : G.DegreeRankStructure (r + 1),
      S.filtration = D.dependentQuotientFiltration ∧ S.ComplexityLE Q ∧
      l ∣ G.grid ∧ bchSubgroupCoordinates G.basis G.lattice = scaledIntegerGrid G.grid ∧
      (∀ i j, rationalLogHeight (G.basis.repr (D.dependentQuotientMap (E.basis j)) i) ≤ Q) ∧
      ∃ Λ : Subgroup E.filtration.Group, Λ ≤ E.lattice ∧
        (Λ.subgroupOf E.lattice).Characteristic ∧ (Λ.subgroupOf E.lattice).Normal ∧
        (Λ.subgroupOf E.lattice).FiniteIndex ∧ (Λ.relIndex E.lattice : ℝ) ≤ Real.exp Q ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m),
          (T.withLattice Λ m hm hin hout).ComplexityLE Q ∧
          ∃ hmap : Λ ≤ G.lattice.comap (mapOfSteps
              (hL := E.filtration.lowerCentralSeries_eq_bot)
              (hM := G.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap),
            ∃ V₀ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) I Q,
              V₀.frequency = V.frequency ∧ V₀.lipBound = V.lipBound ∧
              (∀ i x, V₀.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk x)) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 G.basis
               ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp Q ∧
                 ∃ U : G.UnitVerticalObservable (S.realSubgroup s (r + 1)) (Fin k) Q,
                   (∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
                     U.frequency (D.dependentQuotientMap x) = V.frequency x) ∧
                   (∀ z : G.RealGroup, z ∈ G.realLattice →
                     ∃ a : ℤ, realifyFunctional U.frequency z.coord = a) ∧
                   ∀ (σ : Type) (w : σ → ℕ),
                     (E.withLattice Λ m hm hin hout).HasUniformLowerRankUnitFamily
                       (T.withLattice Λ m hm hin hout)
                       (mapDifferenceObservable V₀ U D.dependentQuotientMap hmap) w Q)

theorem exists_covered_dependentQuotient_comparison (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P Q v : ℝ}
      {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (J : D.CoefficientBases Q) {n : ℕ}
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
      (T : E.DegreeRankStructure (r + 1)) {I : Type} [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
      (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) I v),
      T.filtration = D.coefficientFreeFiltration → 0 ≤ v → T.ComplexityLE v →
      (∀ i j, rationalLogHeight (E.basis.repr (D.coefficientFreeGenerator i) j) ≤ v) →
      V.frequency = J.freeFrequency D →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp v →
        D.HasCoveredDependentComparison E T V l ((v + C) ^ C) := by
  obtain ⟨a, ha, hmodel⟩ := exists_native_dependentQuotient_unit_model s
  obtain ⟨c, hc, hcover⟩ := exists_native_source_unit_cover
  obtain ⟨b, _, hcomparison⟩ := exists_uniform_dependentQuotient_comparison s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let K₀ := (A₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (K₀ + (K₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ b₀ p q P Q v W out H R D J n E T I _ _ _ _ _ V hT hv hTc hgen hV l hl hlv
  have hshift (x : ℝ) (hx : 0 ≤ x) (a : ℕ) (ha : 2 ≤ a) : x ≤ (x + a) ^ a := by
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      x ≤ x + a := le_add_of_nonneg_right (Nat.cast_nonneg _)
      _ = (x + a) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : 1 ≤ a)
  let A := (v + a) ^ a
  let K := (A + c) ^ c
  have hvA : v ≤ A := hshift v hv a ha
  have hA : 0 ≤ A := hv.trans hvA
  have hAK : A ≤ K := hshift A hA c hc
  have hK : 0 ≤ K := hA.trans hAK
  have htotal : K + (K + b) ^ b ≤ (v + C) ^ C := by
    simpa [A₀, K₀, A, K, Polynomial.eval₂_pow] using hbudget v hv
  have hKC : K ≤ (v + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (K + b) ^ b)).trans htotal
  have hAC : A ≤ (v + C) ^ C := hAK.trans hKC
  have hcomparisonC : (K + b) ^ b ≤ (v + C) ^ C := (le_add_of_nonneg_left hK).trans htotal
  obtain ⟨d, hd, G, S, hSF, hSc, hdiv, hcoords, hproj, ξ, hξ, _, hint, hunit⟩ :=
    hmodel D J E T hT hv hTc hgen (fun i => by rw [← hV]; exact V.height i) l hl hlv
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hcoverT, hmap, hpreserve⟩ :=
    hcover (I := I) E T G D.dependentQuotientMap hA (hTc.mono T hvA) hSc.1 hproj
  obtain ⟨V₀, hV₀, hVlip, hVobs⟩ := hpreserve (V.mono hvA)
  refine ⟨d, hd, G, S, hSF, hSc.mono S hAC, hdiv, hcoords,
    (fun i j => (hproj i j).trans hAC), Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hKC), m, hm, hin, hout,
    hcoverT.mono _ hKC, hmap, V₀.mono hKC, hV₀, hVlip, hVobs, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 G.basis
  obtain ⟨k, hk, hkbound, U, hU⟩ := hunit
  refine ⟨k, hk, hkbound.trans (Real.exp_le_exp.mpr hAC), U.mono hAC, ?_, ?_, ?_⟩
  · intro x hx
    change U.frequency (D.dependentQuotientMap x) = V.frequency x
    rw [hU, hV]
    exact hξ x hx
  · intro z hz
    change ∃ a : ℤ, realifyFunctional U.frequency z.coord = a
    rw [hU]
    exact hint z hz
  · intro σ w
    have hfreq₀ : V₀.frequency = J.freeFrequency D := hV₀.trans hV
    have hfreqU : ∀ x ∈ D.coefficientFreeFiltration.layer s (r + 1),
        (U.mono hAK).frequency (D.dependentQuotientMap x) = J.freeFrequency D x := by
      intro x hx
      change U.frequency (D.dependentQuotientMap x) = _
      rw [hU]
      exact hξ x hx
    have h := hcomparison D J (E.withLattice Λ m hm hin hout) G
      (T.withLattice Λ m hm hin hout) S I (Fin k) σ V₀ (U.mono hAK) hmap
      hT hSF hK hcoverT (hSc.mono S hAK) (fun i j => (hproj i j).trans hAK)
      hfreq₀ hfreqU w
    exact h.mono hcomparisonC

end Erdos3.NativeRankRelation.CommonData

end

end OAI

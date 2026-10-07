import OAI.Combinatorics.Progressions.Polynomial.PhaseBandCoordinateLifts

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def inducedMarkedLipschitzBound (s d u e : ℕ) (p : ℝ) (R : ℝ≥0) : ℝ≥0 :=
  2 * phaseBandQuotientConstant (s + 1) d ⌈Real.exp p⌉₊ R
    ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
    (markedLocalBoxConstant s d ⌈Real.exp p⌉₊ u e ⌈Real.exp p⌉₊ p (R + 1)
      ⟨Real.exp p, Real.exp_nonneg _⟩)

theorem exists_induced_marked_observable_explicit (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m e u : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
      (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]
      (E : RationalFilteredNilmanifold (L ⧸ J) u e)
      (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
        (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (t : ℝ) ≤ p → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr
        (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ V : E.Space → ℂ, (∀ x, ‖V x‖ ≤ 1) →
      (letI := E.metricSpace; LipschitzWith ⟨Real.exp p, Real.exp_nonneg _⟩ V) →
      letI := D.metricSpace
      ∃ G : D.Space → ℂ,
        LipschitzWith (inducedMarkedLipschitzBound s d u e p
          ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩) G ∧
        (∀ g : D.RealGroup,
          (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
          G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g) ∧
        ∀ x, ‖G x‖ ≤ 2 := by
  obtain ⟨C, hC, hrepresentatives⟩ := exists_marked_phase_band_representatives s hs
  refine ⟨C, hC, ?_⟩
  intro I L _ _ r d t m e u F v w marked hw hv hm _ _ _ _ D J hJ _ _ _ _ E hmap p hp hD hE ht hmp hdir hphase heval hint hlat V hnorm hV
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  let φ := normalizedMarkedPhase F v w marked t m
  let R : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), Real.exp_nonneg _⟩
  let K : ℝ≥0 := ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
  let H := ⌈Real.exp p⌉₊
  let A := markedLocalBoxConstant s d H u e H p (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩
  let f := markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V
  have hR : 1 ≤ R := Real.one_le_exp (by positivity)
  have norm_iff (z : Fin t → ℝ) : ‖z‖ ≤ 1 / 4 ↔ ∀ i, |z i| ≤ 1 / 4 := by
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) (x := z))
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hct (i j k) : RationalHeightLE (lieStructureConstants E.basis i j k) H :=
    rationalHeightLE_ceil_exp (hE.2.2.1 i j k)
  have hrep (g : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4) :
      ∃ x : D.RealGroup, (QuotientGroup.mk x : D.Space) = QuotientGroup.mk g ∧
        torusPhaseLinear φ x.coord = torusPhaseLinear φ g.coord ∧
        ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ R :=
    hrepresentatives F v w marked hw hv D hp hD ht hm hmp hdir hphase hint hlat g ((norm_iff _).mp hg)
  have hdist (g h : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
      (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
      dist (f g) (f h) ≤ phaseBandQuotientConstant (s + 1) d H R K A *
        dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h) := by
    apply phase_band_quotient_dist_le D φ hint hc R K A hR
      (torusPhaseLinear_group_lipschitz_exp D φ hp hD.1 ht hphase) hrep f
      (fun x => markedLocalCoefficientValue_norm_le F v w marked hw hv t m hm D J hJ E hmap V hnorm x)
      (fun x y hx hy hxy => markedLocalCoefficientValue_eq_on_small_cosets
        F v w marked hw hv t m hm D J hJ E hmap hint V x y ((norm_iff _).mp hx) ((norm_iff _).mp hy) hxy)
      (fun x y hx hy => ?_) g h hg hh
    exact markedLocalCoefficientValue_coordinate_dist_le F v w marked hw hv t m hm D J hJ E hmap
      hp hD.1 ht hmp hdir hphase heval hc hct (R + 1) ⟨Real.exp p, Real.exp_nonneg _⟩
      (le_add_of_nonneg_left (by positivity)) V hV x y hx hy
  let X := {g : D.RealGroup // ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4}
  obtain ⟨G, hG, hGeq, hGnorm⟩ := exists_complex_extension_along_map
    (fun x : X => (QuotientGroup.mk x.val : D.Space)) (fun x : X => f x.val)
    (phaseBandQuotientConstant (s + 1) d H R K A) 1
    (fun x y => hdist x.val y.val x.property y.property)
    (fun x => markedLocalCoefficientValue_norm_le F v w marked hw hv t m hm D J hJ E hmap V hnorm x.val)
  refine ⟨G, hG, ?_, ?_⟩
  · intro g hg
    exact hGeq ⟨g, (norm_iff _).mpr hg⟩
  · intro x
    simpa only [NNReal.coe_one, mul_one] using hGnorm x

theorem induced_marked_observable_scaled_parameter
    {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u t m : ℕ}
    (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (hm : 0 < m)
    (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (E : RationalFilteredNilmanifold (L ⧸ J) u e)
    (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
      (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)
    (V : E.Space → ℂ) (G : D.Space → ℂ)
    (hG : ∀ g : D.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk g) = markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g)
    (a : Fin t → ℝ) (ha : ∀ i, |a i| ≤ 1 / 4) (g : D.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    G (QuotientGroup.mk (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g)) =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ g.coord⟩ : E.RealGroup)) := by
  rw [hG]
  · exact markedLocalCoefficientValue_scaled_parameter F v w marked hw hv t m hm D J hJ E hmap V a g hg
  · intro i
    rw [torusPhaseLinear_mul D, hg, add_zero]
    change |torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterDirection F v w marked t ((m : ℝ) • a)) i| ≤ 1 / 4
    rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm]
    exact ha i

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem localPhaseMarkedOrbit_induced_value
    {s r N d e k : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
    (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
    (hmap : ∀ z : E.RealGroup, z ∈ E.realLattice →
      (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice)
    (V : Q.Space → ℂ) (G : E.Space → ℂ)
    (hG : ∀ z : E.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm E (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V z)
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4) (n : ℤ) :
    G (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      V (QuotientGroup.mk (⟨D.dependentQuotientMap.toLinearMap.baseChange ℝ
        (∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val))⟩ : Q.RealGroup)) := by
  let φ := normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t m
  let g : E.RealGroup := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m)
  let γ : E.RealGroup := D.scaledLocalAffineCorrectingElement t u c h₀ m h
  let ε : E.RealGroup := D.localPhaseMarkedSmallElement t u c h₀ m h
  let z : E.RealGroup :=
    ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩
  have hγ : γ ∈ E.realLattice := D.scaledLocalAffineCorrectingElement_mem_realLattice
    t u c h₀ m E hdir h
  have hcoset : (QuotientGroup.mk g : E.Space) = QuotientGroup.mk (ε * z) := by
    calc
      _ = QuotientGroup.mk (g * γ⁻¹) :=
        (quotient_mk_mul_mem E.realLattice g ⟨γ⁻¹, E.realLattice.inv_mem hγ⟩).symm
      _ = _ := congrArg QuotientGroup.mk (D.localPhaseMarkedOrbit_lift_factorization t x y u c h₀ m hs h n)
  have hz : torusPhaseLinear φ z.coord = 0 := normalizedMarkedPhase_real_pure
    D.coefficientFreeFiltration D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    t m z.coord (D.localPhaseMarkedLift_pure t x y u c h₀ m h n)
  have hε : ε = realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t
        ((m : ℝ) • (fun i => -affineCyclicTorusLocalLift u c h₀ h i)) := by
    change realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t _ = _
    apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_neg, neg_mul]
  change G (QuotientGroup.mk g) = _
  rw [hcoset, hε]
  apply (induced_marked_observable_scaled_parameter D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer hm E (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V G hG
    (fun i => -affineCyclicTorusLocalLift u c h₀ h i)
    (fun i => by simpa only [abs_neg] using hsmall i) z hz).trans
  exact congrArg (fun a => V (QuotientGroup.mk (⟨a⟩ : Q.RealGroup)))
    (D.localPhaseMarkedLift_base_projection t x y u c h₀ m hm h n)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d e k l : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (hs : 1 ≤ s)
  (M : RationalFilteredNilmanifold
    (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s l)
  (Q : RationalFilteredNilmanifold D.DependentQuotient k e)
  (hφ : E.lattice ≤ Q.lattice.comap (mapOfSteps
    (hL := E.filtration.lowerCentralSeries_eq_bot) (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
  (hmap : ∀ z : M.RealGroup, z ∈ M.realLattice →
    (⟨(D.markedDependentEvaluation t 0).baseChange ℝ z.coord⟩ : Q.RealGroup) ∈ Q.realLattice)
  (hdir : ∀ a : Fin t → ℤ,
    (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
        M.filtration.Group) ∈ M.lattice)

include hs hdir

theorem induced_local_value_eq_nativeSpaceMap (V : Q.Space → ℂ) (G : M.Space → ℂ)
    (hG : ∀ z : M.RealGroup,
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm M (D.dependentWordIdeal 0 2 0) le_rfl Q hmap V z)
    (a : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4)
    (ha : a.log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    G (QuotientGroup.mk ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m))) =
      V (E.nativeSpaceMap Q D.dependentQuotientMap hφ (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => n) a))) := by
  apply (D.localPhaseMarkedOrbit_induced_value t x y u c h₀ m hm hs M Q hmap hdir V G hG h hsmall n).trans
  have hcoord : (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => n) a).coord =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
        ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
    rw [E.filtration.realification.polynomialOrbitEval_coord, ha]
    simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]
  rw [nativeSpaceMap_mk]
  apply congrArg (fun z : Q.RealGroup => V (QuotientGroup.mk z))
  apply NilpotentLieBCHGroup.ext
  change _ = D.dependentQuotientMap.toLinearMap.baseChange ℝ _
  rw [hcoord]

variable [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
  [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]

theorem exists_local_induced_comparison_correlation {A I J : Type*} [Fintype I] [Fintype J]
    {degree : ℕ} {z q₁ q₂ qV : ℝ} {S : Subgroup E.RealGroup} {T : Subgroup Q.RealGroup}
    (V : E.UnitVerticalObservable S I qV) (U : Q.UnitVerticalObservable T J qV)
    (G : J → M.Space → ℂ)
    (hG : ∀ j (z : M.RealGroup),
      (∀ i, |torusPhaseLinear (normalizedMarkedPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t m) z.coord i| ≤ 1 / 4) →
      G j (QuotientGroup.mk z) = markedLocalCoefficientValue D.coefficientFreeFiltration
        D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t m hm M (D.dependentWordIdeal 0 2 0) le_rfl Q hmap (U.observable j) z)
    (a v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (h : ZMod N) (hsmall : ∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 4)
    (ha : a.log = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val))
    (f : A → ZMod N → ℂ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hI : (Fintype.card I : ℝ) ≤ Real.exp q₁) (hJ : (Fintype.card J : ℝ) ≤ Real.exp q₂)
    (B : NativeVectorCorrelation degree N z (fun ai : A × I => fun n =>
      f ai.1 n * star (V.observable ai.2 (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v))))) :
    Nonempty (NativeVectorCorrelation degree N (z + q₁ + q₂)
      (fun ij : A × ((I × I) × (I × J)) => fun n =>
        f ij.1 n * star (G ij.2.2.2 (QuotientGroup.mk
          ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
            (correlationInput (h.val : ℤ) (n.val : ℤ)) (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
        star (V.observable ij.2.1.1 (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v)) *
          star (V.observable ij.2.1.2 (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a)))) *
        star (mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2.2 (QuotientGroup.mk
          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a))))) := by
  have hvalue (j : J) (n : ZMod N) := D.induced_local_value_eq_nativeSpaceMap
    t x y u c h₀ m hm hs M E Q hφ hmap hdir (U.observable j) (G j) (hG j) a h hsmall ha (n.val : ℤ)
  have htwo := exists_native_two_unit_comparison f
    (fun i n => V.observable i (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) v)))
    (fun i n => V.observable i (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a)))
    (fun j n => U.observable j (E.nativeSpaceMap Q D.dependentQuotientMap hφ (QuotientGroup.mk
      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (n.val : ℤ)) a))))
    (fun n => V.unit _) (fun n => U.unit _) hq₁ hq₂ hI hJ B
  simpa only [hvalue, mapDifferenceObservable] using htwo

end Erdos3.NativeRankRelation.CommonData

end

end OAI

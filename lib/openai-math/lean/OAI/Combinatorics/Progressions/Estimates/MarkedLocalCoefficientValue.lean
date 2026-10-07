import OAI.Combinatorics.Progressions.Geometry.NormalizedMarkedChart

namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem normalizedMarkedPhase_real_eq_zero_iff (hm : 0 < m)
    (z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z = 0 ↔
      z ∈ (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ := by
  have hker : LinearMap.ker (normalizedMarkedPhase F v w marked t m).toLinearMap =
      LinearMap.ker (markedQuotientPhase F v w marked t).toLinearMap := by
    ext x
    change normalizedMarkedPhase F v w marked t m x = 0 ↔ markedQuotientPhase F v w marked t x = 0
    rw [normalizedMarkedPhase_apply]
    simp [show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne']
  let e := ((RationalTorus.basis t).baseChange ℝ).equivFun
  change e ((normalizedMarkedPhase F v w marked t m).toLinearMap.baseChange ℝ z) = 0 ↔
    z ∈ (LinearMap.ker (markedQuotientPhase F v w marked t).toLinearMap).baseChange ℝ
  rw [← hker, realification_ker, LinearMap.mem_ker]
  constructor
  · intro hz
    exact e.injective (hz.trans (e.map_zero).symm)
  · intro hz
    rw [hz, map_zero]

noncomputable def normalizedMarkedRetraction (g : E.RealGroup) : E.RealGroup :=
  realMarkedParameterElement F v w marked hw hv t
    ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord)) * g

theorem normalizedMarkedRetraction_phase (hm : 0 < m) (g : E.RealGroup) :
    torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (normalizedMarkedRetraction F v w marked hw hv t m E g).coord = 0 := by
  unfold normalizedMarkedRetraction
  rw [torusPhaseLinear_mul E]
  change torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
    (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord))) +
        torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0
  rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm]
  exact neg_add_cancel _

theorem normalizedMarkedRetraction_pure (hm : 0 < m) (g : E.RealGroup) :
    (normalizedMarkedRetraction F v w marked hw hv t m E g).coord ∈
      (markedQuotientPolynomialAlgebra F v w marked t).toSubmodule.baseChange ℝ :=
  (normalizedMarkedPhase_real_eq_zero_iff F v w marked t m hm _).mp
    (normalizedMarkedRetraction_phase F v w marked hw hv t m E hm g)

theorem normalizedMarkedRetraction_right_mul (g h : E.RealGroup)
    (hh : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) h.coord = 0) :
    normalizedMarkedRetraction F v w marked hw hv t m E (g * h) =
      normalizedMarkedRetraction F v w marked hw hv t m E g * h := by
  unfold normalizedMarkedRetraction
  rw [torusPhaseLinear_mul E, hh, add_zero]
  exact (mul_assoc _ _ _).symm

theorem normalizedMarkedRetraction_scaled_parameter (hm : 0 < m) (a : Fin t → ℝ) (g : E.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    normalizedMarkedRetraction F v w marked hw hv t m E
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g) = g := by
  have hphase : torusPhaseLinear (normalizedMarkedPhase F v w marked t m)
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g).coord = a := by
    rw [torusPhaseLinear_mul E, hg, add_zero]
    exact normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm a
  unfold normalizedMarkedRetraction
  rw [hphase, smul_neg, ← realMarkedParameterElement_inv]
  exact inv_mul_cancel_left _ _

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ) (hm : 0 < m)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

noncomputable def normalizedMarkedPureRetraction (g : D.RealGroup) :
    realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (markedQuotientPolynomialAlgebra F v w marked t) :=
  ⟨normalizedMarkedRetraction F v w marked hw hv t m D g,
    normalizedMarkedRetraction_pure F v w marked hw hv t m D hm g⟩

variable (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e)
  (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
    (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

noncomputable def markedLocalCoefficientValue (V : E.Space → ℂ) (g : D.RealGroup) : ℂ :=
  V (markedPureSpaceMap F v w marked t D J hJ E 0 hmap
    (QuotientGroup.mk (normalizedMarkedPureRetraction F v w marked hw hv t m hm D g)))

theorem markedLocalCoefficientValue_apply (V : E.Space → ℂ) (g : D.RealGroup) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ
        (normalizedMarkedRetraction F v w marked hw hv t m D g).coord⟩ : E.RealGroup)) := rfl

theorem markedLocalCoefficientValue_scaled_parameter (V : E.Space → ℂ) (a : Fin t → ℝ) (g : D.RealGroup)
    (hg : torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord = 0) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V
      (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • a) * g) =
      V (QuotientGroup.mk (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ g.coord⟩ : E.RealGroup)) := by
  rw [markedLocalCoefficientValue_apply, normalizedMarkedRetraction_scaled_parameter F v w marked hw hv t m D hm a g hg]

theorem markedLocalCoefficientValue_eq_on_small_cosets
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice →
      IntegralVector (normalizedMarkedPhase F v w marked t m z.coord))
    (V : E.Space → ℂ) (g h : D.RealGroup)
    (hg : ∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4)
    (hh : ∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) h.coord i| ≤ 1 / 4)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h) :
    markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g =
      markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V h := by
  let φ := normalizedMarkedPhase F v w marked t m
  let R := normalizedMarkedPureRetraction F v w marked hw hv t m hm D
  have hph : torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord :=
    torusPhaseLinear_eq_of_small D φ hphase g h hg hh heq
  have hdiff : (R g)⁻¹ * R h ∈ D.realLattice.comap
      (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t)).subtype := by
    change (normalizedMarkedRetraction F v w marked hw hv t m D g)⁻¹ *
      normalizedMarkedRetraction F v w marked hw hv t m D h ∈ D.realLattice
    have hcalc : (normalizedMarkedRetraction F v w marked hw hv t m D g)⁻¹ *
        normalizedMarkedRetraction F v w marked hw hv t m D h = g⁻¹ * h := by
      dsimp only [φ] at hph
      unfold normalizedMarkedRetraction
      rw [hph]
      group
    rw [hcalc]
    exact QuotientGroup.eq.mp heq
  have hq : (QuotientGroup.mk (R g) : _ ⧸ D.realLattice.comap
      (realificationSubgroup (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (markedQuotientPolynomialAlgebra F v w marked t)).subtype) = QuotientGroup.mk (R h) :=
    QuotientGroup.eq.mpr hdiff
  exact congrArg (fun x => V (markedPureSpaceMap F v w marked t D J hJ E 0 hmap x)) hq

end Erdos3

end

end OAI

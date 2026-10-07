import OAI.Combinatorics.Progressions.Estimates.MarkedLocalCoefficientValue
import OAI.Combinatorics.Progressions.Nilpotent.BCHPairCoordinateMetric

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t m : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem realMarkedParameterDirection_coordinate_norm_le {p : ℝ}
    (ht : (t : ℝ) ≤ p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (a : Fin t → ℝ) :
    ‖(e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)‖ ≤
      Real.exp (2 * p) * ‖a‖ := by
  have hentries (i : Fin t) (j : Fin d) :
      |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ Real.exp p := by
    have hi : (RationalTorus.basis t i : Fin t → ℚ) = Pi.single i 1 := Pi.basisFun_apply ℚ (Fin t) i
    have h := hdir i j
    rw [hi] at h
    exact (rational_abs_real_le_numerator _).trans ((rationalLogHeight_le_iff _ _).mp h).1
  have hnorm : ‖(e.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t a)‖ ≤
      (t : ℝ) * ‖a‖ * Real.exp p := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    exact realMarkedParameterDirection_coordinate_le F v w marked t e a (norm_nonneg _)
      (fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i) hentries j
  apply hnorm.trans
  have ht' : (t : ℝ) ≤ Real.exp p := ht.trans (by linarith [Real.add_one_le_exp p])
  calc
    (t : ℝ) * ‖a‖ * Real.exp p ≤ Real.exp p * ‖a‖ * Real.exp p := by gcongr
    _ = Real.exp (2 * p) * ‖a‖ := by rw [show 2 * p = p + p by ring, Real.exp_add]; ring

theorem normalizedMarkedPhase_coordinate_norm_le {p : ℝ}
    (hd : (d : ℝ) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x‖ ≤
      Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  exact scalarExtension_coordinate_norm_le e (RationalTorus.basis t)
    (normalizedMarkedPhase F v w marked t m).toLinearMap
    (by simpa only [Fintype.card_fin] using hd)
    (fun i j => by
      change rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p
      exact hphase i j) x

noncomputable def markedPhaseRemovalLinear :
    (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) →ₗ[ℝ]
      (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  (realMarkedParameterDirection F v w marked t).comp
    ((m : ℝ) • (-torusPhaseLinear (normalizedMarkedPhase F v w marked t m)))

theorem markedPhaseRemovalLinear_apply (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    markedPhaseRemovalLinear F v w marked t m x =
      realMarkedParameterDirection F v w marked t
        ((m : ℝ) • -(torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x)) := rfl

theorem markedPhaseRemovalLinear_coordinate_norm_le {p : ℝ}
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    ‖(e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x)‖ ≤
      Real.exp (5 * p) * ‖(e.baseChange ℝ).equivFun x‖ := by
  rw [markedPhaseRemovalLinear_apply]
  apply (realMarkedParameterDirection_coordinate_norm_le F v w marked t e ht hdir _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m), norm_neg]
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) x‖) ≤
        Real.exp (2 * p) * (Real.exp p * (Real.exp (2 * p) * ‖(e.baseChange ℝ).equivFun x‖)) := by
      gcongr
      exact normalizedMarkedPhase_coordinate_norm_le F v w marked t m e hd hphase x
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem markedPhaseRemovalLinear_coordinate_dist_le {p : ℝ}
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (e.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (e j) i) ≤ p)
    (x y : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :
    dist ((e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x))
      ((e.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m y)) ≤
      Real.exp (5 * p) * dist ((e.baseChange ℝ).equivFun x) ((e.baseChange ℝ).equivFun y) := by
  simpa only [map_sub, ← dist_eq_norm] using
    markedPhaseRemovalLinear_coordinate_norm_le F v w marked t m e hd ht hm hdir hphase (x - y)

variable (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem normalizedMarkedRetraction_coord (g : D.RealGroup) :
    (normalizedMarkedRetraction F v w marked hw hv t m D g).coord =
      lieBCH (s + 1) (markedPhaseRemovalLinear F v w marked t m g.coord) g.coord := rfl

theorem normalizedMarkedRetraction_coordinate_dist_le {p B : ℝ} {H : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hB : 1 ≤ B) (g h : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B)
    (hh : ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ B) :
    dist ((D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D g).coord)
      ((D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D h).coord) ≤
      (bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p)) *
        dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord) := by
  let A := Real.exp (5 * p)
  have hA : 1 ≤ A := Real.one_le_exp (by positivity)
  have hBA : B ≤ A * B := by nlinarith
  have hbox (x : D.RealGroup) (hx : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ B) :
      ‖(D.basis.baseChange ℝ).equivFun (markedPhaseRemovalLinear F v w marked t m x.coord)‖ ≤ A * B :=
    (markedPhaseRemovalLinear_coordinate_norm_le F v w marked t m D.basis hd ht hm hdir hphase x.coord).trans
      (mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _))
  rw [normalizedMarkedRetraction_coord, normalizedMarkedRetraction_coord, mul_assoc]
  have hbch := lieBCH_pair_coordinate_dist_le (s := s + 1)
    (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc
    _ _ _ _ (hB.trans hBA) (by positivity)
    (hbox g hg) (hg.trans hBA) (hbox h hh) (hh.trans hBA)
    (markedPhaseRemovalLinear_coordinate_dist_le F v w marked t m D.basis hd ht hm hdir hphase _ _)
    (le_mul_of_one_le_left dist_nonneg hA)
  simpa only [Fintype.card_fin] using hbch

theorem normalizedMarkedRetraction_coordinate_norm_le {p B : ℝ} {H : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hB : 1 ≤ B) (g : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B) :
    ‖(D.basis.baseChange ℝ).equivFun (normalizedMarkedRetraction F v w marked hw hv t m D g).coord‖ ≤
      (bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p)) * B := by
  have hzero : normalizedMarkedRetraction F v w marked hw hv t m D 1 = 1 := by
    apply NilpotentLieBCHGroup.ext
    rw [normalizedMarkedRetraction_coord, coord_one, map_zero,
      lieBCH_zero_left D.filtration.realification.lowerCentralSeries_eq_bot]
  have h := normalizedMarkedRetraction_coordinate_dist_le F v w marked t m hw hv D
    hp hd ht hm hdir hphase hc hB g 1 hg (by simpa using (show (0 : ℝ) ≤ B by linarith))
  rw [hzero, coord_one, map_zero, dist_zero_right, dist_zero_right] at h
  exact h.trans (mul_le_mul_of_nonneg_left hg (mul_nonneg
    (bchBoxCoordinateBound_nonneg _ _ _ (mul_nonneg (Real.exp_nonneg _) (by linarith))) (Real.exp_nonneg _)))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def markedRetractionBoxConstant (s d H : ℕ) (p : ℝ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨bchBoxCoordinateBound (s + 1) d H (Real.exp (5 * p) * B) * Real.exp (5 * p),
    mul_nonneg (bchBoxCoordinateBound_nonneg _ _ _ (mul_nonneg (Real.exp_nonneg _) B.coe_nonneg))
      (Real.exp_nonneg _)⟩

noncomputable def markedEvaluationBoxRadius (s d H : ℕ) (p : ℝ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨Real.exp (2 * p), Real.exp_nonneg _⟩ * markedRetractionBoxConstant s d H p B * B + 1

noncomputable def markedLocalBoxConstant (s d H u e Ht : ℕ) (p : ℝ) (B ℓ : ℝ≥0) : ℝ≥0 :=
  ℓ * bchBoxMetricConstant u e Ht (markedEvaluationBoxRadius s d H p B) *
    ⟨Real.exp (2 * p), Real.exp_nonneg _⟩ * markedRetractionBoxConstant s d H p B

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e u : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ) (hm : 0 < m)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)
  (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (E : RationalFilteredNilmanifold (L ⧸ J) u e)
  (hmap : ∀ z : D.RealGroup, z ∈ D.realLattice →
    (⟨(markedBaseEvaluation F v w marked t J hJ 0).baseChange ℝ z.coord⟩ : E.RealGroup) ∈ E.realLattice)

theorem markedLocalCoefficientValue_norm_le (V : E.Space → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (g : D.RealGroup) :
    ‖markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g‖ ≤ 1 := hV _

variable [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ J))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ J))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ J))] [T2Space (ℝ ⊗[ℚ] (L ⧸ J))]

theorem markedLocalCoefficientValue_coordinate_dist_le {p : ℝ} {H Ht : ℕ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (heval : ∀ i j, rationalLogHeight (E.basis.repr
      (markedBaseEvaluation F v w marked t J hJ 0 (D.basis j)) i) ≤ p)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (hct : ∀ i j k, RationalHeightLE (lieStructureConstants E.basis i j k) Ht)
    (B ℓ : ℝ≥0) (hB : 1 ≤ B) (V : E.Space → ℂ)
    (hV : letI := E.metricSpace; LipschitzWith ℓ V)
    (g h : D.RealGroup)
    (hg : ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ B)
    (hh : ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ B) :
    dist (markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V g)
      (markedLocalCoefficientValue F v w marked hw hv t m hm D J hJ E hmap V h) ≤
        markedLocalBoxConstant s d H u e Ht p B ℓ *
          dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord) := by
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := E.metricSpace
  let q := markedBaseEvaluation F v w marked t J hJ 0
  let a (x : D.RealGroup) : E.RealGroup :=
    ⟨q.baseChange ℝ (normalizedMarkedRetraction F v w marked hw hv t m D x).coord⟩
  let R := markedRetractionBoxConstant s d H p B
  let T := markedEvaluationBoxRadius s d H p B
  let Δ := dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord)
  have hT : 1 ≤ T := by
    dsimp only [T, markedEvaluationBoxRadius]
    exact le_add_of_nonneg_left (by positivity)
  have hB' : (1 : ℝ) ≤ B := hB
  have hnorm (x : D.RealGroup) (hx : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ B) :
      ‖(E.basis.baseChange ℝ).equivFun (a x).coord‖ ≤ T := by
    have hr := normalizedMarkedRetraction_coordinate_norm_le F v w marked t m hw hv D
      hp hd ht hmp hdir hphase hc hB' x hx
    have he := scalarExtension_coordinate_norm_le D.basis E.basis q
      (by simpa only [Fintype.card_fin] using hd) heval
      (normalizedMarkedRetraction F v w marked hw hv t m D x).coord
    change ‖(E.basis.baseChange ℝ).equivFun (a x).coord‖ ≤
      Real.exp (2 * p) * (R : ℝ) * B + 1
    calc
      _ ≤ Real.exp (2 * p) * ‖(D.basis.baseChange ℝ).equivFun
          (normalizedMarkedRetraction F v w marked hw hv t m D x).coord‖ := he
      _ ≤ Real.exp (2 * p) * ((R : ℝ) * B) := mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
      _ ≤ _ := by ring_nf; linarith
  have hevaldist : dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
      ((E.basis.baseChange ℝ).equivFun (a h).coord) ≤ Real.exp (2 * p) * (R : ℝ) * Δ := by
    have hr := normalizedMarkedRetraction_coordinate_dist_le F v w marked t m hw hv D
      hp hd ht hmp hdir hphase hc hB' g h hg hh
    have he := scalarExtension_coordinate_dist_le D.basis E.basis q
      (by simpa only [Fintype.card_fin] using hd) heval
      (normalizedMarkedRetraction F v w marked hw hv t m D g).coord
      (normalizedMarkedRetraction F v w marked hw hv t m D h).coord
    exact he.trans ((mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)).trans_eq (mul_assoc _ _ _).symm)
  have hgroup : dist (a g) (a h) ≤ bchBoxMetricConstant u e Ht T * (Real.exp (2 * p) * (R : ℝ) * Δ) := by
    have hb := dist_le_bchBoxMetricConstant (E.basis.baseChange ℝ) (lieStructureConstants E.basis)
      (fun i j k => (realLieBasis_structure E.basis i j k).symm) hct T hT
      (show 0 ≤ Real.exp (2 * p) * (R : ℝ) * Δ by dsimp [Δ]; positivity) (a g) (a h)
      (fun i => by
        calc
          _ ≤ ‖(E.basis.baseChange ℝ).equivFun (a g).coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((E.basis.baseChange ℝ).equivFun (a g).coord) i
          _ ≤ T := hnorm g hg)
      (fun i => by
        calc
          _ ≤ ‖(E.basis.baseChange ℝ).equivFun (a h).coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((E.basis.baseChange ℝ).equivFun (a h).coord) i
          _ ≤ T := hnorm h hh)
      (fun i => by
        calc
          _ ≤ dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
              ((E.basis.baseChange ℝ).equivFun (a h).coord) := by
            simpa only [Real.dist_eq, Basis.equivFun_apply] using
              dist_le_pi_dist ((E.basis.baseChange ℝ).equivFun (a g).coord)
                ((E.basis.baseChange ℝ).equivFun (a h).coord) i
          _ ≤ _ := hevaldist)
    simpa only [Fintype.card_fin] using hb
  have hproj := quotientMetricSpace_lipschitz_mk (E.basis.baseChange ℝ) E.realLattice E.realLattice_closed_discrete.1
  have hvalue := (hV.comp hproj).dist_le_mul (a g) (a h)
  simp only [Function.comp_apply, mul_one] at hvalue
  change dist (V (QuotientGroup.mk (a g))) (V (QuotientGroup.mk (a h))) ≤ _
  apply hvalue.trans
  apply (mul_le_mul_of_nonneg_left hgroup ℓ.coe_nonneg).trans_eq
  change (ℓ : ℝ) * ((bchBoxMetricConstant u e Ht T : ℝ) * (Real.exp (2 * p) * (R : ℝ) * Δ)) =
    (((ℓ : ℝ) * (bchBoxMetricConstant u e Ht T : ℝ) * Real.exp (2 * p)) * (R : ℝ)) * Δ
  ring

end Erdos3

end

end OAI

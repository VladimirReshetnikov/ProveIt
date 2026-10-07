import OAI.Combinatorics.Progressions.Geometry.MarkedLocalObservableMetric

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem torusPhaseLinear_realLattice_integral {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))
    (γ : D.RealGroup) (hγ : γ ∈ D.realLattice) :
    ∃ a : Fin t → ℤ, torusPhaseLinear φ γ.coord = fun i => (a i : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨a, ha⟩ := hphase z hz
  refine ⟨a, funext fun i => ?_⟩
  change torusPhaseLinear φ ((1 : ℝ) ⊗ₜ[ℚ] z.coord) i = (a i : ℝ)
  rw [torusPhaseLinear_tmul, _root_.one_mul, ha i, Rat.cast_intCast]

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t m : ℕ)
  (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d)

theorem realMarkedParameterElement_scaled_integer_mem
    (hdir : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
        D.filtration.Group) ∈ D.lattice) (a : Fin t → ℤ) :
    (realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ))) :
      D.RealGroup) ∈ D.realLattice := by
  have h := markedDirection_mem_realLattice_of_smul F v w marked t D (m : ℚ)
    (fun i => (a i : ℚ)) (hdir a)
  have heq : realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ))) =
      (⟨realMarkedDirection F v w marked t ((m : ℚ) • (fun i => (a i : ℚ)))⟩ : D.RealGroup) := by
    apply NilpotentLieBCHGroup.ext
    change realMarkedParameterDirection F v w marked t _ = _
    rw [← realMarkedParameterDirection_rat]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast]
  exact heq ▸ h

theorem marked_phase_correction_coordinate_norm_le {p R : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hmp : (m : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p)
    (hphase : ∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p)
    (hR : 1 ≤ R) (g z γ : D.RealGroup) (hg : g = z * γ)
    (hgphase : ‖torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord‖ ≤ 1 / 4)
    (hz : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R) :
    ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t
      ((m : ℝ) • torusPhaseLinear (normalizedMarkedPhase F v w marked t m) γ.coord))‖ ≤
        2 * Real.exp (5 * p) * R := by
  let φ := normalizedMarkedPhase F v w marked t m
  have hsum : torusPhaseLinear φ g.coord = torusPhaseLinear φ z.coord + torusPhaseLinear φ γ.coord := by
    rw [hg, torusPhaseLinear_mul D]
  have hγ : torusPhaseLinear φ γ.coord = torusPhaseLinear φ g.coord - torusPhaseLinear φ z.coord := by
    rw [hsum, add_sub_cancel_left]
  have hzphase : ‖torusPhaseLinear φ z.coord‖ ≤ Real.exp (2 * p) * R :=
    (normalizedMarkedPhase_coordinate_norm_le F v w marked t m D.basis hd hphase z.coord).trans
      (mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _))
  have hγnorm : ‖torusPhaseLinear φ γ.coord‖ ≤ 1 / 4 + Real.exp (2 * p) * R := by
    rw [hγ]
    exact (norm_sub_le _ _).trans (add_le_add hgphase hzphase)
  have hlarge : 1 ≤ Real.exp (2 * p) * R :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) hR
  have hγnorm' : ‖torusPhaseLinear φ γ.coord‖ ≤ 2 * Real.exp (2 * p) * R := by
    nlinarith
  have h := realMarkedParameterDirection_coordinate_norm_le F v w marked t D.basis ht hdir
    ((m : ℝ) • torusPhaseLinear φ γ.coord)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)] at h
  apply h.trans
  calc
    Real.exp (2 * p) * ((m : ℝ) * ‖torusPhaseLinear φ γ.coord‖) ≤
        Real.exp (2 * p) * (Real.exp p * (2 * Real.exp (2 * p) * R)) := by gcongr
    _ = 2 * Real.exp (5 * p) * R := by
      rw [show 5 * p = 2 * p + p + 2 * p by ring, Real.exp_add, Real.exp_add]
      ring

theorem exists_marked_phase_band_representatives (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {r d t m : ℕ}
      (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
      (_hw : ∀ i, 0 < w i) (_hv : ∀ i, v i ∈ F.layer (w i) 1)
      [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t)]
      (D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (t : ℝ) ≤ p → 0 < m → (m : ℝ) ≤ Real.exp p →
      (∀ i j, rationalLogHeight
        (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) →
      (∀ i j, rationalLogHeight (normalizedMarkedPhase F v w marked t m (D.basis j) i) ≤ p) →
      (∀ z : D.filtration.Group, z ∈ D.lattice →
        IntegralVector (normalizedMarkedPhase F v w marked t m z.coord)) →
      (∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          D.filtration.Group) ∈ D.lattice) →
      ∀ g : D.RealGroup,
        (∀ i, |torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord i| ≤ 1 / 4) →
        ∃ z : D.RealGroup,
          (QuotientGroup.mk z : D.Space) = QuotientGroup.mk g ∧
          torusPhaseLinear (normalizedMarkedPhase F v w marked t m) z.coord =
            torusPhaseLinear (normalizedMarkedPhase F v w marked t m) g.coord ∧
          ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨A, hA, hrep⟩ := exists_realification_representatives_exp_bound (s + 1)
  obtain ⟨B, hB, hprod⟩ := exists_bch_group_product_exp_bound (s + 1) (A + 2)
  refine ⟨(A + 10) + B + 2, by omega, ?_⟩
  intro I L _ _ r d t m F v w marked hw hv _ _ _ D p hp hD ht hm hmp hdir hphase hint hlat g hg
  let φ := normalizedMarkedPhase F v w marked t m
  let H := ⌈Real.exp p⌉₊
  have hc (i j k) : RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨z, hz, γ, hγ, heq⟩ := hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice
    D.grid H (p + 1) D.grid_pos D.inner_grid hc (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
  let R := Real.exp (((p + 1) + A) ^ A)
  have hR : 1 ≤ R := Real.one_le_exp (by positivity)
  have hznorm : ‖(D.basis.baseChange ℝ).equivFun z.coord‖ ≤ R :=
    (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr (fun i => by
      simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using hz i)
  obtain ⟨a, ha⟩ := torusPhaseLinear_realLattice_integral D φ hint γ hγ
  let δ : D.RealGroup := realMarkedParameterElement F v w marked hw hv t ((m : ℝ) • (fun i => (a i : ℝ)))
  have hδ : δ ∈ D.realLattice := realMarkedParameterElement_scaled_integer_mem F v w marked hw hv t m D hlat a
  have hδphase : torusPhaseLinear φ δ.coord = torusPhaseLinear φ γ.coord := by
    change torusPhaseLinear φ (realMarkedParameterDirection F v w marked t _) = _
    rw [normalizedMarkedPhase_real_scaled_parameter F v w marked t m hm, ha]
  have hδnorm : ‖(D.basis.baseChange ℝ).equivFun δ.coord‖ ≤ 2 * Real.exp (5 * p) * R := by
    change ‖(D.basis.baseChange ℝ).equivFun (realMarkedParameterDirection F v w marked t _)‖ ≤ _
    rw [← ha]
    exact marked_phase_correction_coordinate_norm_le F v w marked t m D hp hD.1 ht hmp hdir hphase
      hR g z γ heq ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun i => by
        simpa only [Real.norm_eq_abs] using hg i)) hznorm
  let q := p + (A + 10 : ℕ)
  have hpq : p + 1 ≤ q := by dsimp [q]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) A]
  have hq : 0 ≤ q := by positivity
  have hinput : 2 * Real.exp (5 * p) * R ≤ Real.exp ((q + 2) ^ (A + 2)) := by
    have hQ : 6 ≤ q + 2 := by dsimp [q]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) A]
    have hpQ : p ≤ q + 2 := by linarith
    have hQpow : q + 2 ≤ (q + 2) ^ A := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ q + 2) (by omega : 1 ≤ A)
    have hRpow : ((p + 1) + A) ^ A ≤ (q + 2) ^ A :=
      pow_le_pow_left₀ (by positivity) (by dsimp [q]; push_cast; linarith) A
    have hexp : 1 + 5 * p + ((p + 1) + A) ^ A ≤ (q + 2) ^ (A + 2) := by
      calc
        _ ≤ 7 * (q + 2) ^ A := by nlinarith
        _ ≤ (q + 2) ^ A * (q + 2) ^ 2 :=
          by nlinarith [pow_nonneg (by linarith : 0 ≤ q + 2) A, sq_nonneg (q + 2 - 3)]
        _ = _ := (pow_add _ _ _).symm
    calc
      _ ≤ Real.exp 1 * Real.exp (5 * p) * Real.exp (((p + 1) + A) ^ A) := by
        gcongr
        linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp (1 + 5 * p + ((p + 1) + A) ^ A) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hRinput : R ≤ Real.exp ((q + 2) ^ (A + 2)) := by
    apply le_trans ?_ hinput
    have he : 1 ≤ Real.exp (5 * p) := Real.one_le_exp (by positivity)
    nlinarith [Real.exp_nonneg (5 * p)]
  refine ⟨z * δ, ?_, ?_, ?_⟩
  · rw [heq]
    exact (QuotientGroup.mk_mul_of_mem z hδ).trans
      (QuotientGroup.mk_mul_of_mem z (show γ ∈ D.realLattice from hγ)).symm
  · rw [heq, torusPhaseLinear_mul D, torusPhaseLinear_mul D, hδphase]
  · have hbound := hprod (D.basis.baseChange ℝ) (lieStructureConstants D.basis) H q
      D.filtration.realification.lowerCentralSeries_eq_bot [z, δ]
      (fun i j k => (realLieBasis_structure D.basis i j k).symm) hq
      (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ q))
      (by simpa using (show 2 ≤ s + 1 by omega))
      ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hpq)) hc
      (by
        intro x hx i
        have hxnorm : ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ Real.exp ((q + 2) ^ (A + 2)) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hznorm.trans hRinput
          · exact hδnorm.trans hinput
        calc
          _ ≤ ‖(D.basis.baseChange ℝ).equivFun x.coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((D.basis.baseChange ℝ).equivFun x.coord) i
          _ ≤ _ := hxnorm)
    have hfinal := Real.exp_le_exp.mpr (shifted_center_power_bound (A + 10) B hp)
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr
    intro i
    simpa only [List.prod_cons, List.prod_nil, mul_one, Real.norm_eq_abs, Basis.equivFun_apply] using
      (hbound i).trans hfinal

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}
  (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
  (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

include hphase in
theorem torusPhaseLinear_eq_of_close (g h : D.RealGroup)
    (heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h)
    (hclose : dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) < 1) :
    torusPhaseLinear φ g.coord = torusPhaseLinear φ h.coord := by
  obtain ⟨a, ha⟩ := torusPhaseLinear_realLattice_integral D φ hphase (g⁻¹ * h) (QuotientGroup.eq.mp heq)
  rw [torusPhaseLinear_mul, torusPhaseLinear_inv] at ha
  funext i
  have hai : -torusPhaseLinear φ g.coord i + torusPhaseLinear φ h.coord i = (a i : ℝ) := congrFun ha i
  have hi : |(a i : ℝ)| < 1 := by
    rw [← hai, neg_add_eq_sub, abs_sub_comm]
    exact (dist_le_pi_dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) i).trans_lt hclose
  have hzero : a i = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hi)
  rw [hzero, Int.cast_zero] at hai
  linarith

include hphase in
theorem torusPhaseLinear_eq_in_band_of_near (g h z : D.RealGroup)
    (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4)
    (hz : (QuotientGroup.mk z : D.Space) = QuotientGroup.mk h)
    (hnear : dist (torusPhaseLinear φ z.coord) (torusPhaseLinear φ g.coord) < 1 / 4) :
    torusPhaseLinear φ z.coord = torusPhaseLinear φ h.coord := by
  apply torusPhaseLinear_eq_of_close D φ hphase z h hz
  have hgh : dist (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord) ≤ 1 / 2 := by
    have h := dist_le_norm_add_norm (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord)
    linarith
  have h := dist_triangle (torusPhaseLinear φ z.coord) (torusPhaseLinear φ g.coord) (torusPhaseLinear φ h.coord)
  linarith

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem torusPhaseLinear_group_lipschitz (H : ℕ)
    (hH : ∀ i j, RationalHeightLE (φ (D.basis j) i) H) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound t d H) (fun g : D.RealGroup => torusPhaseLinear φ g.coord) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (RationalTorus.nilmanifold t).filtration.realification.lowerCentralSeries_eq_bot)
    ((RationalTorus.basis t).baseChange ℝ)
  have hf := lipschitz_realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot)
    D.basis (RationalTorus.basis t) φ H (fun i j => by
      change RationalHeightLE (φ (D.basis j) i) H
      exact hH i j)
  have hc := (RationalTorus.nilmanifold t).filtration.realification.stepOne_coordinates_lipschitz
    ((RationalTorus.basis t).baseChange ℝ)
  have h := hc.comp hf
  change LipschitzWith (1 * coordinateLipschitzBound (Fintype.card (Fin t)) (Fintype.card (Fin d)) H)
    (fun g : D.RealGroup => torusPhaseLinear φ g.coord) at h
  simpa only [one_mul, Fintype.card_fin] using h

theorem torusPhaseLinear_group_lipschitz_exp {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hcoords : ∀ i j, rationalLogHeight (φ (D.basis j) i) ≤ p) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    LipschitzWith ⟨Real.exp ((p + 3) ^ 2), Real.exp_nonneg _⟩
      (fun g : D.RealGroup => torusPhaseLinear φ g.coord) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  apply (torusPhaseLinear_group_lipschitz D φ ⌈Real.exp p⌉₊
    (fun i j => rationalHeightLE_ceil_exp (hcoords i j))).weaken
  have h := coordinateLipschitzBound_le_exp t d ⌈Real.exp p⌉₊
    (show 0 ≤ p + 1 by linarith) (ht.trans (by linarith : p ≤ p + 1))
    (hd.trans (by linarith : p ≤ p + 1)) (ceil_exp_le_exp_add_one hp)
  change (coordinateLipschitzBound t d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp ((p + 3) ^ 2)
  simpa only [show p + 1 + 2 = p + 3 by ring] using h

include hphase in
theorem exists_nearby_phase_band_lift {K : ℝ≥0}
    (hK : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      LipschitzWith K (fun g : D.RealGroup => torusPhaseLinear φ g.coord))
    (g h : D.RealGroup)
    (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
    letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
    letI := D.metricSpace
    let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
    0 < ρ → (K : ℝ) * (2 * ρ) < 1 / 4 →
      ∃ z : D.RealGroup, (QuotientGroup.mk z : D.Space) = QuotientGroup.mk h ∧
        torusPhaseLinear φ z.coord = torusPhaseLinear φ h.coord ∧ dist z g < 2 * ρ := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  dsimp only
  intro hρ hnear
  let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
  obtain ⟨z, hzg, hz⟩ := rightCosetMetricSpace_exists_lift D.realLattice D.realLattice_closed_discrete.1
    g (2 * ρ) (QuotientGroup.mk h) (by
      change dist (QuotientGroup.mk h : D.Space) (QuotientGroup.mk g) < 2 * ρ
      rw [dist_comm]
      change ρ < 2 * ρ
      linarith)
  refine ⟨z, hz, ?_, hzg⟩
  apply torusPhaseLinear_eq_in_band_of_near D φ hphase g h z hg hh hz
  exact ((hK.dist_le_mul z g).trans (mul_le_mul_of_nonneg_left hzg.le K.coe_nonneg)).trans_lt hnear

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def phaseBandCoordinateConstant (s d H : ℕ) (R : ℝ≥0) : ℝ≥0 :=
  bchLogMetricConstant s d H R * bchLogMetricConstant s d H 1

noncomputable def phaseBandQuotientConstant (s d H : ℕ) (R K L : ℝ≥0) : ℝ≥0 :=
  2 * phaseBandCoordinateConstant s d H R * L +
    16 * (K + bchLogMetricConstant s d H 1 + phaseBandCoordinateConstant s d H R + 1)

theorem phase_band_quotient_dist_le {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t H : ℕ} (D : RationalFilteredNilmanifold L s d)
    (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)
    (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (R K A : ℝ≥0) (hR : 1 ≤ R)
    (hK : letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      LipschitzWith K (fun g : D.RealGroup => torusPhaseLinear φ g.coord))
    (hrep : ∀ g : D.RealGroup, ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4 →
      ∃ x : D.RealGroup, (QuotientGroup.mk x : D.Space) = QuotientGroup.mk g ∧
        torusPhaseLinear φ x.coord = torusPhaseLinear φ g.coord ∧
        ‖(D.basis.baseChange ℝ).equivFun x.coord‖ ≤ R)
    (u : D.RealGroup → ℂ) (hu : ∀ g, ‖u g‖ ≤ 1)
    (hsame : ∀ g h : D.RealGroup, ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4 →
      ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4 →
      (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h → u g = u h)
    (hbox : ∀ g h : D.RealGroup, ‖(D.basis.baseChange ℝ).equivFun g.coord‖ ≤ (R : ℝ) + 1 →
      ‖(D.basis.baseChange ℝ).equivFun h.coord‖ ≤ (R : ℝ) + 1 →
      dist (u g) (u h) ≤ A *
        dist ((D.basis.baseChange ℝ).equivFun g.coord) ((D.basis.baseChange ℝ).equivFun h.coord))
    (g h : D.RealGroup) (hg : ‖torusPhaseLinear φ g.coord‖ ≤ 1 / 4)
    (hh : ‖torusPhaseLinear φ h.coord‖ ≤ 1 / 4) :
    letI := D.metricSpace
    dist (u g) (u h) ≤ phaseBandQuotientConstant s d H R K A *
      dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h) := by
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := D.metricSpace
  let C := bchLogMetricConstant s d H 1
  let B := phaseBandCoordinateConstant s d H R
  let S : ℝ := (K : ℝ) + C + B + 1
  let ρ := dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk h)
  change dist (u g) (u h) ≤ (2 * (B : ℝ) * A + 16 * S) * ρ
  by_cases heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk h
  · have huu := hsame g h hg hh heq
    have hρ : ρ = 0 := by simp only [ρ, heq, dist_self]
    simp only [huu, hρ, dist_self, mul_zero, le_refl]
  have hρ : 0 < ρ := dist_pos.mpr heq
  have hS : 0 ≤ S := by dsimp [S]; positivity
  by_cases hnear : S * ρ < 1 / 8
  · have hsmall (T : ℝ≥0) (hT : (T : ℝ) ≤ S) : (T : ℝ) * (2 * ρ) < 1 / 4 := by
      have ht := mul_le_mul_of_nonneg_right hT hρ.le
      nlinarith
    have hKS : (K : ℝ) ≤ S := by dsimp [S]; linarith [C.coe_nonneg, B.coe_nonneg]
    have hCS : (C : ℝ) ≤ S := by dsimp [S]; linarith [K.coe_nonneg, B.coe_nonneg]
    have hBS : (B : ℝ) ≤ S := by dsimp [S]; linarith [K.coe_nonneg, C.coe_nonneg]
    obtain ⟨x, hxq, hxp, hx⟩ := hrep g hg
    have hxphase : ‖torusPhaseLinear φ x.coord‖ ≤ 1 / 4 := by rw [hxp]; exact hg
    have hρx : dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk h) = ρ := by rw [hxq]
    obtain ⟨y, hyq, hyp, hyx⟩ := exists_nearby_phase_band_lift D φ hphase hK x h hxphase hh
      (by rw [hρx]; exact hρ) (by rw [hρx]; exact hsmall K hKS)
    rw [hρx] at hyx
    have hyphase : ‖torusPhaseLinear φ y.coord‖ ≤ 1 / 4 := by rw [hyp]; exact hh
    have hdxy : dist x y < 2 * ρ := by simpa only [dist_comm] using hyx
    have hCnear : (C : ℝ) * dist x y < 1 := by
      have ht := (mul_le_mul_of_nonneg_left hdxy.le C.coe_nonneg).trans_lt (hsmall C hCS)
      linarith
    have hcoords := dist_coordinates_le_of_near_box (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
      (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc R hR x y
      (fun i => by
        calc
          _ ≤ ‖(D.basis.baseChange ℝ).equivFun x.coord‖ := by
            simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using
              norm_le_pi_norm ((D.basis.baseChange ℝ).equivFun x.coord) i
          _ ≤ R := hx)
      (by simpa only [Fintype.card_fin] using hCnear)
    have hraw : bchBoxCoordinateBound s d H R * (C : ℝ) ≤ B := by
      change bchBoxCoordinateBound s d H R * (C : ℝ) ≤
        (bchBoxCoordinateBound s d H R + 1) * (C : ℝ)
      nlinarith [C.coe_nonneg]
    have hxy : dist ((D.basis.baseChange ℝ).equivFun x.coord)
        ((D.basis.baseChange ℝ).equivFun y.coord) ≤ (B : ℝ) * dist x y := by
      apply (show _ ≤ bchBoxCoordinateBound s d H R * (C : ℝ) * dist x y by
        simpa only [Fintype.card_fin, basisHomeomorph_apply] using hcoords).trans
      exact mul_le_mul_of_nonneg_right hraw dist_nonneg
    have hxy' : dist ((D.basis.baseChange ℝ).equivFun x.coord)
        ((D.basis.baseChange ℝ).equivFun y.coord) ≤ (B : ℝ) * (2 * ρ) :=
      hxy.trans (mul_le_mul_of_nonneg_left hdxy.le B.coe_nonneg)
    have hybox : ‖(D.basis.baseChange ℝ).equivFun y.coord‖ ≤ (R : ℝ) + 1 := by
      have ht := norm_sub_norm_le ((D.basis.baseChange ℝ).equivFun y.coord)
        ((D.basis.baseChange ℝ).equivFun x.coord)
      rw [← dist_eq_norm, dist_comm] at ht
      have hclose := hxy'.trans_lt (hsmall B hBS)
      linarith
    have hux := hsame x g hxphase hg hxq
    have huy := hsame y h hyphase hh hyq
    calc
      dist (u g) (u h) = dist (u x) (u y) := by rw [hux, huy]
      _ ≤ A * dist ((D.basis.baseChange ℝ).equivFun x.coord)
          ((D.basis.baseChange ℝ).equivFun y.coord) := hbox x y (by linarith) hybox
      _ ≤ A * ((B : ℝ) * (2 * ρ)) := mul_le_mul_of_nonneg_left hxy' A.coe_nonneg
      _ ≤ (2 * (B : ℝ) * A + 16 * S) * ρ := by nlinarith [mul_nonneg hS hρ.le]
  · have hdist := (dist_le_norm_add_norm (u g) (u h)).trans (add_le_add (hu g) (hu h))
    have hf : 1 / 8 ≤ S * ρ := le_of_not_gt hnear
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * B) A.coe_nonneg) hρ.le]

end Erdos3

end

end OAI

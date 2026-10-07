/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.NativeParameterCoverBudget
import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
import OAI.Combinatorics.Progressions.Sampling.NativeGridRightDictionary

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_coordinateBox_cover {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d H : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    let n := (boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε + 1) ^ d
    ∃ centers : Fin n → coordinateBox
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B,
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ)
      ∀ x : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ) B, ∃ j, dist x (centers j) ≤ ε := by
  classical
  have hcover := exists_coordinateBox_metric_cover
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ) (lieStructureConstants D.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hc B hB hε
  change ∃ centers : (Fin d → Fin (boxCoverMeshCount B
      (bchBoxMetricConstant s (Fintype.card (Fin d)) H B) ε + 1)) →
      coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B,
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ∀ x : coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B, ∃ j, dist x (centers j) ≤ ε at hcover
  rw [Fintype.card_fin] at hcover
  obtain ⟨c, hc⟩ := hcover
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let N := boxCoverMeshCount B (bchBoxMetricConstant s d H B) ε
  let I := Fin d → Fin (N + 1)
  have hcard : Fintype.card I = (N + 1) ^ d := by simp only [I, Fintype.card_fun, Fintype.card_fin]
  let e : I ≃ Fin ((N + 1) ^ d) := Fintype.equivFinOfCardEq hcard
  refine ⟨fun i => c (e.symm i), ?_⟩
  intro x
  obtain ⟨j, hj⟩ := hc x
  refine ⟨e j, ?_⟩
  simpa only [e.symm_apply_apply] using hj

theorem exists_native_group_parameter_cover (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) (B : ℝ≥0) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 1 ≤ B →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) → 0 < ε → 1 / ε ≤ Real.exp p →
      let A := coordinateBox (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.basis.baseChange ℝ) B
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ centers : Fin n → A,
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          ∀ x : A, ∃ j, dist x (centers j) ≤ ε := by
  obtain ⟨C₀, _, hsize⟩ := exists_bchBoxCover_count_budget s r
  refine ⟨1 + C₀ + 2, by omega, ?_⟩
  intro L _ _ _ _ _ _ d D B p ε hp hD hB hBp hε hεinv
  let H := ⌈Real.exp p⌉₊
  have hh : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  obtain ⟨c, hc⟩ := D.exists_native_coordinateBox_cover hh B hB hε
  have hcount := hsize d H B (p := p + 1) (by linarith) (by linarith [hD.1])
    (ceil_exp_le_exp_add_one hp)
    (hBp.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) r))) hε
    (hεinv.trans (Real.exp_le_exp.mpr (by linarith)))
  have hshift : ((p + 1) + C₀) ^ C₀ ≤ (p + (1 + C₀ + 2 : ℕ)) ^ (1 + C₀ + 2) := by
    simpa only [Nat.cast_one] using shifted_center_power_bound 1 C₀ hp
  exact ⟨_, by positivity, hcount.trans (Real.exp_le_exp.mpr hshift), c, hc⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_frozen_parameter_fiber (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (H : Finset G) (a u : G → D.RealGroup), H.Nonempty →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, ∀ i, |(D.basis.baseChange ℝ).repr (u h).coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (∀ h ∈ H, (D.basis.baseChange ℝ).equivFun (u h).coord ∈ realDenominatorGrid q) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ a₀ u₀ : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr a₀.coord i| ≤ Real.exp ((p + 2) ^ k)) ∧
          (∀ i, |(D.basis.baseChange ℝ).repr u₀.coord i| ≤ Real.exp ((p + 2) ^ k)) ∧
          (D.basis.baseChange ℝ).equivFun u₀.coord ∈ realDenominatorGrid q ∧
          letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)
          ∀ h ∈ H', dist (a h) a₀ ≤ ε ∧ u h = u₀ := by
  obtain ⟨b, _, hcover⟩ := exists_native_group_parameter_cover s k
  let A := k + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C b) ^ b +
      (Polynomial.X + Polynomial.C (A + 5)) ^ (A + 5))
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D p ε hp hD hε hεp q hq hqp H a u hH ha hu hugrid
  classical
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let B : ℝ≥0 := ⟨Real.exp ((p + 2) ^ k), (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := by
    change (1 : ℝ) ≤ Real.exp ((p + 2) ^ k)
    exact Real.one_le_exp (pow_nonneg (by linarith) _)
  obtain ⟨n, hn, hnp, centers, hnet⟩ := hcover D B hp hD hB le_rfl hε hεp
  have hac (h : {h // h ∈ H}) : a h ∈ coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) B :=
    ha h h.property
  choose index hindex using fun h : {h // h ∈ H} => hnet ⟨a h, hac h⟩
  let label (h : G) : Fin n := if hh : h ∈ H then index ⟨h, hh⟩ else ⟨0, hn⟩
  have hlabel (h : G) (hh : h ∈ H) : dist (a h) (centers (label h)).val ≤ ε := by
    simpa only [label, dite_eq_left hh, Subtype.dist_eq] using hindex ⟨h, hh⟩
  let S : Set (Fin d → ℝ) := {v | (∀ i, |v i| ≤ B) ∧ v ∈ realDenominatorGrid q}
  have hA : 2 ≤ A := by dsimp [A]; omega
  have hpow : (p + 2) ^ k ≤ (p + A) ^ A := by
    have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by linarith) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith) (by dsimp [A]; omega))
  obtain ⟨hS, hScard⟩ := finite_card_real_grid_box S q
    ⌈(q : ℝ) * Real.exp ((p + A) ^ A)⌉₊ hq (fun _ hv => hv.2)
    (fun v hv i => (hv.1 i).trans (Real.exp_le_exp.mpr hpow)) (Nat.le_ceil _)
  have hScount : (S.ncard : ℝ) ≤ Real.exp ((p + (A + 5 : ℕ)) ^ (A + 5)) := by
    apply (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hScard)).trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using grid_box_count_le_exp A d q hA hp hD.1 hqp
  let colors : Set (Fin n × (Fin d → ℝ)) := Set.univ ×ˢ S
  have hcolors : colors.Finite := (Set.toFinite (Set.univ : Set (Fin n))).prod hS
  let code (h : G) : Fin n × (Fin d → ℝ) :=
    (label h, (D.basis.baseChange ℝ).equivFun (u h).coord)
  have hcode (h : G) (hh : h ∈ H) : code h ∈ colors :=
    ⟨Set.mem_univ _, hu h hh, hugrid h hh⟩
  have hcost : (p + b) ^ b + (p + (A + 5 : ℕ)) ^ (A + 5) ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have hcount : (colors.ncard : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [colors, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul hnp hScount (Nat.cast_nonneg _) (Real.exp_pos _).le).trans
      (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hcost)
  obtain ⟨⟨j, z⟩, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H hH code colors hcolors hcode hcount
  obtain ⟨h₀, hh₀⟩ := hnonempty
  refine ⟨H', hsub, ⟨h₀, hh₀⟩, hdense, (centers j).val, u h₀,
    (centers j).property, hu h₀ (hsub hh₀), hugrid h₀ (hsub hh₀), ?_⟩
  intro h hh
  have hi : label h = j := congrArg Prod.fst (hconstant h hh)
  refine ⟨by simpa only [hi] using hlabel h (hsub hh), ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply (D.basis.baseChange ℝ).equivFun.injective
  exact (congrArg Prod.snd (hconstant h hh)).trans (congrArg Prod.snd (hconstant h₀ hh₀)).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_quotient_parameter_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ε : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ε → 1 / ε ≤ Real.exp p →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ ∃ centers : Fin n → D.Space,
        letI := D.metricSpace
        ∀ x : D.Space, ∃ j, dist x (centers j) ≤ ε := by
  obtain ⟨A, hA, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C₀, _, hsize⟩ := exists_bchBoxCover_count_budget s A
  refine ⟨(A + 1) + C₀ + 2, by omega, ?_⟩
  intro L _ _ _ _ _ _ d D p ε hp hD hε hεinv
  let H := ⌈Real.exp p⌉₊
  let B : ℝ≥0 := ⟨Real.exp (((p + 1) + A) ^ A), (Real.exp_pos _).le⟩
  have hB : 1 ≤ B := Real.one_le_exp (pow_nonneg (by positivity) _)
  have hh : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)
  have hr := hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid H (p + 1)
    D.grid_pos D.inner_grid hh (by linarith)
    (by simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p + 1 by linarith))
    (ceil_exp_le_exp_add_one hp) (hD.2.1.trans (Real.exp_le_exp.mpr (by linarith)))
  obtain ⟨c, hc⟩ := D.exists_native_coordinateBox_cover hh B hB hε
  let t := p + (A + 1 : ℕ)
  have hpt : p ≤ t := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hp1t : p + 1 ≤ t := by dsimp [t]; push_cast; linarith
  have hBt : (B : ℝ) ≤ Real.exp ((t + 2) ^ A) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  have hcount := hsize d H B (p := t) (hp.trans hpt) (hD.1.trans hpt)
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1t)) hBt hε
    (hεinv.trans (Real.exp_le_exp.mpr hpt))
  have hshift : (t + C₀) ^ C₀ ≤ (p + ((A + 1) + C₀ + 2 : ℕ)) ^ ((A + 1) + C₀ + 2) :=
    shifted_center_power_bound (A + 1) C₀ hp
  refine ⟨_, by positivity, hcount.trans (Real.exp_le_exp.mpr hshift),
    fun j => QuotientGroup.mk (c j).val, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := D.metricSpace
  have hproj : LipschitzWith 1 (QuotientGroup.mk : D.RealGroup → D.Space) :=
    quotientMetricSpace_lipschitz_mk (D.basis.baseChange ℝ) D.realLattice D.realLattice_closed_discrete.1
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨r, hr, γ, hγ, hg⟩ := hr g
    obtain ⟨j, hj⟩ := hc ⟨r, hr⟩
    refine ⟨j, ?_⟩
    change dist (QuotientGroup.mk g : D.Space) (QuotientGroup.mk (c j).val) ≤ ε
    have heq : (QuotientGroup.mk g : D.Space) = QuotientGroup.mk r := by
      rw [hg]
      exact QuotientGroup.mk_mul_of_mem r (show γ ∈ D.realLattice from hγ)
    rw [heq]
    have hdist : dist (QuotientGroup.mk r : D.Space) (QuotientGroup.mk (c j).val) ≤ dist r (c j).val := by
      simpa only [NNReal.coe_one, one_mul] using hproj.dist_le_mul r (c j).val
    exact hdist.trans hj

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_positive_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p ρ : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → 0 < ρ →
      1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      letI := D.metricSpace
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ ψ : Fin n → D.Space → ℝ,
          (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
          (∀ x, ∑ i, ψ i x = 1) ∧
          (∀ i, LipschitzWith K (ψ i)) ∧
          ∀ i x y, 0 < ψ i x → 0 < ψ i y → dist x y ≤ ρ := by
  obtain ⟨A, _, hcover⟩ := exists_native_quotient_parameter_cover s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ a + 4
  let B := T + (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * B + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p ρ hp hD hρ hρinv
  let t := p + (p + 2) ^ a + 4
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (show 0 ≤ p + 2 by linarith) a]
  have ht : 0 ≤ t := hp.trans hpt
  let r : ℝ≥0 := ⟨ρ / 4, (div_pos hρ (by norm_num)).le⟩
  have hr : 0 < r := div_pos hρ (by norm_num)
  have hrinv : 1 / (r : ℝ) ≤ Real.exp t := by
    calc
      _ = 4 * (1 / ρ) := by change 1 / (ρ / 4) = 4 * (1 / ρ); ring
      _ ≤ Real.exp 4 * Real.exp ((p + 2) ^ a) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)]) hρinv
          (by positivity) (Real.exp_pos _).le
      _ = Real.exp (4 + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨n, hn, hnb, c, hc⟩ := hcover D ht (hD.mono D hpt) (show 0 < (r : ℝ) from hr) hrinv
  let b := t + (t + A) ^ A
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have htb : t ≤ b := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hAb : (t + A) ^ A ≤ b := le_add_of_nonneg_left ht
  have hcost : 2 * b + 2 ≤ (p + C) ^ C := by
    simpa [B, T, X, b, t, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : b ≤ (p + C) ^ C := by linarith
  let K : ℝ≥0 := (2 * n + 1) / r
  have hK : (K : ℝ) ≤ Real.exp ((p + C) ^ C) :=
    (metricPartition_constant_le_exp n r hb
      (hnb.trans (Real.exp_le_exp.mpr hAb))
      (hrinv.trans (Real.exp_le_exp.mpr htb))).trans (Real.exp_le_exp.mpr hcost)
  let := D.metricSpace
  let ψ := metricTentPartition c r
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr (hAb.trans hbC)), K, hK, ψ,
    fun i x => ⟨metricTentPartition_nonneg c r i x, metricTentPartition_le_one c hr hc i x⟩,
    sum_metricTentPartition c hr hc, fun i => ?_, ?_⟩
  · simpa only [Fintype.card_fin] using lipschitz_metricTentPartition c hr hc i
  · intro i x y hx hy
    have hxc : dist x (c i) < 2 * (r : ℝ) := by
      by_contra h
      have hz := metricTentPartition_zero_of_far c r i x (le_of_not_gt h)
      change 0 < metricTentPartition c r i x at hx
      linarith
    have hyc : dist y (c i) < 2 * (r : ℝ) := by
      by_contra h
      have hz := metricTentPartition_zero_of_far c r i y (le_of_not_gt h)
      change 0 < metricTentPartition c r i y at hy
      linarith
    have htri := dist_triangle x (c i) y
    rw [dist_comm (c i) y] at htri
    change dist x (c i) < 2 * (ρ / 4) at hxc
    change dist y (c i) < 2 * (ρ / 4) at hyc
    linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_sub_positive_sum_le {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ) (error : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (herr : ∀ i, 0 < w i → ‖t - c i‖ ≤ error) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ error := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * (t - c i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i * error := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      rcases (hw i).eq_or_lt with hi | hi
      · rw [← hi, zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (herr i hi) (hw i)
    _ = error := by rw [← Finset.sum_mul, hsum, one_mul]

theorem exists_complex_partition_approximation {I X : Type*} [Fintype I]
    [PseudoMetricSpace X] (w : I → X → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    {rho : ℝ} (hdiam : ∀ i x y, 0 < w i x → 0 < w i y → dist x y ≤ rho)
    (F : X → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧
      ∀ x, ‖F x - ∑ i, (w i x : ℂ) * c i‖ ≤ (K : ℝ) * rho := by
  classical
  have hchoose (i : I) : ∃ c : ℂ, ‖c‖ ≤ 1 ∧
      ∀ x, 0 < w i x → ‖F x - c‖ ≤ (K : ℝ) * rho := by
    by_cases hi : ∃ y, 0 < w i y
    · obtain ⟨y, hy⟩ := hi
      refine ⟨F y, hF y, fun x hx => ?_⟩
      have h := hLip.dist_le_mul x y
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hdiam i x y hx hy) K.coe_nonneg)
    · refine ⟨0, by norm_num, fun x hx => False.elim (hi ⟨x, hx⟩)⟩
  choose c hc herr using hchoose
  exact ⟨c, hc, fun x => norm_sub_positive_sum_le (fun i => w i x) c (F x) _
    (fun i => hw i x) (hsum x) (fun i => herr i x)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pi_fin_card_le_exp {α : Type*} [Fintype α] [DecidableEq α]
    (n : α → ℕ) {p q : ℝ} (hq : 0 ≤ q) (hα : (Fintype.card α : ℝ) ≤ p)
    (hn : ∀ a, (n a : ℝ) ≤ Real.exp q) :
    (Fintype.card (∀ a, Fin (n a)) : ℝ) ≤ Real.exp (p * q) := by
  rw [Fintype.card_pi, Nat.cast_prod]
  simp only [Fintype.card_fin]
  calc
    (∏ a, (n a : ℝ)) ≤ ∏ _a : α, Real.exp q :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun a _ => hn a)
    _ = Real.exp ((Fintype.card α : ℝ) * q) := by
      rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hα hq)

namespace RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_factor_partitions (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} [Fintype α] [DecidableEq α]
      {L : α → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : α → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {p rho : ℝ},
      0 ≤ p → (Fintype.card α : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < rho → 1 / rho ≤ Real.exp ((p + 2) ^ a) →
      letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
      ∃ n : α → ℕ, (∀ i, 0 < n i) ∧ (∀ i, (n i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (Fintype.card (∀ i, Fin (n i)) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ K : α → ℝ≥0, (∀ i, (K i : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ ψ : ∀ i, Fin (n i) → (D i).Space → ℝ,
            (∀ i j x, 0 ≤ ψ i j x ∧ ψ i j x ≤ 1) ∧
            (∀ i x, ∑ j, ψ i j x = 1) ∧
            (∀ i j, LipschitzWith (K i) (ψ i j)) ∧
            ∀ i j x y, 0 < ψ i j x → 0 < ψ i j y → dist x y ≤ rho := by
  obtain ⟨c, _, hpart⟩ := exists_native_positive_partition s a
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.X * R + R)
  refine ⟨C, hC, ?_⟩
  intro α _ _ L _ _ _ _ _ _ d D p rho hp hα hD hrho hscale
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  choose n hn hnb K hKb ψ hunit hsum hLip hdiam using
    (fun i => hpart (D i) hp (hD i) hrho hscale)
  have hR : 0 ≤ (p + c) ^ c := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c)) _
  have hbudget' : p * (p + c) ^ c + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [R, Polynomial.eval₂_pow] using hbudget p hp
  have hsmall : (p + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (mul_nonneg hp hR)).trans hbudget'
  have hlarge : p * (p + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right hR).trans hbudget'
  refine ⟨n, hn, fun i => (hnb i).trans (Real.exp_le_exp.mpr hsmall),
    (pi_fin_card_le_exp n hR hα hnb).trans (Real.exp_le_exp.mpr hlarge),
    K, fun i => (hKb i).trans (Real.exp_le_exp.mpr hsmall), ψ, hunit, hsum, hLip, hdiam⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_bounded_complex_partition_approximation {I X : Type*} [Fintype I]
    [PseudoMetricSpace X] (w : I → X → ℝ)
    (hw : ∀ i x, 0 ≤ w i x) (hsum : ∀ x, ∑ i, w i x = 1)
    {rho : ℝ} (hdiam : ∀ i x y, 0 < w i x → 0 < w i y → dist x y ≤ rho)
    (F : X → ℂ) (B : ℝ≥0) (hF : ∀ x, ‖F x‖ ≤ B) {K : ℝ≥0} (hLip : LipschitzWith K F) :
    ∃ c : I → ℂ, (∀ i, ‖c i‖ ≤ B) ∧
      ∀ x, ‖F x - ∑ i, (w i x : ℂ) * c i‖ ≤ (K : ℝ) * rho := by
  classical
  have hchoose (i : I) : ∃ c : ℂ, ‖c‖ ≤ B ∧
      ∀ x, 0 < w i x → ‖F x - c‖ ≤ (K : ℝ) * rho := by
    by_cases hi : ∃ y, 0 < w i y
    · obtain ⟨y, hy⟩ := hi
      refine ⟨F y, hF y, fun x hx => ?_⟩
      have h := hLip.dist_le_mul x y
      rw [dist_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hdiam i x y hx hy) K.coe_nonneg)
    · exact ⟨0, by simpa only [norm_zero] using B.coe_nonneg,
        fun x hx => False.elim (hi ⟨x, hx⟩)⟩
  choose c hc herr using hchoose
  exact ⟨c, hc, fun x => norm_sub_positive_sum_le (fun i => w i x) c (F x) _
    (fun i => hw i x) (hsum x) (fun i => herr i x)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_positive_partition_sum_le_one {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖∑ i, (w i : ℂ) * c i‖ ≤ 1 := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * c i‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      exact mul_le_of_le_one_right (hw i) (hc i)
    _ = 1 := hsum

theorem complex_partition_approximation_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ‖T x - ∑ i, (w i x : ℂ) * c i x‖) ≤
      ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hcap (x : X) : ‖T x - ∑ i, (w i x : ℂ) * c i x‖ ≤ 2 := by
    have hb := norm_positive_partition_sum_le_one (fun i => w i x) (fun i => c i x)
      (fun i => hw i x) (hsum x) (fun i => hc i x)
    exact (norm_sub_le _ _).trans (by linarith [hT x])
  have h := expect_abs_le_of_exceptional_set E
    (fun x => ‖T x - ∑ i, (w i x : ℂ) * c i x‖) hε
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact norm_sub_positive_sum_le (fun i => w i x) (fun i => c i x) (T x) ε
        (fun i => hw i x) (hsum x) (fun i => hgood i x hx))
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

theorem norm_correlation_sub_le_mean {X : Type*} [Fintype X]
    (f u v : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(𝔼 x, f x * star (u x)) - (𝔼 x, f x * star (v x))‖ ≤
      𝔼 x, ‖u x - v x‖ := by
  rw [← Finset.expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply Finset.expect_le_expect
  intro x _
  rw [← mul_sub, ← star_sub, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf x)

theorem exists_correlating_summand_of_mean {X I : Type*} [Fintype X] [Fintype I]
    (f u : X → ℂ) (v : I → X → ℂ) {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 < M) (hcard : (Fintype.card I : ℝ) ≤ M)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (herr : (𝔼 x, ‖u x - ∑ i, v i x‖) ≤ ρ / 2)
    (hcorr : ρ ≤ ‖𝔼 x, f x * star (u x)‖) :
    ∃ i, ρ / (2 * M) ≤ ‖𝔼 x, f x * star (v i x)‖ := by
  have he := (norm_correlation_sub_le_mean f u (fun x => ∑ i, v i x) hf).trans herr
  have hsum : ρ / 2 ≤ ‖∑ i, 𝔼 x, f x * star (v i x)‖ := by
    have ht := norm_le_norm_add_norm_sub
      (𝔼 x, f x * star (∑ i, v i x)) (𝔼 x, f x * star (u x))
    have hm : (𝔼 x, f x * star (∑ i, v i x)) = ∑ i, 𝔼 x, f x * star (v i x) := by
      simp only [star_sum, Finset.mul_sum, Finset.expect_sum_comm]
    rw [norm_sub_rev] at ht
    rw [hm] at he ht
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ))
    (fun i => 𝔼 x, f x * star (v i x)) (by linarith : 0 < ρ / 2) hM
    (by simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcard)
    (by simpa only [one_mul] using hsum)
  exact ⟨i, by simpa only [div_div] using hi⟩

theorem mean_error_mul_bounded {X : Type*} [Fintype X]
    (u v b : X → ℂ) {B ε : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖b x‖ ≤ B) (he : (𝔼 x, ‖u x - v x‖) ≤ ε) :
    (𝔼 x, ‖u x * b x - v x * b x‖) ≤ B * ε := by
  calc
    _ ≤ 𝔼 x, B * ‖u x - v x‖ := by
      apply Finset.expect_le_expect
      intro x _
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = B * (𝔼 x, ‖u x - v x‖) := (Finset.mul_expect _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left he hB

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_observable_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ h, (S h).orbit = (T h).orbit ∧ (S h).normBound ≤ 1 ∧
          (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C)) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  classical
  obtain ⟨A, _, hpartition⟩ := exists_native_positive_partition s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hD hT hcap N _ weight hweight hcorr
  let q := (p + A) ^ A
  have hq : 0 ≤ q := pow_nonneg (by positivity) _
  have hcost : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  let rho := Real.exp (-(2 * p + 1))
  have hrho : 0 < rho := Real.exp_pos _
  have hrhoinv : 1 / rho ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ = Real.exp (2 * p + 1) := by simp only [rho, one_div, ← Real.exp_neg, neg_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  let := D.metricSpace
  obtain ⟨n, hn, hnq, K, hK, ψ, hψ, hsum, hLip, hdiam⟩ :=
    hpartition D hp hD hrho hrhoinv
  let U (h : G) (i : Fin n) : D.Niltest (fun _ : Unit => 1) :=
    D.sectionNiltest (T h).orbit (fun z (_ : Unit) => ψ i z)
      (fun z _ => hψ i z) K (fun _ => hLip i) (some ())
  have hlog : Real.log (3 + (K : ℝ)) ≤ (p + C) ^ C := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp q := Real.one_le_exp hq
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (q + 2) := by
        rw [Real.exp_add]
        nlinarith [mul_le_mul_of_nonneg_left h4 (Real.exp_nonneg q)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hU (h : G) (i : Fin n) : (U h i).orbit = (T h).orbit ∧ (U h i).normBound ≤ 1 ∧
      (U h i).UnitIntervalValued ∧ (U h i).ComplexityLE ((p + C) ^ C) := by
    refine ⟨rfl, le_rfl, ?_, ?_⟩
    · exact D.sectionNiltest_unit_interval _ _ _ _ _ _
    · exact D.sectionNiltest_complexityLE _ _ _ _ _ _ (hD.mono D hpC) hlog
  have hchoose (h : {h // h ∈ H}) : ∃ i : Fin n,
      Real.exp (-p) / (2 * Real.exp q) ≤
        ‖𝔼 x, weight h.val x * star ((U h.val i).evalCyclic N (fun _ => x))‖ := by
    obtain ⟨c, hc, happ⟩ := exists_complex_partition_approximation ψ
      (fun i z => (hψ i z).1) hsum hdiam (T h.val).observable
      (fun z => ((T h.val).norm_le z).trans (hcap h.val h.property)) (T h.val).lipschitz
    have hprecision : ((T h.val).lipBound : ℝ) * rho ≤ Real.exp (-p) / 2 := by
      have hbudgetT := Niltest.observable_budget (hT h.val h.property)
      have hlip : ((T h.val).lipBound : ℝ) ≤ Real.exp p := by
        have hnorm := (T h.val).normBound.coe_nonneg
        linarith
      calc
        _ ≤ Real.exp p * rho := mul_le_mul_of_nonneg_right hlip hrho.le
        _ = Real.exp (-p - 1) := by
          dsimp [rho]
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := exp_sub_one_le_half_exp _
    obtain ⟨i, hi⟩ := exists_correlating_summand Finset.univ_nonempty (weight h.val)
      (fun x => (T h.val).evalCyclic N (fun _ => x))
      (fun i x => (U h.val i).evalCyclic N (fun _ => x) * c i)
      (Real.exp_pos (-p)) (Real.exp_pos q) (by simpa only [Fintype.card_fin] using hnq)
      (fun x _ => hweight h.val h.property x)
      (fun x _ => by
        rw [norm_sub_rev]
        exact (happ (D.cyclicOrbitPoint (T h.val).orbit N (fun _ => x))).trans hprecision)
      (hcorr h.val h.property)
    refine ⟨i, hi.trans ?_⟩
    have heq : finiteCorrelation Finset.univ (weight h.val)
        (fun x => (U h.val i).evalCyclic N (fun _ => x) * c i) =
        star (c i) * finiteCorrelation Finset.univ (weight h.val)
          (fun x => (U h.val i).evalCyclic N (fun _ => x)) := by
      simp only [finiteCorrelation, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [heq, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans_eq (one_mul _)
  choose choice hchoice using hchoose
  let code : G → Fin n := fun h => if hh : h ∈ H then choice ⟨h, hh⟩ else ⟨0, hn⟩
  obtain ⟨i, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H hH code Set.univ (Set.toFinite _)
      (fun _ _ => Set.mem_univ _) (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fin] using hnq)
  refine ⟨H', fun h => U h i, hsub, hnonempty, ?_, fun h => hU h i, fun _ _ => rfl, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    have hcode : choice ⟨h, hsub hh⟩ = i := by
      simpa only [code, dite_eq_left (hsub hh)] using hconstant h hh
    have hc := hchoice ⟨h, hsub hh⟩
    rw [hcode] at hc
    apply le_trans _ hc
    calc
      _ ≤ Real.exp (-(p + q) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(p + q)) / 2 := exp_sub_one_le_half_exp _
      _ = Real.exp (-p) / (2 * Real.exp q) := by
        rw [show -(p + q) = -p - q by ring, Real.exp_sub]
        ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection
import OAI.Combinatorics.Progressions.Estimates.LinearCoefficientSplitting
import OAI.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode

namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem realifyFunctional_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : ℝ ⊗[ℚ] V) : realifyFunctional (0 : V →ₗ[ℚ] ℚ) x = 0 := by
  apply (mem_realified_frequency_kernel_iff (0 : V →ₗ[ℚ] ℚ) x).mp
  rw [LinearMap.ker_zero, Submodule.baseChange_top]
  trivial

theorem exists_linear_frequency_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧ (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  by_cases hη : η = 0
  · subst η
    refine ⟨1, 0, a, 0, Nat.zero_lt_one, hH, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro i
      exact realifyFunctional_zero (a i)
    · intro i j
      simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply, abs_zero]
      positivity
    · refine ⟨0, ?_⟩
      ext z
      simp
  · exact exists_biased_linear_coefficient_splitting b η hη hH hheight T hT a hδ hbias

theorem exists_bounded_frequency_kernel_spanning {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ v : ι → V, Submodule.span ℚ (Set.range v) = LinearMap.ker η ∧
      ∀ i j, RationalHeightLE (b.repr (v i) j) (2 * H ^ 2) := by
  classical
  by_cases hη : η = 0
  · subst η
    refine ⟨b, ?_, ?_⟩
    · rw [LinearMap.ker_zero]
      exact b.span_eq
    · intro i j
      have hh : 1 ≤ 2 * H ^ 2 := (one_le_pow₀ hH).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact rationalHeightLE_one hh
      · exact rationalHeightLE_zero hh
  · obtain ⟨u, _, _, _, hu, huheight, _⟩ := exists_bounded_frequency_direction b η hη hH hheight
    exact ⟨fun i => b i - η (b i) • u, frequencyKernel_spanning b η u hu,
      frequencyKernel_spanning_height b η u hheight huheight⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Classical

theorem exists_frequency_kernel_basis_logHeight
    {V : Type*} [AddCommGroup V] [Module ℚ V] {d D : ℕ}
    (b : Basis (Fin d) ℚ V) (P : Submodule ℚ V)
    (vP : Fin d → V) (hP : Submodule.span ℚ (Set.range vP) = P)
    (eta : Fin D → V →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hD : (D : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (b.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (b j)) ≤ p) :
    ∃ n : ℕ, n ≤ d ∧
      ∃ bk : Basis (Fin n) ℚ (finiteFrequencyKernel P eta (List.finRange D)),
        ∀ i j, rationalLogHeight (b.repr (bk i : V) j) ≤
          ((2 * p + 6) ^ 2 + 2) ^ 63 := by
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHp : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  choose v hv hh using fun i => exists_bounded_frequency_kernel_spanning b (eta i) hH
    (fun j => rationalHeightLE_ceil_exp (heta i j))
  let U : Option (Fin D) → Submodule ℚ V := fun z => z.elim P (fun i => LinearMap.ker (eta i))
  let gen : Option (Fin D) → Fin d → V := fun z => z.elim vP v
  have hgen (z) : Submodule.span ℚ (Set.range (gen z)) = U z := by
    cases z with
    | none => exact hP
    | some i => exact hv i
  have hHmono : H ≤ 2 * H ^ 2 := by nlinarith
  have hHe : ((2 * H ^ 2 : ℕ) : ℝ) ≤ Real.exp (2 * p + 4) := by
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ = 2 * (H : ℝ) ^ 2 := by push_cast; rfl
      _ ≤ Real.exp 2 * (Real.exp (p + 1)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hheight (z) (i j) : rationalLogHeight (b.repr (gen z i) j) ≤ 2 * p + 4 := by
    apply rationalLogHeight_le_of_height (H := 2 * H ^ 2) _ hHe
    cases z with
    | none => exact (rationalHeightLE_ceil_exp (hvP i j)).mono hHmono
    | some k => exact hh k i j
  have hcount : (Fintype.card (Option (Fin D)) : ℝ) ≤ 2 * p + 4 := by
    simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨n, hn, bk, hbk⟩ := exists_submodule_intersection_basis_logHeight b U gen hgen
    (by linarith : 0 ≤ 2 * p + 4)
    (by simpa only [Fintype.card_fin] using (show (d : ℝ) ≤ 2 * p + 4 by linarith))
    (by simpa only [Fintype.card_fin] using (show (d : ℝ) ≤ 2 * p + 4 by linarith))
    hcount hheight
  have hK : (⨅ z, U z) = finiteFrequencyKernel P eta (List.finRange D) := by
    ext x
    simp only [Submodule.mem_iInf, mem_finiteFrequencyKernel, List.mem_finRange, forall_true_left]
    constructor
    · intro h
      exact ⟨h none, fun i => h (some i)⟩
    · intro h z
      cases z with
      | none => exact h.1
      | some i => exact h.2 i
  refine ⟨n, by simpa only [Fintype.card_fin] using hn,
    bk.map (LinearEquiv.ofEq _ _ hK), ?_⟩
  intro i j
  simpa only [Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    show 2 * p + 4 + 2 = 2 * p + 6 by ring] using hbk i j

theorem exists_frequency_code_kernel_basis_logHeight
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {d D : ℕ}
    (b : Basis (Fin d) ℚ V) (P : Submodule ℚ V)
    (vP : Fin d → V) (hP : Submodule.span ℚ (Set.range vP) = P)
    (eta : J → V →ₗ[ℚ] ℚ) (code : Fin D → Option J) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hD : (D : ℝ) ≤ p)
    (hvP : ∀ i j, rationalLogHeight (b.repr (vP i) j) ≤ p)
    (heta : ∀ i j, rationalLogHeight (eta i (b j)) ≤ p) :
    ∃ n : ℕ, n ≤ d ∧ ∃ bk : Basis (Fin n) ℚ (frequencyCodeKernel P eta code),
      ∀ i j, rationalLogHeight (b.repr (bk i : V) j) ≤ ((2 * p + 6) ^ 2 + 2) ^ 63 := by
  apply exists_frequency_kernel_basis_logHeight b P vP hP
    (fun i => (code i).elim 0 eta) hp hd hD hvP
  intro i j
  cases code i with
  | none => simpa [rationalLogHeight] using hp
  | some k => exact heta k j

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Dynamics.ScalarBaseAllowancePowerBudget
import OAI.Combinatorics.Progressions.Dynamics.ScalarEndpointScalePowerBudget
import OAI.Combinatorics.Progressions.Estimates.UnconditionedCommonSideScalarRatioBounds

namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

theorem exists_scalarEndpoint_late_prime_common_side
    (n scalarE scalarC scalarF inputPower earlyExponent : ℕ)
    (hn : 2 ≤ n) (hE : 2 ≤ scalarE) (hC : 2 ≤ scalarC) (_hF : 2 ≤ scalarF)
    (hInput : max 1 earlyExponent ≤ inputPower) :
    ∃ latePower : ℕ, 2 ≤ latePower ∧ ∃ sizePower : ℕ, 2 ≤ sizePower ∧
    ∀ {p : ℝ}, 2 ≤ p →
      let b := (p + 2) ^ inputPower
      let scalarInput := (b + 2) ^ scalarE
      let ratio := unconditionedCommonSideScalarRatio n
      let t := (8 * ((ratio * n : ℕ) + 1 : ℝ) * (scalarInput + 1) + 2) ^ scalarC
      p ≤ t ∧ (p + 2) ^ earlyExponent ≤ t ∧
      (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ sizePower ∧
      ∃ (P : Fin n → ℕ) (hprime : ∀ j, (P j).Prime) (S : ℕ),
        S = unconditionedCommonSide P ∧ 0 < S ∧
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n + 1) * P j) ∧
        (∀ j, Real.exp p ≤ (P j : ℝ) ∧ P j ≤ S) ∧
        (∀ j, Real.exp t ≤ (P j : ℝ) ∧ (P j : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) ∧
        (∀ j, (S : ℝ) / (P j : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n)) ∧
        Real.exp t ≤ (S : ℝ) ∧ (S : ℝ) ≤ (ratio : ℝ) * Real.exp t ∧
        (S : ℝ) ≤ Real.exp ((p + 2) ^ latePower) ∧
        ∀ nX : ℕ, (nX : ℝ) ≤ p →
          let : ∀ j, NeZero (P j) := fun j => ⟨(hprime j).ne_zero⟩
          unconditionedSpatialWidthCutoff ((n : ℝ) * (S : ℝ))
            (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2) ^ sizePower) := by
  let ratio := unconditionedCommonSideScalarRatio n
  obtain ⟨A, _, hChoose⟩ := exists_unconditioned_late_prime_common_side_budget n
  obtain ⟨latePower, hLate, hScale⟩ :=
    exists_scalarEndpointScale_power_budget n ratio scalarE scalarC inputPower earlyExponent hE hC hInput
  obtain ⟨sizePower, hSize, hCutoff⟩ :=
    exists_scalarLatePrimeCutoff_composite_power_budget n ratio scalarE scalarC scalarF A inputPower
  refine ⟨latePower, hLate, sizePower, hSize, ?_⟩
  intro p hp b scalarInput ratio' t
  have hScale' := hScale p hp
  change p ≤ t ∧ (p + 2) ^ earlyExponent ≤ t ∧
    (ratio' : ℝ) * Real.exp t ≤ Real.exp ((p + 2) ^ latePower) at hScale'
  have hCutoff' := hCutoff p hp
  change (scalarInput + scalarF) ^ scalarF ≤ (p + 2) ^ sizePower ∧
    (t + 2) ^ A ≤ (p + 2) ^ sizePower at hCutoff'
  refine ⟨hScale'.1, hScale'.2.1, hCutoff'.1, ?_⟩
  obtain ⟨P, hprime, S, hinj, hcompare, hrange, hearly, hS, hSpos, hleS,
    _, _, hWidth⟩ := hChoose p t hp hScale'.1
  have hSeq : S = unconditionedCommonSide P := hS
  have ht0 : 0 ≤ t := (by linarith : 0 ≤ p).trans hScale'.1
  have hSup : (S : ℝ) ≤ (ratio' : ℝ) * Real.exp t := by
    rw [hSeq]
    exact unconditionedCommonSide_scalar_bound_of_range P ht0 (fun j => (hrange j).2)
  have hSlo : Real.exp t ≤ (S : ℝ) :=
    (hrange (⟨0, by omega⟩ : Fin n)).1.trans
      (Nat.cast_le.mpr (hleS (⟨0, by omega⟩ : Fin n)))
  refine ⟨P, hprime, S, hSeq, hSpos, hinj, hcompare,
    (fun j => ⟨hearly j, hleS j⟩), hrange, ?_, hSlo, hSup,
    hSup.trans hScale'.2.2, ?_⟩
  · intro j
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hprime j).pos)).mpr
    rw [hSeq]
    exact unconditionedCommonSide_le_exp_extra_mul P (fun j => (hprime j).pos) hcompare j
  · intro nX hnX
    let : ∀ j, NeZero (P j) := fun j => ⟨(hprime j).ne_zero⟩
    exact (hWidth nX hnX).trans (Real.exp_le_exp.mpr hCutoff'.2)

end Erdos3

end

end OAI

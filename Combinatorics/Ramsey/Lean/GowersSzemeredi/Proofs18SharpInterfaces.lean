import GowersSzemeredi.Proofs18PolyCubicDegree
import GowersSzemeredi.Proofs18GenericSzemeredi
import GowersSzemeredi.Proofs18Consequences

/-! Parameterized final exponents and the elementary coloring conversion.

These interfaces and conversions do not depend on a particular class
cover or envelope recursion. The legacy cover results and the final route
share these declarations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- The Theorem 18.1 exponent with `k + c` in place of the printed `k + 10`. -/
def section18ExponentAt (c : Nat) (alpha : Real) (k : Nat) : Real :=
  alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + c)))

/-- Theorem 18.1 at degree `k` with the exponent `section18ExponentAt c`. -/
def Theorem181AtSharp (c k : Nat) : Prop :=
  ∀ (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha k →
        ∃ M : Nat, ∃ P : Fin M → ModAP N,
          IsPartition (fun i => (P i).carrier) Finset.univ ∧
          (∀ i, (P i).IsProper) ∧
          (N : Real) ^ section18ExponentAt c alpha k ≤
            averageCellSize (fun i => (P i).carrier) ∧
          section18ExponentAt c alpha k * N ≤
            ∑ i, ‖∑ s ∈ (P i).carrier, balanced A s‖

/-- At `c = 10` it is the catalogue's Theorem 18.1 at degree `k`. -/
theorem theorem181AtSharp_ten_iff (k : Nat) : Theorem181AtSharp 10 k ↔ Theorem181At k :=
  Iff.rfl

/-- Increasing the offset decreases the exponent on the unit interval. -/
theorem section18ExponentAt_antitone {c c' k : Nat} {alpha : Real} (hc : c ≤ c')
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    section18ExponentAt c' alpha k ≤ section18ExponentAt c alpha k :=
  pow_le_pow_of_le_one ha ha1
    (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- A smaller constant gives a stronger statement. -/
theorem Theorem181AtSharp.mono {c c' k : Nat} (h : Theorem181AtSharp c k) (hc : c ≤ c') :
    Theorem181AtSharp c' k := by
  intro alpha ha ha2
  obtain ⟨N0, hN0⟩ := h alpha ha ha2
  refine ⟨N0, fun N _ _ hN A hA => ?_⟩
  obtain ⟨M, P, hp, hpr, h1, h2⟩ := hN0 N hN A hA
  have hle : section18ExponentAt c' alpha k ≤ section18ExponentAt c alpha k :=
    section18ExponentAt_antitone hc ha.le (by linarith)
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  exact ⟨M, P, hp, hpr, (Real.rpow_le_rpow_of_exponent_le hN1 hle).trans h1,
    (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)).trans h2⟩

theorem Theorem181AtSharp.of_function_discrepancy {c k : Nat}
    (h : ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 → ∃ beta sigma T : Real,
      section18ExponentAt c alpha k ≤ beta ∧ section18ExponentAt c alpha k ≤ sigma ∧
        FunctionDiscrepancyBound k alpha beta sigma T) :
    Theorem181AtSharp c k := by
  intro alpha hα hα2
  obtain ⟨beta, sigma, T, hb, hs, hT⟩ := h alpha hα hα2
  refine ⟨⌈T⌉₊, fun N _ _ hN A hnot => ?_⟩
  obtain ⟨M, Q, hpart, hproper, hsize, hdisc⟩ :=
    hT N ((Nat.le_ceil T).trans (by exact_mod_cast hN)) (balanced A)
      (balanced_discValued A) hnot
  refine ⟨M, Q, hpart, hproper, ?_, ?_⟩
  · have hN1 : (1 : Real) ≤ N := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hs).trans hsize
  · exact (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)).trans hdisc

theorem section18ExponentAt_le_of_inv_le {alpha : Real} (hα : 0 < alpha) (hα2 : alpha ≤ 1 / 2)
    {x : Real} (hx : 0 < x) {μ k c : Nat} (hμ : μ + 1 ≤ 2 ^ (k + c))
    (hxinv : x⁻¹ ≤ (2 / alpha) ^ (2 ^ μ)) : section18ExponentAt c alpha k ≤ x := by
  have hαone : alpha ≤ 1 := by linarith only [hα2]
  unfold section18ExponentAt
  have h1 : alpha ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + c))) ≤ alpha ^ (2 ^ (μ + 1)) :=
    pow_le_pow_of_le_one hα.le hαone (Nat.pow_le_pow_right (by norm_num) hμ)
  have h2 : alpha ^ (2 ^ (μ + 1)) = (alpha ^ 2) ^ (2 ^ μ) := by
    rw [pow_succ, mul_comm (2 ^ μ) 2, pow_mul]
  have h3 : (alpha ^ 2) ^ (2 ^ μ) ≤ (alpha / 2) ^ (2 ^ μ) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith only [hα, hα2]) _
  have h4 : (alpha / 2) ^ (2 ^ μ) = ((2 / alpha) ^ (2 ^ μ))⁻¹ := by rw [← inv_pow, inv_div]
  have h5 : ((2 / alpha) ^ (2 ^ μ))⁻¹ ≤ x := by
    have h := inv_anti₀ (inv_pos.mpr hx) hxinv
    rwa [inv_inv] at h
  calc _ ≤ alpha ^ (2 ^ (μ + 1)) := h1
    _ = (alpha ^ 2) ^ (2 ^ μ) := h2
    _ ≤ (alpha / 2) ^ (2 ^ μ) := h3
    _ = ((2 / alpha) ^ (2 ^ μ))⁻¹ := h4
    _ ≤ x := h5

theorem theorem181AtSharp_of_polyEnvBound {c d μ : Nat} (h : PolyEnvBound d μ)
    (hμ : μ + 1 ≤ 2 ^ (d + c)) : Theorem181AtSharp c d := by
  apply Theorem181AtSharp.of_function_discrepancy
  intro alpha ha ha2
  obtain ⟨b, s, T, hB, b0, -, s0, -, bi, si⟩ := h alpha ha ha2
  exact ⟨b, s, T, section18ExponentAt_le_of_inv_le ha ha2 b0 hμ bi,
    section18ExponentAt_le_of_inv_le ha ha2 s0 hμ si, hB⟩

/-- The two-colour threshold with `k + c` in place of the printed `k + 9`. -/
def twoColorThresholdAt (c k : Nat) : Real :=
  (2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^
    ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))

/-- Corollary 18.7 at length `k` with the threshold `twoColorThresholdAt c`. -/
def Corollary187AtSharp (c k : Nat) : Prop :=
  ∀ N : Nat, twoColorThresholdAt c k ≤ N → ∀ color : Nat → Fin 2, HasMonochromaticAP N 2 color k

theorem corollary187AtSharp_nine_iff (k : Nat) : Corollary187AtSharp 9 k ↔ Corollary187At k :=
  Iff.rfl

theorem szemerediThresholdAt_half (c k : Nat) :
    szemerediThresholdAt c (1 / 2 : Real) k = twoColorThresholdAt c k := by
  simp only [szemerediThresholdAt, twoColorThresholdAt]
  norm_num

/-- One of the two colour classes has at least half of `[1, N]`. -/
theorem two_color_class_half (N : Nat) (color : Nat → Fin 2) :
    ∃ c : Fin 2,
      (N : Real) / 2 ≤ (((Finset.Icc 1 N).filter fun x => color x = c).card : Real) :=
  exists_color_class_ge (by decide) N color

/-- **Theorem 18.2 at a length and constant gives Corollary 18.7 there.** -/
theorem Theorem182AtSharp.corollary_18_7 {c k : Nat} (h : Theorem182AtSharp c k) :
    Corollary187AtSharp c k := by
  intro N hN color
  exact hasMonochromaticAP_of_density (by decide)
    (h (1 / 2) N (by norm_num) (by norm_num)
      (by simpa only [szemerediThresholdAt_half] using hN)) color

end LeanProofs.GowersSzemeredi

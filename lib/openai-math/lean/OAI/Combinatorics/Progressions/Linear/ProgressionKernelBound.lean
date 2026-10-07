import OAI.Combinatorics.Progressions.Estimates.DyadicCountingParameters

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_progression_kernel_bound (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ)
        (a b : ZMod N) (parameter : ℝ) (f g : ZMod N → ℝ),
      0 ≤ parameter → parameter ≤ 1 →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) g (fun _ => 1 + xi) →
      ∀ S : Finset I, S.card ≤ s → IsUnit (b - a) →
        (∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i)) →
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) →
        |𝔼 x, 𝔼 d, (∏ i ∈ S, mu i (x + slopes i * d)) *
          countingKernel parameter (f (x + a * d)) (g (x + b * d))| < 1 + tau := by
  obtain ⟨delta, hdelta, C0, hC0, hparameters⟩ := exists_counting_kernel_parameters s htau
  obtain ⟨C, hC, xi0, hxi0, hstage⟩ := exists_pivot_stage_bound s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hodd hN I _ slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare S hS hab hends hpairs
  obtain ⟨n, hqcap, hsmall⟩ := hparameters p hp
  let v : Fin 0 → ZMod N := Fin.elim0
  have hc := pivotCompatible_zero v S slopes a b hab hends hpairs
  have h := hstage hp hxi hxib hodd hN n hqcap slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare v S
    (by simpa only [zero_add] using hS) hc
  rw [pivotStageCount_zero] at h
  simpa only [pow_zero] using h.trans_lt (hsmall S.card hS)

end Erdos3

end

end OAI

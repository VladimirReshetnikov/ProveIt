import OAI.Combinatorics.Progressions.Sampling.CyclicIntervalSampling

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cyclicInterval_zeroExtension_average {N : ℕ} [NeZero N]
    (a len : ℕ) (hbound : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (f : ℤ → ℂ) :
    (𝔼 n : ZMod N, finiteIndicator (cyclicInterval (a : ZMod N) len) n * f (n.val : ℤ)) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n) := by
  let I := cyclicInterval (a : ZMod N) len
  have hrep : (𝔼 n ∈ I, f (n.val : ℤ)) =
      𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f n := by
    simpa only [finiteCorrelation, one_mul, star_star] using
      cyclicInterval_representative_correlation a len hbound hshort
        (fun _ : ZMod N => (1 : ℂ)) (fun n => star (f n))
  have hstar (n : ZMod N) : star (finiteIndicator I n) = finiteIndicator I n := by
    by_cases hn : n ∈ I <;> simp [finiteIndicator, hn]
  have h := finiteCorrelation_mul_indicator I (fun _ : ZMod N => (1 : ℂ))
    (fun n => star (f (n.val : ℤ)))
  simp only [finiteCorrelation, one_mul, star_mul, star_star, hstar, hrep] at h
  have hcard : I.card = len := cyclicInterval_card _ (by omega)
  simpa only [hcard, ZMod.card, Complex.ofReal_div, Complex.ofReal_natCast, mul_comm] using h

end Erdos3

end

end OAI

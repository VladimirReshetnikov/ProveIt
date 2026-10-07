import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialSlots

theorem loweringAt_patchValue {X : Type*} {d : ℕ} {w : Fin d → ℕ}
    (A : PolynomialSlots X d w) (hw : Monotone w) (Φ : PatchKernel d) (t : X → ℝ) :
    ((A.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ) = (A.slots t).patchValue Φ := by
  unfold TriangularSlots.patchValue
  apply tsum_congr
  intro b
  congr 1
  rw [shearTransformedSlots_residual]
  exact A.top_factorization_residual t b

theorem exists_fixed_kernel_patch_function {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
    {d s N : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (hw : Monotone w)
    (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (Φ : PatchKernel d)
    {M : ℝ} (hM : 0 ≤ M) (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hN : 0 < N) (hsmall : patchTopNetError d s N M < 1 / 4)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
    (score : Ω → T → ℝ) (hscore : ∀ a t, |score a t| ≤ 1)
    {δ : ℝ} (_hδ : 0 < δ)
    (hpositive : ∀ a ∈ productive, δ ≤
      (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue Φ))
    (herror : Φ.lip * patchTopNetError d s N M ≤ δ / 2) :
    ∃ (B : PolynomialSlots X d w) (retained : Finset Ω),
      (∀ i, realPolynomialMass (B.center i) ≤ M) ∧
      retained ⊆ productive ∧
      outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s) ≤ outer.mass retained ∧
      ∀ a ∈ retained, δ / 2 ≤ (localLaw a).mean (fun t => score a t *
        (B.shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ) := by
  obtain ⟨code, rep, hnet⟩ := exists_shear_observable_net A hw hpos hs Φ hM hA hN hsmall
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass productive code
  refine ⟨A (rep i), productive.filter (fun a => code a = i), hA _, Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s) ≤
        outer.mass productive / Fintype.card (PatchTopCoefficientIndex d s → Fin (N + 1)) := by
      apply div_le_div_of_nonneg_left (outer.mass_nonneg productive)
      · exact_mod_cast Fintype.card_pos (α := PatchTopCoefficientIndex d s → Fin (N + 1))
      · exact_mod_cast patchTopCoefficientCode_card d s N
    apply hcard.trans
    convert hi using 1; try rfl
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha
    obtain ⟨ha, hcode⟩ := Finset.mem_filter.mp ha
    have hclose (t : T) :
        dist (((A a).slots (point a t)).patchValue Φ)
          (((A (rep i)).shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ) ≤
            Φ.lip * patchTopNetError d s N M := by
      have h := hnet a ((A a).loweringAt (point a t))
      rw [hcode, loweringAt_patchValue] at h
      exact h
    let u := fun t => score a t * ((A a).slots (point a t)).patchValue Φ
    let v := fun t => score a t *
      ((A (rep i)).shearTransformedSlots hw ((A a).loweringAt (point a t))).patchValue Φ
    have he : |(localLaw a).mean (fun t => u t - v t)| ≤ Φ.lip * patchTopNetError d s N M := by
      apply (localLaw a).abs_mean_le_on_support
      intro t _
      change |score a t * _ - score a t * _| ≤ _
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hscore a t) (abs_nonneg _)).trans
        (by simpa only [one_mul, Real.dist_eq] using hclose t)
    rw [(localLaw a).mean_sub] at he
    have hp := hpositive a ha
    change δ ≤ (localLaw a).mean u at hp
    change δ / 2 ≤ (localLaw a).mean v
    linarith [le_abs_self ((localLaw a).mean u - (localLaw a).mean v)]

end PolynomialSlots
end Erdos3

end

end OAI

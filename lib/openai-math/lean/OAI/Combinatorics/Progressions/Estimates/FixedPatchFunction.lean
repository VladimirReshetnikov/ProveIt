import OAI.Combinatorics.Progressions.Linear.FixedKernelPatchFunction
import OAI.Combinatorics.Progressions.Sampling.PatchKernelGridBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem fixed_weight_patch_function {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
    {d s N J : ℕ} {w : Fin d → ℕ}
    (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
    (hw : Monotone w) (hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s)
    {M L δ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hA : ∀ a i, realPolynomialMass ((A a).center i) ≤ M)
    (hΦ : ∀ a, ((Φ a).lip : ℝ) ≤ L)
    (hN : 8 ≤ N) (hkernel : 2 * L * (patchKernelGridRadius N : ℝ) ≤ δ / 2)
    (hJ : 0 < J) (hsmall : patchTopNetError d s J (M + 1 / 4) < 1 / 4)
    (hhomogeneous : ((2 * ((N + 1) ^ d : ℕ) + 1 : ℝ≥0) / patchKernelGridRadius N : ℝ≥0) *
      patchTopNetError d s J (M + 1 / 4) ≤ δ / (4 * ((N + 1 : ℕ) : ℝ) ^ d))
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
    (score : Ω → T → ℝ) (hscore : ∀ a t, |score a t| ≤ 1)
    (hpositive : ∀ a ∈ productive, δ ≤
      (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue (Φ a))) :
    ∃ (i : Fin d → Fin (N + 1)) (B : PolynomialSlots X d w)
      (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
      (∀ j, realPolynomialMass (B.center j) ≤ M + 1 / 4) ∧
      retained ⊆ productive ∧
      outer.mass productive /
        (((N + 1 : ℕ) : ℝ) ^ d * ((J + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s)) ≤ outer.mass retained ∧
      ∀ a ∈ retained, δ / (4 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
        (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (point a t))).patchValue
            (gridPatchKernel d N hN i)) := by
  let P : Ω → PolynomialPatch X s d := fun a =>
    ⟨w, hpos, hs, hw, A a, Φ a⟩
  have hk (a) : 2 * ((Φ a).lip : ℝ) * (patchKernelGridRadius N : ℝ) ≤ δ / 2 :=
    (mul_le_mul (mul_le_mul_of_nonneg_left (hΦ a) (by norm_num))
      le_rfl (patchKernelGridRadius N).coe_nonneg
      (mul_nonneg (by norm_num) hL)).trans hkernel
  have hchoose (a : Ω) : ∃ i : Fin d → Fin (N + 1), a ∈ productive →
      δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤ (localLaw a).mean (fun t => score a t *
        ((P a).gridKernelReplacement hN i).value (point a t)) := by
    by_cases ha : a ∈ productive
    · obtain ⟨i, hi⟩ := (P a).exists_gridKernelReplacement_score hN (localLaw a) (point a)
        (score a) (hscore a) hδ (hpositive a ha) (hk a)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨fun _ => 0, fun h => (ha h).elim⟩
  choose code hcode using hchoose
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass productive code
  let Q := productive.filter (fun a => code a = i)
  let A' : Ω → PolynomialSlots X d w := fun a => ((P a).gridKernelReplacement hN i).form
  have hA' (a) (j) : realPolynomialMass ((A' a).center j) ≤ M + 1 / 4 := by
    change realPolynomialMass ((A a).center j + MvPolynomial.C (uniformBoxGrid (1 / 4) N i j)) ≤ _
    apply (realPolynomialMass_add_le _ _).trans
    rw [realPolynomialMass_C]
    exact add_le_add (hA a j) (uniformBoxGrid_mem (by norm_num) (by omega : 0 < N) i j)
  have hδ' : 0 < δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hpositive' (a) (ha : a ∈ Q) : δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
      (localLaw a).mean (fun t => score a t * ((A' a).slots (point a t)).patchValue
        (gridPatchKernel d N hN i)) := by
    obtain ⟨ha, hai⟩ := Finset.mem_filter.mp ha
    have h := hcode a ha
    rw [hai] at h
    exact h
  have he : (gridPatchKernel d N hN i).lip * patchTopNetError d s J (M + 1 / 4) ≤
      (δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d)) / 2 := by
    simp only [gridPatchKernel]
    convert hhomogeneous using 1; ring
  obtain ⟨B, retained, hB, hretained, hmass, hlocal⟩ :=
    PolynomialSlots.exists_fixed_kernel_patch_function A' hw hpos hs (gridPatchKernel d N hN i)
      (by linarith : 0 ≤ M + 1 / 4) hA' hJ hsmall outer Q localLaw point score hscore hδ' hpositive' he
  refine ⟨i, B, A', retained, hB, fun a ha => (Finset.mem_filter.mp (hretained ha)).1, ?_, ?_⟩
  · have hi' : outer.mass productive / ((N + 1 : ℕ) : ℝ) ^ d ≤ outer.mass Q := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at hi
      convert hi using 1; try rfl
      congr 1
      ext a
      simp only [Q, Finset.mem_filter]
    apply le_trans _ hmass
    rw [← div_div]
    exact div_le_div_of_nonneg_right hi' (by positivity)
  · intro a ha
    convert hlocal a ha using 1; ring

end Erdos3

end

end OAI

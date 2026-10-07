import OAI.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest
import OAI.Combinatorics.Progressions.Polynomial.PatchTopNetPolynomialBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

private theorem exp_neg_le_div {P a b D : ℝ} (hD : 0 < D)
    (hDb : D ≤ Real.exp b) (hP : a + b ≤ P) :
    Real.exp (-P) ≤ Real.exp (-a) / D := by
  apply (le_div_iff₀ hD).mpr
  calc
    _ ≤ Real.exp (-P) * Real.exp b := mul_le_mul_of_nonneg_left hDb (Real.exp_nonneg _)
    _ = Real.exp (-P + b) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exists_fixed_weight_patch_function_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω T : Type*} [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ},
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (_hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p →
      (∀ a i, realPolynomialMass ((A a).center i) ≤ p) →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℝ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤
        (localLaw a).mean (fun t => score a t * ((A a).slots (point a t)).patchValue (Φ a))) →
      ∃ (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
        (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ p + 1 / 4) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ C)) ≤ (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (point a t))).patchValue Ψ) := by
  obtain ⟨a, ha, htop⟩ := exists_patch_top_net_budget s
  let X : Polynomial ℕ := Polynomial.X
  let R : Polynomial ℕ := (X + 1) * (2 * X + 11)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (3 * R + (4 * R + 2) ^ a + X + 5)
  refine ⟨C, hC, ?_⟩
  intro X₀ Ω T _ _ _ d w A Φ hw hpos hs p hp hd hA hΦ outer productive localLaw point score hscore hpositive
  let r := (p + 1) * (2 * p + 11)
  let q := 4 * r
  have hr : 11 ≤ r := by dsimp only [r]; nlinarith
  have hpR : p + 1 ≤ r := by dsimp only [r]; nlinarith
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have hpq : p ≤ q := by dsimp only [q]; linarith
  have hbudget' : 3 * r + (q + 2) ^ a + p + 5 ≤ (p + 2) ^ C := by
    simpa [X, R, r, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + 2) ^ a := by positivity
  have hmassBudget : r + (q + 2) ^ a ≤ (p + 2) ^ C := by linarith
  have hscoreBudget : p + (r + 3) ≤ (p + 2) ^ C := by linarith
  have hLipBudget : 2 * r + 2 ≤ (p + 2) ^ C := by linarith
  obtain ⟨N, hN, _, hNerror, hNcount, hNlip⟩ :=
    exists_patch_kernel_mesh d hp (Real.exp_nonneg p) hd (le_refl (Real.exp p))
  let K : ℝ≥0 := (2 * ((N + 1) ^ d : ℕ) + 1) / patchKernelGridRadius N
  have hKq : (K : ℝ) ≤ Real.exp q := hNlip.trans (Real.exp_le_exp.mpr (by dsimp only [q]; linarith))
  have hMq : p + 1 / 4 ≤ Real.exp q := by
    have h := (Real.add_one_le_exp p).trans (Real.exp_le_exp.mpr hpq)
    linarith
  obtain ⟨J, hJ, _, hJcount, hJsmall, hJerror⟩ :=
    htop d (p + 1 / 4) K q hq (by linarith) K.coe_nonneg (hd.trans hpq) hMq hKq
  have htwocount : 2 * ((N + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (r + 1) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp r := mul_le_mul h2 (by exact_mod_cast hNcount) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlocalScore : Real.exp (-q) ≤ Real.exp (-p) / (2 * ((N + 1 : ℕ) : ℝ) ^ d) :=
    exp_neg_le_div (by positivity) htwocount (by dsimp only [q]; linarith)
  have hhomogeneous : (K : ℝ) * patchTopNetError d s J (p + 1 / 4) ≤
      Real.exp (-p) / (4 * ((N + 1 : ℕ) : ℝ) ^ d) := by
    apply hJerror.trans
    have h := div_le_div_of_nonneg_right hlocalScore (by norm_num : (0 : ℝ) ≤ 2)
    convert h using 1; ring
  obtain ⟨i, B, localForm, retained, hB, hretained, hmass, hlocal⟩ :=
    fixed_weight_patch_function A Φ hw hpos hs hp (Real.exp_nonneg p) (Real.exp_pos (-p)) hA hΦ
      hN hNerror hJ hJsmall hhomogeneous outer productive localLaw point score hscore hpositive
  refine ⟨gridPatchKernel d N hN i, B, localForm, retained,
    hNlip.trans (Real.exp_le_exp.mpr hLipBudget), hB, hretained, ?_, ?_⟩
  · let D : ℝ := ((N + 1 : ℕ) : ℝ) ^ d * ((J + 1 : ℕ) : ℝ) ^ (d * (d + 1) ^ s)
    have hD : 0 < D := by dsimp only [D]; positivity
    have hDupper : D ≤ Real.exp ((p + 2) ^ C) := by
      calc
        D ≤ Real.exp r * Real.exp ((q + 2) ^ a) := by
          exact mul_le_mul (by exact_mod_cast hNcount) (by exact_mod_cast hJcount)
            (by positivity) (Real.exp_nonneg _)
        _ = Real.exp (r + (q + 2) ^ a) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hmassBudget
    have hi : Real.exp (-((p + 2) ^ C)) ≤ 1 / D := by
      simpa only [neg_zero, Real.exp_zero] using
        exp_neg_le_div (P := (p + 2) ^ C) (a := 0) hD hDupper (by linarith)
    exact (mul_le_mul_of_nonneg_left hi (outer.mass_nonneg productive)).trans
      (by simpa only [mul_one_div, D] using hmass)
  · intro x hx
    have hfourcount : 4 * ((N + 1 : ℕ) : ℝ) ^ d ≤ Real.exp (r + 3) := by
      have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      calc
        _ ≤ Real.exp 3 * Real.exp r := mul_le_mul h4 (by exact_mod_cast hNcount) (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (exp_neg_le_div (by positivity) hfourcount hscoreBudget).trans (hlocal x hx)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_unrestricted_fixed_weight_patch_function (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {X Ω T : Type*} [Fintype X] [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ},
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (_hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℤ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤ (localLaw a).mean (fun t =>
        score a t * ((A a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a))) →
      ∃ (Ψ : PatchKernel d) (B : PolynomialSlots X d w)
        (localForm : Ω → PolynomialSlots X d w) (retained : Finset Ω),
        (Ψ.lip : ℝ) ≤ Real.exp ((p + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (p + 2) ^ E) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ E)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ E)) ≤ (localLaw a).mean (fun t => score a t *
          (B.shearTransformedSlots hw ((localForm a).loweringAt (fun i => (point a t i : ℝ)))).patchValue Ψ) := by
  obtain ⟨C, hC, hfixed⟩ := exists_fixed_weight_patch_function_budget s
  let Z : Polynomial ℕ := Polynomial.X
  let Q := Z + Polynomial.C (s + 1) * (2 * Z + 1) ^ s + 2
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((Q + 2) ^ C + Q + 1)
  refine ⟨E, hE, ?_⟩
  intro X Ω T _ _ _ _ d w A Φ hw hpos hs p hp hd hX hΦ outer productive localLaw point score hscore hpositive
  let q : ℝ := p + ((s : ℝ) + 1) * (2 * p + 1) ^ s + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by
    have : 0 ≤ ((s : ℝ) + 1) * (2 * p + 1) ^ s := by positivity
    dsimp only [q]
    linarith
  have hbudget' : (q + 2) ^ C + q + 1 ≤ (p + 2) ^ E := by
    simpa [Z, Q, q, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_one] using hbudget p hp
  have hpower : (q + 2) ^ C ≤ (p + 2) ^ E := by linarith
  have hmassBudget : q + 1 / 4 ≤ (p + 2) ^ E := by
    have : 0 ≤ (q + 2) ^ C := by positivity
    linarith
  choose norm hnorm hperm using fun a => (A a).exists_coefficient_normalized
  have hnormMass (a) (i) : realPolynomialMass ((norm a).center i) ≤ q := by
    have h := (norm a).center_mass_le_of_normalized hpos s hs (hnorm a) i
    have hbound : (((s + 1) * (Fintype.card X + d + 1) ^ s : ℕ) : ℝ) ≤
        ((s : ℝ) + 1) * (2 * p + 1) ^ s := by
      push_cast
      gcongr
      linarith
    have ht := h.trans hbound
    dsimp only [q]
    linarith
  have hvalues (a : Ω) (t : X → ℤ) :
      ((norm a).slots (fun i => (t i : ℝ))).patchValue (Φ a) =
        ((A a).slots (fun i => (t i : ℝ))).patchValue (Φ a) := by
    obtain ⟨e, he⟩ := hperm a t
    unfold TriangularSlots.patchValue
    simp_rw [he]
    exact e.tsum_eq (fun b => (Φ a).value
      (((A a).slots (fun i => (t i : ℝ))).residual b))
  have hnormScore (a) (ha : a ∈ productive) : Real.exp (-q) ≤
      (localLaw a).mean (fun t => score a t *
        ((norm a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a)) := by
    simp_rw [hvalues]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive a ha)
  obtain ⟨Ψ, B, localForm, retained, hLip, hMass, hretained, hprob, hlocal⟩ :=
    hfixed norm Φ hw hpos hs q hq (hd.trans hpq) hnormMass
      (fun a => (hΦ a).trans (Real.exp_le_exp.mpr hpq)) outer productive localLaw
      (fun a t i => (point a t i : ℝ)) score hscore hnormScore
  refine ⟨Ψ, B, localForm, retained, hLip.trans (Real.exp_le_exp.mpr hpower),
    fun i => (hMass i).trans hmassBudget, hretained, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hpower))
      (outer.mass_nonneg productive)).trans hprob
  · intro a ha
    exact (Real.exp_le_exp.mpr (neg_le_neg hpower)).trans (hlocal a ha)

end Erdos3

end

end OAI

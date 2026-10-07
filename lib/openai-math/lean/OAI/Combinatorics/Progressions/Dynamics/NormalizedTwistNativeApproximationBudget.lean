import OAI.Combinatorics.Progressions.Estimates.AllocatedApproximationError
import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistNativeApproximation

namespace OAI

section

namespace Erdos3

noncomputable def allocatedModelTestLog (u p : ℝ) : ℝ := 2 * u + 5 * p + 12

noncomputable def allocatedModelUnitThreshold (u p K C : ℝ) : ℝ :=
  (Real.exp (-(u + 3)) / Real.exp p ^ 2) /
    max 1 (K * (2 * C) / Real.exp (-(u + 3)))

theorem allocatedModelUnitThreshold_bounds {u p K C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) :
    0 < allocatedModelUnitThreshold u p K C ∧
      allocatedModelUnitThreshold u p K C ≤ 1 ∧
      Real.exp (-(2 * u + 4 * p + 7)) ≤ allocatedModelUnitThreshold u p K C := by
  let τ := Real.exp (-(u + 3))
  let D := max 1 (K * (2 * C) / τ)
  have hτ : 0 < τ := Real.exp_pos _
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hτ1 : τ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hep : 1 ≤ Real.exp p := Real.one_le_exp hp
  have hnum : τ / Real.exp p ^ 2 ≤ 1 :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos p))).mpr (by nlinarith)
  have hbound : D ≤ 2 * Real.exp (2 * p + u + 3) := by
    apply max_le
    · have he : 1 ≤ Real.exp (2 * p + u + 3) := Real.one_le_exp (by positivity)
      linarith
    · calc
        _ ≤ Real.exp p * (2 * Real.exp p) / τ := by gcongr
        _ = 2 * Real.exp (2 * p + u + 3) := by
          dsimp only [τ]
          rw [show 2 * p + u + 3 = p + p + (u + 3) by ring]
          simp only [Real.exp_add, Real.exp_neg, div_eq_mul_inv, inv_inv]
          ring
  refine ⟨div_pos (div_pos hτ (sq_pos_of_pos (Real.exp_pos p))) hD,
    (div_le_iff₀ hD).mpr (by nlinarith [le_max_left 1 (K * (2 * C) / τ)]), ?_⟩
  change _ ≤ (τ / Real.exp p ^ 2) / D
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 6)) / 2 := by
      rw [show -(2 * u + 4 * p + 7) = -(2 * u + 4 * p + 6) - 1 by ring,
        Real.exp_sub]
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    _ = (τ / Real.exp p ^ 2) / (2 * Real.exp (2 * p + u + 3)) := by
      dsimp only [τ]
      rw [show -(2 * u + 4 * p + 6) = -(u + 3) - (p + p) - (2 * p + u + 3) by ring,
        Real.exp_sub, Real.exp_sub, Real.exp_add]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD hbound

theorem allocatedModelTestLog_detection {u p K C d : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hd : d ≤ Real.exp p) :
    0 ≤ allocatedModelTestLog u p ∧
      d * Real.exp (-allocatedModelTestLog u p) ≤ allocatedModelUnitThreshold u p K C / 8 ∧
      Real.exp (-allocatedModelTestLog u p) ≤ allocatedModelUnitThreshold u p K C / 4 := by
  have hα := (allocatedModelUnitThreshold_bounds hu hp hK hC hKp hCp).2.2
  have h8 : (8 : ℝ) ≤ Real.exp 5 := by
    have h2 := Real.add_one_le_exp (2 : ℝ)
    have h3 := Real.add_one_le_exp (3 : ℝ)
    have he : Real.exp 5 = Real.exp 2 * Real.exp 3 := by
      rw [show (5 : ℝ) = 2 + 3 by norm_num, Real.exp_add]
    rw [he]
    nlinarith
  have hsmall : Real.exp (-(2 * u + 4 * p + 12)) ≤
      allocatedModelUnitThreshold u p K C / 8 := by
    calc
      _ = Real.exp (-(2 * u + 4 * p + 7)) / Real.exp 5 := by
        rw [← Real.exp_sub]; congr 1; ring
      _ ≤ Real.exp (-(2 * u + 4 * p + 7)) / 8 :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) h8
      _ ≤ _ := div_le_div_of_nonneg_right hα (by norm_num)
  have htest : Real.exp (-allocatedModelTestLog u p) ≤
      Real.exp (-(2 * u + 4 * p + 12)) := by
    apply Real.exp_le_exp.mpr
    unfold allocatedModelTestLog
    linarith
  refine ⟨by unfold allocatedModelTestLog; positivity, ?_, ?_⟩
  · calc
      _ ≤ Real.exp p * Real.exp (-allocatedModelTestLog u p) := by gcongr
      _ = Real.exp (-(2 * u + 4 * p + 12)) := by
        rw [← Real.exp_add]; congr 1; unfold allocatedModelTestLog; ring
      _ ≤ _ := hsmall
  · have hpos := (allocatedModelUnitThreshold_bounds hu hp hK hC hKp hCp).1
    linarith [htest.trans hsmall]

theorem allocatedModel_size_bounds {u p Q K C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) :
    2 / Real.exp (-Q) ≤ Real.exp (Q + 2) ∧
      1 + 4 * (K * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤
        Real.exp (2 * Q + 2 * u + 4 * p + 30) := by
  constructor
  · rw [Real.exp_neg, div_eq_mul_inv, inv_inv, Real.exp_add]
    nlinarith [Real.add_one_le_exp (2 : ℝ), Real.exp_pos Q]
  · let L := 2 * Q + 2 * u + 4 * p + 6
    have hL : 0 ≤ L := by dsimp only [L]; positivity
    have hlarge : 1 ≤ Real.exp L := Real.one_le_exp hL
    have hratio : 4 * (K * (2 * C)) ^ 2 /
        (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) ≤ 16 * Real.exp L := by
      calc
        _ ≤ 4 * (Real.exp p * (2 * Real.exp p)) ^ 2 /
            (Real.exp (-Q) ^ 2 * Real.exp (-(u + 3)) ^ 2) := by gcongr
        _ = 16 * Real.exp L := by
          dsimp only [L]
          rw [Real.exp_neg, Real.exp_neg,
            show 2 * Q + 2 * u + 4 * p + 6 = Q + Q + ((u + 3) + (u + 3)) + ((p + p) + (p + p)) by ring]
          simp only [Real.exp_add]
          field_simp
          ring
    calc
      _ ≤ 17 * Real.exp L := by linarith
      _ ≤ Real.exp L * Real.exp 24 := by
        nlinarith [Real.add_one_le_exp (24 : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [L]; ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_native_approximation_with_budget
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) [∀ i, NeZero (N i)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {periodCap coverCap : ℝ} {lip : ℝ≥0}
    {Tests : Ω → Type*} [∀ z, Nonempty (Tests z)]
    (μ : FiniteProbabilityWeights Ω)
    (physical : Ω → T → integerBox N)
    (site : Ω → T → X → ℤ)
    (hphysical : ∀ z t, (physical z t).val = site z t)
    (slices : ∀ z, Tests z → Finset T)
    (tests : ∀ z, Tests z → T → ℂ)
    (w : X → ℕ) (degree : ℕ)
    {u p budget K C : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ budget)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ K)
    (htests : ∀ z j t, ‖tests z j t‖ ≤ 1)
    (hdetect : ∀ signal : (X → ℤ) → ℂ,
      (∀ t, ‖signal t‖ ≤ 1) →
      (∀ t, t ∉ integerBox N → signal t = 0) →
      allocatedModelUnitThreshold u p K C ≤ sampledSliceSeminorm μ site slices tests signal →
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
        (G : integerBox N → ℂ),
        Nonempty (NativeSampleModel w degree budget (fun t : integerBox N => t.val) G) ∧
        Real.exp (-budget) ≤ ‖(FiniteProbabilityWeights.uniformFinset (integerBox N)
          (integerBox_nonempty N)).correlation (fun t => signal t.val)
            (fun t => star (W.eval N poly t.val) * G t)‖)
    {Ptail : ℝ} (hPtail : u + 2 * p + budget + 30 ≤ Ptail)
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N)
      (integerBox_nonempty N)).excessMass (μ.siteLaw physical) C ≤
        6 * positiveProjectionAccuracy Ptail)
    (input : integerBox N → ℂ) (hinput : ∀ t, ‖input t‖ ≤ Real.exp p) :
    ∃ (nterms : ℕ) (_ : 0 < nterms)
      (Q : Fin nterms → (integerBox N → ℂ))
      (coeff : Fin nterms → ℝ) (err : integerBox N → ℂ),
      (∀ i, Q i ∈ twistedNativeSampleFunctions w degree budget
        (fun t : integerBox N => t.val)
        (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap lip)
          (t : integerBox N) => W.eval N poly t.val)) ∧
      input = (∑ i, coeff i • Q i) + err ∧
      (∑ i, |coeff i|) ≤ Real.exp (budget + 2) ∧
      sampledSliceSeminorm μ physical slices tests err ≤ Real.exp (-u) ∧
      (nterms : ℝ) ≤ Real.exp (2 * budget + 2 * u + 4 * p + 30) := by
  obtain ⟨nterms, hnterms, Q, coeff, err, hQ, heq, hcoeff, herr, hterms⟩ :=
    exists_normalizedTwist_native_approximation N poly μ physical site hphysical slices tests
      w degree budget hK hC (Real.exp_pos p) (Real.exp_pos (-budget))
      (Real.exp_pos (-(u + 3))) hsize htests hdetect hexcess input hinput
  have hbounds := allocatedModel_size_bounds hu hp hbudget hK hC hKp hCp
  refine ⟨nterms, hnterms, Q, coeff, err, hQ, heq, hcoeff.trans hbounds.1,
    herr.trans ?_, hterms.trans hbounds.2⟩
  exact allocated_native_approximation_error hu hp hbudget hK (Real.exp_nonneg p)
    hKp le_rfl le_rfl hPtail le_rfl

end Erdos3.VectorPolynomial

end

end OAI

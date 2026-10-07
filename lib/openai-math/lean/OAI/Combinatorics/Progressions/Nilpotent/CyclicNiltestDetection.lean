import OAI.Combinatorics.Progressions.Dynamics.CyclicDetectionBudget
import OAI.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
import OAI.Combinatorics.Progressions.Estimates.CyclicIntervalCubeComparison

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem boxNiltestDetection_succ.{u,v} {s c : ℕ}
    (hI : BoxNiltestDetection.{u,v} s (fun p => (p + c) ^ c)) :
    ∃ C : ℕ, 2 ≤ C ∧ BoxNiltestDetection.{u,v} (s + 1) (fun p => (p + C) ^ C) := by
  classical
  obtain ⟨av, _, hav⟩ := exists_verticalDecompositionBudget_bound
  obtain ⟨bs, _, hder⟩ := exists_vertical_derivative_detection s
  obtain ⟨C, hC, hbudget⟩ := exists_boxDetectionStepBudget_bound s av bs c
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT z lengths _ f hf hc
  let Q := translatedIntegerBox z lengths
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty lengths z
  obtain ⟨η, U, hU, hcorrU, hchar⟩ :=
    T.exists_detection_vertical_mode av hav hp hT hQ f hf hc
  let r := boxModeBudget av p
  let q := boxInductionInputBudget av bs p
  let ℓ := boxRetainedBudget av p
  let ρ := Real.exp (-r)
  let δ := Real.exp (-(ℓ + p))
  let η0 := Real.exp (-((q + c) ^ c))
  let μ := Real.exp (-ℓ)
  let P := fun h : σ → ℤ =>
    ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative f h) (multiplicativeDerivative U.eval h)‖ ∧
    δ * Q.card < ((derivativeSupport Q h).card : ℝ)
  have hcost := boxInductionInputBudget_bounds av bs hp
  have hq : 0 ≤ q := hp.trans hcost.2.2
  have hρsq : Real.exp (-q) ≤ ρ ^ 2 / 2 := by
    have hq' : 2 * r + 1 ≤ q := hcost.2.1
    have he : ρ ^ 2 = Real.exp (-2 * r) := by
      dsimp [ρ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact (Real.exp_le_exp.mpr (by linarith : -q ≤ -2 * r - 1)).trans
      (exp_sub_one_le_half_exp (-2 * r))
  have hweight := weight_correlating_large_box_overlaps z lengths f U.eval
    (ρ := ρ) (B := Real.exp (p + 1)) (δ := δ)
    (Real.exp_nonneg _) (Real.exp_pos _) (Real.exp_nonneg _) hf
    (fun x _ => U.eval_budget hU x) hcorrU
  have hμ : μ ≤ ∑ h ∈ cubeDifferenceSupport Q,
      (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) * (if P h then (1 : ℝ) else 0) :=
    (retained_exponential_weight (Fintype.card σ) (r := r) hσ).trans hweight
  have hretained (h : σ → ℤ) (hh : h ∈ cubeDifferenceSupport Q) (hP : P h) :
      δ * Q.card ≤ ((derivativeSupport Q h).card : ℝ) ∧
      η0 ≤ finiteSupportGowersNorm (s + 1) (derivativeSupport Q h) (multiplicativeDerivative f h) := by
    refine ⟨hP.2.le, ?_⟩
    let lens := fun i => ((lengths i : ℤ) - |h i|).toNat
    let origin := fun i => z i + max 0 (-h i)
    let : ∀ i, NeZero (lens i) := fun i => ⟨(box_overlap_length_pos z lengths hh i).ne'⟩
    have hR : derivativeSupport Q h = translatedIntegerBox origin lens :=
      derivativeSupport_translatedIntegerBox z lengths h
    have hunit : ∀ x ∈ translatedIntegerBox origin lens, ‖multiplicativeDerivative f h x‖ ≤ 1 := by
      rw [← hR]
      intro x hx
      obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
      simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
        mul_le_mul (hf x hx) (hf (x + h) hxh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hcorr : Real.exp (-q) ≤ ‖finiteCorrelation (translatedIntegerBox origin lens)
        (multiplicativeDerivative f h) (multiplicativeDerivative U.eval h)‖ := by
      rw [← hR]
      exact hρsq.trans hP.1
    have hd := hder c hI D (p + 1) q (by linarith) hq (hσ.trans hcost.2.2) hcost.1
      w hw U hU (fun g => ((realifyFunctional η g.coord : ℝ) : CircleFourier.Circle)) hchar
      h origin lens (multiplicativeDerivative f h) hunit hcorr
    rwa [← hR] at hd
  have hgowers := box_gowers_lower_bound_of_overlaps z lengths s f P
    (Real.exp_nonneg _) (Real.exp_nonneg _) hμ hretained
  have hpow : Real.exp (-boxDetectionStepBudget s av bs c p) ≤
      finiteSupportGowersNorm (s + 2) Q f ^ (2 ^ (s + 2)) :=
    (box_detection_exponential_product s av bs c (Fintype.card σ) hσ).trans hgowers
  have hnorm : 0 ≤ finiteSupportGowersNorm (s + 2) Q f := by
    rw [finiteSupportGowersNorm_eq_restricted (translatedIntegerBox_reflectsPairSums lengths z)]
    exact restrictedGowersNorm_nonneg (s + 1) _ _
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    (exp_neg_le_of_pow hnorm (boxDetectionStepBudget_nonneg s av bs c hp)
      (pow_ne_zero _ (by norm_num)) hpow)

theorem exists_boxNiltestDetection.{u,v} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ BoxNiltestDetection.{u,v} s (fun p => (p + C) ^ C) := by
  induction s with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro σ _ _ L _ _ d _ _ _ _ D p hp hσ w hw T hT z lengths _ f hf hc
    have hb : 2 * p ≤ (p + (2 : ℕ)) ^ 2 := by
      norm_num only [Nat.cast_ofNat]
      nlinarith [sq_nonneg p]
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans
      (boxNiltestDetection_zero D p hp hσ w hw T hT z lengths f hf hc)
  | succ s ih =>
    obtain ⟨c, _, hc⟩ := ih
    exact boxNiltestDetection_succ hc

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem exists_intervalNiltestDetection.{u} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      1 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∀ (a : ℤ) (len : ℕ) [NeZero len] (f : ℤ → ℂ),
      (∀ x ∈ Finset.Ico a (a + len), ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (Finset.Ico a (a + len)) f
        (fun x => T.eval (fun _ => x))‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1)
        (Finset.Ico a (a + len)) f := by
  obtain ⟨C, hC, hdet⟩ := exists_boxNiltestDetection s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp w hw T hT a len hlen f hf hc
  have hunit : ∀ x ∈ translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => len),
      ‖f (x 0)‖ ≤ 1 := by
    intro x hx
    exact hf (x 0) (Finset.mem_Ico.mpr ((mem_translatedIntegerBox _ _ x).mp hx 0))
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation
      (translatedIntegerBox (fun _ : Fin 1 => a) (fun _ => len)) (fun x => f (x 0)) T.eval‖ := by
    rwa [oneDimensionalBox_correlation]
  have hp0 : 0 ≤ p := by linarith
  have hdim : (Fintype.card (Fin 1) : ℝ) ≤ p := by simpa using hp
  have hh := @hdet (Fin 1) inferInstance inferInstance L inferInstance inferInstance d
    inferInstance inferInstance inferInstance inferInstance D p hp0 hdim w hw T hT
    (fun _ => a) (fun _ => len) (fun _ => hlen) (fun x => f (x 0)) hunit hcorr
  simpa only [oneDimensionalBox_norm] using hh

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CyclicNiltestDetection.{u} (s : ℕ) (F : ℝ → ℝ) : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (p : ℝ),
    0 ≤ p → ∀ (w : Fin 1 → ℕ), (∀ i, 0 < w i) →
    ∀ (T : D.Niltest w), T.ComplexityLE p →
    ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℂ),
    (∀ x, ‖f x‖ ≤ 1) →
    Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (fun x => T.eval (fun _ => (x.val : ℤ)))‖ →
    Real.exp (-F p) ≤ gowersNorm (s + 1) f

theorem cyclicNiltestDetection_zero.{u} : CyclicNiltestDetection.{u} 0 (fun p => 2 * p) := by
  intro L _ _ d _ _ _ _ D p hp w hw T hT N _ f hf hc
  have hh := RationalFilteredNilmanifold.Niltest.detection_step_zero_sample
    D T hT Finset.univ (fun x : ZMod N => fun _ => (x.val : ℤ)) f hc
  have he : Real.exp (-p) / Real.exp p = Real.exp (-(2 * p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [he, ← gowersNorm_one] at hh

theorem exists_cyclicNiltestDetection_succ.{u} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNiltestDetection.{u} (s + 1) (fun p => (p + C) ^ C) := by
  obtain ⟨c, _, hdet⟩ := exists_intervalNiltestDetection.{u} (s + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_cyclicDetectionBudget_bound s c
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D p hp w hw T hT N _ f hf hc
  obtain ⟨i, hi, hcorr, hvol⟩ := exists_correlating_cyclicQuarter f
    (fun x => T.eval (fun _ => (x.val : ℤ))) (Real.exp_pos (-p)) (Real.exp_pos p)
    hf (fun x => T.eval_budget hT _) hc
  let a := quarterLower N i
  let len := quarterUpper N i - quarterLower N i
  have hb := quarter_bounds N i
  have hlen : len ≤ N := by dsimp [len]; omega
  have hcard : (cyclicQuarter N i).card = len :=
    cyclicInterval_card (a : ZMod N) hlen
  have hlenpos : 0 < len := by rw [← hcard]; exact hi.card_pos
  let : NeZero len := ⟨hlenpos.ne'⟩
  have hshort : 2 * ((len : ℤ) - 1) < N := by
    have hs := quarter_short N (NeZero.pos N) i
    dsimp [len]
    omega
  have hbound : a + len ≤ N := by dsimp [a, len]; omega
  have hvolume : Real.exp (-(2 * p + 8)) ≤ (len : ℝ) / N := by
    rw [hcard] at hvol
    exact (cyclic_retained_volume_exp p).trans hvol
  have hcorr' : Real.exp (-(p + 8)) ≤ ‖finiteCorrelation
      (Finset.Ico (a : ℤ) (a + len)) (fun x => f (x : ZMod N))
      (fun x => T.eval (fun _ => x))‖ := by
    change Real.exp (-p) / 8 ≤ ‖finiteCorrelation (cyclicInterval (a : ZMod N) len) f
      (fun x => T.eval (fun _ => (x.val : ℤ)))‖ at hcorr
    rw [cyclicInterval_representative_correlation a len hbound hshort f
      (fun x => T.eval (fun _ => x))] at hcorr
    have he : Real.exp (-(p + 8)) ≤ Real.exp (-p) / 8 := by
      simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using exp_sub_eight_le_eighth_exp (-p)
    exact he.trans hcorr
  have hlocal := hdet D (p + 8) (by linarith) w hw T (hT.mono (by linarith))
    (a : ℤ) len (fun x => f (x : ZMod N)) (fun x _ => hf _) hcorr'
  have hpow := cyclicInterval_gowersNorm_lower_pow (a : ℤ) len (s + 1) hshort f
    (Real.exp_nonneg (-(2 * p + 8))) (Real.exp_nonneg (-((p + 8 + c) ^ c))) hvolume hlocal
  have hpower : Real.exp (-cyclicCutoffBudget s c p) ≤
      gowersNorm (s + 2) (fun x => f x * finiteIndicator (cyclicInterval (a : ZMod N) len) x)
        ^ (2 ^ (s + 2)) := by
    apply (cyclic_cutoff_exponential_product s c p).trans
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, Int.cast_natCast] at hpow ⊢
    exact hpow
  have hcut := exp_neg_le_of_pow (gowersNorm_nonneg (s + 1) _)
    (cyclicCutoffBudget_nonneg s c hp) (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hpower
  have htransfer := gowersNorm_transfer_cyclicInterval s f hf (a : ZMod N) len
    (Real.exp_pos (-cyclicCutoffBudget s c p))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (cyclicCutoffBudget_nonneg s c hp))) hcut
  exact (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp))).trans
    ((cyclic_transfer_exponential s c p).trans htransfer)

theorem exists_cyclicNiltestDetection.{u} (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNiltestDetection.{u} s (fun p => (p + C) ^ C) := by
  cases s with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro L _ _ d _ _ _ _ D p hp w hw T hT N _ f hf hc
    have hb : 2 * p ≤ (p + (2 : ℕ)) ^ 2 := by
      norm_num only [Nat.cast_ofNat]
      nlinarith [sq_nonneg p]
    exact (Real.exp_le_exp.mpr (neg_le_neg hb)).trans
      (cyclicNiltestDetection_zero D p hp w hw T hT N f hf hc)
  | succ s => exact exists_cyclicNiltestDetection_succ s

end Erdos3

end

end OAI

/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.NormalizedTwistExtractionBudget
import OAI.Combinatorics.Progressions.Nilpotent.MajorTranslationPartnerNiltest
import OAI.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates
import OAI.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse

namespace OAI

section

namespace Erdos3

theorem exists_majorPhaseLowFourierExtraction_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := (p + a) ^ a + p + 1
      q ≤ (p + C) ^ C ∧ (q + b) ^ b ≤ (p + C) ^ C ∧
        3 * q + 16 ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C b) ^ b + 3 * Q + 16)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  let q : ℝ := (p + a) ^ a + p + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ (q + b) ^ b := by positivity
  have htotal : q + (q + b) ^ b + 3 * q + 16 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  change q ≤ _ ∧ (q + b) ^ b ≤ _ ∧ 3 * q + 16 ≤ _
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators

theorem normalizedTwistFrequencyPolynomial_truncate_correlation
    {X Ω : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (cover d : ℕ) (W : ∀ j, Submodule ℝ (J j → ℝ))
    (a : (Σ j, J j) → ℤ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
    (hann : ∀ j, d < j.val + 1 →
      W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
    (s : Finset Ω) (u : Ω → X → ℝ) (signal : Ω → ℂ) :
    ‖𝔼 x ∈ s, (Real.fourierChar (MvPolynomial.eval (u x)
      (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * signal x‖ =
    ‖𝔼 x ∈ s, (Real.fourierChar (MvPolynomial.eval (u x)
      (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly)) : ℂ) *
        signal x‖ := by
  have he (x : Ω) :
      (Real.fourierChar (MvPolynomial.eval (u x)
        (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * signal x =
      (Real.fourierChar (normalizedTwistHighFrequencyConstant cover d a poly) : ℂ) *
        ((Real.fourierChar (MvPolynomial.eval (u x)
          (normalizedTwistFrequencyPolynomial cover (truncateTaggedFrequency d a) poly)) : ℂ) *
            signal x) := by
    rw [normalizedTwistFrequencyPolynomial_low_add_constant cover d W a poly hcoeff hann,
      map_add, eval_C, Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_expect, norm_mul, Circle.norm_coe, one_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_normalizedTwist_high_frequency_removal_on_progression (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (cover : ℕ) (_hcover : 0 < cover) (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        N Rrank (W j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ →
      ∀ j, d < j.val + 1 → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  choose c hc hinverse using fun j : Fin m =>
    OrdinaryPolynomialPhase.exists_ordinary_polynomial_phase_affine_inverse (j.val + 1)
      (Nat.succ_pos _)
  let B := (∑ j, c j) + 2
  have hcB (j : Fin m) : c j ≤ B :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Nat.le_add_right _ _)
  have hB : 2 ≤ B := by dsimp [B]; omega
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ d D htd R cover hcover a poly hpoly W hcoeff p Rrank hp
    hR hRcap hcoverp ha q hq hqp start K hK hKp N hN origin lengths hlengths hNL hX hlarge hRrank hrank hcorr
  have hbudget' : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hbase : 1 ≤ p + B := by
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hlocal (j : Fin m) : (p + c j) ^ c j ≤ (p + B) ^ B := by
    have hb : p + (c j : ℝ) ≤ p + B := by
      have hh : (c j : ℝ) ≤ B := Nat.cast_le.mpr (hcB j)
      linarith
    apply (pow_le_pow_left₀ (by positivity) hb _).trans
    exact pow_le_pow_right₀ hbase (hcB j)
  rcases highest_nonannihilating_tag d W a with hann | ⟨h, hd, hw, hhigher⟩
  · exact hann
  · exfalso
    have hhigh (j : Fin m) (hj : h < j) :
        integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) =
          MvPolynomial.C ((integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)).coeff 0) :=
      integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hhigher j hj)
    have hdegree (j : Fin m) := integerRowPolynomial_totalDegree_le
      (fun i => a ⟨j, i⟩) (hpoly j)
    have hphase : (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ h.val + 1 := by
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact taggedScalar_sum_degree h _ hdegree hhigh
    have htop : homogeneousComponent (h.val + 1) (normalizedTwistFrequencyPolynomial cover a poly) =
        MvPolynomial.C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
          (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h)) := by
      rw [normalizedTwistFrequencyPolynomial, homogeneousComponent_C_mul,
        taggedScalar_sum_top h _ hdegree hhigh]
    have hcost : p + (p + c h) ^ c h ≤ (p + C) ^ C := by linarith [hlocal h]
    have hap := hinverse h D (by omega) (normalizedTwistFrequencyPolynomial cover a poly)
      hphase R p hp hR hRcap q hq hqp start K hK hKp N hN origin lengths hlengths hNL hX
      (fun i => (Real.exp_le_exp.mpr (by linarith : (p + c h) ^ c h ≤ (p + C) ^ C)).trans
        (hlarge i)) (by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hcorr)
    apply normalizedTwistFrequencyPolynomial_top_not_approximation cover hcover h a poly
      (W h) N Rrank (Real.exp ((p + c h) ^ c h)) hN
      ?_ (hrank h hd) ?_ hw htop hap
    · calc
        _ ≤ Real.exp p * Real.exp ((p + c h) ^ c h) :=
          mul_le_mul_of_nonneg_right hcoverp (Real.exp_nonneg _)
        _ = Real.exp (p + (p + c h) ^ c h) := (Real.exp_add _ _).symm
        _ ≤ Rrank := (Real.exp_le_exp.mpr hcost).trans hRrank
    · intro i
      exact (ha ⟨h, i⟩).trans ((Real.exp_le_exp.mpr
        (by linarith [pow_nonneg (show 0 ≤ p + B by positivity) B] : p ≤ (p + C) ^ C)).trans hRrank)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_rank_localized_correlating_frequency (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (d : ℕ) (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        ∀ j, d < j.val + 1 → U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  obtain ⟨aC, _, hselect⟩ := exists_localized_correlating_frequency
  obtain ⟨bC, _, hremove⟩ := exists_normalizedTwist_high_frequency_removal_on_progression m
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedTwistExtractionBudget aC bC
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W d D htd R N poly hpoly
    U hcoeff p Rrank hp hR hcap hX hJ hmod hcover hLip hN hRrank hrank hcorr
  let q : ℝ := (p + aC) ^ aC + 3 * p + 16
  have hpow : 0 ≤ (p + aC) ^ aC := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsideq : 3 * p + 16 ≤ q := by dsimp [q]; linarith
  have hfreqq : (p + aC) ^ aC ≤ q := by dsimp [q]; linarith
  have hbudget' : q + (q + bC) ^ bC + 3 * p + 16 ≤ (p + C) ^ C := hbudget p hp
  have hremoven : 0 ≤ (q + bC) ^ bC := by positivity
  have hqfinal : q ≤ (p + C) ^ C := by linarith
  have hremovefinal : (q + bC) ^ bC ≤ (p + C) ^ C := by linarith
  have hsidefinal : 3 * p + 16 ≤ (p + C) ^ C := hsideq.trans hqfinal
  have hsmallN (i : X) : Real.exp (3 * p + 16) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hsidefinal).trans (hN i)
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected⟩ :=
    hselect W N poly R.eval p hp hJ hmod hLip hsmallN
      (fun u _ => (R.norm_eval_le u).trans hcap) hcorr
  let R' := R.scalarAffinePullback (W.modulus : ℚ) (fun i => (start i : ℚ))
  have hR' : R'.ComplexityLE q := hR.mono hpq
  have hR'cap : (R'.normBound : ℝ) ≤ 1 := hcap
  have hR'eval (v : X → ℤ) :
      R'.eval v = R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) := by
    simpa only [R', Int.cast_natCast, add_comm] using
      R.scalarAffinePullback_eval_integer (W.modulus : ℤ) (fun i => (start i : ℤ)) v
  have hzero : translatedIntegerBox (0 : X → ℤ) length = integerBox length := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hlong (i : X) : Real.exp ((q + bC) ^ bC) ≤ (length i : ℝ) := by
    calc
      _ = Real.exp ((q + bC) ^ bC + (3 * p + 16)) * Real.exp (-(3 * p + 16)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((p + C) ^ C) * Real.exp (-(3 * p + 16)) := by
        gcongr
        linarith
      _ ≤ (N i : ℝ) * Real.exp (-(3 * p + 16)) :=
        mul_le_mul_of_nonneg_right (hN i) (Real.exp_nonneg _)
      _ ≤ _ := hlength i
  have hselected' : Real.exp (-q) ≤ ‖𝔼 v ∈ translatedIntegerBox (0 : X → ℤ) length,
      (Real.fourierChar (MvPolynomial.eval
        (fun i => ((start i : ℤ) : ℝ) + (W.modulus : ℝ) * (v i : ℝ))
        (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) * R'.eval v‖ := by
    rw [hzero]
    simpa only [hR'eval, Int.cast_natCast] using
      (Real.exp_le_exp.mpr (neg_le_neg hfreqq)).trans hselected
  have hann := hremove J d D htd R' W.cover W.cover_pos a poly hpoly U hcoeff q Rrank
    hq hR' hR'cap (hcover.trans (Real.exp_le_exp.mpr hpq))
    (fun i => (ha i).trans (Real.exp_le_exp.mpr hfreqq))
    W.modulus W.modulus_pos (hmod.trans (Real.exp_le_exp.mpr hpq))
    (fun i => (start i : ℤ)) (Real.exp (3 * p + 16))
    (Real.one_le_exp (by positivity)) (Real.exp_le_exp.mpr hsideq)
    (fun i => (N i : ℝ)) (fun i => (Real.exp_pos _).trans_le (hN i))
    0 length hpos hcomparison (hX.trans hpq) hlong
    ((Real.exp_le_exp.mpr hremovefinal).trans hRrank) hrank hselected'
  refine ⟨start, length, a, hpos, hlength, hcomparison, hinside, ?_, ?_, hann⟩
  · exact fun i => (ha i).trans (Real.exp_le_exp.mpr (hfreqq.trans hqfinal))
  · exact (Real.exp_le_exp.mpr (neg_le_neg (hfreqq.trans hqfinal))).trans hselected

theorem exists_low_localized_correlating_frequency (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (d : ℕ) (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (Fintype.card X : ℝ) ≤ p → (Fintype.card (Σ j, J j) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        (∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0) ∧
        (normalizedTwistFrequencyPolynomial W.cover a poly).totalDegree ≤ d := by
  obtain ⟨C, hC, hextract⟩ := exists_rank_localized_correlating_frequency m
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W d D htd R N poly hpoly
    U hcoeff p Rrank hp hR hcap hX hJ hmod hcover hLip hN hRrank hrank hcorr
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected, hann⟩ :=
    hextract J W d D htd R N poly hpoly U hcoeff p Rrank hp hR hcap hX hJ
      hmod hcover hLip hN hRrank hrank hcorr
  refine ⟨start, length, truncateTaggedFrequency d a, hpos, hlength, hcomparison, hinside,
    ?_, ?_, ?_, normalizedTwistFrequencyPolynomial_low_degree W.cover d a poly hpoly⟩
  · intro i
    by_cases hi : i.1.val + 1 ≤ d
    · simpa only [truncateTaggedFrequency, ite_eq_left hi] using ha i
    · simp only [truncateTaggedFrequency, ite_eq_right hi, Int.cast_zero, abs_zero]
      exact Real.exp_nonneg _
  · rw [← normalizedTwistFrequencyPolynomial_truncate_correlation W.cover d U a poly
      hcoeff hann (integerBox length)
      (fun v i => (start i : ℝ) + (W.modulus : ℝ) * v i)
      (fun v => R.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i))]
    exact hselected
  · intro j hj i
    simp only [truncateTaggedFrequency, ite_eq_right (not_le_of_gt hj)]

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct Classical

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates
    (cover : ℕ) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (ha : ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))) :
    normalizedTwistFrequencyPolynomial cover a poly = 0 := by
  have hz (j : Fin m) : integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) = 0 := by
    ext α
    rw [integerRowPolynomial_coeff, AddMonoidAlgebra.coeff_zero, ← integerRowLinear_apply]
    exact ha j (hm j α)
  simp only [normalizedTwistFrequencyPolynomial, hz, Finset.sum_const_zero, mul_zero]

theorem exists_normalizedTwist_uniform_box_frequency_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (cover : ℕ), 0 < cover → ∀ (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ (p Rrank : ℝ), 2 ≤ p →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ)) -
        (if ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
          then 1 else 0)‖ ≤ Real.exp (-p) := by
  classical
  obtain ⟨C, hC, hremove⟩ := exists_normalizedTwist_high_frequency_removal_on_progression m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ cover hcover a poly hpoly U hm p Rrank hp hcoverp ha
    q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank
  by_cases hann : ∀ j, U j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩))
  · rw [ite_eq_left hann, normalizedTwistFrequencyPolynomial_eq_zero_of_annihilates cover a poly U hm hann]
    let : ∀ i, NeZero (lengths i) := fun i => ⟨(hlengths i).ne'⟩
    simp only [map_zero, Real.fourierChar.map_zero_eq_one, Circle.coe_one,
      Finset.expect_const (translatedIntegerBox_nonempty lengths origin), sub_self, norm_zero]
    exact (Real.exp_pos _).le
  · rw [ite_eq_right hann, sub_zero]
    apply le_of_lt
    by_contra! hcorr
    let R := Niltest.const (RationalTorus.trivialNilmanifold 0) (fun _ : X => 1) 1
    have hR : R.ComplexityLE p := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ hp
    have hcap : (R.normBound : ℝ) ≤ 1 := by simp [R, Niltest.const]
    have hcorr' : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ := by
      simpa only [R, Niltest.eval_const, mul_one] using hcorr
    have hall := hremove J 0 (RationalTorus.trivialNilmanifold 0) le_rfl R cover hcover a poly hpoly U
      (fun j α _ => hm j α) p Rrank (by linarith) hR hcap hcoverp ha q hq hqp
      start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank
      (fun j _ => hrank j) hcorr'
    exact hann (fun j => hall j (Nat.succ_pos _))

theorem exists_normalizedTwist_uniform_box_fourier_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      {F : Type*} [Fintype F] (cover : ℕ), 0 < cover →
      ∀ (frequency : F → (Σ j, J j) → ℤ) (coeff : F → ℂ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ (p Rrank : ℝ), 2 ≤ p →
      (cover : ℝ) ≤ Real.exp p → (∀ b i, |(frequency b i : ℝ)| ≤ Real.exp p) →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        ∑ b, coeff b * (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover (frequency b) poly)) : ℂ)) -
        ∑ b, coeff b * (if ∀ j, U j ≤ LinearMap.ker
          (integerRowLinear (fun i => frequency b ⟨j, i⟩)) then 1 else 0)‖ ≤
        (∑ b, ‖coeff b‖) * Real.exp (-p) := by
  obtain ⟨C, hC, hfreq⟩ := exists_normalizedTwist_uniform_box_frequency_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ F _ cover hcover frequency coeff poly hpoly U hm p Rrank hp hcoverp ha
    q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank
  simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hfreq cover hcover (frequency b) poly hpoly U hm p Rrank hp hcoverp (ha b)
      q hq hqp start K hK hKp N hN origin lengths hlengths hNL hdim hlarge hRrank hrank)
    (norm_nonneg _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

noncomputable def majorPhaseSample {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (r : (X → ℤ) → ℂ) (u : X → ℤ) : ℂ :=
  ((Ψ.value (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J d poly i) - c i - (β u i : ℝ)) : ℂ) *
    (Real.fourierChar (MvPolynomial.eval (fun j => ((Sum.elim u (β u) j : ℤ) : ℝ)) F) : ℂ)) * r u

theorem exists_majorPhase_low_localized_correlating_frequency (m d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1)) (_hd : 0 < d)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J d poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u‖ →
      ∃ (start length : X → ℕ) (a : (Σ j, J j) → ℤ),
        (∀ i, 0 < length i) ∧
        (∀ i, (N i : ℝ) * Real.exp (-((p + C) ^ C)) ≤ length i) ∧
        (∀ i, (N i : ℝ) ≤ Real.exp ((p + C) ^ C) * W.modulus * length i) ∧
        (∀ v ∈ integerBox length,
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) ∈ integerBox N) ∧
        (∀ j, |(a j : ℝ)| ≤ Real.exp ((p + C) ^ C)) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 v ∈ integerBox length,
          (Real.fourierChar (MvPolynomial.eval
            (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
            (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
          majorPhaseSample J d poly Ψ c F β R.eval
            (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)‖ ∧
        (∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0) ∧
        (normalizedTwistFrequencyPolynomial W.cover a poly).totalDegree ≤ d := by
  obtain ⟨aC, _, hpartner⟩ := exists_majorTranslation_partner_niltest d
  obtain ⟨bC, _, hextract⟩ :=
    NormalizedPolynomialTwist.exists_low_localized_correlating_frequency m
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseLowFourierExtraction_budget aC bC
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W D htd R hd
    N poly hpoly U hcoeff Ψ c F hF β hβ p Rrank hp hR hcap hdim hmod hcover hLip hΨ
    hN hRrank hrank hcorr
  let w := lowTaggedWeight J d
  have hw : ∀ i, 0 < w i := lowTaggedWeight_pos J d
  have hwd : ∀ i, w i ≤ d := lowTaggedWeight_le J d
  let := weightedBasisIndex_finite w d hw
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  let A := fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i)
  have hdimMajor : ((Fintype.card X + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.add_le_add_left (lowTaggedIndex_card_le J d) _
  let M := majorTranslationPartnerModel w d hw hwd D htd
  let : FiniteDimensional ℚ (PairAlgebra (weightedSubalgebra w d) L) :=
    M.basis.finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] PairAlgebra (weightedSubalgebra w d) L) :=
    realification_moduleTopology_t2 M.basis
  obtain ⟨S, hSnorm, hS, hSeval⟩ :=
    hpartner w hw hwd D htd R hd Ψ F hF A hA p hp hdimMajor hΨ hR hcap
  have hsample (u : X → ℤ) (hu : u ∈ integerBox N) :
      S.eval u = majorPhaseSample J d poly Ψ c F β R.eval u := by
    have hclose : ∀ i, |MvPolynomial.eval (fun j => (u j : ℝ)) (A i) - (β u i : ℝ)| ≤ 1/2 := by
      simpa only [A, map_sub, eval_C] using hβ u hu
    simpa only [majorPhaseSample, A, map_sub, eval_C] using hSeval u (β u) hclose
  let q : ℝ := (p + aC) ^ aC + p + 1
  have hpow : 0 ≤ (p + aC) ^ aC := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hSq : S.ComplexityLE q := hS.mono (by dsimp [q]; linarith)
  have hcapS : (S.normBound : ℝ) ≤ 1 := by rw [hSnorm]; rfl
  have hX : (Fintype.card X : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.le_add_right (Fintype.card X) (Fintype.card (Σ j, J j))
  have hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.le_add_left (Fintype.card (Σ j, J j)) (Fintype.card X)
  obtain ⟨_, hfinal, hside⟩ := hbudget p hp
  have hcorrS : Real.exp (-q) ≤ ‖𝔼 u ∈ integerBox N, W.eval N poly u * S.eval u‖ := by
    have heq : (𝔼 u ∈ integerBox N, W.eval N poly u * S.eval u) =
        𝔼 u ∈ integerBox N, W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u := by
      apply Finset.expect_congr rfl
      intro u hu
      rw [hsample u hu]
    rw [heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hcorr
  obtain ⟨start, length, a, hpos, hlength, hcomparison, hinside, ha, hselected, hhigh, hdegree⟩ :=
    hextract J W d M le_rfl S N poly hpoly U hcoeff q Rrank hq hSq hcapS
      (hX.trans hpq) (hJ.trans hpq)
      (hmod.trans (Real.exp_le_exp.mpr hpq)) (hcover.trans (Real.exp_le_exp.mpr hpq))
      (hLip.trans (Real.exp_le_exp.mpr hpq))
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hN i))
      ((Real.exp_le_exp.mpr hfinal).trans hRrank) hrank hcorrS
  refine ⟨start, length, a, hpos, ?_, ?_, hinside, ?_, ?_, hhigh, hdegree⟩
  · intro i
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hside))
      (Nat.cast_nonneg (N i))).trans (hlength i)
  · intro i
    exact (hcomparison i).trans (by
      gcongr)
  · exact fun j => (ha j).trans (Real.exp_le_exp.mpr hfinal)
  · have heq : (𝔼 v ∈ integerBox length,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
        S.eval (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i)) =
        𝔼 v ∈ integerBox length,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (W.modulus : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
        majorPhaseSample J d poly Ψ c F β R.eval
          (fun i => (start i : ℤ) + (W.modulus : ℤ) * v i) := by
      apply Finset.expect_congr rfl
      intro v hv
      rw [hsample _ (hinside v hv)]
    rw [heq] at hselected
    exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hselected

end Erdos3.VectorPolynomial

end

end OAI

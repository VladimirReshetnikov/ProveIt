/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments
import OAI.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
import OAI.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer
import OAI.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def cyclicCarry {N : ℕ} (h n : ZMod N) : ℝ :=
  if N ≤ h.val + n.val then 1 else 0

noncomputable def circleCarryCutoff (δ : ℝ≥0) (x : CircleFourier.Circle) : ℝ :=
  linearCutoff (1 / 6) δ (dist x ((1 / 2 : ℝ) : CircleFourier.Circle))

noncomputable def smoothCyclicCarry (N : ℕ) (δ : ℝ≥0) (x : Fin 2 → ℤ) : ℝ :=
  circleCarryCutoff δ ((((x 0 : ℝ) + (x 1 : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)

theorem circleCarryCutoff_range (δ : ℝ≥0) (x : CircleFourier.Circle) :
    0 ≤ circleCarryCutoff δ x ∧ circleCarryCutoff δ x ≤ 1 := linearCutoff_range _ _ _

theorem circleCarryCutoff_lipschitz (δ : ℝ≥0) (hδ : 0 < δ) :
    LipschitzWith δ⁻¹ (circleCarryCutoff δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply ((linearCutoff_lipschitz (1 / 6) δ hδ).dist_le_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [Real.dist_eq]
  exact abs_dist_sub_le _ _ _

theorem circle_dist_half_of_unit_interval {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    dist (t : CircleFourier.Circle) ((1 / 2 : ℝ) : CircleFourier.Circle) = |t - 1 / 2| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  apply (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).mpr
  norm_num only [abs_one]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem smoothCyclicCarry_eq_of_outside {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (h n : ZMod N)
    (hn : n ∉ cyclicCutNeighborhood N ((N : ℤ) - h.val) (3 * N * (δ : ℝ))) :
    smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] = cyclicCarry h n := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  let s : ℝ := h.val + n.val
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s < 2 * N := by
    have hh : (h.val : ℝ) < N := Nat.cast_lt.mpr h.val_lt
    have hn' : (n.val : ℝ) < N := Nat.cast_lt.mpr n.val_lt
    dsimp [s]
    linarith
  have ht0 : 0 ≤ s / (3 * N) := by positivity
  have ht2 : s / (3 * N) ≤ 2 / 3 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hdist := circle_dist_half_of_unit_interval ⟨ht0, ht2.trans (by norm_num)⟩
  change linearCutoff (1 / 6) δ (dist ((s / (3 * N) : ℝ) : CircleFourier.Circle)
    ((1 / 2 : ℝ) : CircleFourier.Circle)) = cyclicCarry h n
  rw [hdist]
  by_cases hw : N ≤ h.val + n.val
  · have hsN : (N : ℝ) ≤ s := by dsimp [s]; exact_mod_cast hw
    have ht1 : 1 / 3 ≤ s / (3 * N) := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    rw [linearCutoff_eq_one _ _ hδ (abs_le.mpr ⟨by linarith, by linarith⟩)]
    simp only [cyclicCarry, hw, ite_true]
  · have hsN : s < (N : ℝ) := by dsimp [s]; exact_mod_cast Nat.lt_of_not_ge hw
    have hgap := lt_of_not_ge (fun hh => hn ((mem_cyclicCutNeighborhood _ _ _ _).mpr hh))
    simp only [Int.cast_sub, Int.cast_natCast] at hgap
    rw [abs_of_neg (by dsimp [s] at hsN; linarith)] at hgap
    have hfar : 1 / 6 + (δ : ℝ) ≤ |s / (3 * N) - 1 / 2| := by
      rw [abs_of_neg (by
        have : s / (3 * N) < 1 / 3 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
        linarith)]
      have ht : s / (3 * N) ≤ 1 / 3 - (δ : ℝ) := by
        apply (div_le_iff₀ (by positivity)).mpr
        dsimp [s]
        nlinarith
      linarith
    rw [linearCutoff_eq_zero _ _ hfar]
    simp only [cyclicCarry, hw, ite_false]

theorem smoothCyclicCarry_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ) :
    (𝔼 x : Fin 2 → ZMod N,
      |cyclicCarry (x 0) (x 1) - smoothCyclicCarry N δ (fun j => ((x j).val : ℤ))|) ≤
      6 * (δ : ℝ) + 1 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hrow (h : ZMod N) :
      (𝔼 n : ZMod N, |cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)]|) ≤
        6 * (δ : ℝ) + 1 / N := by
    let E := cyclicCutNeighborhood N ((N : ℤ) - h.val) (3 * N * (δ : ℝ))
    have hcard : (E.card : ℝ) ≤ 6 * N * (δ : ℝ) + 1 := by
      simpa only [show 2 * (3 * (N : ℝ) * (δ : ℝ)) = 6 * N * (δ : ℝ) by ring] using
        cyclicCutNeighborhood_card_le N ((N : ℤ) - h.val) (by positivity : 0 ≤ 3 * N * (δ : ℝ))
    have hcap (n : ZMod N) :
        |cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)]| ≤ 1 := by
      have hr := circleCarryCutoff_range δ
        (((((h.val : ℤ) : ℝ) + ((n.val : ℤ) : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)
      change 0 ≤ smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] ∧
        smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)] ≤ 1 at hr
      unfold cyclicCarry
      split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hh := expect_abs_le_of_exceptional_set E
      (fun n => cyclicCarry h n - smoothCyclicCarry N δ ![(h.val : ℤ), (n.val : ℤ)])
      (by norm_num : (0 : ℝ) ≤ 0) hcap (fun n hn => by
        rw [smoothCyclicCarry_eq_of_outside δ hδ h n hn, sub_self, abs_zero])
    simp only [zero_add, one_mul, ZMod.card] at hh
    apply hh.trans
    apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ 6 * N * (δ : ℝ) + 1 := hcard
      _ = (6 * (δ : ℝ) + 1 / N) * N := by field_simp
  rw [expect_fin_two]
  exact (Finset.expect_le_expect (fun h _ => hrow h)).trans_eq (Fintype.expect_const _)

theorem exists_smoothCyclicCarry_expansion (N : ℕ) (δ : ℝ≥0) (hδ : 0 < δ)
    {p : ℝ} (hp : 0 ≤ p) (hinv : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ x : ℂ))) := by
  let Ψ : (Fin 1 → CircleFourier.Circle) → ℂ := fun v => (circleCarryCutoff δ (v 0) : ℂ)
  have hΨ (v : Fin 1 → CircleFourier.Circle) : ‖Ψ v‖ ≤ (1 : ℝ≥0) := by
    change ‖(circleCarryCutoff δ (v 0) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (circleCarryCutoff_range δ _).1]
    exact (circleCarryCutoff_range δ _).2
  have hcoord : LipschitzWith 1 (fun v : Fin 1 → CircleFourier.Circle => v 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [NNReal.coe_one, one_mul] using dist_le_pi_dist v w 0
  have hLip : LipschitzWith δ⁻¹ Ψ := by
    simpa only [mul_one, one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp ((circleCarryCutoff_lipschitz δ hδ).comp hcoord)
  let T := RationalTorus.affineNiltest 1 0
    (fun _ : Fin 2 => fun _ : Fin 1 => 1 / (3 * (N : ℝ))) Ψ 1 δ⁻¹ hΨ hLip
  have hlog : Real.log (3 + (δ : ℝ)⁻¹) ≤ p + 4 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 := Real.one_le_exp hp
    have h4 : 4 ≤ Real.exp (4 : ℝ) := by linarith [Real.add_one_le_exp (4 : ℝ)]
    rw [Real.exp_add]
    nlinarith
  have hT : T.ComplexityLE (p + 4) :=
    RationalTorus.affineNiltest_complexity 1 0
      (fun _ : Fin 2 => fun _ : Fin 1 => 1 / (3 * (N : ℝ))) Ψ 1 δ⁻¹ hΨ hLip
      (by linarith) (by norm_num; linarith)
      (by simpa only [NNReal.coe_one, NNReal.coe_inv, show (2 : ℝ) + 1 = 3 by norm_num] using hlog)
  refine ⟨NativeIntegerExpansion.ofTest T hT ?_⟩
  intro x
  simp only [T, RationalTorus.affineNiltest_eval, smoothCyclicCarry, Ψ,
    Fin.sum_univ_two,
    Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_add]
  apply congrArg (fun t : ℝ => (circleCarryCutoff δ (t : CircleFourier.Circle) : ℂ))
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothCyclicCarry_fixed_shift_mean_error {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ZMod N) :
    (𝔼 n : ZMod N, |cyclicCarry k n -
      smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]|) ≤ 6 * (δ : ℝ) + 1 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  let E := cyclicCutNeighborhood N ((N : ℤ) - k.val) (3 * N * (δ : ℝ))
  have hcard : (E.card : ℝ) ≤ 6 * N * (δ : ℝ) + 1 := by
    simpa only [show 2 * (3 * (N : ℝ) * (δ : ℝ)) = 6 * N * (δ : ℝ) by ring] using
      cyclicCutNeighborhood_card_le N ((N : ℤ) - k.val) (by positivity : 0 ≤ 3 * N * (δ : ℝ))
  have hcap (n : ZMod N) :
      |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| ≤ 1 := by
    have hr := circleCarryCutoff_range δ
      (((((k.val : ℤ) : ℝ) + ((n.val : ℤ) : ℝ)) / (3 * N) : ℝ) : CircleFourier.Circle)
    change 0 ≤ smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)] ∧
      smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)] ≤ 1 at hr
    unfold cyclicCarry
    split_ifs <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hh := expect_abs_le_of_exceptional_set E
    (fun n => cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)])
    (by norm_num : (0 : ℝ) ≤ 0) hcap (fun n hn => by
      rw [smoothCyclicCarry_eq_of_outside δ hδ k n hn, sub_self, abs_zero])
  simp only [zero_add, one_mul, ZMod.card] at hh
  apply hh.trans
  apply (div_le_iff₀ hN).mpr
  calc
    _ ≤ 6 * N * (δ : ℝ) + 1 := hcard
    _ = (6 * (δ : ℝ) + 1 / N) * N := by field_simp

theorem exists_fixed_shift_smoothCyclicCarry_expansion (N : ℕ) (δ : ℝ≥0)
    (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) (hinv : (δ : ℝ)⁻¹ ≤ Real.exp p) (k : ℤ) :
    Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ ![k, x 1] : ℂ))) := by
  obtain ⟨E⟩ := exists_smoothCyclicCarry_expansion N δ hδ hp hinv
  let A : Fin 2 → Fin 2 → ℤ := ![![0, 0], ![0, 1]]
  let b : Fin 2 → ℤ := ![k, 0]
  have hinput (x : Fin 2 → ℤ) : integerAffineMap A b x = ![k, x 1] := by
    funext i
    fin_cases i <;> simp [integerAffineMap, A, b, Fin.sum_univ_two]
  simpa only [hinput] using
    (show Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (p + 4)
      (fun x => (smoothCyclicCarry N δ (integerAffineMap A b x) : ℂ))) from
        ⟨E.affinePullback A b⟩)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_quadratic_diagonal_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        (fun k : (Fin W.outputDim × Fin W.outputDim) ×
            (Fin W.outputDim × Fin W.outputDim) => fun x =>
          (W.eval k.1.1 (fun _ => x 1) * W.eval k.1.2 (correlationInput (x 1) (x 0))) *
            (W.eval k.2.1 (correlationInput (x 0) (x 1)) * W.eval k.2.2 (fun _ => x 0))) := by
  have hbound : mixedCorrelationDegree 1 = (fun _ : Fin 2 => 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hbound]
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence ([0, 1] : List (Fin 2))
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Option (Fin 2) → Fin 2 := fun j => match j with
    | none => 0
    | some _ => 1
  have E := (hexpand W (by decide)).coordinatePullback a
  have hleft (k : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval k (coordinateTranslatedInput [0, 1] (fun j => x (a j))) =
        W.eval k (fun _ => x 1 + x 0) := by
    apply congrArg (W.eval k)
    funext i
    fin_cases i <;> simp [coordinateTranslatedInput, a]
  have hright (k : (Fin W.outputDim × Fin W.outputDim) ×
      (Fin W.outputDim × Fin W.outputDim)) (x : Fin 2 → ℤ) :
      coordinateTranslationExpansion W.eval [0, 1] k (fun j => x (a j)) =
      (W.eval k.1.1 (fun _ => x 1) * W.eval k.1.2 (correlationInput (x 1) (x 0))) *
        (W.eval k.2.1 (correlationInput (x 0) (x 1)) * W.eval k.2.2 (fun _ => x 0)) := by
    simp only [coordinateTranslationExpansion]
    apply congrArg₂ (fun z w : ℂ => z * w)
    · apply congrArg₂ (fun z w : ℂ => z * w)
      · rfl
      · apply congrArg (W.eval k.1.2)
        funext i
        fin_cases i <;> rfl
    · apply congrArg₂ (fun z w : ℂ => z * w)
      · apply congrArg (W.eval k.2.1)
        funext i
        fin_cases i <;> rfl
      · apply congrArg (W.eval k.2.2)
        funext i
        fin_cases i <;> rfl
  refine ⟨E.left_dimension, E.right_dimension, ?_⟩
  intro k l
  obtain ⟨F⟩ := E.expansion k l
  exact ⟨by simpa only [Fintype.card_fin, Nat.reduceSub, hleft, hright] using F⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def quadraticMixedTriple (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star ((W.eval a.1 (correlationInput (x 1) (x 0)) *
    W.eval a.2.1 (correlationInput (x 0) (x 1))) * W.eval a.2.2 (fun _ => x 0))

theorem quadraticDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticDiagonalDerivative a x‖ ≤ 1 := by
  simp only [quadraticDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem quadraticMixedTriple_norm (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticMixedTriple a x‖ ≤ 1 := by
  simp only [quadraticMixedTriple, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
      (W.norm_eval _ _))).trans (W.norm_eval _ _)

theorem quadraticDiagonalDerivative_unit (x : Fin 2 → ℤ) :
    ∑ a, ‖W.quadraticDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [quadraticDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem quadraticMixedTriple_unit (x : Fin 2 → ℤ) :
    ∑ a, ‖W.quadraticMixedTriple a x‖ ^ 2 = 1 := by
  simp only [quadraticMixedTriple, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem exists_quadratic_diagonal_derivative_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        W.quadraticDiagonalDerivative W.quadraticMixedTriple := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 3 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + 3 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hthree : 3 * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdim2 := card_product_le_exp_two hdim hdim
  have hdim3 : (Fintype.card (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) : ℝ) ≤
      Real.exp (3 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    apply (mul_le_mul hdim hdim2 (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨hdim2.trans (Real.exp_le_exp.mpr htwo),
    hdim3.trans (Real.exp_le_exp.mpr hthree), ?_⟩
  intro a b
  obtain ⟨F⟩ := (hdiag W).expansion a.2 ((a.1, b.1), (b.2.1, b.2.2))
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star ((W.eval a.1 (fun _ => x 1) * W.eval b.1 (correlationInput (x 1) (x 0))) *
        (W.eval b.2.1 (correlationInput (x 0) (x 1)) * W.eval b.2.2 (fun _ => x 0))))) =
      (fun x => W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple b x)) := by
    funext x
    simp only [quadraticDiagonalDerivative, quadraticMixedTriple, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def cyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

noncomputable def wrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def diagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem wrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.wrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [wrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem diagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.diagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [diagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem wrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.wrappedDiagonalDerivative N a x =
      ∑ k, W.diagonalWrapCoefficient N a.2 k x * W.quadraticDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [diagonalWrapCoefficient, quadraticDiagonalDerivative]
      ring

theorem cyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.cyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cyclicDiagonalDerivative, wrappedDiagonalDerivative]
    rw [hval, ite_eq_left hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cyclicDiagonalDerivative, quadraticDiagonalDerivative]
    rw [hval, ite_eq_right hcut, sub_zero]

theorem exists_diagonalWrapCoefficient_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (W.diagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_integer_translation_equivalence_budget 1
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have htop : W.multi.realSubgroup (mixedCorrelationDegree 1) =
      W.model.filtration.realification.subgroup 2 := by
    have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
    simpa only [hsum] using W.multi.realSubgroup_top
  let V : W.model.UnitVerticalObservable (W.model.filtration.realification.subgroup 2)
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (htop.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (htop.symm ▸ hz) hL }
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model V (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hdim
    0 (fun _ => -(N : ℤ))
  let A : Fin 2 → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := E.expansion k j
  have H := F.linearPullbackHom A
  have heval (i : Fin W.outputDim) (x : Fin 2 → ℤ) (c : ℤ) :
      V.observable i (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
        (fun _ : Fin 2 => 1) ((fun l => A l x) + fun _ => c) (W.multi.orbitToOrdinary W.orbit))) =
      W.eval i (fun _ => x 1 + x 0 + c) := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have heq : (W.diagonalWrapCoefficient N j k) =
      (fun x => V.observable k (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
          (fun _ : Fin 2 => 1) ((fun l => A l x) + 0) (W.multi.orbitToOrdinary W.orbit))) *
        star (V.observable j (QuotientGroup.mk (W.model.filtration.realification.polynomialOrbitEval
          (fun _ : Fin 2 => 1) ((fun l => A l x) + fun _ => -(N : ℤ))
          (W.multi.orbitToOrdinary W.orbit))))) := by
    funext x
    rw [show (0 : Fin 2 → ℤ) = (fun _ => 0) from rfl, heval, heval]
    simp only [diagonalWrapCoefficient, add_zero, sub_eq_add_neg]
  exact ⟨heq.symm ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

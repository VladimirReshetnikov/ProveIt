import OAI.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem additiveTriple_coefficients_mem (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (a : τ →₀ ℕ) :
    coefficients q a ∈ F.additiveTripleSubalgebra i hi c hc := by
  by_cases ha : a = 0
  · rw [ha, hq0]
    exact (F.additiveTripleSubalgebra i hi c hc).zero_mem
  · have hpos : 0 < Finsupp.weight w a :=
      NilpotentLieFiltration.positive_weight_of_ne_zero w hw ha
    exact F.additiveTripleLayer_antitone i c (Nat.succ_le_of_lt hpos) (hq a)

noncomputable def restrictAdditiveTriplePolynomial (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    VectorPolynomial τ ℚ (F.additiveTripleSubalgebra i hi c hc) :=
  restrictCoefficients (F.additiveTripleSubalgebra i hi c hc).toSubmodule q
    (F.additiveTriple_coefficients_mem i hi c hc w hw q hq hq0)

theorem restrictAdditiveTriplePolynomial_adapted (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.additiveTripleFiltration i hi c hc).Adapted w
      (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) := by
  apply ((F.additiveTripleFiltration i hi c hc).adapted_iff_coefficients w _).mpr
  intro a
  change (coefficients (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) a : L × L × L) ∈
    F.additiveTripleLayer i c (Finsupp.weight w a)
  rw [restrictAdditiveTriplePolynomial, coefficients_restrictCoefficients]
  exact hq a

theorem restrictAdditiveTriplePolynomial_eval (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℚ) :
    (eval (V := F.additiveTripleSubalgebra i hi c hc) x
      (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0) : L × L × L) = eval x q :=
  eval_restrictCoefficients (F.additiveTripleSubalgebra i hi c hc).toSubmodule q
    (F.additiveTriple_coefficients_mem i hi c hc w hw q hq hq0) x

noncomputable def restrictAdditiveTripleOrbit (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) : (F.additiveTripleFiltration i hi c hc).PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F.restrictAdditiveTriplePolynomial i hi c hc w hw q hq hq0)
    (F.restrictAdditiveTriplePolynomial_adapted i hi c hc w hw q hq hq0)

theorem restrictAdditiveTripleOrbit_eval (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℤ) :
    (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w x
      (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0)).coord : L × L × L) =
      eval (fun j => (x j : ℚ)) q :=
  F.restrictAdditiveTriplePolynomial_eval i hi c hc w hw q hq hq0 _

theorem restrictAdditiveTripleOrbit_zero (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0
      (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0
    (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0)).coord : L × L × L) = 0
  rw [F.restrictAdditiveTripleOrbit_eval]
  simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hq0

theorem exists_additiveTripleOrbit_of_coefficients (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    ∃ g : (F.additiveTripleFiltration i hi c hc).PolynomialOrbit w,
      (F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : τ → ℤ,
        (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w x g).coord : L × L × L) =
          eval (fun j => (x j : ℚ)) q :=
  ⟨F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0,
    F.restrictAdditiveTripleOrbit_zero i hi c hc w hw q hq hq0,
    F.restrictAdditiveTripleOrbit_eval i hi c hc w hw q hq hq0⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI

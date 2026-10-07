import OAI.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) :
    VectorPolynomial σ ℚ (L × L) := pair (weightedDilation w q p) p

@[simp] theorem coefficients_dilationPair (w : σ → ℕ) (q : ℚ)
    (p : VectorPolynomial σ ℚ L) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a =
      (q ^ Finsupp.weight w a • coefficients p a, coefficients p a) := by
  simp only [dilationPair, coefficients_pair, coefficients_weightedDilation]

theorem eval_dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (dilationPair w q p) = (eval (fun i => q ^ w i * x i) p, eval x p) := by
  simp only [dilationPair, eval_pair, eval_weightedDilation]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients (w : σ → ℕ) (q : ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a ∈ F.dilationPairLayer q (Finsupp.weight w a) := by
  rw [coefficients_dilationPair, F.mem_dilationPairLayer]
  have ha := (F.adapted_iff_coefficients w p).mp hp a
  exact ⟨(F.layer _).smul_mem _ ha, ha, by simp⟩

theorem exists_dilationPair_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i) (q : ℚ)
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) (hp0 : coefficients p 0 = 0) :
    ∃ g : (F.dilationPairFiltration q).PolynomialOrbit w,
      (F.dilationPairFiltration q).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairFiltration q).polynomialOrbitEval w x g).coord : L × L) =
          (eval (fun i => q ^ w i * (x i : ℚ)) p, eval (fun i => (x i : ℚ)) p) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_dilationPairOrbit_of_coefficients q w hw (dilationPair w q p)
    (F.dilationPair_coefficients w q hp) (by simp only [coefficients_dilationPair, hp0, smul_zero]; rfl)
  exact ⟨g, hg0, fun x => (hg x).trans (eval_dilationPair w q p _)⟩

theorem exists_integer_dilationPair_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i) (q : ℤ)
    (p : F.PolynomialOrbit w) (hp0 : F.polynomialOrbitEval w 0 p = 1) :
    ∃ g : (F.dilationPairFiltration (q : ℚ)).PolynomialOrbit w,
      (F.dilationPairFiltration (q : ℚ)).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairFiltration (q : ℚ)).polynomialOrbitEval w x g).coord : L × L) =
          ((F.polynomialOrbitEval w (fun i => q ^ w i * x i) p).coord,
            (F.polynomialOrbitEval w x p).coord) := by
  have hz : coefficients p.log 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  obtain ⟨g, hg0, hg⟩ := F.exists_dilationPair_orbit w hw (q : ℚ) p.log p.adapted hz
  exact ⟨g, hg0, fun x => by
    simpa only [F.polynomialOrbitEval_coord, Int.cast_mul, Int.cast_pow] using hg x⟩

end NilpotentLieFiltration

end Erdos3

end

end OAI

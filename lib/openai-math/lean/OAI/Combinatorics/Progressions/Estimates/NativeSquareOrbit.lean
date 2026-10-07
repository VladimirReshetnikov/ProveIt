import OAI.Combinatorics.Progressions.Polynomial.NativePolynomialOrbit
import OAI.Combinatorics.Progressions.Polynomial.RealSquarePolynomialFactors

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

theorem nativeSquareOrbit_fst (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        F.realification.polynomialOrbitEval w x
          (F.nativePolynomialOrbit w (F.realSquareFstPolynomialHom w r)) := by
  apply NilpotentLieBCHGroup.ext
  have h := congrArg (eval (fun i => (x i : ℚ))) (F.realSquareFstPolynomialHom_polynomial w r)
  rw [eval_map] at h
  exact h.symm

theorem nativeSquareOrbit_snd (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (x : σ → ℤ) :
    F.realSquareSndHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        F.realification.polynomialOrbitEval w x
          (F.nativePolynomialOrbit w (F.realSquareSndPolynomialHom w r)) := by
  apply NilpotentLieBCHGroup.ext
  have h := congrArg (eval (fun i => (x i : ℚ))) (F.realSquareSndPolynomialHom_polynomial w r)
  rw [eval_map] at h
  exact h.symm

theorem nativeNormalizedSquareOrbit_fst (h : σ → ℤ) (ε γ : F.realification.Group)
    (g : F.RealAdaptedPolynomialGroup w) (r : F.squareFiltration.RealAdaptedPolynomialGroup w)
    (hf : F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      normalizedShiftLog s (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
        (F.realAdaptedPolynomialMap w g.coord)) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.squareFiltration.nativePolynomialOrbit w r)) =
        ε⁻¹ * F.realification.polynomialOrbitEval w (fun i => x i + h i)
          (F.nativePolynomialOrbit w g) * γ⁻¹ := by
  rw [F.nativeSquareOrbit_fst, mul_assoc]
  apply NilpotentLieBCHGroup.ext
  have hh := congrArg (eval (fun i => (x i : ℚ))) hf
  rw [eval_normalizedShiftLog] at hh
  change eval (fun i => (x i : ℚ))
      (F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord) =
    lieBCH s (-ε.coord)
      (lieBCH s (eval (fun i => ((x i + h i : ℤ) : ℚ))
        (F.realAdaptedPolynomialMap w g.coord)) (-γ.coord))
  simpa only [Int.cast_add] using hh

theorem nativeNormalizedSquareObservable_product (Γ : Subgroup F.Group)
    (h : σ → ℤ) (ε γ : F.realification.Group)
    (hγ : γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom)
    (u : F.realification.Group ⧸ Γ.map NilpotentLieBCHGroup.realificationHom → ℂ)
    (g : F.RealAdaptedPolynomialGroup w) (r : F.squareFiltration.RealAdaptedPolynomialGroup w)
    (hf : F.realAdaptedPolynomialMap w (F.realSquareFstPolynomialHom w r).coord =
      normalizedShiftLog s (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
        (F.realAdaptedPolynomialMap w g.coord))
    (hs : F.realSquareSndPolynomialHom w r = g) (x : σ → ℤ) :
    F.realSquareObservable Γ ε u
      (QuotientGroup.mk (F.squareFiltration.realification.polynomialOrbitEval w x
        (F.squareFiltration.nativePolynomialOrbit w r))) =
      u (QuotientGroup.mk (F.realification.polynomialOrbitEval w (fun i => x i + h i)
        (F.nativePolynomialOrbit w g))) *
      star (u (QuotientGroup.mk (F.realification.polynomialOrbitEval w x
        (F.nativePolynomialOrbit w g)))) := by
  apply F.realSquareObservable_recovers_product Γ ε γ _ _ hγ u
  · exact F.nativeNormalizedSquareOrbit_fst w h ε γ g r hf x
  · rw [F.nativeSquareOrbit_snd, hs]

end Erdos3.NilpotentLieFiltration

end

end OAI

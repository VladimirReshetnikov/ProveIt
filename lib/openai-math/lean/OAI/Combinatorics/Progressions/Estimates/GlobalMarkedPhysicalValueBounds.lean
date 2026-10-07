import OAI.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

open Module VectorPolynomial
open scoped Classical TensorProduct

attribute [local irreducible] fullTaggedSlowProjectionChart weightedAdaptedRealChartHom
  realChartSubstitute

variable {m s : ℕ} {X ι L : Type*} [Fintype X] [LieRing L] [LieAlgebra ℚ L]
    {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
    (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (A : GlobalMarkedNativeFactors F b ω hF (fullTaggedVariableWeight J) W g E R)

variable (U : ∀ j, Submodule ℝ (J j → ℝ))
    (Q : ∀ j, Matrix (J j) (J j) ℚ)
    (hQ : ∀ j y, y ∈ U j → fullTaggedRealMatrixProjection J Q j y = y)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j) (c : ∀ j, U j)
    (p budget : ℝ) (a Ce : ℕ) (hp : 0 ≤ p)
    (hcharts : ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
      (Fintype.card τ : ℝ) ≤ p →
      ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
        (hγ : ∀ i, γ i ∈ weightedSupportLE v (fullTaggedVariableWeight J i))
        (T : τ → ℝ), (∀ i, 0 < T i) →
      ∀ mass : ℝ, 1 ≤ mass →
        (∀ i, realPolynomialMass (scaleMvPolynomialAxes T
          (MvPolynomial.aeval γ
            (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J Q)
              (fun i => (N i : ℝ)) poly (fun j => (c j).val) i))) ≤ mass) →
        (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
          Real.exp budget * mass ^ s ≤ Real.exp ((p + 2) ^ a)) →
        F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
          (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) v γ hγ A.left))
    {H d : ℝ} (hheight : ∀ j i k, rationalLogHeight (Q j i k) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (hbudget : ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
      Real.exp budget * (max 1 (d * Real.exp H)) ^ s ≤ Real.exp ((p + 2) ^ a))

include hQ hm hp hcharts hheight hdim hbudget

theorem left_physical_value_bound (x : X → ℤ) (hx : x ∈ integerBox N) (i : ι) :
    |(b.baseChange ℝ).repr
      (F.adaptedPolynomialRealValueHom (fullTaggedVariableWeight J)
        (fun z => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x z : ℝ))
        A.left).coord i| ≤ Real.exp ((p + Ce) ^ Ce) := by
  apply F.value_bound_of_terminal_chart_control b (fullTaggedVariableWeight J)
    (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J Q)
      (fun i => (N i : ℝ)) poly (fun j => (c j).val))
    p budget a Ce hp A.left hcharts _ (max 1 (d * Real.exp H)) (le_max_left _ _)
    (fun z => fullTaggedSlowProjectionChart_physical_abs_le_rational
      J U Q hQ N poly hm c x hx hheight hdim z) hbudget i

theorem left_physical_orbit_value_bound (x : X → ℤ) (hx : x ∈ integerBox N) (i : ι) :
    |(b.baseChange ℝ).repr
      (F.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x)
        ((F.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm
          A.left)).coord i| ≤ Real.exp ((p + Ce) ^ Ce) := by
  rw [← F.realification.polynomialOrbitRealEval_integer,
    F.nativeFrozenMarkedOrbitCoordinates_symm_realEval]
  exact A.left_physical_value_bound J U Q hQ N poly hm c p budget a Ce hp
    hcharts hheight hdim hbudget x hx i

omit hQ hm hp hcharts hheight hdim hbudget in

theorem right_physical_orbit_value_grid [Fintype ι] (q : ℕ)
    (hgrid : F.PolynomialRationalGrid b (fullTaggedVariableWeight J) q A.right)
    (x : X → ℤ) :
    (b.baseChange ℝ).equivFun
      (F.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x)
        ((F.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm
          A.right)).coord ∈ realDenominatorGrid q := by
  rw [← F.realification.polynomialOrbitRealEval_integer,
    F.nativeFrozenMarkedOrbitCoordinates_symm_realEval]
  exact F.polynomialRationalGrid_value b (fullTaggedVariableWeight J) q A.right hgrid _

end Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

end

end OAI

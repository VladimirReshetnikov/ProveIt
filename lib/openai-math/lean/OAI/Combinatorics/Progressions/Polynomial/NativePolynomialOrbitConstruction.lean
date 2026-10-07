import OAI.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
import OAI.Combinatorics.Progressions.Lattices.LatticeNormalizedRefiltering

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

structure NativePolynomialOrbitFactors {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (eta : L →ₗ[ℚ] ℚ) (A : σ → ℝ) (p : ℝ) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  adapted : ∀ k, D.filtration.layer k = Submodule.span ℚ (basis '' {i | k ≤ weight i})
  basis_height : ∀ i j, rationalLogHeight (D.basis.repr (basis i) j) ≤ p
  subalgebra : LieSubalgebra ℚ D.filtration.AssociatedGraded
  generator : Fin (finrank ℚ L) → D.filtration.AssociatedGraded
  spanning : Submodule.span ℚ (Set.range generator) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule (D.filtration.associatedGradedBasis basis weight adapted)
    weight subalgebra.toSubmodule
  generator_height : ∀ i j, rationalLogHeight
    ((D.filtration.associatedGradedBasis basis weight adapted).repr (generator i) j) ≤ p
  kills_top : ∀ z ∈ D.filtration.realGradedRefiltrationLayer subalgebra s,
    realifyFunctional eta z = 0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  latticeConstant : D.RealGroup
  latticeConstant_mem : latticeConstant ∈ D.realLattice
  slow : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  rational : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group
  product : slow * middle * rational *
    D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) latticeConstant = g
  slow_bound : ∀ α i, |(basis.baseChange ℝ).repr
    (coefficients (slow.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
      Real.exp p / monomialScale A α
  rational_grid : (fun z : (σ →₀ ℕ) × Fin (finrank ℚ L) => (basis.baseChange ℝ).repr
    (coefficients (rational.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
      realDenominatorGrid denominator
  middle_zero : coefficients (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
  rational_zero : coefficients (rational.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
  middle_coefficients : ∀ α, coefficients
    (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
      D.filtration.realGradedRefiltrationLayer subalgebra (Finsupp.weight (fun _ => 1) α)

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p q : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

noncomputable def mono (hpq : p ≤ q) (hA : ∀ i, 0 < A i) :
    NativePolynomialOrbitFactors D g eta A q :=
  { R with
    basis_height := fun i j => (R.basis_height i j).trans hpq
    generator_height := fun i j => (R.generator_height i j).trans hpq
    denominator_bound := R.denominator_bound.trans (Real.exp_le_exp.mpr hpq)
    slow_bound := fun α i => (R.slow_bound α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (monomialScale_pos A hA α).le) }

theorem middle_values (t : σ → ℝ) :
    eval₂ t (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra R.subalgebra) := by
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra R.subalgebra)).toSubmodule
    (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).mpr
  exact D.filtration.normalized_refiltration_coefficients_mem_first
    (fun _ : σ => 1) R.subalgebra (fun _ => Nat.zero_lt_one) R.middle.coord
    R.middle_coefficients R.middle_zero

theorem middle_top_frequency (α : σ →₀ ℕ) (hα : Finsupp.weight (fun _ => 1) α = s) :
    realifyFunctional eta (coefficients (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) = 0 := by
  apply R.kills_top
  simpa only [hα] using R.middle_coefficients α

theorem middle_bracket_frequency (α β : σ →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β = s) :
    realifyFunctional eta
      ⁅coefficients (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α,
        coefficients (R.middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) β⁆ = 0 := by
  apply R.kills_top
  simpa only [hαβ] using D.filtration.realGradedRefiltrationLayer_lie_mem R.subalgebra
    (R.middle_coefficients α) (R.middle_coefficients β)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem eval_niltest (T : D.Niltest (fun _ : σ => 1))
    (hT : g = ⟨⟨T.orbit.log, T.orbit.property⟩⟩) (x : σ → ℤ) :
    T.eval x = T.observable (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.slow *
        D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.middle *
        D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.rational)) :=
  Niltest.eval_of_lattice_factorization D (fun _ : σ => 1) T R.slow R.middle R.rational
    R.latticeConstant R.latticeConstant_mem (R.product.trans hT) x

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_native_polynomial_orbit_factors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ k, D.filtration.layer k = Submodule.span ℚ (b '' {i | k ≤ w i}))
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ (g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (eta : L →ₗ[ℚ] ℚ) (A : σ → ℝ),
      (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      D.filtration.ControlledSymbolFactorization b w hF eta A
        (D.filtration.realPolynomialSymbolHom b w hF (fun _ => 1) g) p →
      Nonempty (NativePolynomialOrbitFactors D g eta A ((p + C) ^ C)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_lattice_normalized_refiltered_factorization s
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 4) ^ 11 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d _ _ _ D b w hF p hp hD hσ hb g eta A hA hfactor
  let r := (p + 4) ^ 11 + p + 2
  have hgeom : 0 ≤ (p + 4) ^ 11 := by positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have h2r : 2 ≤ r := by dsimp [r]; linarith
  have hgr : (p + 4) ^ 11 ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hfinal : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  have hApos (i : σ) : 0 < A i := (Real.exp_pos _).trans_le (hA i)
  obtain ⟨m₀, hm₀, hin, hout, hE⟩ := D.exists_prescribed_adapted_model
    b w hF hp hD (fun i j => (hb i j).trans (by linarith))
  let E := D.filtration.ofAdaptedBasis b w hF D.lattice m₀ hm₀ hin hout
  have hfactor' : ∀ _j : Unit,
      E.filtration.ControlledSymbolFactorization E.basis w hF eta A
        (E.filtration.realPolynomialSymbolHom E.basis w hF (fun _ => 1) g) r := by
    intro _
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration b w hF hfactor hpr hApos
  obtain ⟨U, v, m, κ, slow, middle, rat, hv, hU, hheight, hfreq, hm, hmp, hκ,
      hproduct, hslow, hrat, hmid0, hrat0, hcoeff, _hvalues⟩ :=
    hnormalize E w hF (fun _ : Unit => eta) r hr (hE.mono E hgr)
      (hσ.trans hpr) (by norm_num; linarith) A
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hA i)) g hfactor'
  exact ⟨{
    basis := b
    weight := w
    adapted := hF
    basis_height := fun i j => (hb i j).trans hpC
    subalgebra := U
    generator := v
    spanning := hv
    graded := hU
    generator_height := fun i j => (hheight i j).trans hfinal
    kills_top := hfreq ()
    denominator := m
    denominator_pos := hm
    denominator_bound := hmp.trans (Real.exp_le_exp.mpr hfinal)
    latticeConstant := κ
    latticeConstant_mem := hκ
    slow := slow
    middle := middle
    rational := rat
    product := hproduct
    slow_bound := fun α i => (hslow α i).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hfinal) (monomialScale_pos A hApos α).le)
    rational_grid := hrat
    middle_zero := hmid0
    rational_zero := hrat0
    middle_coefficients := hcoeff }⟩

end Erdos3

end

end OAI

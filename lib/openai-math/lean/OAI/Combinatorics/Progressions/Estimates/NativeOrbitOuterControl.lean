import OAI.Combinatorics.Progressions.Geometry.SymbolRepresentativeTransport
import OAI.Combinatorics.Progressions.Polynomial.NativePolynomialOrbitConstruction
import OAI.Combinatorics.Progressions.Polynomial.PolynomialBasisTransport
import OAI.Combinatorics.Progressions.Polynomial.PolynomialGridValues

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

theorem exists_native_orbit_coefficient_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (∀ i, 0 < A i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) m R.rational ∧
        D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
          (Real.exp ((p + C) ^ C)) R.slow := by
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2) ^ 3 + X + (X + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ s d D g eta A p R hp hD hA
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hdimD : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hD.1
  let m := matrixDenominator (fun i j => D.basis.repr (R.basis j) i) * R.denominator
  have hmb : (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + p) :=
    NilpotentLieFiltration.original_coordinate_denominator_bound R.basis D.basis hp hdim hdimD
      R.basis_height R.denominator R.denominator_bound
  have hcost : (p + 2) ^ 3 + p + (p + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hden : (p + 2) ^ 3 + p ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (sq_nonneg _)).trans hcost
  have hslow : (p + 3) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hcost
  have hs := D.filtration.polynomialSlowBound_change_basis_exp R.basis D.basis
    (fun _ : σ => 1) A hA hp hdim R.basis_height R.slow R.slow_bound
  exact ⟨m, Nat.mul_pos (matrixDenominator_pos _) R.denominator_pos,
    hmb.trans (Real.exp_le_exp.mpr hden),
    D.filtration.polynomialRationalGrid_change_basis R.basis D.basis
      (fun _ : σ => 1) R.denominator R.rational R.rational_grid,
    D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
      (Real.exp_le_exp.mpr hslow) R.slow hs⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

namespace NativePolynomialOrbitFactors

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
  {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
  (R : NativePolynomialOrbitFactors D g eta A p)

noncomputable def slowValue (x : σ → ℤ) : D.RealGroup :=
  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.slow

noncomputable def rationalValue (x : σ → ℤ) : D.RealGroup :=
  D.filtration.adaptedPolynomialRealValueHom (fun _ : σ => 1) (fun i => (x i : ℝ)) R.rational

def HasOuterValueControl (b : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp b ∧
    (∀ x : σ → ℤ, (D.basis.baseChange ℝ).equivFun (R.rationalValue x).coord ∈
      realDenominatorGrid m) ∧
    ∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ A i) → ∀ i,
      |(D.basis.baseChange ℝ).repr (R.slowValue x).coord i| ≤ Real.exp b

theorem hasOuterValueControl_mono {a b : ℝ} (h : R.HasOuterValueControl a) (hab : a ≤ b) :
    R.HasOuterValueControl b := by
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := h
  exact ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hab), hrat,
    fun x hx i => (hslow x hx i).trans (Real.exp_le_exp.mpr hab)⟩

end NativePolynomialOrbitFactors

theorem exists_native_orbit_outer_control (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (∀ i, 0 < A i) → Fintype.card σ ≤ k →
      R.HasOuterValueControl ((p + C) ^ C) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  let K := (s + 1) * (k + 1) ^ s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C K)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D g eta A p R hp hD hA hk
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := hcoeff R hp hD hA
  have htotal : (p + a) ^ a + (K : ℝ) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (Nat.cast_nonneg K)).trans htotal
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hcost), ?_, ?_⟩
  · intro x
    exact D.filtration.polynomialRationalGrid_value D.basis (fun _ : σ => 1) m R.rational hrat x
  · intro x hx i
    have hs := D.filtration.polynomialSlowBound_value D.basis (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) A hA (Real.exp_nonneg _) R.slow hslow
      (fun j => (x j : ℝ)) hx i
    have hcard : (Fintype.card σ : ℝ) ≤ k := by exact_mod_cast hk
    have hK : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s ≤ K := by
      dsimp [K]
      push_cast
      gcongr
    have hKexp : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    apply hs.trans
    calc
      _ ≤ (K : ℝ) * Real.exp ((p + a) ^ a) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
      _ ≤ Real.exp K * Real.exp ((p + a) ^ a) :=
        mul_le_mul_of_nonneg_right hKexp (Real.exp_nonneg _)
      _ = Real.exp ((K : ℝ) + (p + a) ^ a) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI

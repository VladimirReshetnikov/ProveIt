import OAI.Combinatorics.Progressions.Estimates.RefilteredReconstructionDiagram
import OAI.Combinatorics.Progressions.Lattices.RetainedLatticeNormalization

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

def HasNativeLowerDegreeOrbit {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) : Prop :=
  ∃ (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
    (qbar : (F.gradedRefiltration W).quotientTop.realification.PolynomialOrbit w),
    VectorPolynomial.map
      (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      q.log = p ∧ coefficients q.log 0 = 0 ∧ DegreeLE w s qbar.log ∧
    ∀ x, (F.gradedRefiltration W).quotientTop.realification.polynomialOrbitEval w x qbar =
      (F.gradedRefiltration W).realQuotientStepHom
        ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl
        ((F.gradedRefiltration W).realification.polynomialOrbitEval w x q)

theorem hasNativeLowerDegreeOrbit_of_coefficients {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) : F.HasNativeLowerDegreeOrbit W w p := by
  apply F.exists_native_refiltered_quotient_orbits W w hw p hp hzero

end NilpotentLieFiltration

theorem exists_retained_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨C, hC, hnormalize⟩ := exists_retained_lattice_normalization (s + 1)
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF U v n p hp hD hσ hJ hv hU hheight hn hnp A hA g hfactor
  obtain ⟨v₀, m, κ, E, b, R, hv₀, hW, hvheight, hm, hmp, hnm, hκ, hprod,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hnormalize D w hF U v n p hp hD hσ hJ hv hU hheight hn hnp A hA g hfactor
  refine ⟨v₀, m, κ, E, b, R, hv₀, hW, hvheight, hm, hmp, hnm, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, hvalues, ?_⟩
  apply D.filtration.hasNativeLowerDegreeOrbit_of_coefficients (⨅ j, U j) (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) b.coord hcoeff hb0

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_affine_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n den : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, 0 < den j) →
      (∀ j, ((n j * den j ^ (s + 1) : ℕ) : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (shift : σ → ℚ)
        (oldScale : J → ℚ) (oldShift offset : J → σ → ℚ)
        (a : J → ℤ) (oldSides : J → σ → ℝ) (oldBudget loss : J → ℝ),
      (∀ j, a j ≠ 0) →
      (∀ j, oldScale j * ((a j : ℚ) / den j) = r) →
      (∀ j i, oldScale j * offset j i + oldShift j i = shift i) →
      (∀ j i, 0 < oldSides j i) → (∀ j, 0 ≤ loss j) →
      (∀ j i, Real.exp (-loss j) * (|(((a j : ℚ) / den j : ℚ) : ℝ)| * A i) ≤ oldSides j i) →
      (∀ j, oldBudget j + ((s + 1 : ℕ) : ℝ) * loss j ≤ p) →
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF (oldSides j)
        ((T.scalarAffinePullback (oldScale j) (oldShift j)).symbol D.basis w hF)
        (oldBudget j) (n j) (U j)) →
      let current := T.scalarAffinePullback r shift
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨current.orbit.log, current.orbit.property⟩⟩
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j * den j ^ (s + 1) ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨C, hC, hnormalize⟩ := exists_retained_lower_degree_factorization s
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ _ D w hF U v n den p hp hD hσ hJ hv hU hheight
    hn hden hnp A hA T r shift oldScale oldShift offset a oldSides oldBudget loss
    ha hr hshift hSides hloss hphysical hbudget hold current g
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  have hfactor : ∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g)
      p (n j * den j ^ (s + 1)) (U j) := by
    intro j
    change D.filtration.SymbolFactorizationIn D.basis w hF A
      ((T.scalarAffinePullback r shift).symbol D.basis w hF) p (n j * den j ^ (s + 1)) (U j)
    have htransport := T.scalarAffinePullback_transition_factorization D.basis w hF
      (oldScale j) r (oldShift j) shift (offset j) (hold j) (a j) (den j)
      (ha j) (hden j) (hr j) (hshift j) (hSides j) hApos (hloss j) (hphysical j)
    exact htransport.mono D.filtration D.basis w hF (hbudget j) hApos
  exact hnormalize D w hF U v (fun j => n j * den j ^ (s + 1)) p hp hD hσ hJ hv hU hheight
    (fun j => Nat.mul_pos (hn j) (pow_pos (hden j) _)) hnp A hA g hfactor

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_physical_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n aux oldModulus : J → ℕ)
      (M : ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, 0 < aux j) → (∀ j, 0 < oldModulus j) → 0 < M →
      (∀ j, oldModulus j ∣ M) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      (∀ j, (aux j : ℝ) ≤ Real.exp p) →
      ∀ W A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ (T : D.Niltest (fun _ : σ => 1)) (shift : σ → ℚ)
        (oldShift : J → σ → ℚ) (oldSides : J → σ → ℝ),
      (∀ j i, 0 < oldSides j i) → (∀ i, (M : ℝ) * A i ≤ W i) →
      (∀ j i, Real.exp (-p) * W i ≤ ((oldModulus j : ℝ) * aux j) * oldSides j i) →
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF (oldSides j)
        ((T.scalarAffinePullback ((oldModulus j : ℚ) * aux j) (oldShift j)).symbol D.basis w hF)
        p (n j) (U j)) →
      let current := T.scalarAffinePullback (M : ℚ) shift
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨current.orbit.log, current.orbit.property⟩⟩
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j * aux j ^ (s + 1) ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_retained_lower_degree_factorization s
  let Q : Polynomial ℕ := (Polynomial.C (s + 2) * Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ _ D w hF U v n aux oldModulus M p hp hD hσ hJ
    hv hU hheight hn haux hOld hM hdiv hnp hauxp W A hA T shift oldShift oldSides
    hSides hcurrent hphysical hold current g
  let P : ℝ := (s + 2 : ℕ) * p
  have hpP : p ≤ P := by
    dsimp only [P]
    have hs : (1 : ℝ) ≤ (s + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ s + 2)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hp
  have hP : 0 ≤ P := hp.trans hpP
  have hcost : (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  have hfactor : ∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g)
      P (n j * aux j ^ (s + 1)) (U j) := by
    intro j
    change D.filtration.SymbolFactorizationIn D.basis w hF A
      ((T.scalarAffinePullback (M : ℚ) shift).symbol D.basis w hF) P _ _
    have ht := T.scalarAffinePullback_residue_factorization D.basis w hF
      (hOld j) hM (haux j) (hdiv j) (oldShift j) shift (hold j) (hSides j) hApos hp
      (hphysical j) hcurrent
    have hbound : p + ((s + 1 : ℕ) : ℝ) * p ≤ P := by
      apply le_of_eq
      dsimp only [P]
      push_cast
      ring
    exact ht.mono D.filtration D.basis w hF hbound hApos
  have hden : ∀ j, ((n j * aux j ^ (s + 1) : ℕ) : ℝ) ≤ Real.exp P := by
    intro j
    have he : (((s + 1 : ℕ) : ℝ) + 1) * p = P := by
      dsimp only [P]
      push_cast
      ring
    simpa only [he] using residueTransition_denominator_bound (hnp j) (hauxp j) (s + 1)
  obtain ⟨v₀, m, κ, E, b, R, hv₀, hgraded, hvheight, hm, hmp, hnm, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, hvalues, hlower⟩ :=
    hnormalize D w hF U v (fun j => n j * aux j ^ (s + 1)) P hP (hD.mono D hpP)
      (hσ.trans hpP) (hJ.trans hpP) hv hU (fun j i k => (hheight j i k).trans hpP)
      (fun j => Nat.mul_pos (hn j) (pow_pos (haux j) _)) hden A
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hA i)) g hfactor
  refine ⟨v₀, m, κ, E, b, R, hv₀, hgraded, fun i k => (hvheight i k).trans hcost,
    hm, hmp.trans (Real.exp_le_exp.mpr hcost), hnm, hκ, hprod, ?_, hR, hb0, hR0, hcoeff, hvalues, hlower⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
    (monomialScale_pos A hApos α).le)

end Erdos3

end

end OAI

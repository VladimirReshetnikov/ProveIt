import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_niltest_family_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (T0 : D.Niltest (fun _ : σ => 1)) (T : J → D.Niltest (fun _ : σ => 1))
      (_hOrbit : ∀ j, (T j).orbit = T0.orbit) (eta : J → L →ₗ[ℚ] ℚ)
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (∀ j, (T j).ComplexityLE p) →
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ p) →
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (T j).observable (z • x) =
          CircleFourier.character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (T j).observable x) →
      ∀ (origin : J → σ → ℤ) (lengths : J → σ → ℕ),
      (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (T j).eval x‖) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      (∀ j i, Real.exp (-p) * A i ≤ lengths j i) →
      ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
        (T0.symbol D.basis w hF) ((p + C) ^ C) := by
  obtain ⟨c, hc, hstep⟩ := exists_translated_step_drop s hs
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c +
    Polynomial.C s * Polynomial.X + Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ _ D w hF T0 T hOrbit eta p hp hσ hT hη hvert
    origin lengths hlengths hbias A hA hrelative j
  have hbound : (p + c) ^ c + s * p + p ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hsp : 0 ≤ (s : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hlength (i : σ) : Real.exp ((p + c) ^ c) ≤ (lengths j i : ℝ) := by
    calc
      _ = Real.exp (-p) * Real.exp ((p + c) ^ c + p) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * A i := mul_le_mul_of_nonneg_left
        ((Real.exp_le_exp.mpr (by linarith : (p + c) ^ c + p ≤ (p + C) ^ C)).trans (hA i))
        (Real.exp_nonneg _)
      _ ≤ _ := hrelative j i
  have hsingle := hstep D w hF p hp hσ (T j) (hT j) (eta j) (hη j) (hvert j)
    (origin j) (lengths j) (hlengths j) hlength (hbias j)
  have hsymbol : (T j).symbol D.basis w hF = T0.symbol D.basis w hF := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun q : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => q.log)
      (hOrbit j)
  rw [hsymbol] at hsingle
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  have hrescaled := ControlledSymbolFactorization.rescale D.filtration D.basis w hF hsingle
    (fun i => by exact_mod_cast hlengths j i) hApos hp (hrelative j)
  exact ControlledSymbolFactorization.mono D.filtration D.basis w hF hrescaled (by linarith) hApos

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_lattice_normalized_niltest_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (T0 : D.Niltest (fun _ : σ => 1)) (T : J → D.Niltest (fun _ : σ => 1))
      (_hOrbit : ∀ j, (T j).orbit = T0.orbit) (eta : J → L →ₗ[ℚ] ℚ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, (T j).ComplexityLE p) →
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ p) →
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (T j).observable (z • x) =
          CircleFourier.character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (T j).observable x) →
      ∀ (origin : J → σ → ℤ) (lengths : J → σ → ℕ), (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (T j).eval x‖) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      (∀ j i, Real.exp (-p) * A i ≤ lengths j i) →
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨T0.orbit.log, T0.orbit.property⟩⟩
      ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤
          (p + C) ^ C) ∧
        (∀ j x, x ∈ D.filtration.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, hc, hfamily⟩ := exists_niltest_family_step_drop s hs
  obtain ⟨k, _, hnormalize⟩ := exists_lattice_normalized_refiltered_factorization s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let P : Polynomial ℕ := Q + (Q + Polynomial.C k) ^ k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ _ d _ _ _ _ D w hF T0 T hOrbit eta p hp hD hσ hJ hT hη hvert
    origin lengths hlengths hbias A hA hrelative
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hc1 : 1 ≤ c := by omega
    have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
    have hpbase : 1 ≤ p + c := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg c)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hpbase hc1)
  have hbound : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hk0 : 0 ≤ (q + k) ^ k := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hkC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨T0.orbit.log, T0.orbit.property⟩⟩
  have hfactor : ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) q :=
    hfamily D w hF T0 T hOrbit eta p hp hσ hT hη hvert origin lengths hlengths hbias A
      (fun i => (Real.exp_le_exp.mpr hqC).trans (hA i)) hrelative
  obtain ⟨W, v, m, κ, E, b, R, hv, hW, hheight, hfreq, hm, hmp, hκ, hebr,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hnormalize D w hF eta q hq (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
      (hσ.trans hpq) (hJ.trans hpq) A
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hA i)) g hfactor
  refine ⟨W, v, m, κ, E, b, R, hv, hW, (fun i j => (hheight i j).trans hkC), hfreq,
    hm, hmp.trans (Real.exp_le_exp.mpr hkC), hκ, hebr, ?_, hR, hb0, hR0, hcoeff, hvalues⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hkC)
    (monomialScale_pos A (fun i => (Real.exp_pos _).trans_le (hA i)) α).le)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_simultaneous_niltest_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (T0 : D.Niltest (fun _ : σ => 1)) (T : J → D.Niltest (fun _ : σ => 1))
      (_hOrbit : ∀ j, (T j).orbit = T0.orbit) (eta : J → L →ₗ[ℚ] ℚ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, (T j).ComplexityLE p) →
      (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ p) →
      (∀ j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        (T j).observable (z • x) =
          CircleFourier.character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
            (T j).observable x) →
      ∀ (origin : J → σ → ℤ) (lengths : J → σ → ℕ), (∀ j i, 0 < lengths j i) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (T j).eval x‖) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      (∀ j i, Real.exp (-p) * A i ≤ lengths j i) →
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨T0.orbit.log, T0.orbit.property⟩⟩
      ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : Fin d → D.filtration.AssociatedGraded) (m : ℕ)
        (e₀ p₀ r₀ : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤
          (p + C) ^ C) ∧
        (∀ j x, x ∈ D.filtration.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ e₀ * p₀ * r₀ = g ∧
        (∀ t : σ → ℝ, eval₂ t (D.filtration.realGradedSymbolPolynomial D.basis w hF (fun _ => 1)
          (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) p₀).coord) ∈ realificationLieSubalgebra W) ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
          coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 ∧
        (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
            realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, hc, hfamily⟩ := exists_niltest_family_step_drop s hs
  obtain ⟨k, _, hcommon⟩ := exists_common_refiltered_factorization s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let H : Polynomial ℕ := ((Q + 2) ^ 2 + 2) ^ 63 + 1
  let P : Polynomial ℕ := (Q + 2) ^ k + H + Q
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ _ d _ _ _ _ D w hF T0 T hOrbit eta p hp hD hσ hJ hT hη hvert
    origin lengths hlengths hbias A hA hrelative
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hc1 : 1 ≤ c := by omega
    have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
    have hpbase : 1 ≤ p + c := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg c)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hpbase hc1)
  have hbound : (q + 2) ^ k + (((q + 2) ^ 2 + 2) ^ 63 + 1) + q ≤ (p + C) ^ C := by
    simpa [P, H, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hf0 : 0 ≤ (q + 2) ^ k := by positivity
  have hi0 : 0 ≤ ((q + 2) ^ 2 + 2) ^ 63 + 1 := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hfC : (q + 2) ^ k ≤ (p + C) ^ C := by linarith
  have hiC : ((q + 2) ^ 2 + 2) ^ 63 + 1 ≤ (p + C) ^ C := by linarith
  let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨T0.orbit.log, T0.orbit.property⟩⟩
  have hfactor : ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) q :=
    hfamily D w hF T0 T hOrbit eta p hp hσ hT hη hvert origin lengths hlengths hbias A
      (fun i => (Real.exp_le_exp.mpr hqC).trans (hA i)) hrelative
  have hresult :=
    hcommon D.filtration D.basis w hF eta q hq
      (by simpa only [Fintype.card_fin] using hD.1.trans hpq) (hσ.trans hpq) (hJ.trans hpq)
      (fun i j l => (hD.2.2.1 i j l).trans hpq) A
      (fun i => (Real.exp_le_exp.mpr hfC).trans (hA i)) g hfactor
  obtain ⟨W, v, m, e₀, p₀, r₀, hv, hW, hheight, hfreq, hm, hmp, hepr,
      hmid, he, hr, he0, hr0, hp0, hvalues⟩ := hresult
  let e := Fintype.equivFin (Fin d)
  have hrange : Set.range (fun i => v (e i)) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i
      exact ⟨j, congrArg v hj⟩
  have hv' : Submodule.span ℚ (Set.range (fun i => v (e i))) = W.toSubmodule := by
    rw [hrange]
    exact hv
  refine ⟨W, (fun i => v (e i)), m, e₀, p₀, r₀, hv', hW, ?_, hfreq, hm,
    hmp.trans (Real.exp_le_exp.mpr hfC), hepr, hmid, ?_, hr, he0, hr0, hp0, hvalues⟩
  · intro i j
    exact (hheight (e i) j).trans hiC
  · intro α i
    exact (he α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hfC)
      (monomialScale_pos A (fun i => (Real.exp_pos _).trans_le (hA i)) α).le)

end Erdos3

end

end OAI

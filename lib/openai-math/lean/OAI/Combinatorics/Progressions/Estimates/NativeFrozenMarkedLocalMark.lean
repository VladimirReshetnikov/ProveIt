import OAI.Combinatorics.Progressions.Estimates.FrozenMarkedLeftOrbitBound
import OAI.Combinatorics.Progressions.Polynomial.PrescribedFastPolynomialFactorization
import OAI.Combinatorics.Progressions.Sampling.NativeMarkedDiagramScoreLift

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]

theorem sectionCorrectedPolynomial_map (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (hS : Function.RightInverse S φ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) :
    map ((φ.baseChange ℝ).restrictScalars ℚ) (sectionCorrectedPolynomial φ S p q) = q := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, sectionCorrectedPolynomial_coefficients]
  change φ.baseChange ℝ (coefficients p a -
    S.baseChange ℝ (φ.baseChange ℝ (coefficients p a) - coefficients q a)) = _
  rw [map_sub, linearMap_baseChange_rightInverse φ S hS]
  abel

namespace NilpotentLieFiltration

variable {ι κ : Type*} {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (τ : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ)

theorem real_projected_discrepancy_mem_shifted
    (p : F.realification.adaptedLieSubalgebra w)
    (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
      (F.realPolynomialSymbolMap b ω hF w p) = G.realPolynomialSymbolMap c τ hG w q) :
    F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w p - q ∈
        G.realification.shiftedAdaptedIdeal w := by
  let r : G.realification.adaptedLieSubalgebra w :=
    F.realification.filteredPolynomialMap G.realification
      (realLieHomToRat (realificationLieHom φ))
      (F.realificationLieHom_mem_layer G φ hφ) w p
  have he : G.realSymbolOfPolynomial c τ hG w r.val =
      G.realSymbolOfPolynomial c τ hG w q.val := by
    calc
      _ = G.realSymbolOfPolynomial c τ hG w
        (map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) p.val) :=
        congrArg (G.realSymbolOfPolynomial c τ hG w)
          (F.realification.filteredPolynomialMap_coe G.realification
            (realLieHomToRat (realificationLieHom φ))
            (F.realificationLieHom_mem_layer G φ hφ) w p)
      _ = (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) :=
        (F.realFilteredPolynomialSymbolMap_polynomial G φ hφ b ω hF c τ hG w p).symm
      _ = _ := hcompat
  have h := (G.realSymbolOfPolynomial_eq_iff_symbolMap_eq c τ hG w r q).mp he
  exact (G.realification.polynomialSymbolMap_eq_iff w r q).mp h

theorem sectionCorrectedPolynomial_prescribed_symbol
    (S : M →ₗ[ℚ] L) (hS : Function.RightInverse S φ)
    (hSlayer : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (x : F.RealPolynomialSymbol w) (q : G.realification.adaptedLieSubalgebra w)
    (hcompat : (F.filteredPolynomialSymbolMap G φ hφ w).toLinearMap.baseChange ℝ x =
      G.realPolynomialSymbolMap c τ hG w q) :
    ∃ p : F.realification.adaptedLieSubalgebra w,
      p.val = sectionCorrectedPolynomial φ.toLinearMap S
        (F.realSymbolRepresentative b ω hF w x) q.val ∧
      F.realPolynomialSymbolMap b ω hF w p = x ∧
      F.realification.filteredPolynomialMap G.realification
        (realLieHomToRat (realificationLieHom φ))
        (F.realificationLieHom_mem_layer G φ hφ) w p = q := by
  let p₀ : F.realification.adaptedLieSubalgebra w :=
    F.realAdaptedSymbolRepresentative b ω hF w x
  have hp₀ : F.realPolynomialSymbolMap b ω hF w p₀ = x := by
    dsimp only [p₀]
    exact F.realPolynomialSymbolMap_representative b ω hF w x
  let φR : (ℝ ⊗[ℚ] L) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] M) := realLieHomToRat (realificationLieHom φ)
  let hφR := F.realificationLieHom_mem_layer G φ hφ
  let δ : G.realification.adaptedLieSubalgebra w :=
    F.realification.filteredPolynomialMap G.realification φR hφR w p₀ - q
  have hδ : δ ∈ G.realification.shiftedAdaptedIdeal w := by
    apply F.real_projected_discrepancy_mem_shifted G φ hφ b ω hF c τ hG w p₀ q
    rw [hp₀]
    exact hcompat
  have hd (a : σ →₀ ℕ) :
      coefficients (map ((S.baseChange ℝ).restrictScalars ℚ) δ.val) a ∈
        F.realification.layer (Finsupp.weight w a + 1) := by
    rw [coefficients_map]
    exact baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w a + 1))
      (F.layer (Finsupp.weight w a + 1)) S (hSlayer _) (hδ a)
  let d : F.realification.adaptedLieSubalgebra w :=
    ⟨map ((S.baseChange ℝ).restrictScalars ℚ) δ.val,
      fun a => F.realification.antitone (Nat.le_succ _) (hd a)⟩
  have hdz : F.realPolynomialSymbolMap b ω hF w d = 0 := by
    apply (F.realPolynomialSymbolMap_eq_zero_iff b ω hF w d).mpr
    exact (F.realification.polynomialSymbolMap_eq_zero_iff w d).mpr hd
  refine ⟨p₀ - d, rfl, ?_, ?_⟩
  · rw [map_sub, hdz, sub_zero]
    exact hp₀
  · apply Subtype.ext
    exact sectionCorrectedPolynomial_map φ.toLinearMap S hS
      (F.realSymbolRepresentative b ω hF w x) q.val

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)

theorem exists_filtered_linear_section
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (φ : L →ₗ[ℚ] M)
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) :
    ∃ S : M →ₗ[ℚ] L, Function.RightInverse S φ ∧
      ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j := by
  classical
  have hmem (k : κ) : c k ∈ G.layer (v k) := by
    rw [hG]
    exact Submodule.subset_span ⟨k, (show v k ≤ v k from le_rfl), rfl⟩
  choose x hx hφx using fun k => hsurj (v k) (c k) (hmem k)
  let S := c.constr ℚ x
  have hS (k : κ) : S (c k) = x k := c.constr_basis ℚ x k
  refine ⟨S, ?_, ?_⟩
  · have heq : φ.comp S = LinearMap.id := by
      apply c.ext
      intro k
      change φ (S (c k)) = c k
      rw [hS, hφx]
    intro y
    exact congrArg (fun f : M →ₗ[ℚ] M => f y) heq
  · intro j y hy
    have hle : G.layer j ≤ (F.layer j).comap S := by
      rw [hG]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change S (c k) ∈ F.layer j
      rw [hS]
      exact F.antitone hk (hx k)
    exact hle hy

theorem exists_formal_marked_orbit_restoration
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    (w : σ → ℕ) (g : F.realification.PolynomialOrbit w)
    (q : G.realification.PolynomialOrbit w) :
    ∃ restored : F.realification.PolynomialOrbit w,
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w z restored) =
            G.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := F.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z q →
        F.realification.polynomialOrbitRealEval w z restored =
          F.realification.polynomialOrbitRealEval w z g := by
  obtain ⟨S, hS, hSlayer⟩ := F.exists_filtered_linear_section G c v hG φ.toLinearMap hsurj
  let P := sectionCorrectedPolynomial φ.toLinearMap S g.log q.log
  have hP : F.realification.Adapted w P := by
    apply (F.realification.adapted_iff_coefficients w P).mpr
    intro a
    rw [show P = sectionCorrectedPolynomial φ.toLinearMap S g.log q.log from rfl,
      sectionCorrectedPolynomial_coefficients]
    apply Submodule.sub_mem
    · exact (F.realification.adapted_iff_coefficients w g.log).mp g.adapted a
    · apply baseChange_mem_of_mapsTo (G.layer (Finsupp.weight w a))
        (F.layer (Finsupp.weight w a)) S (hSlayer _)
      apply Submodule.sub_mem
      · exact F.realificationLieHom_mem_layer G φ hφ _ _
          ((F.realification.adapted_iff_coefficients w g.log).mp g.adapted a)
      · exact (G.realification.adapted_iff_coefficients w q.log).mp q.adapted a
  let restored := polynomialOrbitOfLog P hP
  have hm : map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.log = q.log :=
    sectionCorrectedPolynomial_map φ.toLinearMap S hS g.log q.log
  refine ⟨restored, hm, ?_, ?_⟩
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ z P) = eval₂ z q.log
    rw [← hm]
    exact (eval₂_map (realificationLieHom φ).toLinearMap z P).symm
  · intro z hz
    have hc := congrArg NilpotentLieBCHGroup.coord hz
    change φ.toLinearMap.baseChange ℝ (eval₂ z g.log) = eval₂ z q.log at hc
    apply NilpotentLieBCHGroup.ext
    change eval₂ z P = eval₂ z g.log
    dsimp only [P, sectionCorrectedPolynomial]
    rw [map_sub, eval₂_map, map_sub, eval₂_map, hc, sub_self, map_zero, sub_zero]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem externalCandidate_stepZero_coord_eq_zero (F : NilpotentLieFiltration L 0)
    (x : L) : x = 0 := by
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [F.terminal, Submodule.mem_bot] using hx

theorem externalCandidate_stepZero_group_eq_one (F : NilpotentLieFiltration L 0)
    (g : F.Group) : g = 1 := by
  apply NilpotentLieBCHGroup.ext
  exact F.externalCandidate_stepZero_coord_eq_zero g.coord

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

variable {L M σ τ X Ω : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d : ℕ}
    (D : RationalFilteredNilmanifold L 0 d)
    (G : NilpotentLieFiltration M 0)

theorem exists_step_zero_external_marked_candidate
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ) (v : τ → ℕ)
    (mark : G.realification.PolynomialOrbit w)
    (observable : X → D.Space → ℂ)
    (localOrbit : Ω → D.filtration.realification.PolynomialOrbit v) :
    ∃ ambient : D.filtration.realification.PolynomialOrbit w,
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) ambient.log = mark.log ∧
      ∀ (a : Ω) (x : X) (u : σ → ℝ) (z : τ → ℝ),
        observable x (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitRealEval w u ambient)) =
        observable x (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitRealEval v z (localOrbit a))) := by
  refine ⟨1, ?_, ?_⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    exact (G.realification.externalCandidate_stepZero_coord_eq_zero _).trans
      (G.realification.externalCandidate_stepZero_coord_eq_zero _).symm
  · intro a x u z
    exact congrArg (fun g : D.RealGroup => observable x (QuotientGroup.mk g))
      ((D.filtration.realification.externalCandidate_stepZero_group_eq_one _).trans
        (D.filtration.realification.externalCandidate_stepZero_group_eq_one _).symm)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n t : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s n)
    (hEF : E.filtration = D.filtration.gradedRefiltration W)

noncomputable def includedRefilteredOrbit (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) :
    D.filtration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog
    (map ((realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap.restrictScalars ℚ) g.log)
    (E.filtration.realification.adapted_map D.filtration.realification _
      (E.filtration.realificationLieHom_mem_layer D.filtration
        (D.filtration.gradedRefiltrationSubalgebra W).incl (by
          intro j x hx
          apply D.filtration.gradedRefiltrationLayer_le W j
          exact (D.filtration.mem_gradedRefiltration_layer W j x).mp (hEF ▸ hx))) w g.adapted)

@[simp] theorem includedRefilteredOrbit_log (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) :
    (D.includedRefilteredOrbit W E hEF w g).log =
      map ((realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap.restrictScalars ℚ) g.log := rfl

theorem includedRefilteredOrbit_realEval (w : σ → ℕ)
    (g : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    D.filtration.realification.polynomialOrbitRealEval w x
        (D.includedRefilteredOrbit W E hEF w g) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (E.filtration.realification.polynomialOrbitRealEval w x g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom
    (D.filtration.gradedRefiltrationSubalgebra W).incl).toLinearMap x g.log

noncomputable def externalCandidateOrbit (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) :
    D.filtration.realification.PolynomialOrbit w :=
  left * D.includedRefilteredOrbit W E hEF w middle * right

theorem externalCandidateOrbit_realEval (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    D.filtration.realification.polynomialOrbitRealEval w x
        (D.externalCandidateOrbit W E hEF w left right middle) =
      D.filtration.realification.polynomialOrbitRealEval w x left *
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (E.filtration.realification.polynomialOrbitRealEval w x middle) *
      D.filtration.realification.polynomialOrbitRealEval w x right := by
  simp only [externalCandidateOrbit, map_mul, includedRefilteredOrbit_realEval]

theorem externalCandidateOrbit_mark_realEval
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (w : σ → ℕ) (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w) (x : σ → ℝ) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitRealEval w x
        (D.externalCandidateOrbit W E hEF w left right middle)) =
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitRealEval w x left) *
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (E.filtration.realification.polynomialOrbitRealEval w x middle)) *
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitRealEval w x right) := by
  rw [externalCandidateOrbit_realEval, map_mul, map_mul]

theorem exists_restored_external_candidate_of_frozen_score [Fintype J]
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (w : σ → ℕ) (left right : D.filtration.realification.PolynomialOrbit w)
    (middle : E.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (H : Finset Ω) (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ)
    (leftAt rightAt : X → D.RealGroup)
    (hleft : ∀ a ∈ H, ∀ j,
      D.filtration.realification.polynomialOrbitEval w (point a j) left = leftAt (physical a j))
    (hright : ∀ a ∈ H, ∀ j,
      D.filtration.realification.polynomialOrbitEval w (point a j) right = rightAt (physical a j))
    (hmark : ∀ a ∈ H, ∀ j,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ
        (leftAt (physical a j) *
          realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (E.filtration.realification.polynomialOrbitEval w (point a j) middle) *
          rightAt (physical a j)) =
        G.realification.polynomialOrbitEval w (point a j) marked)
    (observable : X → D.Space → ℂ) (weight : X → ℂ) {δ : ℝ}
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      observable (physical a j) (QuotientGroup.mk
        (leftAt (physical a j) *
          realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (E.filtration.realification.polynomialOrbitEval w (point a j) middle) *
          rightAt (physical a j))))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
      (∀ x : σ → ℝ, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w x restored) =
          G.realification.polynomialOrbitRealEval w x marked) ∧
      (∀ x : σ → ℝ, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w x
          (D.externalCandidateOrbit W E hEF w left right middle)) =
            G.realification.polynomialOrbitRealEval w x marked →
        D.filtration.realification.polynomialOrbitRealEval w x restored =
          D.filtration.realification.polynomialOrbitRealEval w x
            (D.externalCandidateOrbit W E hEF w left right middle)) ∧
      (∀ a ∈ H, ∀ j,
        D.filtration.realification.polynomialOrbitEval w (point a j) restored =
          leftAt (physical a j) *
            realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
              (hM := D.filtration.lowerCentralSeries_eq_bot)
              (D.filtration.gradedRefiltrationSubalgebra W).incl
              (E.filtration.realification.polynomialOrbitEval w (point a j) middle) *
            rightAt (physical a j)) ∧
      ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
        observable (physical a j) (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval w (point a j) restored)))).re := by
  let candidate := D.externalCandidateOrbit W E hEF w left right middle
  obtain ⟨restored, hm, hglobal, hkeep⟩ :=
    D.filtration.exists_formal_marked_orbit_restoration G φ hφ c v hG hsurj w candidate marked
  have heval (a : Ω) (ha : a ∈ H) (j : J) :
      D.filtration.realification.polynomialOrbitEval w (point a j) candidate =
        leftAt (physical a j) *
          realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (E.filtration.realification.polynomialOrbitEval w (point a j) middle) *
          rightAt (physical a j) := by
    simpa only [polynomialOrbitRealEval_integer, hleft a ha j, hright a ha j] using
      D.externalCandidateOrbit_realEval W E hEF w left right middle (fun i => (point a j i : ℝ))
  have hretained (a : Ω) (ha : a ∈ H) (j : J) :
      D.filtration.realification.polynomialOrbitEval w (point a j) restored =
        leftAt (physical a j) *
          realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (E.filtration.realification.polynomialOrbitEval w (point a j) middle) *
          rightAt (physical a j) := by
    have hk := hkeep (fun i => (point a j i : ℝ)) (by
      simpa only [polynomialOrbitRealEval_integer, heval a ha j] using hmark a ha j)
    simpa only [polynomialOrbitRealEval_integer, heval a ha j] using hk
  refine ⟨restored, hm, hglobal, hkeep, hretained, ?_⟩
  intro a ha
  simpa only [hretained a ha] using hscore a ha

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem formal_mark_realEval
    {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (g : F.realification.PolynomialOrbit w) (marked : G.realification.PolynomialOrbit w)
    (hm : map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log)
    (x : σ → ℝ) :
    realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ (F.realification.polynomialOrbitRealEval w x g) =
      G.realification.polynomialOrbitRealEval w x marked := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom φ (eval₂ x g.log) = eval₂ x marked.log
  rw [← hm]
  exact (eval₂_map (realificationLieHom φ).toLinearMap x g.log).symm

theorem formal_mark_of_realEval
    {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (g : F.realification.PolynomialOrbit w) (marked : G.realification.PolynomialOrbit w)
    (hm : ∀ x : σ → ℝ, realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ (F.realification.polynomialOrbitRealEval w x g) =
      G.realification.polynomialOrbitRealEval w x marked) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  calc
    _ = realificationLieHom φ (eval₂ x g.log) :=
      eval₂_map (realificationLieHom φ).toLinearMap x _
    _ = _ := congrArg NilpotentLieBCHGroup.coord (hm x)

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ ι κ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
    (hE : E.filtration = D.filtration.gradedRefiltration W)

variable (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hEF : EF.filtration = Fmark.filtration.gradedRefiltration (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hφ

attribute [local irreducible] NilpotentLieFiltration.associatedGradedMap
  NilpotentLieFiltration.gradedRefiltrationMap
  includedRefilteredOrbit externalCandidateOrbit

theorem refiltered_mark_realification_commutes (z : E.RealGroup) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl z) =
    realificationMap (hnil := EF.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
      (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := EF.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) z) := by
  have hc : φ.toLinearMap.comp (D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap =
      (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl.toLinearMap.comp ((D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)).toLinearMap := by
    ext x
    exact (D.filtration.gradedRefiltrationMap_apply Fmark.filtration φ hφ W x).symm
  have he := congrArg (fun g => g.baseChange ℝ) hc
  apply NilpotentLieBCHGroup.ext
  change φ.toLinearMap.baseChange ℝ
      ((D.filtration.gradedRefiltrationSubalgebra W).incl.toLinearMap.baseChange ℝ z.coord) =
    (Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl.toLinearMap.baseChange ℝ
      (((D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)).toLinearMap.baseChange ℝ z.coord)
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using
    congrArg (fun g => g z.coord) he

theorem externalCandidateOrbit_marked_realEval (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (leftMarked rightMarked : Fmark.filtration.realification.PolynomialOrbit w)
    (hleft : map (realLieHomToRat (realificationLieHom φ)).toLinearMap left.log = leftMarked.log)
    (hright : map (realLieHomToRat (realificationLieHom φ)).toLinearMap right.log = rightMarked.log)
    (middle : E.filtration.realification.PolynomialOrbit w)
    (markedMiddle : EF.filtration.realification.PolynomialOrbit w)
    (hmiddle : map (realLieHomToRat (realificationLieHom (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W))).toLinearMap middle.log = markedMiddle.log) (x : σ → ℝ) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitRealEval w x
        (D.externalCandidateOrbit W E hE w left right middle)) =
      Fmark.filtration.realification.polynomialOrbitRealEval w x
        (Fmark.externalCandidateOrbit
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) EF hEF
          w leftMarked rightMarked markedMiddle) := by
  have hl := D.filtration.formal_mark_realEval Fmark.filtration φ w left leftMarked hleft x
  have hr := D.filtration.formal_mark_realEval Fmark.filtration φ w right rightMarked hright x
  have hm := E.filtration.formal_mark_realEval EF.filtration
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) w middle markedMiddle hmiddle x
  rw [D.externalCandidateOrbit_realEval, Fmark.externalCandidateOrbit_realEval]
  simp only [map_mul, hl, hr,
    D.refiltered_mark_realification_commutes Fmark φ hφ W E EF, hm]

theorem externalCandidateOrbit_formal_mark (w : σ → ℕ)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (leftMarked rightMarked : Fmark.filtration.realification.PolynomialOrbit w)
    (hleft : map (realLieHomToRat (realificationLieHom φ)).toLinearMap left.log = leftMarked.log)
    (hright : map (realLieHomToRat (realificationLieHom φ)).toLinearMap right.log = rightMarked.log)
    (middle : E.filtration.realification.PolynomialOrbit w)
    (markedMiddle : EF.filtration.realification.PolynomialOrbit w)
    (hmiddle : map (realLieHomToRat (realificationLieHom (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W))).toLinearMap middle.log = markedMiddle.log) :
    map (realLieHomToRat (realificationLieHom φ)).toLinearMap
        (D.externalCandidateOrbit W E hE w left right middle).log =
      (Fmark.externalCandidateOrbit (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) EF hEF w leftMarked rightMarked markedMiddle).log := by
  apply D.filtration.formal_mark_of_realEval Fmark.filtration φ w
  intro x
  exact D.externalCandidateOrbit_marked_realEval Fmark φ hφ W E hE EF hEF
    w left right leftMarked rightMarked hleft hright middle markedMiddle hmiddle x

theorem exists_ambient_restored_candidate_of_marked_quotient_score [Fintype J]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {nQ nQF : ℕ}
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = E.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸ EF.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = EF.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace EF.Space]
    (w : σ → ℕ) (q : Q.filtration.realification.PolynomialOrbit w)
    (markedMiddle : EF.filtration.realification.PolynomialOrbit w)
    (hcompat : E.topQuotientMarkedOrbit EF (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W E hE EF hEF) Q hQ QF hQF q =
      EF.topQuotientOrbit QF hQF markedMiddle)
    (left right : D.filtration.realification.PolynomialOrbit w)
    (leftMarked rightMarked desiredMark : Fmark.filtration.realification.PolynomialOrbit w)
    (hleftMark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap left.log = leftMarked.log)
    (hrightMark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap right.log = rightMarked.log)
    (H : Finset Ω) (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ)
    (leftAt rightAt : X → D.RealGroup)
    (hleft : ∀ a ∈ H, ∀ j,
      D.filtration.realification.polynomialOrbitEval w (point a j) left = leftAt (physical a j))
    (hright : ∀ a ∈ H, ∀ j,
      D.filtration.realification.polynomialOrbitEval w (point a j) right = rightAt (physical a j))
    (hmarkAgree : ∀ a ∈ H, ∀ j,
      Fmark.filtration.realification.polynomialOrbitEval w (point a j)
        (Fmark.externalCandidateOrbit (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) EF hEF w leftMarked rightMarked markedMiddle) =
      Fmark.filtration.realification.polynomialOrbitEval w (point a j) desiredMark)
    (observable : X → D.Space → ℂ) (weight : X → ℂ) (K : ℝ≥0)
    (externalAt : X → EF.Space)
    (hexternal : ∀ a ∈ H, ∀ j, externalAt (physical a j) = QuotientGroup.mk
      (EF.filtration.realification.polynomialOrbitEval w (point a j) markedMiddle))
    (hrecovery : ∀ x source, positiveImageSlice (E.markedTopQuotientDiagram EF (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (fun z => observable x (QuotientGroup.mk (leftAt x *
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl z * rightAt x)))
      (E.markedTopQuotientDiagram EF (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (E.markedTopQuotientDiagram EF (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
      observable x (QuotientGroup.mk (leftAt x *
        realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl source * rightAt x)))
    {δ : ℝ}
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
      positiveImageSlice (E.markedTopQuotientDiagram EF (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
        (fun z => observable (physical a j) (QuotientGroup.mk (leftAt (physical a j) *
          realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl z * rightAt (physical a j))))
        (externalAt (physical a j)) (QuotientGroup.mk
          (Q.filtration.realification.polynomialOrbitEval w (point a j) q)))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit w,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = desiredMark.log ∧
      (∀ x : σ → ℝ, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w x restored) =
          Fmark.filtration.realification.polynomialOrbitRealEval w x desiredMark) ∧
      ∀ a ∈ H, δ ≤ ((localLaw a).complexMean (fun j => weight (physical a j) *
        observable (physical a j) (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitEval w (point a j) restored)))).re := by
  let frozen : X → E.RealGroup → ℂ := fun x z => observable x (QuotientGroup.mk
    (leftAt x * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl z * rightAt x))
  obtain ⟨middle, _, hmiddle, hmiddleScore⟩ :=
    E.exists_marked_diagram_external_score_lift EF (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W E hE EF hEF) Q hQ QF hQF
      K frozen hrecovery
      (D.refilteredMarkedMap_layer_surjective Fmark φ hφ W E hE EF hEF
        b ω hD c ν hF hW hsurj)
      q markedMiddle hcompat H localLaw physical point weight externalAt hexternal hscore
  have hformal := D.externalCandidateOrbit_formal_mark Fmark φ hφ W E hE EF hEF
    w left right leftMarked rightMarked hleftMark hrightMark middle markedMiddle hmiddle
  have hsiteMark : ∀ a ∈ H, ∀ j,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (leftAt (physical a j) *
          realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (E.filtration.realification.polynomialOrbitEval w (point a j) middle) *
          rightAt (physical a j)) =
        Fmark.filtration.realification.polynomialOrbitEval w (point a j) desiredMark := by
    intro a ha j
    have he := D.filtration.formal_mark_realEval Fmark.filtration φ w
      (D.externalCandidateOrbit W E hE w left right middle)
      (Fmark.externalCandidateOrbit (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) EF hEF w leftMarked rightMarked markedMiddle)
      hformal (fun i => (point a j i : ℝ))
    rw [D.externalCandidateOrbit_realEval] at he
    simpa only [polynomialOrbitRealEval_integer, hleft a ha j, hright a ha j,
      hmarkAgree a ha j] using he
  obtain ⟨restored, hm, hglobal, _, _, hscores⟩ :=
    D.exists_restored_external_candidate_of_frozen_score W E hE Fmark.filtration φ hφ
      c ν hF hsurj w left right middle desiredMark H localLaw physical point leftAt rightAt
      hleft hright hsiteMark observable weight hmiddleScore
  exact ⟨restored, hm, hglobal, hscores⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ η L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (S : M →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ G.layer j, S y ∈ F.layer j)
    (hsection : Function.RightInverse S φ)

include hsection

theorem frozenMarkedOuter_product_mark_eq
    (v : η → ℕ)
    (g E P R : (F.realification.adaptedPolynomialFiltration v).Group)
    (hfactor : E * P * R = g)
    (EF RF : (G.realification.adaptedPolynomialFiltration v).Group)
    (hE : F.realPolynomialGroupMap G φ hφ v E = EF)
    (hR : F.realPolynomialGroupMap G φ hφ v R = RF)
    (w : σ → ℕ) (leftMark rightMark : G.realification.PolynomialOrbit w)
    (kE kR : F.realification.Group)
    (hkE : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ kR = 1)
    (x : η → ℝ) (y : σ → ℝ)
    (hleft : G.adaptedPolynomialRealValueHom v x EF =
      G.realification.polynomialOrbitRealEval w y leftMark)
    (hright : G.adaptedPolynomialRealValueHom v x RF =
      G.realification.polynomialOrbitRealEval w y rightMark) :
    realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ
      (F.realification.polynomialOrbitRealEval w y
          (F.frozenMarkedLeftOrbit G w S hS leftMark kE) *
        F.adaptedPolynomialRealValueHom v x P *
        F.realification.polynomialOrbitRealEval w y
          (F.frozenMarkedRightOrbit G w S hS rightMark kR)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (F.adaptedPolynomialRealValueHom v x g) := by
  have hl := F.formal_mark_realEval G φ w
    (F.frozenMarkedLeftOrbit G w S hS leftMark kE) leftMark
    (F.frozenMarkedLeftOrbit_formal_mark G w S hS φ hφ hsection leftMark kE hkE) y
  have hr := F.formal_mark_realEval G φ w
    (F.frozenMarkedRightOrbit G w S hS rightMark kR) rightMark
    (F.frozenMarkedRightOrbit_formal_mark G w S hS φ hφ hsection rightMark kR hkR) y
  rw [← hfactor]
  simp only [map_mul, hl, hr]
  rw [← F.realPolynomialGroupMap_value G φ hφ v E x,
    ← F.realPolynomialGroupMap_value G φ hφ v R x, hE, hR, hleft, hright]

end Erdos3.NilpotentLieFiltration

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.FormalCurrentInputBounds
import OAI.Combinatorics.Progressions.Estimates.UniformControlledCurrentStage

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Matrix

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_bracket_polynomial_step
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (hgraded : BasisHomogeneousBrackets (b.baseChange ℝ) w)
    {d H J l : ℕ} (hd : 0 < d)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w d x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P Pd : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPU : ∀ α, coefficients P α ∈ U)
    (hPgraded : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPd : Pd = map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P)
    (hPdE : ∀ α, coefficients Pd α ∈ E.baseChange ℝ)
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hsmallhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients small α = 0)
    (hrationalhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients rational α = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (coefficients Pd α) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B P' : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realBracketSystem f k).restrictScalars ℚ) A = small ∧
      map ((realBracketSystem f k).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      P' = bchRemove s A P B ∧ lieBCH s (lieBCH s A P') B = P ∧
      coefficients P' 0 = coefficients P 0 ∧
      P' ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
      (∀ α, coefficients P' α ∈ U) ∧
      (∀ α t, ⁅coefficients (map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P') α,
        (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ) ∧
      ∀ r < d, map ((basisGradeProjection (b.baseChange ℝ) w r).restrictScalars ℚ) P' =
        map ((basisGradeProjection (b.baseChange ℝ) w r).restrictScalars ℚ) P := by
  obtain ⟨Q, hQ, hQzero⟩ := exists_subspace_coordinate_polynomial e Pd hPdE
  have hPd0 : coefficients Pd 0 = 0 := by
    rw [hPd]
    exact gradedPolynomialSubmodule_projection_homogeneous (b.baseChange ℝ) w (fun _ => 1)
      P hPgraded d 0 (by simpa using Nat.ne_of_lt hd)
  have hcoeff (α : σ →₀ ℕ) : bracketSystemLift e (coefficients Q α) = coefficients Pd α := by
    have h := congrArg (fun p => coefficients p α) hQ
    simpa only [coefficients_map, LinearMap.restrictScalars_apply] using h
  have hsmall0 : coefficients small 0 = 0 := hsmallhom 0 (by simpa using Nat.ne_of_lt hd)
  have hrational0 : coefficients rational 0 = 0 := hrationalhom 0 (by simpa using Nat.ne_of_lt hd)
  have h := exists_ambient_bracket_correction_polynomials b e f k hH hl hA he hp hrows hcols hHp hlp
    T hT Q small rational (hQzero 0 hPd0) hsmall0 hrational0 hsmall hrational
    (fun α => by rw [hcoeff]; exact heq α)
  obtain ⟨m, A, B, hm, hmp, hAQ, hBQ, hAB, hAzero, hBzero, hAnorm, hBgrid, hres⟩ := h
  have hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients A α = 0 :=
    fun α hα => hAzero α (hsmallhom α hα)
  have hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ d → coefficients B α = 0 :=
    fun α hα => hBzero α (hrationalhom α hα)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers (E.baseChange ℝ) d hE A P B
    (fun α => (hAB α).1) (fun α => (hAB α).2)
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    d A hAhom (fun α => hE _ (hAB α).1)
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    d B hBhom (fun α => hE _ (hAB α).2)
  refine ⟨m, A, B, bchRemove s A P B, hm, hmp, hAQ, hBQ, hAB, hAhom, hBhom, hAnorm, hBgrid,
    rfl, bchRemove_factorization F.realification.lowerCentralSeries_eq_bot A P B,
    bchRemove_constant F.realification.lowerCentralSeries_eq_bot A P B
      (hAzero 0 hsmall0) (hBzero 0 hrational0),
    bchRemove_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w hgraded (fun _ => 1) s A P B
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A P B (fun α => hEU _ (hAB α).1) hPU
      (fun α => hEU _ (hAB α).2), ?_, hgrades.2⟩
  intro α t
  rw [hgrades.1, ← hPd]
  simpa only [hQ] using hres α t

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_bracket_induction_step (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) =
      coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) =
      coefficients B.coord α)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hSR : PolynomialLiftSystem P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V)
    (hleft : ∀ t α, coefficients (S t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ t α, coefficients (R t - monomial 0 (k t) + ⁅B.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := fun t => dualAdjoint A⁻¹ (S t)
    let R' := fun t => dualAdjoint B (R t)
    A * P' * B = P ∧ (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ d < j - 1,
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
      (∀ d < j, ∀ t α,
        ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V) ∧
      PolynomialLiftSystem P' S' R' ∧
      ∀ t α,
        coefficients (S' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        coefficients (R' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅coefficients P'.coord α, k t⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' S' R'
  let Vq := V.restrictScalars ℚ
  let p := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ Vq ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hp : p ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [coefficients_map]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have ha : A.coord ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hb : B.coord ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [← hB α]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hkl (t : κ) : k t ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hstep : j - 1 + 2 = j + 1 := by omega
  have hrem (t : κ) (α : σ →₀ ℕ) :
      coefficients (⁅P.coord - p, monomial (R := ℚ) 0 (k t)⁆ :
        VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P.coord α) (k t) (hkl t) (fun d hd => hlower d hd t α)
    rw [hstep] at h
    simpa only [p, coefficients_lie_constant, map_sub, Finsupp.sub_apply, coefficients_map,
      LinearMap.restrictScalars_apply] using h
  have hnorm := F.realification.polynomialFiltration.current_layer_normalization hs
    (coefficientLieSubalgebra U) (coefficientSubmodule Vq)
    (fun X hX Y hY => coefficientSubmodule_invariant U Vq hUV X Y hX hY)
    hj P A B hPU hAU hBU ha hb S R (fun t => monomial 0 (k t)) p hp hSR
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq j _).mpr
      (fun α => (hW j _).mpr (hR t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hrem t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hleft t α)))
    (fun t => (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
      (fun α => (hW (j + 1) _).mpr (hright t α)))
  obtain ⟨hprod, hP'U, _, _, hS'R', hcurrent⟩ := hnorm
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w (j - 1) - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x := by
    intro x hx
    exact sub_eq_zero.mp hx
  have haE : ∀ α, coefficients A.coord α ∈ E := fun α => sub_eq_zero.mpr (hA α)
  have hbE : ∀ α, coefficients B.coord α ∈ E := fun α => sub_eq_zero.mpr (hB α)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers E (j - 1) hE A.coord P.coord B.coord haE hbE
  have hgrade : VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P'.coord =
      p - A.coord - B.coord := hgrades.1
  have hcur (t : κ) (α : σ →₀ ℕ) :
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P'.coord α), k t⁆ ∈ V := by
    apply F.real_mem_of_homogeneous_mem_sup_next b w hlayers V hV j
    · have h := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
        (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1}
          (coefficients P'.coord α)) (hk t)
      simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at h
      exact h
    · have h := (hW (j + 1) _).mp
        ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp
          (hcurrent t).2.2 α)
      rw [← hgrade, coefficients_lie_constant, coefficients_map] at h
      exact h
  have hall (d : ℕ) (hd : d < j) (t : κ) (α : σ →₀ ℕ) :
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V := by
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · have h := congrArg (fun Q => coefficients Q α) (hgrades.2 d hlt)
      simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
      have he : basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) =
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := h
      rw [he]
      exact hlower d hlt t α
    · exact hcur t α
  refine ⟨hprod, hP'U, hgrades.2, hall, hS'R', fun t α => ⟨?_, ?_, ?_⟩⟩
  · exact (hW (j + 1) _).mp
      ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp (hcurrent t).1 α)
  · exact (hW (j + 1) _).mp
      ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp (hcurrent t).2.1 α)
  · have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P'.coord α) (k t) (hkl t) (fun d hd => hall d (by omega) t α)
    rw [hstep] at h
    have ht := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem h
      (Submodule.mem_sup_left (hcur t α))
    simpa only [sub_lie, sub_add_cancel] using ht

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {μ ι κ σ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {V : Submodule ℚ L}

include hlayers in
theorem bracket_array_matching_remainder
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (j : ℕ)
    (X : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (A : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hX : ∀ t α, coefficients (X t) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hA : map ((realBracketSystem f k).restrictScalars ℚ) A =
      liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (X t))) :
    ∀ t α, coefficients (X t - ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈
      V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hmatch := bracket_system_matches_lift_array f k A _ hA
  intro t
  exact F.polynomial_lift_matching_remainder b w hlayers (V.baseChange ℝ) hV j
    (X t) _ (hX t) (hmatch t)

include hlayers in
theorem bracket_arrays_match_lifts
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) (j : ℕ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hR : ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hA : map ((realBracketSystem f k).restrictScalars ℚ) A =
      liftQuotientArray f (fun t => map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))
    (hB : map ((realBracketSystem f k).restrictScalars ℚ) B =
      liftQuotientArray f (fun t => map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) :
    (∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) -
      ⁅A, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
    ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) +
      ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  refine ⟨F.bracket_array_matching_remainder b w hlayers hV f k j _ A hS hA, ?_⟩
  have hneg : ∀ t α, coefficients (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule := by
    intro t α
    rw [map_neg, Finsupp.neg_apply]
    exact Submodule.neg_mem _ (hR t α)
  have hmatch := F.bracket_array_matching_remainder b w hlayers hV f k j _ B hneg hB
  intro t α
  have he : R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t) + ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆ =
      -(-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) - ⁅B, monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)⁆) := by abel
  rw [he, map_neg, Finsupp.neg_apply]
  exact Submodule.neg_mem _ (hmatch t α)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_bracket_equation (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j) (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hSR : PolynomialLiftSystem P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V) :
    ∀ t α, ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α) -
        basisGradeProjection (b.baseChange ℝ) w j (coefficients (R t) α)) ∈ V := by
  let Vq := V.restrictScalars ℚ
  let p := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  have hW (d : ℕ) (x : ℝ ⊗[ℚ] L) :
      x ∈ Vq ⊔ F.realification.layer d ↔ x ∈ V ⊔ (F.realLayer d).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer d).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hp : p ∈ F.realification.polynomialFiltration.layer (j - 1) := by
    intro α
    rw [coefficients_map]
    exact F.realGradeProjection_mem_layer b w hlayers (j - 1) _
  have hk1 (t : κ) : k t ∈ F.realification.layer 1 := by
    rw [F.realification.one_eq_top]
    trivial
  have hstep : j - 1 + 2 = j + 1 := by omega
  intro t α
  have hrem : (⁅P.coord - p, monomial (R := ℚ) 0 (k t)⁆ : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
      coefficientSubmodule Vq ⊔ F.realification.polynomialFiltration.layer (j + 1) := by
    apply (mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mpr
    intro β
    apply (hW (j + 1) _).mpr
    have h := F.real_current_bracket_remainder b w hlayers V (j - 1)
      (coefficients P.coord β) (k t) (hk1 t) (fun d hd => hlower d hd t β)
    rw [hstep] at h
    simpa only [p, coefficients_lie_constant, map_sub, Finsupp.sub_apply,
      coefficients_map, LinearMap.restrictScalars_apply] using h
  have hconst : monomial (R := ℚ) (0 : σ →₀ ℕ) (k t) ∈ F.realification.polynomialFiltration.layer 1 :=
    F.realification.monomial_mem_polynomialLayer 1 0 (hk1 t)
  have h := F.realification.polynomialFiltration.adjoint_current_layer_relation
    (coefficientLieSubalgebra U) (coefficientSubmodule Vq)
    (fun X hX Y hY => coefficientSubmodule_invariant U Vq hUV X Y hX hY)
    hs (by omega) P hPU (R t) (monomial 0 (k t)) p hp hconst
    ((mem_coefficient_sup_polynomialLayer F.realification Vq j _).mpr
      (fun β => (hW j _).mpr (hR t β))) hrem
  rw [← hSR t] at h
  have hc := (hW (j + 1) _).mp
    ((mem_coefficient_sup_polynomialLayer F.realification Vq (j + 1) _).mp h α)
  have hscalar : ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (coefficients (S t) α - coefficients (R t) α) ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    simpa only [p, map_sub, Finsupp.sub_apply, coefficients_lie_constant,
      coefficients_map, LinearMap.restrictScalars_apply] using hc
  have hhom : basisGradeProjection (b.baseChange ℝ) w j
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ =
      ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ := by
    have hh := (hgraded.baseChange b w).projection_lie (b.baseChange ℝ) w
      (basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1}
        (coefficients P.coord α)) (hk t)
    simp only [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hh
    exact hh
  have hproj := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j _ hscalar
  simpa only [map_sub, hhom] using hproj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_current_bracket_equation_mod (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j) (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V) :
    ∀ t α, ⁅basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α), k t⁆ -
      (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α) -
        basisGradeProjection (b.baseChange ℝ) w j (coefficients (R t) α)) ∈ V := by
  obtain ⟨S₀, hS₀, herror⟩ := PolynomialLiftSystemMod.exact_left (V.restrictScalars ℚ) P S R hSR
  have hcurrent := F.formal_current_bracket_equation b w hlayers hgraded hs U V hUV hV
    k hk hj P hPU S₀ R hS₀ hR hlower
  intro t α
  have he := hV j (coefficients (S t - S₀ t) α) (herror t α)
  simp only [map_sub, Finsupp.sub_apply] at he
  have h := V.sub_mem (hcurrent t α) he
  convert h using 1
  abel

include hlayers in
theorem formal_bracket_induction_step_mod (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (k : κ → ℝ ⊗[ℚ] L) (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 (k t) = k t)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), k t⁆ ∈ V)
    (hleft : ∀ t α, coefficients (S t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hright : ∀ t α, coefficients (R t - monomial 0 (k t) + ⁅B.coord, monomial 0 (k t)⁆) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := fun t => dualAdjoint A⁻¹ (S t)
    let R' := fun t => dualAdjoint B (R t)
    A * P' * B = P ∧ (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ d < j - 1,
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
      (∀ d < j, ∀ t α,
        ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), k t⁆ ∈ V) ∧
      PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      ∀ t α,
        coefficients (S' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        coefficients (R' t - monomial 0 (k t)) α ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule ∧
        ⁅coefficients P'.coord α, k t⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' S' R'
  obtain ⟨S₀, hS₀, herror⟩ := PolynomialLiftSystemMod.exact_left (V.restrictScalars ℚ) P S R hSR
  have hleft₀ (t : κ) (α : σ →₀ ℕ) :
      coefficients (S₀ t - monomial 0 (k t) - ⁅A.coord, monomial 0 (k t)⁆) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).sub_mem
      (hleft t α) (Submodule.mem_sup_left (herror t α))
    simp only [map_sub, Finsupp.sub_apply] at h ⊢
    convert h using 1
    abel
  have hstep := F.formal_bracket_induction_step b w hlayers hgraded hs U V hUV hV k hk hj
    P A B hPU hAU hBU hA hB S₀ R hS₀ hR hlower hleft₀ hright
  obtain ⟨hprod, hU, hbelow, hbracket, _, hnext⟩ := hstep
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hAU
  refine ⟨hprod, hU, hbelow, hbracket,
    PolynomialLiftSystemMod.remove U (V.restrictScalars ℚ) hUV P A B hAU S R hSR,
    fun t α => ⟨?_, (hnext t α).2.1, (hnext t α).2.2⟩⟩
  have he := dualAdjoint_mem_coefficientSubmodule U (V.restrictScalars ℚ) hUV A⁻¹
    (S t - S₀ t) hAi (herror t)
  have heq : dualAdjoint A⁻¹ (S t) - monomial 0 (k t) =
      dualAdjoint A⁻¹ (S t - S₀ t) + (dualAdjoint A⁻¹ (S₀ t) - monomial 0 (k t)) := by
    rw [dualAdjoint_sub]
    abel
  change coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ _
  rw [heq, map_add, Finsupp.add_apply]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (he α)) (hnext t α).1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_formal_bracket_step
    (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    {j H J Q l : ℕ} (hj : 2 ≤ j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p) (hcols : (Fintype.card ν : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) ≤ Real.exp p)
    (hMp : (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * M ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (hSgraded : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRgraded : ∀ t, R t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hS : ∀ t α, coefficients (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hR : ∀ t α, coefficients (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hlower : ∀ d < j - 1, ∀ t α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ)
    (hsmall : ∀ t α, ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ ≤ M / monomialScale T α)
    (hrational : ∀ t α, (b.baseChange ℝ).equivFun (coefficients (R t) α) ∈ realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun t => dualAdjoint A⁻¹ (S t)
      let R' := fun t => dualAdjoint B (R t)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ t α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        ∀ t α,
          coefficients (S' t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let π := (basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ
  let Pd := VectorPolynomial.map
    ((basisGradeProjection (b.baseChange ℝ) w (j - 1)).restrictScalars ℚ) P.coord
  let small := liftQuotientArray f (fun t => VectorPolynomial.map π (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))
  let rational := liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hcurrent := F.formal_current_bracket_equation_mod b w hlayers hgraded hs U (V.baseChange ℝ)
    hUV hV (fun t => (1 : ℝ) ⊗ₜ[ℚ] k t) hk hj P hPU S R hSR hR hlower
  have harr := bracket_array_equation_of_current_relation f k
    (basisGradeProjection (b.baseChange ℝ) w j) Pd S R (fun t α => by
      rw [coefficients_map]
      exact hcurrent t α)
  have hsmallhom := projected_lift_array_homogeneous b w f k hj hk S hSgraded
  have hrhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients rational α = 0 := by
    intro α hα
    change coefficients (liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α = 0
    rw [liftQuotientArray_map_neg, map_neg, Finsupp.neg_apply]
    rw [projected_lift_array_homogeneous b w f k hj hk R hRgraded α hα, neg_zero]
  have hsbound (α : σ →₀ ℕ) : ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α :=
    (projected_lift_array_bound b w f k hj hk hf T hTpos hM S hsmall α).trans
      (div_le_div_of_nonneg_right hMp (monomialScale_pos T hTpos α).le)
  have hrgrid (α : σ →₀ ℕ) : coefficients rational α ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
    change coefficients (liftQuotientArray f (fun t => VectorPolynomial.map π (-(R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t))))) α ∈ _
    rw [liftQuotientArray_map_neg, map_neg, Finsupp.neg_apply]
    exact realDenominatorGrid_neg _ (projected_lift_array_grid b w f k hj hk l R hrational α)
  have h := F.exists_controlled_bracket_polynomial_step b w hlayers U e f k (hgraded.baseChange b w)
    (by omega : 0 < j - 1) hE hEU hH (Nat.mul_pos (matrixDenominator_pos _) hl)
    hA he hp hrows hcols hHp hlp T hT P.coord Pd hPU hPgraded rfl
    (fun α => by rw [coefficients_map]; exact hPE α) small rational hsmallhom hrhom hsbound hrgrid harr
  obtain ⟨m, a, c, Pnew, hm, hmp, haQ, hcQ, hac, hahom, hchom, hanorm, hcgrid,
    hremove, _, hconstant, hnewgraded, _, _, _⟩ := h
  have hmatching := F.bracket_arrays_match_lifts b w hlayers hV f k j S R a c hS hR haQ hcQ
  have hstep := F.formal_bracket_induction_step_mod b w hlayers hgraded hs U (V.baseChange ℝ) hUV hV
    (fun t => (1 : ℝ) ⊗ₜ[ℚ] k t) hk hj P ⟨a⟩ ⟨c⟩ hPU
    (fun α => hEU _ (hac α).1) (fun α => hEU _ (hac α).2)
    (fun α => hE _ (hac α).1) (fun α => hE _ (hac α).2) S R hSR hR hlower hmatching.1 hmatching.2
  obtain ⟨hprod, hnewU, hbelow, hbrackets, hlifts, hrems⟩ := hstep
  refine ⟨m, ⟨a⟩, ⟨c⟩, hm, hmp, hac, hahom, hchom, hanorm, hcgrid,
    hprod, ?_, ?_, hnewU, hbelow, hbrackets, hlifts, hrems⟩
  · change coefficients (bchRemove s a P.coord c) 0 = coefficients P.coord 0
    rw [← hremove]
    exact hconstant
  · change bchRemove s a P.coord c ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    rw [← hremove]
    exact hnewgraded

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_bracket_step :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (_hk : ∀ z, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k z) = (1 : ℝ) ⊗ₜ[ℚ] k z)
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hquotient : (Fintype.card ι : ℝ) ≤ p)
    (_hkernel : (Fintype.card κ : ℝ) ≤ p) (_hsource : (Fintype.card ν : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSgraded : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hS : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hR : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hlower : ∀ d < j - 1, ∀ z α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ)
    (_hsmall : ∀ z α, ‖(b.baseChange ℝ).equivFun (coefficients (S z) α)‖ ≤ M / monomialScale T α)
    (_hrational : ∀ z α, (b.baseChange ℝ).equivFun (coefficients (R z) α) ∈ realDenominatorGrid l),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈ realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun z => dualAdjoint A⁻¹ (S z)
      let R' := fun z => dualAdjoint B (R z)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ z α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        ∀ z α,
          coefficients (S' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨C, hC, hCbound⟩ := exists_bracket_uniform_budget
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν σ _ _ _ _ _ _ s F b w hF E V hgraded hs U hUV hV e f k hk j H J Q l
    hj hE hEU hH hl hA he hf p M hp hM hambient hquotient hkernel hsource
    hHp hJp hQp hlp hMp T hT P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
  let q := bracketConstructionBudget p
  let r := bracketCorrectionBudget p
  have hq : 0 ≤ q := bracketConstructionBudget_nonneg hp
  have hr : 0 ≤ r := bracketCorrectionBudget_nonneg hp
  obtain ⟨hpq, hrowsq, hdenq, hnormq⟩ := bracket_construction_budget_bounds hp
  have hrows : (Fintype.card (κ × ι) : ℝ) ≤ q := by
    apply le_trans _ hrowsq
    rw [Fintype.card_prod, Nat.cast_mul, pow_two]
    exact mul_le_mul (hkernel.trans (by linarith)) (hquotient.trans (by linarith))
      (Nat.cast_nonneg _) (by linarith)
  have hpplus : Real.exp p ≤ Real.exp ((p + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hquotient hambient (fun i z =>
    (show (((quotientCoordinateMatrix b f i z).den) : ℝ) ≤ Q from Nat.cast_le.mpr (hf i z).2).trans
      (hQp.trans hpplus))
  have hEden := matrixDenominator_le_exp_power (bracketLiftMatrix b e) hp 1 hambient hsource (fun i z =>
    (show (((bracketLiftMatrix b e i z).den) : ℝ) ≤ J from Nat.cast_le.mpr (he i z).2).trans
      (hJp.trans hpplus))
  have hden : ((matrixDenominator (quotientCoordinateMatrix b f) * l : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hD hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdenq
  have hnorm : (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * M ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul (current_layer_coordinate_factor_bound hp (Fintype.card μ) Q hambient hQp)
          hMp hM (Real.exp_nonneg _)
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hnormq
  have htotal : separationBudget q + r ≤ (p + C) ^ C := hCbound p hp
  have hcut : separationBudget q ≤ (p + C) ^ C := by linarith
  have hout : r ≤ (p + C) ^ C := by linarith [separationBudget_nonneg hq]
  have hTq : ∀ i, Real.exp (separationBudget q) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hcut).trans (hT i)
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  obtain ⟨m, A, B, hm, hmbound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders⟩ :=
    F.exists_controlled_formal_bracket_step b w hF hgraded hs Uq hUV hV e f k hk hj hE hEU
      hH hl hA he hf hq hM hrows (hsource.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
      hden hnorm T hTq P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
  have houtputs := bracket_correction_budget_bounds hp (Fintype.card ν) J
    (matrixDenominator (bracketLiftMatrix b e)) hsource hJp hEden
  let n := matrixDenominator (bracketLiftMatrix b e) * m
  have hnbound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (matrixDenominator (bracketLiftMatrix b e) : ℝ) * (m : ℝ) := Nat.cast_mul _ _
      _ ≤ (matrixDenominator (bracketLiftMatrix b e) : ℝ) * Real.exp ((q + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmbound (Nat.cast_nonneg _)
      _ ≤ Real.exp r := houtputs.2
      _ ≤ _ := Real.exp_le_exp.mpr hout
  refine ⟨n, A, B, Nat.mul_pos (matrixDenominator_pos _) hm, hnbound,
    hAB, hAhom, hBhom, ?_, hBgrid, hprod, hconstant, hnewgraded, hnewU,
    hbelow, hbrackets, hlifts, hremainders⟩
  intro α
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  exact (hAnorm α).trans (div_le_div_of_nonneg_right
    (houtputs.1.trans (Real.exp_le_exp.mpr hout)) (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_controlled_bracket_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (_hk : ∀ z, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k z) = (1 : ℝ) ⊗ₜ[ℚ] k z)
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    (_hstructure : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hquotient : (Fintype.card ι : ℝ) ≤ p)
    (_hkernel : (Fintype.card κ : ℝ) ≤ p) (_hsource : (Fintype.card ν : ℝ) ≤ p)
    (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) ∈ E.baseChange ℝ)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hSR : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R)
    (_hSgraded : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hS : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hR : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈
      V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hlower : ∀ d < j - 1, ∀ z α,
      ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ)
    (_hsmall : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S z))
    (_hrational : ∀ z, CoefficientGrid (b.baseChange ℝ) l (R z))
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hsmallShift : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hrationalShift : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (_hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈ realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let S' := fun z => dualAdjoint A⁻¹ (S z)
      let R' := fun z => dualAdjoint B (R z)
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ d < j - 1,
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        (∀ d < j, ∀ z α,
          ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α), (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ) ∧
        PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' S' R' ∧
        (∀ z α,
          coefficients (S' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (R' z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k z)) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          ⁅coefficients P'.coord α, (1 : ℝ) ⊗ₜ[ℚ] k z⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) (S' z) ∧
          CoefficientGrid (b.baseChange ℝ) n (R' z) ∧
          S' z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          R' z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) ∧
          small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 := by
  obtain ⟨D, _, hstage⟩ := exists_uniform_formal_bracket_step
  obtain ⟨E, _, hremove⟩ := exists_formal_derivative_removal_control s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D + (Q + Polynomial.C E) ^ E + 1
  obtain ⟨C, hC, hCbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν σ _ _ _ _ _ _ _ F b w hF Esource V hgraded hs U hUV hV e f k hk
    j H J Qheight l hj hE hEU hH hl hA he hf hstructure p hp
    hambient hquotient hkernel hsource hvariables hHp hJp hQp hlp T hT P hPU hPgraded hPE
    S R hSR hSgraded hRgraded hS hR hlower hsmall hrational
    small rational extra hsystem hsmallShift hrationalShift hsmallBound hrationalGrid
  let d := (p + D) ^ D
  let q := p + d
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hqE : 0 ≤ (q + E) ^ E := by positivity
  have htotal : d + (q + E) ^ E + 1 ≤ (p + C) ^ C := by
    simpa [B, Q, q, d, Polynomial.eval₂_pow] using hCbound p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hremCap : (q + E) ^ E ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  obtain ⟨n₀, A, Bcorr, hn₀, hn₀bound, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders⟩ :=
    hstage F b w hF hgraded hs U hUV hV e f k hk hj hE hEU hH hl hA he hf hp
      (Real.exp_nonneg p) hambient hquotient hkernel hsource hHp hJp hQp hlp le_rfl
      T hTD P hPU hPgraded hPE S R hSR hSgraded hRgraded hS hR hlower
      (fun z => (coefficientBound_iff_norm (b.baseChange ℝ) T hTpos (Real.exp_nonneg p) (S z)).mp (hsmall z))
      hrational
  let Lden := l * n₀
  have hLden : 0 < Lden := Nat.mul_pos hl hn₀
  have hLbound : (Lden : ℝ) ≤ Real.exp q := by
    calc
      _ = (l : ℝ) * (n₀ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp p * Real.exp d := mul_le_mul hlp hn₀bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  obtain ⟨m, hm, hmbound, hLm, hcontrol⟩ := hremove F b w hF hgraded H q hH hq
    (hambient.trans hpq) (hvariables.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    hstructure Lden hLden hLbound
  have hlL : l ∣ Lden := dvd_mul_right l n₀
  have hnL : n₀ ∣ Lden := dvd_mul_left n₀ l
  have hAg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    (j - 1) A.coord hAhom (fun α => hE _ (hAB α).1)
  have hBg := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    (j - 1) Bcorr.coord hBhom (fun α => hE _ (hAB α).2)
  have hAraw : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) A.coord).mpr hAnorm
  have hAinput : CoefficientBound (b.baseChange ℝ) T (Real.exp ((q + 2) ^ 1)) A.coord := by
    apply CoefficientBound.mono _ T hTpos hAraw
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    dsimp [q]
    linarith
  have hBinput : CoefficientGrid (b.baseChange ℝ) Lden Bcorr.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hn₀ hnL (hBgrid α)
  have hinputCap : Real.exp p ≤ Real.exp ((q + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  obtain ⟨hboundLifts, hboundDerivative, hshiftLifts, hshiftDerivative⟩ :=
    hcontrol T hTpos A Bcorr hAg hBg hAinput hBinput S R small rational
      hSgraded hRgraded hsmallShift hrationalShift
      (fun z => CoefficientBound.mono _ T hTpos (hsmall z) hinputCap)
      (fun z α => realDenominatorGrid_subset_of_dvd hl hlL (hrational z α))
      (fun i => CoefficientBound.mono _ T hTpos (hsmallBound i)
        (div_le_div_of_nonneg_right hinputCap (hTpos i).le))
      (fun i α => realDenominatorGrid_subset_of_dvd hl hlL (hrationalGrid i α))
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hsystem' := PolynomialDerivativeSystemMod.remove Uq ((V.baseChange ℝ).restrictScalars ℚ)
    hUV P A Bcorr (fun α => hEU _ (hAB α).1) small rational extra hsystem
  have hfinalCap : Real.exp ((q + E) ^ E) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hremCap
  refine ⟨m, A, Bcorr, hm, hmbound.trans hfinalCap, hAB, hAhom, hBhom, ?_, ?_,
    hprod, hconstant, hnewgraded, hnewU, hbelow, hbrackets, hlifts, hremainders,
    hsystem', ?_, ?_⟩
  · intro α
    exact (hAnorm α).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdCap)
      (monomialScale_pos T hTpos α).le)
  · intro α
    exact realDenominatorGrid_subset_of_dvd hn₀ (dvd_trans hnL hLm) (hBgrid α)
  · intro z
    exact ⟨CoefficientBound.mono _ T hTpos (hboundLifts z).1 hfinalCap,
      (hboundLifts z).2, (hshiftLifts z).1, (hshiftLifts z).2⟩
  · intro i
    exact ⟨CoefficientBound.mono _ T hTpos (hboundDerivative i).1
      (div_le_div_of_nonneg_right hfinalCap (hTpos i).le),
      (hboundDerivative i).2, (hshiftDerivative i).1, (hshiftDerivative i).2⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_homogeneous_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X M : Type} {η V : Type*} [Fintype X] [DecidableEq X] [Fintype η]
      [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
      [LieRing M] [LieAlgebra ℚ M] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (basis : Basis η ℝ V)
      (pvec : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ V)
      (_hhom : ∀ α, Finsupp.weight (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) α ≠ k →
        coefficients pvec α = 0)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom pvec) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis pvec := by
  obtain ⟨C, hC, hdetect⟩ := exists_majorPhase_detected_decomposition m k hk
  refine ⟨C, hC, ?_⟩
  intro X M η V _ _ _ _ _ _ _ _ _ t e _ _ _ _ J _ basis pvec hhom
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hsupport (j : η) : coordinate (basis.coord j).toAddMonoidHom pvec ∈
      weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) k := by
    have hh : (coordinate (basis.coord j).toAddMonoidHom pvec).IsWeightedHomogeneous
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) k := by
      intro α hα
      by_contra hweight
      apply hα
      rw [coeff_coordinate, hhom α hweight, map_zero]
    intro α hα
    exact (hh (MvPolynomial.mem_support_iff.mp hα)).le
  have hscalar (j : η) : MajorPhaseDetectedConclusion (L := M) J k U poly c
      (coordinate (basis.coord j).toAddMonoidHom pvec) N ((p + C) ^ C) :=
    hdetect J (W j) D htk (R j) N poly hpoly U hcoeff Ψ c
      (coordinate (basis.coord j).toAddMonoidHom pvec) (hsupport j)
      β hβ p Rrank hp (hR j) (hRcap j) hdim (hmod j) (hcover j) hLip hΨ hN hRrank hrank (hcorr j)
  exact majorPhaseVectorDetectedConclusion_of_coordinates J k U poly c N ((p + C) ^ C)
    basis pvec hhom hscalar

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_restricted_grade_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (residual : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J))
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
              (fullTaggedVariableWeight J) fast k residual))) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight J) fast k residual)) ∧
      ∀ (u : X → ℝ) (z : ∀ j, J j → ℝ),
        eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2))
          (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) fast k residual) =
        eval₂ (Sum.elim u (lowTaggedCoordinates J k z))
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) fast k residual)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_homogeneous_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis residual
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  constructor
  · apply hdetect J basis
      (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual))
      _ W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim
      hmod hcover hLip hΨ hN hRrank hrank hcorr
    exact lowTaggedVectorRestrict_homogeneous J k _
      (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF (fullTaggedVariableWeight J) fast k residual)
  · intro u z
    apply lowTaggedVectorRestrict_eval_real J k _ _ u z
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF (fullTaggedVariableWeight J)
      fast k residual α (ne_of_gt hα)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_restricted_grade_major_matching (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
              (fullTaggedVariableWeight J) fast k (left⁻¹ * Z * right⁻¹).coord))) β (R j).eval u‖) →
      FullTaggedDetectedMajorGradeConclusion (M := M) F b ω hF J k fast basis lift
        Z left right K₀ U poly c N ((p + C) ^ C) := by
  obtain ⟨C, hC, hdetect⟩ := exists_full_restricted_grade_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower periodCap coverCap Lip W D htk R N poly hpoly U hcoeff
    Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hdetected := hdetect F b ω hF J fast basis (left⁻¹ * Z * right⁻¹).coord
    W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover
    hLip hΨ hN hRrank hrank hcorr
  exact fullTaggedDetectedMajorGradeConclusion_of_vector_detection F b ω hF J k fast basis lift
    Z left right K₀ U poly c N ((p + C) ^ C) hfast hsection hK₀ hlower hdetected.1

end Erdos3.NilpotentLieFiltration

end

end OAI

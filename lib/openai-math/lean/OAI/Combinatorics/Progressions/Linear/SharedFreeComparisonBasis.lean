import OAI.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

theorem exists_layer_basis_of_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r n : ℕ}
    {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)
    {p : ℝ} (hT : T.ComplexityLE p) (i j : Fin (s + 1))
    (K : Submodule ℚ L) (hK : T.filtration.layer i.val j.val = K) :
    ∃ k : Basis (Fin (finrank ℚ K)) ℚ K,
      ∀ a b, rationalLogHeight (E.basis.repr (k a : L) b) ≤ p := by
  subst K
  exact ⟨T.basis i j, hT.2 i j⟩

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3

open Module

variable {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]

theorem exists_firstProjection_basis_logHeight
    (e : Basis μ ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ}
    (hk : ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ c : Basis (Fin (finrank ℚ (K.map (LinearMap.proj 0)))) ℚ (K.map (LinearMap.proj 0)),
      ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p := by
  have hspan : Submodule.span ℚ (Set.range (fun a => (k a : Fin 4 → V))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hproj : Submodule.span ℚ (Set.range (fun a => (k a : Fin 4 → V) 0)) =
      K.map (LinearMap.proj 0) := by
    change Submodule.span ℚ (Set.range
      ((LinearMap.proj (0 : Fin 4) : (Fin 4 → V) →ₗ[ℚ] V) ∘ fun a => (k a : Fin 4 → V))) = _
    rw [Set.range_comp, ← Submodule.map_span, hspan]
  apply exists_submodule_basis_of_spanning_logHeight e _ (fun a => (k a : Fin 4 → V) 0) hproj
  intro a i
  simpa only [Pi.basis_repr] using hk a ⟨0, i⟩

theorem exists_fourPetalSpace_basis_logHeight
    (e : Basis μ ℚ V) (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (b : Basis (Fin (finrank ℚ D)) ℚ D) (k : Basis (Fin (finrank ℚ K)) ℚ K)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ c : Basis (Fin (finrank ℚ (fourPetalSpace D K))) ℚ (fourPetalSpace D K),
      ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ preimageBasisBudget (4 * p) := by
  let : FiniteDimensional ℚ V := e.finiteDimensional_of_finite
  have hp4 : p ≤ 4 * p := by linarith only [hp]
  have hspan (U : Submodule ℚ V) (a : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (a j : V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ a)) = U
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hkspan : Submodule.span ℚ (Set.range (fun j => (k j : Fin 4 → V))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top, Submodule.range_subtype]
  apply exists_preimage_basis_logHeight e (Pi.basis (fun _ : Fin 4 => e)) D K
    (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)
    (fun j => (b j : V)) (fun j => (k j : Fin 4 → V)) (hspan D b) hkspan
    (mul_nonneg (by norm_num) hp)
  · simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  · have hD : (finrank ℚ D : ℝ) ≤ Fintype.card μ := by
      exact_mod_cast D.finrank_le.trans_eq (finrank_eq_card_basis e)
    simpa only [Fintype.card_fin] using (hD.trans hdim).trans hp4
  · have hK : (finrank ℚ K : ℝ) ≤ 4 * Fintype.card μ := by
      exact_mod_cast four_submodule_finrank_le e K
    simpa only [Fintype.card_fin] using hK.trans
      (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  · exact fun a i => (hb a i).trans hp4
  · exact fun a i => (hk a i).trans hp4
  · rintro a ⟨j, i⟩
    by_cases hj : j = 0
    · subst j
      simpa [Pi.basis_repr, LinearMap.single_apply] using (hb a i).trans hp4
    · simpa [Pi.basis_repr, LinearMap.single_apply, hj, Ne.symm hj, rationalLogHeight] using
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hp)

end Erdos3

end

section

namespace Erdos3

theorem preimageBasisBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    preimageBasisBudget p ≤ preimageBasisBudget q := by
  have hq : 0 ≤ q := hp.trans hpq
  unfold preimageBasisBudget sparseGeneratorBudget
  gcongr

theorem fourRefinementBasisBudget_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    fourRefinementBasisBudget p ≤ fourRefinementBasisBudget q :=
  add_le_add hpq (preimageBasisBudget_mono (by positivity)
    (mul_le_mul_of_nonneg_left hpq (by norm_num)))

noncomputable def sharedFreeComparisonBasisBudget (q p : ℝ) : ℝ :=
  let A := q + fourRefinementBasisBudget (q + coefficientFourHeightBudget p)
  A + preimageBasisBudget (4 * A)

theorem exists_sharedFreeComparisonBasisBudget_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeComparisonBasisBudget q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := X + V (4 * X)
  let A : Polynomial ℕ := Polynomial.X + F (Polynomial.X + H Polynomial.X)
  let T : Polynomial ℕ := A + V (4 * A)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hheight : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hupper : sharedFreeComparisonBasisBudget q p ≤ sharedFreeComparisonBasisBudget p p := by
    have hA := add_le_add hqp (fourRefinementBasisBudget_mono (add_nonneg hq hheight)
      (add_le_add hqp (le_refl (coefficientFourHeightBudget p))))
    have hA0 : 0 ≤ q + fourRefinementBasisBudget (q + coefficientFourHeightBudget p) :=
      add_nonneg hq (fourRefinementBasisBudget_nonneg (add_nonneg hq hheight))
    dsimp only [sharedFreeComparisonBasisBudget]
    exact add_le_add hA (preimageBasisBudget_mono (mul_nonneg (by norm_num) hA0)
      (mul_le_mul_of_nonneg_left hA (by norm_num)))
  apply hupper.trans
  simpa [T, A, F, V, G, H, R, sharedFreeComparisonBasisBudget, coefficientFourHeightBudget,
    refiltrationCoordinateBudget, fourRefinementBasisBudget, preimageBasisBudget,
    sparseGeneratorBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_sharedFreeComparisonSpace_basis
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') (d : Fin s) :
    let C := (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)
    let P := fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))
    let K := D.coefficientFreeFiltration.layer (d.val + 1) 2
    ∃ b : Basis (Fin (finrank ℚ (petalComparisonSpace C P K))) ℚ (petalComparisonSpace C P K),
      ∀ a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (b a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P' := by
  intro C P K
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  let H := fourRefinementBasisBudget (Q + coefficientFourHeightBudget P')
  let A := Q + H
  have hH : 0 ≤ H := fourRefinementBasisBudget_nonneg
    (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP'))
  have hA : 0 ≤ A := add_nonneg hQ hH
  have hQA : Q ≤ A := le_add_of_nonneg_right hH
  have hHA : H ≤ A := le_add_of_nonneg_left hQ
  obtain ⟨k, hk⟩ := D.exists_correlation_refined_basis E T hbQ hT F V g hg D' hs hP' hQP' d
  obtain ⟨b, hb⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  obtain ⟨c, hc⟩ := exists_firstProjection_basis_logHeight E.basis _ k
    (fun a i => (hk a i).trans hHA)
  obtain ⟨p, hp⟩ := exists_fourPetalSpace_basis_logHeight E.basis _ _ b k hA
    (by simpa only [Fintype.card_fin] using hT.1.1.trans hQA)
    (fun a i => (hb a i).trans hQA) (fun a i => (hk a i).trans hHA)
  have hK : ∃ k : Basis (Fin (finrank ℚ K)) ℚ K,
      ∀ a i, rationalLogHeight (E.basis.repr (k a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
    exact T.exists_layer_basis_of_eq hT ⟨d.val + 1, by omega⟩ ⟨2, by omega⟩ K
      (congrArg (fun T => T.layer (d.val + 1) 2) hTfil)
  obtain ⟨k₂, hk₂⟩ := hK
  have hpre : 0 ≤ preimageBasisBudget (4 * A) := preimageBasisBudget_nonneg (by positivity)
  have hAL : A ≤ sharedFreeComparisonBasisBudget Q P' := le_add_of_nonneg_right hpre
  have hPL : preimageBasisBudget (4 * A) ≤ sharedFreeComparisonBasisBudget Q P' :=
    le_add_of_nonneg_left hA
  exact exists_petalComparisonSpace_basis_logHeight E.basis C P K c p k₂
    (add_nonneg hA hpre) (fun a i => (hc a i).trans hAL) (fun a i => (hp a i).trans hPL)
    (fun a i => (hk₂ a i).trans (hQA.trans hAL))

end Erdos3.NativeRankRelation.CommonData

end

end OAI

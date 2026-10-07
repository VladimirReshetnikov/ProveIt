import OAI.Combinatorics.Progressions.Estimates.NativeDependentRepresentativeFamily

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace DegreeRankLieFiltration

theorem positiveUnivariate_horizontal_mem {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s r : ℕ} (F : DegreeRankLieFiltration L s r)
    (v : ∀ d : Fin s,
      (F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1))) 1).baseChange ℝ) :
    positiveUnivariate (fun d => (v d).val) ∈
      F.realification.associatedDegree.adaptedLieSubalgebra (fun _ : Unit => 1) := by
  apply positiveUnivariate_coefficients_mem
  intro d
  change (v d).val ∈
    (F.layer (Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1))) 0).baseChange ℝ
  rw [F.rank_zero_eq_one]
  exact (v d).property

end DegreeRankLieFiltration

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_polynomial_corrections (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ h ∈ A.shifts, ∃ E Q : W.family.rank.filtration.realification.associatedDegree.adaptedLieSubalgebra
                  (fun _ : Unit => 1),
                coefficients E.val 0 = 0 ∧ coefficients Q.val 0 = 0 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) E.val ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n Q.val ∧
                ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  ∃ e u : (W.family.rank.filtration.layer
                      (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
                    coefficients E.val (α d) = e.val ∧ coefficients Q.val (α d) = u.val ∧
                    W.family.horizontalCoefficient hs c τ hG (α d) h -
                        W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
                        W.family.rank.filtration.realHorizontalMap
                          (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
                        W.family.rank.filtration.realHorizontalMap
                          (Finsupp.weight (fun _ : Unit => 1) (α d)) u ∈
                      (fourDependentProjection (D.horizontal
                        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨C, hC, hfamily⟩ := exists_native_dependent_representative_family s hs
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnC, hproj, hrep⟩ := hfamily W hF c τ hG hN
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, hAW, hdensity, n, hn, hnC, hproj, ?_⟩
  intro h hh
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  choose e u he hu hres using (fun d => hrep d (hd d) h hh)
  let E := positiveUnivariate (fun d => (e d).val)
  let Q := positiveUnivariate (fun d => (u d).val)
  refine ⟨⟨E, W.family.rank.filtration.positiveUnivariate_horizontal_mem e⟩,
    ⟨Q, W.family.rank.filtration.positiveUnivariate_horizontal_mem u⟩,
    positiveUnivariate_zero _, positiveUnivariate_zero _, ?_, ?_, ?_⟩
  · exact positiveUnivariate_coefficientBound (W.family.model.basis.baseChange ℝ)
      (fun d => (e d).val) (fun _ : Unit => (N : ℝ))
      (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg _) he
  · exact positiveUnivariate_coefficientGrid (W.family.model.basis.baseChange ℝ)
      (fun d => (u d).val) n hu
  · intro d hd'
    exact ⟨e d, u d, positiveUnivariate_coefficient _ d, positiveUnivariate_coefficient _ d, hres d⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_anchor_polynomial_corrections
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (n : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) :
    let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
    ∃ E Q : W.rank.filtration.realification.associatedDegree.adaptedLieSubalgebra (fun _ : Unit => 1),
      coefficients E.val 0 = 0 ∧ coefficients Q.val 0 = 0 ∧
      CoefficientBound (W.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 3) ^ 2 + (s : ℝ) * p)) E.val ∧
      CoefficientGrid (W.model.basis.baseChange ℝ) n Q.val ∧
      ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
        ∃ e u : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
          coefficients E.val (α d) = e.val ∧ coefficients Q.val (α d) = u.val ∧
          W.horizontalCoefficient hs c τ hG (α d) h₀ -
              W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
              W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) u ∈
            (fourFirstProjection (D.horizontal
              ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  intro α
  obtain ⟨e, u, he, hu, hres⟩ := A.exists_anchor_representative_corrections h₀ hh₀ hs hp hP c τ hG n hdenom
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  let E := positiveUnivariate (fun d => (e (α d)).val)
  let Q := positiveUnivariate (fun d => (u (α d)).val)
  refine ⟨⟨E, W.rank.filtration.positiveUnivariate_horizontal_mem (fun d => e (α d))⟩,
    ⟨Q, W.rank.filtration.positiveUnivariate_horizontal_mem (fun d => u (α d))⟩,
    positiveUnivariate_zero _, positiveUnivariate_zero _, ?_, ?_, ?_⟩
  · exact positiveUnivariate_coefficientBound (W.model.basis.baseChange ℝ)
      (fun d => (e (α d)).val) (fun _ : Unit => (N : ℝ))
      (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg _) (fun d => he (α d) (hd d))
  · exact positiveUnivariate_coefficientGrid (W.model.basis.baseChange ℝ)
      (fun d => (u (α d)).val) n (fun d => hu (α d))
  · intro d hd'
    exact ⟨e (α d), u (α d), positiveUnivariate_coefficient _ d,
      positiveUnivariate_coefficient _ d, hres (α d) hd'⟩

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

end OAI

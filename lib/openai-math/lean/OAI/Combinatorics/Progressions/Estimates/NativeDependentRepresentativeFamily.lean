/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.NativeDependentSelectionBudget
import OAI.Combinatorics.Progressions.Linear.CommonRealDependentProjection
import OAI.Combinatorics.Progressions.Polynomial.NativeDegreePowerBound

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_coordinate_family (s : ℕ) (hs : 1 ≤ s) :
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
            ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.family.dim) ∧
              ∃ f : ∀ d, Basis (Fin (m d)) ℚ
                (W.family.L ⧸ W.family.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
                (∀ d i j, rationalLogHeight
                  ((f d).repr ((W.family.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
                    (W.family.model.basis j)) i) ≤ (p + C) ^ C) ∧
                ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                  (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
                  ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                    ∃ e u : Fin (m d) → ℝ,
                      ‖e‖ ≤ Real.exp ((p + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                      u ∈ realDenominatorGrid n ∧
                      W.family.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                          W.family.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - u ∈
                        realRationalCoordinateSpan (fourDependentProjection
                          (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) ∧
                      ∃ z ∈ (fourDependentProjection
                          (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ,
                        W.family.rank.filtration.realHigherHorizontalCoordinates
                            (Finsupp.weight (fun _ : Unit => 1) (α d)) (f d)
                            (W.family.horizontalCoefficient hs c τ hG (α d) h -
                              W.family.horizontalCoefficient hs c τ hG (α d) h₀ - z) = e + u := by
  obtain ⟨a, _, hcommon⟩ := exists_native_common_rank_relation s hs
  obtain ⟨b, _, hdegrees⟩ := exists_native_degree_approximation_bound s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_dependent_selection_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let P₀ := (p + a) ^ a
  let P := (P₀ + 2) ^ 3 + 2 * P₀
  have hP₀ : 0 ≤ P₀ := by dsimp only [P₀]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP₀P : P₀ ≤ P := by
    have hc : 0 ≤ (P₀ + 2) ^ 3 := by positivity
    dsimp only [P]
    linarith
  obtain ⟨hP₀C, h2PC, hdegreeC⟩ := hbudget p hp
  have hPC : P ≤ (p + C) ^ C := by linarith
  obtain ⟨out, H, q, hHW, hH, hshort, _, hpq, hqP₀, R, ⟨D₀⟩⟩ :=
    hcommon W hF ((Real.exp_le_exp.mpr hP₀C).trans hN)
  obtain ⟨D, l, _, _, hl, hlbound, hdenom⟩ := D₀.exists_common_projected_denominator hP₀
  have hqP : q ≤ P := hqP₀.trans hP₀P
  have hpP : p ≤ P := hpq.trans hqP
  have hlP : (l : ℝ) ≤ Real.exp P := by
    apply hlbound.trans
    apply Real.exp_le_exp.mpr
    dsimp only [P]
    linarith
  obtain ⟨A⟩ := D.exists_sparse_anchors
  obtain ⟨h₀, hh₀⟩ := A.nonempty
  obtain ⟨m, hm, f, hf, n, hn, hnB, hln, happrox⟩ := hdegrees A h₀ hh₀
    (hp.trans hpq) hP hpP hqP c τ hG l hl hlP hdenom
    ((Real.exp_le_exp.mpr hdegreeC).trans hN)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, A.shifts_subset.trans hHW, ?_, m, hm, f, (fun d i j => (hf d i j).trans hdegreeC),
    n, hn, hnB.trans (Real.exp_le_exp.mpr hdegreeC), ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h2PC))
      (Nat.cast_nonneg _)).trans A.density
  · intro t ht
    rw [hdenom t ht]
    exact hln
  · intro d hd h hh
    obtain ⟨e, u, he, hu, hres⟩ := happrox d hd h hh
    obtain ⟨z, hz, hcoords⟩ := D.exists_native_dependent_remainder hs c τ hG (α d) hd (f d) h h₀ e u hres
    refine ⟨e, u, ?_, hu, hres, z, hz, hcoords⟩
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
    exact he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hdegreeC) hscale.le)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_representative_family (s : ℕ) (hs : 1 ≤ s) :
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
              ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                ∃ E Q : (W.family.rank.filtration.layer
                    (Finsupp.weight (fun _ : Unit => 1) (α d)) 1).baseChange ℝ,
                  ‖(W.family.model.basis.baseChange ℝ).equivFun E.val‖ ≤
                    Real.exp ((p + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                  (W.family.model.basis.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid n ∧
                  W.family.horizontalCoefficient hs c τ hG (α d) h -
                      W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
                      W.family.rank.filtration.realHorizontalMap
                        (Finsupp.weight (fun _ : Unit => 1) (α d)) E -
                      W.family.rank.filtration.realHorizontalMap
                        (Finsupp.weight (fun _ : Unit => 1) (α d)) Q ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨a, _, hfamily⟩ := exists_native_dependent_coordinate_family s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_horizontal_lift_budget s a
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  let L := (B + 3) ^ 4
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hBL : B ≤ L := by
    have h := le_power_budget (p := B + 1) (by linarith) (by decide : 1 ≤ 4)
    have heq : B + 1 + 2 = B + 3 := by ring
    rw [heq] at h
    exact (by linarith : B ≤ B + 1).trans h
  obtain ⟨hBC, hcut, hslow, hden⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, k, hk, f, hf, n, hn, hnB, hproj, happrox⟩ :=
    hfamily W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B := hpq.trans (hqP.trans hPB)
  have hdegree (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) = d.val + 1 := by
    simp only [α, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    rw [hdegree]
    omega
  have hpos (d : Fin s) : 1 ≤ Finsupp.weight (fun _ : Unit => 1) (α d) := by
    rw [hdegree]
    omega
  have hnonzero (d : Fin s) : α d ≠ 0 := by
    simp only [α, ne_eq, Finsupp.single_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, not_false_eq_true]
  have hrep (d : Fin s) := W.family.rank.exists_controlled_horizontal_representatives
    ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le (hd d)⟩ (hpos d) hB
    (W.family.complexity.mono W.family.rank hpB) (hk d) (f d) (hf d) hn hnB
    (fun _ : Unit => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hcut).trans hN)
  choose m hm hmB hnm hsolve using hrep
  let M₀ := ∏ d, m d
  have hM₀ : 0 < M₀ := Finset.prod_pos (fun d _ => hm d)
  have hM₀B : (M₀ : ℝ) ≤ Real.exp ((s : ℝ) * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := by
    calc
      _ = ∏ d, (m d : ℝ) := by rw [Nat.cast_prod]
      _ ≤ ∏ _d : Fin s, Real.exp (L + ((L + 2) ^ 3 + (L + 2) ^ 36)) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun d _ => hmB d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hmM₀ (d : Fin s) : m d ∣ M₀ := Finset.dvd_prod_of_mem m (Finset.mem_univ d)
  have hnM : n ∣ n * M₀ := dvd_mul_right _ _
  have hmM (d : Fin s) : m d ∣ n * M₀ := (hmM₀ d).trans (dvd_mul_left _ _)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC,
    R, D, A, h₀, hh₀, hAW, ?_, n * M₀, Nat.mul_pos hn hM₀, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · calc
      ((n * M₀ : ℕ) : ℝ) ≤ Real.exp B *
          Real.exp ((s : ℝ) * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hnB hM₀B (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (B + s * (L + ((L + 2) ^ 3 + (L + 2) ^ 36))) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hden
  · intro t ht
    exact (hproj t ht).trans hnM
  · intro d hd' h hh
    obtain ⟨e, u, he, hu, _, z, hz, hcoords⟩ := happrox d hd' h hh
    have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
      monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
    obtain ⟨E, Q, _, _, hres, hE, hQ⟩ := hsolve d (α d) (hnonzero d)
      (W.family.horizontalCoefficient hs c τ hG (α d) h)
      (W.family.horizontalCoefficient hs c τ hG (α d) h₀) z e u hcoords
      (he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hBL) hscale.le)) hu
    refine ⟨E, Q, ?_, realDenominatorGrid_subset_of_dvd (hm d) (hmM d) hQ, ?_⟩
    · exact hE.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) hscale.le)
    · rw [hres]
      exact hz

end Erdos3

end

end OAI

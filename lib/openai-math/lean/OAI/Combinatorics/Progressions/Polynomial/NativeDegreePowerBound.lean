/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations

namespace OAI

section

namespace Erdos3

theorem exists_native_coordinate_polynomial_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      nativeCoordinateSeparationBudget s P ≤ (P + C) ^ C ∧
      ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P ≤ (P + C) ^ C ∧
      nativeDependentSlowBudget s P ≤ (P + C) ^ C ∧ (P + 3) ^ 7 ≤ (P + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let R := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let G := X + X * (R + 1 + (X + 3) ^ 7)
  let U := 4 * X + (X + 3) ^ 7 + G + Polynomial.C s * X + (X + 3) ^ 2 + 4
  let V := U + (U + 2) ^ 3 + X + 2
  let Z := 2 * V + 2 * (V + ((V + 2) ^ 3 + (V + 2) ^ 36)) +
    ((V + 2) ^ 3 + (V + 2) ^ 18 + V) + 2
  let Q := Z + (Z + Z * ((Z + 2) ^ 7 + Z))
  let cut := ((V + 2) ^ 48 + (V + 2) ^ 24 + V + 1) +
    ((Q + 2) ^ 48 + (Q + 2) ^ 24 + Q + 1)
  let den := Q + (Q + 2) ^ 3 + (Q + 2) ^ 36
  let slow := (Q + 2) ^ 3 + (Q + 2) ^ 18 + Q + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (cut + Polynomial.C (s + 1) * den + slow + (X + 3) ^ 7)
  refine ⟨C, hC, ?_⟩
  intro P hP
  have hU : U.eval₂ (Nat.castRingHom ℝ) P = nativeCoordinateBaseBudget s P := by
    simp [U, G, R, X, nativeCoordinateBaseBudget, horizontalCoordinateBudget,
      refiltrationCoordinateBudget, Polynomial.eval₂_pow]
  have hV : V.eval₂ (Nat.castRingHom ℝ) P = nativeCoordinateInputBudget s P := by
    simp [V, X, Polynomial.eval₂_pow, hU, nativeCoordinateInputBudget]
  have hZ : Z.eval₂ (Nat.castRingHom ℝ) P =
      rankDependentInputBudget (nativeCoordinateInputBudget s P) := by
    simp [Z, Polynomial.eval₂_pow, hV, rankDependentInputBudget]
  have hQ : Q.eval₂ (Nat.castRingHom ℝ) P = nativeDependentBudget s P := by
    simp [Q, Polynomial.eval₂_pow, hZ, nativeDependentBudget, sparseGeneratorBudget]
  have hsum : nativeCoordinateSeparationBudget s P +
      ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P +
      nativeDependentSlowBudget s P + (P + 3) ^ 7 ≤ (P + C) ^ C := by
    simpa [cut, den, slow, X, Polynomial.eval₂_pow, hV, hQ,
      nativeCoordinateSeparationBudget, separationBudget, nativeDependentDenominatorBudget,
      nativeDependentSlowBudget] using hbudget P hP
  have hinput := nativeCoordinateInputBudget_nonneg s hP
  have hdep := nativeDependentBudget_nonneg s hP
  have hcut : 0 ≤ nativeCoordinateSeparationBudget s P :=
    add_nonneg (separationBudget_nonneg hinput) (separationBudget_nonneg hdep)
  have hden : 0 ≤ ((s : ℝ) + 1) * nativeDependentDenominatorBudget s P := by
    unfold nativeDependentDenominatorBudget
    positivity
  have hslow : 0 ≤ nativeDependentSlowBudget s P := by
    unfold nativeDependentSlowBudget
    positivity
  have hf : 0 ≤ (P + 3) ^ 7 := by positivity
  exact ⟨by linarith only [hsum, hden, hslow, hf],
    by linarith only [hsum, hcut, hslow, hf],
    by linarith only [hsum, hcut, hden, hf],
    by linarith only [hsum, hcut, hden, hslow]⟩

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData.SparseAnchors

open Module RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}

theorem exists_uniform_native_degree_approximations
    (A : D.SparseAnchors) (h₀ : ZMod N) (hh₀ : h₀ ∈ A.shifts)
    (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hl : 0 < l) (hlP : (l : ℝ) ≤ Real.exp P)
    (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (hN : Real.exp (nativeCoordinateSeparationBudget s P) ≤ N) :
    let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
    ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.dim) ∧
      ∃ f : ∀ d, Basis (Fin (m d)) ℚ
        (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
        (∀ d i j, rationalLogHeight
          ((f d).repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
            (W.model.basis j)) i) ≤ (P + 3) ^ 7) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((s : ℝ) * nativeDependentDenominatorBudget s P) ∧ l ∣ n ∧
          ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
            ∃ e q : Fin (m d) → ℝ,
              ‖e‖ ≤ Real.exp (nativeDependentSlowBudget s P) /
                monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧ q ∈ realDenominatorGrid n ∧
              W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                  W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - q ∈
                realRationalCoordinateSpan (fourDependentProjection
                  (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) := by
  classical
  intro α
  have hdegree (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  have hnonzero (d : Fin s) : α d ≠ 0 := by
    intro hz
    have h := congrArg (fun x : Unit →₀ ℕ => x ()) hz
    simp [α] at h
  have hchoice (d : Fin s) := A.exists_bounded_native_dependent_approximations h₀ hh₀
    hs hp hP hbP hpP c τ hG l hl hlP hdenom (α d) (hdegree d) (hnonzero d) hN
  choose m hm f hf n hn hnB hln happrox using hchoice
  let n₀ : ℕ := ∏ d : Fin s, n d
  have hn₀ : 0 < n₀ := Finset.prod_pos (fun d _ => hn d)
  have hn₀B : (n₀ : ℝ) ≤ Real.exp ((s : ℝ) * nativeDependentDenominatorBudget s P) := by
    change ((∏ d : Fin s, n d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      ∏ d : Fin s, (n d : ℝ) ≤ ∏ _d : Fin s, Real.exp (nativeDependentDenominatorBudget s P) :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun d _ => hnB d)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have hdvd (d : Fin s) : n d ∣ n₀ := Finset.dvd_prod_of_mem n (Finset.mem_univ d)
  let d₀ : Fin s := ⟨0, by omega⟩
  refine ⟨m, hm, f, hf, n₀, hn₀, hn₀B, (hln d₀).trans (hdvd d₀), ?_⟩
  intro d hd h hh
  obtain ⟨e, q, he, hq, hres⟩ := happrox d h hh
  exact ⟨e, q, he, realDenominatorGrid_subset_of_dvd (hn d) (hdvd d) hq, hres⟩

end Erdos3.NativeRankRelation.CommonData.SparseAnchors

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_degree_approximation_bound (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} {D : R.CommonData P}
      (A : D.SparseAnchors) (h₀ : ZMod N), h₀ ∈ A.shifts →
      0 ≤ p → 0 ≤ P → b ≤ P → p ≤ P →
      ∀ (c : Basis κ ℚ W.L) (τ : κ → ℕ)
        (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
        (l : ℕ), 0 < l → (l : ℝ) ≤ Real.exp P →
        (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l) →
        Real.exp ((P + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ m : Fin s → ℕ, (∀ d, m d ≤ W.dim) ∧
          ∃ f : ∀ d, Basis (Fin (m d)) ℚ
            (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2),
            (∀ d i j, rationalLogHeight
              ((f d).repr ((W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) (α d)) 2).mkQ
                (W.model.basis j)) i) ≤ (P + C) ^ C) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((P + C) ^ C) ∧ l ∣ n ∧
              ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s), ∀ h ∈ A.shifts,
                ∃ e q : Fin (m d) → ℝ,
                  ‖e‖ ≤ Real.exp ((P + C) ^ C) / monomialScale (fun _ : Unit => (N : ℝ)) (α d) ∧
                  q ∈ realDenominatorGrid n ∧
                  W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h -
                      W.nativeCoefficientCoordinates hs c τ hG (α d) (f d) h₀ - e - q ∈
                    realRationalCoordinateSpan (fourDependentProjection
                      (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩ (f d))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_native_coordinate_polynomial_budget s
  refine ⟨C, hC, ?_⟩
  intro κ r N _ b p q P W out H R D A h₀ hh₀ hp hP hbP hpP c τ hG l hl hlP hdenom hN α
  obtain ⟨hcut, hden, hslow, hf⟩ := hbudget P hP
  obtain ⟨m, hm, f, hfheight, n, hn, hnB, hln, happrox⟩ :=
    A.exists_uniform_native_degree_approximations h₀ hh₀ hs hp hP hbP hpP c τ hG l hl hlP hdenom
      ((Real.exp_le_exp.mpr hcut).trans hN)
  have hden0 : 0 ≤ nativeDependentDenominatorBudget s P := by
    have hQ := nativeDependentBudget_nonneg s hP
    unfold nativeDependentDenominatorBudget
    positivity
  have hden' : (s : ℝ) * nativeDependentDenominatorBudget s P ≤ (P + C) ^ C :=
    (mul_le_mul_of_nonneg_right (by linarith : (s : ℝ) ≤ (s : ℝ) + 1) hden0).trans hden
  refine ⟨m, hm, f, (fun d i j => (hfheight d i j).trans hf), n, hn,
    hnB.trans (Real.exp_le_exp.mpr hden'), hln, ?_⟩
  intro d hd h hh
  obtain ⟨e, q, he, hq, hres⟩ := happrox d hd h hh
  refine ⟨e, q, ?_, hq, hres⟩
  have hscale : 0 < monomialScale (fun _ : Unit => (N : ℝ)) (α d) :=
    monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) (α d)
  exact he.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) hscale.le)

end Erdos3

end

end OAI

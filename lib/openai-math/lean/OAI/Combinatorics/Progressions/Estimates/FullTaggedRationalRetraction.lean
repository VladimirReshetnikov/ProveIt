import OAI.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal

namespace OAI

section

namespace Erdos3

variable {T S : Type*} [Fintype T] [Fintype S]

theorem rationalMatrix_real_range_eq_coordinateSpan (P : Matrix T S ℚ) :
    LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
      realRationalCoordinateSpan (LinearMap.range P.mulVecLin) := by
  rw [Matrix.range_mulVecLin P]
  exact (Matrix.range_mulVecLin (Matrix.of (fun i j => (P i j : ℝ)))).trans
    (realRationalCoordinateSpan_span P.col).symm

theorem rationalMatrix_real_fixes_coordinateSpan
    (P : Matrix T T ℚ) (W : Submodule ℚ (T → ℚ))
    (hfix : ∀ x ∈ W, P.mulVecLin x = x)
    (x : T → ℝ) (hx : x ∈ realRationalCoordinateSpan W) :
    Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x := by
  have hspan : Submodule.span ℚ (Set.range (fun w : W => (w : T → ℚ))) = W := by
    have he : Set.range (fun w : W => (w : T → ℚ)) = (W : Set (T → ℚ)) := by
      ext y
      simp
    rw [he, Submodule.span_eq]
  rw [← hspan, realRationalCoordinateSpan_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      funext i
      have he := congrArg (fun z : T → ℚ => (z i : ℝ)) (hfix w w.property)
      change (∑ j, (P i j : ℝ) * ((w : T → ℚ) j : ℝ)) = ((w : T → ℚ) i : ℝ)
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Rat.cast_sum, Rat.cast_mul] using he
  | zero => exact map_zero _
  | add y z _ _ hey hez => rw [map_add, hey, hez]
  | smul a y _ hey => rw [map_smul, hey]

theorem rationalMatrix_real_retraction
    (P : Matrix T T ℚ) (W : Submodule ℚ (T → ℚ))
    (hrange : LinearMap.range P.mulVecLin = W)
    (hfix : ∀ x ∈ W, P.mulVecLin x = x) :
    LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      ∀ x ∈ realRationalCoordinateSpan W,
        Matrix.mulVecLin (fun i j => (P i j : ℝ)) x = x := by
  refine ⟨?_, rationalMatrix_real_fixes_coordinateSpan P W hfix⟩
  rw [rationalMatrix_real_range_eq_coordinateSpan, hrange]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_rational_tag_retraction
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ P : Matrix T T ℚ,
      LinearMap.range P.mulVecLin = W ∧
      (∀ x ∈ W, P *ᵥ x = x) ∧
      P * P = P ∧
      ∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8 := by
  classical
  let B : Matrix T I ℚ := fun t a => (b a : T → ℚ) t
  let H := ⌊Real.exp p⌋₊
  have hH : 1 ≤ H := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hp)
  have hHp : (H : ℝ) ≤ Real.exp p := Nat.floor_le (Real.exp_nonneg p)
  have hB : ∀ t a, RationalHeightLE (B t a) H := by
    intro t a
    obtain ⟨hn, hd⟩ := (rationalLogHeight_le_iff _ _).mp (hb a t)
    exact ⟨Nat.le_floor hn, Nat.le_floor hd⟩
  have hli : LinearIndependent ℚ B.col :=
    b.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hH hB
  have hBrange : LinearMap.range B.mulVecLin = W := by
    rw [Matrix.range_mulVecLin]
    change Submodule.span ℚ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hfix : ∀ x ∈ W, (B * C) *ᵥ x = x := by
    intro x hx
    rw [← hBrange] at hx
    obtain ⟨y, rfl⟩ := hx
    change (B * C) *ᵥ (B *ᵥ y) = B *ᵥ y
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hCB, Matrix.mul_one]
  have hmem : ∀ x, (B * C) *ᵥ x ∈ W := by
    intro x
    rw [← hBrange, ← Matrix.mulVec_mulVec]
    exact ⟨C *ᵥ x, rfl⟩
  refine ⟨B * C, ?_, hfix, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hmem y
    · intro hx
      exact ⟨x, hfix x hx⟩
  · calc
      B * C * (B * C) = B * (C * B) * C := by simp only [Matrix.mul_assoc]
      _ = B * C := by rw [hCB, Matrix.mul_one]
  · have hsolve := rationalSolveHeight_le_budget (Fintype.card I) H hp hI hHp
    have hprod : ((H * rationalSolveHeight (Fintype.card I) H : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ 6) := by
      rw [Nat.cast_mul]
      calc
        _ ≤ Real.exp p * Real.exp ((p + 2) ^ 5) :=
          mul_le_mul hHp hsolve (Nat.cast_nonneg _) (Real.exp_nonneg _)
        _ = Real.exp (p + (p + 2) ^ 5) := (Real.exp_add _ _).symm
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hp5 := le_power_budget hp (by decide : 1 ≤ 5)
          calc
            _ ≤ 2 * (p + 2) ^ 5 := by linarith
            _ ≤ (p + 2) * (p + 2) ^ 5 :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = (p + 2) ^ 6 := by ring
    intro i j
    apply rationalLogHeight_le_of_height (rationalHeightLE_matrix_mul B C hB hC i j)
    exact rational_sum_cost_le_exp (Fintype.card I)
      (H * rationalSolveHeight (Fintype.card I) H) hp 6 1 hprod
      (by simpa using hI.trans (show p ≤ p + 2 by linarith))

theorem exists_bounded_real_rational_tag_retraction
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ P : Matrix T T ℚ,
      LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      (∀ x ∈ realRationalCoordinateSpan W, (fun i j => (P i j : ℝ)) *ᵥ x = x) ∧
      ∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8 := by
  obtain ⟨P, hrange, hfix, _, hheight⟩ :=
    exists_bounded_rational_tag_retraction W b hp hI hb
  obtain ⟨hrangeR, hfixR⟩ := rationalMatrix_real_retraction P W hrange hfix
  exact ⟨P, hrangeR, hfixR, hheight⟩

theorem exists_bounded_real_rational_tag_retraction_grid
    {T I : Type*} [Fintype T] [Fintype I]
    (W : Submodule ℚ (T → ℚ)) (b : Basis I ℚ W)
    {p : ℝ} (hp : 0 ≤ p) (hT : (Fintype.card T : ℝ) ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p)
    (hb : ∀ a t, rationalLogHeight ((b a : T → ℚ) t) ≤ p) :
    ∃ (P : Matrix T T ℚ) (D : ℕ),
      LinearMap.range (Matrix.mulVecLin (fun i j => (P i j : ℝ))) =
        realRationalCoordinateSpan W ∧
      (∀ x ∈ realRationalCoordinateSpan W, (fun i j => (P i j : ℝ)) *ᵥ x = x) ∧
      (∀ i j, rationalLogHeight (P i j) ≤ (p + 2) ^ 8) ∧
      0 < D ∧ (D : ℝ) ≤ Real.exp ((p + 2) ^ 10) ∧
      (∀ i j, ∃ z : ℤ, (D : ℝ) * (P i j : ℝ) = (z : ℝ)) ∧
      ∀ (l : ℕ) (x : T → ℝ), x ∈ realDenominatorGrid l →
        (fun i j => (P i j : ℝ)) *ᵥ x ∈ realDenominatorGrid (D * l) := by
  obtain ⟨P, hrange, hfix, hheight⟩ :=
    exists_bounded_real_rational_tag_retraction W b hp hI hb
  obtain ⟨_, hpos, hden, hint⟩ := rational_matrix_entry_budget P hp 8 hT hT
    (fun i j => (rationalLogHeight_le_iff _ _).mp (hheight i j))
  exact ⟨P, matrixDenominator P, hrange, hfix, hheight, hpos, hden, hint,
    fun l x hx => real_matrix_denominator_grid P l x hx⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedRationalLinearChart
    (P : ∀ j, Matrix (J j) (J j) ℚ) :
    X ⊕ (Σ j, J j) → MvPolynomial (X ⊕ (Σ j, J j)) ℚ
  | Sum.inl x => MvPolynomial.X (Sum.inl x)
  | Sum.inr ⟨j, i⟩ => ∑ a : J j, P j i a • MvPolynomial.X (Sum.inr ⟨j, a⟩)

noncomputable def fullTaggedRealMatrixProjection
    (P : ∀ j, Matrix (J j) (J j) ℚ) (j : Fin m) :
    (J j → ℝ) →ₗ[ℝ] (J j → ℝ) :=
  Matrix.mulVecLin (fun i a => (P j i a : ℝ))

theorem fullTaggedRationalLinearChart_map
    (P : ∀ j, Matrix (J j) (J j) ℚ) (v : X ⊕ (Σ j, J j)) :
    MvPolynomial.map (Rat.castHom ℝ) (fullTaggedRationalLinearChart J P v) =
      fullTaggedLinearMapChart J (fullTaggedRealMatrixProjection J P) v := by
  have hentry (j : Fin m) (a i : J j) :
      fullTaggedRealMatrixProjection J P j (Pi.single a 1) i = (P j i a : ℝ) := by
    exact congrFun (Matrix.mulVec_single_one (Matrix.of fun s t => (P j s t : ℝ)) a) i
  cases v with
  | inl x => simp [fullTaggedRationalLinearChart, fullTaggedLinearMapChart]
  | inr v =>
    simp [fullTaggedRationalLinearChart, fullTaggedLinearMapChart,
      hentry, smul_eq_C_mul]

theorem fullTaggedAffineMatrixChart_top_eq_map
    (P : ∀ j, Matrix (J j) (J j) ℚ) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v)
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v) =
        MvPolynomial.map (Rat.castHom ℝ) (fullTaggedRationalLinearChart J P v) := by
  rw [fullTaggedAffineMapChart_top, fullTaggedRationalLinearChart_map]

theorem fullTaggedRationalLinearChart_homogeneous
    (P : ∀ j, Matrix (J j) (J j) ℚ) (v : X ⊕ (Σ j, J j)) :
    (fullTaggedRationalLinearChart J P v).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact isWeightedHomogeneous_X (R := ℚ) _ _
  | inr v =>
    apply (weightedHomogeneousSubmodule ℚ _ _).sum_mem
    intro a _
    exact (weightedHomogeneousSubmodule ℚ _ _).smul_mem _
      (isWeightedHomogeneous_X (R := ℚ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

theorem fullTaggedRationalLinearChart_support
    (P : ∀ j, Matrix (J j) (J j) ℚ) (v : X ⊕ (Σ j, J j)) :
    fullTaggedRationalLinearChart J P v ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  intro α hα
  exact le_of_eq (fullTaggedRationalLinearChart_homogeneous J P v
    (MvPolynomial.mem_support_iff.mp hα))

theorem RationalTaggedConstraintCertificate.exists_bounded_rational_retractions
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    let q := p + ((p + 2) ^ 2 + 2) ^ 63
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ))
      (P : ∀ j, Matrix (J j) (J j) ℚ) (D : Fin m → ℕ),
      K = {x | ∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (W j)} ∧
      ∀ j,
        LinearMap.range (fullTaggedRealMatrixProjection J P j) = realRationalCoordinateSpan (W j) ∧
        (∀ x ∈ realRationalCoordinateSpan (W j), fullTaggedRealMatrixProjection J P j x = x) ∧
        (∀ i a, rationalLogHeight (P j i a) ≤ (q + 2) ^ 8) ∧
        0 < D j ∧ (D j : ℝ) ≤ Real.exp ((q + 2) ^ 10) ∧
        (∀ i a, ∃ z : ℤ, (D j : ℝ) * (P j i a : ℝ) = (z : ℝ)) ∧
        ∀ (l : ℕ) (x : J j → ℝ), x ∈ realDenominatorGrid l →
          fullTaggedRealMatrixProjection J P j x ∈ realDenominatorGrid (D j * l) := by
  intro q
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  have hpq : p ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp.trans hpq
  have hheight : ((p + 2) ^ 2 + 2) ^ 63 ≤ q := by dsimp [q]; linarith
  choose P D hP using fun j => exists_bounded_real_rational_tag_retraction_grid
    (W j) (b j) hq ((hdim j).trans hpq)
    (by simpa only [Fintype.card_fin] using ((Nat.cast_le.mpr (hn j)).trans (hdim j)).trans hpq)
    (fun a i => (hb j a i).trans hheight)
  refine ⟨W, P, D, ?_, hP⟩
  rw [hK]
  ext x
  simp only [Set.mem_ofPred_eq]
  simp_rw [realRationalCoordinateSpan_basis (W _) (b _)]

end Erdos3.VectorPolynomial

end

end OAI

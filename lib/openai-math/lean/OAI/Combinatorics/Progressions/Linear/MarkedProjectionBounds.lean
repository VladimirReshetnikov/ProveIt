import OAI.Combinatorics.Progressions.Estimates.DescendedLinearMapBounds
import OAI.Combinatorics.Progressions.Estimates.MarkedPureEvaluation

namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hw hv hH hc hgen in
theorem exists_markedShift_bounded_basis (hω : ∀ i, ω i ≤ s) (t : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
        (markedShiftSubalgebra F v w marked t),
      ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
        (e i).val j) (lieTreeHeight (Fintype.card ι) H s) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range (markedShiftGenerator F v w marked hw hv t 0 0))
  rw [markedShiftGenerator_span, markedShiftBiLayer_zero, finrank_top] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  let e := Basis.mk hzli (le_of_eq hzspan.symm)
  refine ⟨e, ?_⟩
  intro i j
  simp only [e, Basis.mk_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact markedShiftGenerator_coordinate_height F b ω hF v w marked hw hv hH hc hgen t 0 0 k j

include hw hv hH hc hgen in
theorem exists_markedShiftLayer_coordinate_basis (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) (h n : ℕ) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ c : Basis (Fin (finrank ℚ (markedShiftBiLayer F v w marked t h n))) ℚ
        (markedShiftBiLayer F v w marked t h n),
      ∀ i j, RationalHeightLE (e.repr (c i).val j)
        ((a + 1) * (rationalSolveHeight d T * T) ^ a) := by
  classical
  dsimp only
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  obtain ⟨c, hc'⟩ := exists_markedShiftLayer_bounded_basis F b ω hF v w marked hw hv hH hc hgen hω t h n
  refine ⟨c, ?_⟩
  intro i j
  have hb := embedding_basis_coordinate_height e (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) (hH.trans (lieTreeHeight_ge_input _ _ _))
    (fun j i => he i j) (c i).val (hc' i) j
  simpa only [Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using hb

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hw hv hH hc hgen in
theorem exists_markedShiftQuotient_bounded_coordinates (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t),
        ∀ i j, RationalHeightLE
          (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i)
          (rationalKernelHeight m B) := by
  let T := lieTreeHeight (Fintype.card ι) H s
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  have hT : 1 ≤ T := hH.trans (lieTreeHeight_ge_input _ _ _)
  have hsolve : 0 < rationalSolveHeight d T := rationalSolveHeight_pos d hT
  have hB : 1 ≤ B := by
    have hTpos : 0 < T := Nat.zero_lt_of_lt hT
    exact Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hex := exists_markedShiftLayer_coordinate_basis F b ω hF v w marked hw hv hH hc hgen hω t e he 2 0
  dsimp only at hex
  rw [markedShiftBiLayer_second] at hex
  obtain ⟨c, hc'⟩ := hex
  have hcoords : ∀ i j, RationalHeightLE (e.repr (c i).val j) B := hc'
  obtain ⟨m, hm, q, hq, f, hf⟩ := exists_bounded_submodule_quotient_basis e
    (markedShiftSecondIdeal F v w marked t).toSubmodule (fun i => (c i).val)
    (span_submodule_basis _ c) hB hcoords
  refine ⟨m, ?_, q, ?_, f, hf⟩
  · simpa only [Fintype.card_fin] using hm
  · simpa only [Fintype.card_fin] using hq

include hw hv hH hc hgen in
theorem exists_markedShiftQuotientLayer_bounded_basis (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s))
    {q Q : ℕ} (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (α : Fin 2 → ℕ) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
    ∃ c : Basis (Fin (finrank ℚ (markedShiftQuotientLayer F v w marked t α))) ℚ
        (markedShiftQuotientLayer F v w marked t α),
      ∀ i j, RationalHeightLE (f.repr (c i).val j) ((d + 1) * (B * Q) ^ d) := by
  dsimp only
  obtain ⟨c, hc'⟩ := exists_markedShiftLayer_coordinate_basis F b ω hF v w marked hw hv hH hc hgen
    hω t e he (α 0) (α 1)
  let π := (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
  have hspan : Submodule.span ℚ (Set.range (fun i => π (c i).val)) =
      markedShiftQuotientLayer F v w marked t α := by
    change Submodule.span ℚ (Set.range (π ∘ (fun i => (c i).val))) = _
    rw [Set.range_comp, ← Submodule.map_span, span_submodule_basis]
    rfl
  apply exists_bounded_submodule_basis_from_spanning f _ (fun i => π (c i).val) hspan
  intro i j
  have h := linearMap_coordinate_height e f π (fun i j => hf j i) (c i).val (hc' i) j
  simpa only [Fintype.card_fin] using h

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r d q : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (e : Basis (Fin d) ℚ (markedShiftSubalgebra F v w marked t))
  {H : ℕ} (he : ∀ i j, RationalHeightLE
    ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr (e i).val j) H)

include he

omit [Fintype ι] in
theorem markedShiftPhase_coordinate_height (i : Fin t) (j : Fin d) :
    RationalHeightLE ((RationalTorus.basis t).repr (markedShiftPhase F v w marked t (e j)) i) H := by
  have h := he j (Sum.inr i)
  rw [F.associatedDegree.polynomialShiftBasis_repr_inr] at h
  exact h

omit [Fintype ι] in
theorem markedShiftEval_zero_coordinate_height (i : ι) (j : Fin d) :
    RationalHeightLE (b.repr (markedShiftEval F v w marked t 0 (e j)) i) H := by
  let z : NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω :=
    ⟨(0, i), by simp⟩
  have h := he j (Sum.inl z)
  rw [F.associatedDegree.polynomialShiftBasis_repr_inl] at h
  change RationalHeightLE (b.repr (eval (fun _ => 0) (e j).val.left.val) i) H
  rw [eval_zero_eq_coefficient]
  exact h

variable (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
  {Q : ℕ} (hQ : 1 ≤ Q)
  (hf : ∀ i j, RationalHeightLE
    (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)

include hQ hf

omit [Fintype ι] in
theorem markedQuotientPhase_coordinate_height (i : Fin t) (j : Fin q) :
    RationalHeightLE ((RationalTorus.basis t).repr (markedQuotientPhase F v w marked t (f j)) i)
      ((d + 1) * (rationalSolveHeight q Q * H) ^ d) := by
  have h := descended_linear_map_coordinate_height e f (RationalTorus.basis t)
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (lieQuotientMap_surjective _) (markedQuotientPhase F v w marked t).toLinearMap hQ hf
    (fun i j => markedShiftPhase_coordinate_height F v w marked t b ω hF e he i j) i j
  change RationalHeightLE ((RationalTorus.basis t).repr
    (markedQuotientPhase F v w marked t (f j)) i)
    ((Fintype.card (Fin d) + 1) * (rationalSolveHeight (Fintype.card (Fin q)) Q * H) ^
      Fintype.card (Fin d)) at h
  simpa only [Fintype.card_fin] using h

variable {ν : Type*} (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
  (hc : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)

include hc

theorem markedBaseEvaluation_zero_coordinate_height (i : ν) (j : Fin q) :
    RationalHeightLE (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (f j)) i)
      ((d + 1) * (rationalSolveHeight q Q * ((Fintype.card ι + 1) * (H * K) ^ Fintype.card ι)) ^ d) := by
  have hcomp (i j) : RationalHeightLE
      (c.repr (markedBaseEvaluation F v w marked t J hJ 0
        (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j))) i)
      ((Fintype.card ι + 1) * (H * K) ^ Fintype.card ι) := by
    rw [markedBaseEvaluation_map]
    exact linearMap_coordinate_height b c (lieQuotientMap J).toLinearMap
      (fun j i => hc i j) (markedShiftEval F v w marked t 0 (e j))
      (fun i => markedShiftEval_zero_coordinate_height F v w marked t b ω hF e he i j) i
  have h := descended_linear_map_coordinate_height e f c
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (lieQuotientMap_surjective _) (markedBaseEvaluation F v w marked t J hJ 0)
    hQ hf hcomp i j
  simpa only [Fintype.card_fin] using h

end Erdos3

end

end OAI

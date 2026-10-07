/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget
import OAI.Combinatorics.Progressions.Linear.JointRationalSpaceDefiningMatrix
import OAI.Combinatorics.Progressions.Linear.RankPreparationSizes

namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def preparationHeight (p : ℝ) (depth : ℕ) : ℕ :=
  ⌊Real.exp ((p + 2) ^ budgetDepthExponent 38 depth)⌋₊

theorem preparationExponent_pos (depth : ℕ) : 1 ≤ budgetDepthExponent 38 depth := by
  induction depth with
  | zero => rfl
  | succ d ih => simp only [budgetDepthExponent]; omega

theorem preparationExponent_mono : Monotone (budgetDepthExponent 38) := by
  apply monotone_nat_of_le_succ
  intro d
  simp only [budgetDepthExponent]
  omega

theorem preparationHeight_pos {p : ℝ} (hp : 0 ≤ p) (depth : ℕ) :
    1 ≤ preparationHeight p depth := by
  apply Nat.le_floor
  norm_cast
  exact Real.one_le_exp (by positivity)

theorem preparationHeight_le_exp (p : ℝ) (depth : ℕ) :
    (preparationHeight p depth : ℝ) ≤ Real.exp ((p + 2) ^ budgetDepthExponent 38 depth) :=
  Nat.floor_le (Real.exp_nonneg _)

theorem preparationHeight_mono {p : ℝ} (hp : 0 ≤ p) : Monotone (preparationHeight p) := by
  intro d e hde
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_right₀ (by linarith) (preparationExponent_mono hde)

theorem rankCutDirectionHeight_le_preparationHeight (ambient columns rows H R depth : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hr : (rows : ℝ) + 1 ≤ p) (hH : H ≤ preparationHeight p depth)
    (hR : (R : ℝ) ≤ Real.exp p) :
    rankCutDirectionHeight ambient columns rows H R ≤ preparationHeight p (depth + 1) := by
  have hpq := le_power_budget hp (preparationExponent_pos depth)
  have hHp : (H : ℝ) ≤ Real.exp ((p + 2) ^ budgetDepthExponent 38 depth) :=
    (Nat.cast_le.mpr hH).trans (preparationHeight_le_exp p depth)
  have hbound := rankCutDirectionHeight_le_exp ambient columns rows H R
    (by positivity : 0 ≤ (p + 2) ^ budgetDepthExponent 38 depth)
    (ha.trans hpq) (hc.trans hpq) (hr.trans hpq) hHp
    (hR.trans (Real.exp_le_exp.mpr hpq))
  apply Nat.le_floor
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  exact shifted_power_budget_le hp (budgetDepthExponent 38 depth) 38

namespace RankPreparationFamily

def PreparedHeights {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s) (p : ℝ) (R : ℕ) : Prop :=
  ∀ i, (L i).Valid (i.val + 1) (preparationHeight p (s - 1 - i.val)) R

theorem PreparedHeights.descend {I J : Type} {s : ℕ} {L : RankPreparationFamily I J s}
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R)
    (upper lower : Fin s) (hlevel : upper.val = lower.val + 1)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ)
    {He : ℕ} (ha : ∀ i, |(a i : ℝ)| ≤ R) (heH : ∀ i, RationalHeightLE (e i) He)
    (hHe : He ≤ preparationHeight p ((s - 1 - upper.val) + 1))
    (he : (fun i => (e i : ℝ)) ∈ (L upper).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) (hl : l.totalDegree ≤ lower.val + 1) :
    (L.descend upper lower a e l).PreparedHeights p R := by
  have hne : upper ≠ lower := by intro h; rw [h] at hlevel; omega
  intro i
  apply (L.descend_valid upper lower hne (fun i => preparationHeight p (s - 1 - i.val))
    (fun _ => preparationHeight_pos hp _) hR hL a e l ha heH he hae hl i).mono_height
  split_ifs with hi
  · subst i
    apply max_le le_rfl
    have hd : s - 1 - lower.val = (s - 1 - upper.val) + 1 := by omega
    rwa [hd]
  · exact le_rfl

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {I J : Type} [Fintype J] [DecidableEq J] {j : ℕ}

noncomputable def initial (p : VectorPolynomial I ℝ (J → ℝ)) : RankPreparationFamily I J (j + 1) :=
  fun i => if i = Fin.last j then RankPreparationLayer.initial p else RankPreparationLayer.empty

theorem initial_potential (p : VectorPolynomial I ℝ (J → ℝ)) :
    (initial (j := j) p).potential = (j + 1) * Fintype.card J := by
  have hr : (fun i => (initial (j := j) p i).rank) = Pi.single (Fin.last j) (Fintype.card J) := by
    funext i
    by_cases hi : i = Fin.last j
    · subst i; simp [initial]
    · simp [initial, hi]
  unfold potential
  rw [hr, layerRankPotential_initial]

theorem initial_value (p : VectorPolynomial I ℝ (J → ℝ)) (x : I → ℝ) :
    (initial (j := j) p).value x = eval x p := by
  have hv (i : Fin (j + 1)) : (initial p i).value x = if i = Fin.last j then eval x p else 0 := by
    by_cases hi : i = Fin.last j <;> simp [initial, hi]
  unfold value
  simp only [hv, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem initial_sized (p : VectorPolynomial I ℝ (J → ℝ)) :
    (initial (j := j) p).Sized (Fintype.card J) 0 := by
  intro i
  by_cases hi : i = Fin.last j
  · simp only [initial, hi, ite_true]
    change Fintype.card J ≤ _ ∧ Fintype.card J ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp
  · simp only [initial, hi, ite_false]
    change Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp

theorem initial_heights (p : VectorPolynomial I ℝ (J → ℝ))
    {budget : ℝ} {R : ℕ} (hbudget : 0 ≤ budget) (hp : DegreeLE (fun _ => 1) (j + 1) p) :
    (initial (j := j) p).PreparedHeights budget R := by
  intro i
  by_cases hi : i = Fin.last j
  · subst i
    simpa only [initial, ite_true, Fin.val_last] using
      RankPreparationLayer.initial_valid p (preparationHeight_pos hbudget _) hp
  · simpa only [initial, hi, ite_false] using
      (RankPreparationLayer.empty_valid (I := I) (J := J) (i.val + 1)
        (preparationHeight budget (j + 1 - 1 - i.val)) R)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationLayer

theorem empty_samplingRank {I J : Type} (d : ℕ) (T : I → ℝ) (R : ℝ) :
    HasLayerSamplingRank d T R (empty : RankPreparationLayer I J).space
      (empty : RankPreparationLayer I J).poly := by
  intro a _ hw
  obtain ⟨w, hw⟩ := hw
  exact (hw (Finset.sum_eq_zero (fun j _ => j.elim))).elim

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

noncomputable def pad (L : RankPreparationFamily I J m) (q : ℕ) :
    RankPreparationFamily I J q := fun j =>
  if hj : j.val < m then L ⟨j.val, hj⟩ else RankPreparationLayer.empty

@[simp] theorem pad_apply_lt (L : RankPreparationFamily I J m) (j : Fin q)
    (hj : j.val < m) : L.pad q j = L ⟨j.val, hj⟩ := by
  simp only [pad, dite_eq_left hj]

@[simp] theorem pad_apply_ge (L : RankPreparationFamily I J m) (j : Fin q)
    (hj : m ≤ j.val) : L.pad q j = RankPreparationLayer.empty := by
  simp only [pad, dite_eq_right (by omega : ¬j.val < m)]

@[simp] theorem pad_apply_castLE (L : RankPreparationFamily I J m) (hmq : m ≤ q)
    (j : Fin m) : L.pad q (j.castLE hmq) = L j := by
  simp only [pad, Fin.val_castLE, dite_eq_left j.isLt]

theorem pad_valid (L : RankPreparationFamily I J m) (H : ℕ → ℕ)
    (R : ℕ) (hL : ∀ j, (L j).Valid (j.val + 1) (H j.val) R) :
    ∀ j, (L.pad q j).Valid (j.val + 1) (H j.val) R := by
  intro j
  by_cases hj : j.val < m
  · simpa only [pad_apply_lt L j hj] using hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact RankPreparationLayer.empty_valid _ _ _

theorem PreparedHeights.pad {L : RankPreparationFamily I J m} {p : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (hmq : m ≤ q) (hp : 0 ≤ p) :
    (L.pad q).PreparedHeights p R := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact (hL ⟨j.val, hj⟩).mono_height
      (preparationHeight_mono hp (by change m - 1 - j.val ≤ q - 1 - j.val; omega))
  · rw [pad_apply_ge L j (by omega)]
    exact RankPreparationLayer.empty_valid _ _ _

theorem pad_samplingRank (L : RankPreparationFamily I J m) (T : I → ℝ) (R : ℝ)
    (hL : ∀ j, HasLayerSamplingRank (j.val + 1) T R (L j).space (L j).poly) :
    ∀ j, HasLayerSamplingRank (j.val + 1) T R (L.pad q j).space
      (L.pad q j).poly := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact RankPreparationLayer.empty_samplingRank _ _ _

theorem pad_degreeLE (L : RankPreparationFamily I J m)
    (hL : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly) :
    ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L.pad q j).poly := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact (RankPreparationLayer.empty_valid _ 0 0).1

theorem pad_coefficients_mem (L : RankPreparationFamily I J m)
    (hL : ∀ j α, coefficients (L j).poly α ∈ (L j).space) :
    ∀ j α, coefficients (L.pad q j).poly α ∈ (L.pad q j).space := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact (RankPreparationLayer.empty_valid 0 0 0).2.1

theorem pad_coordinate_card_le (L : RankPreparationFamily I J m) {M : ℕ}
    (hL : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∀ j, Fintype.card (L.pad q j).Coord ≤ M := by
  intro j
  by_cases hj : j.val < m
  · simpa only [pad_apply_lt L j hj] using hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ M
    simp

theorem Sized.pad {L : RankPreparationFamily I J m} {D t : ℕ}
    (hL : L.Sized D t) (hmq : m ≤ q) : (L.pad q).Sized D t := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    obtain ⟨hc, hb, hr⟩ := hL ⟨j.val, hj⟩
    exact ⟨hc.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by omega)
      (by change m - 1 - j.val ≤ q - 1 - j.val; omega))), hb, hr⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _ ∧ Fintype.card PEmpty ≤ _
    simp

theorem pad_sum {V : Type*} [AddCommMonoid V]
    (L : RankPreparationFamily I J m) (hmq : m ≤ q)
    (f : RankPreparationLayer I J → V) (hf : f RankPreparationLayer.empty = 0) :
    (∑ j, f (L.pad q j)) = ∑ j, f (L j) := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE hmq)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin q => k.val) hij))
  · intro j hj
    have hge : m ≤ j.val := by
      by_contra hnot
      have hlt : j.val < m := by omega
      exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    rw [pad_apply_ge L j hge, hf]
  · intro j
    rw [pad_apply_castLE]

@[simp] theorem pad_value [DecidableEq J] (L : RankPreparationFamily I J m)
    (hmq : m ≤ q) (x : I → ℝ) : (L.pad q).value x = L.value x :=
  pad_sum L hmq (fun layer => layer.value x) (RankPreparationLayer.empty_value x)

theorem pad_coordinate_card (L : RankPreparationFamily I J m) (hmq : m ≤ q) :
    Fintype.card (Σ j, (L.pad q j).Coord) = Fintype.card (Σ j, (L j).Coord) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  exact pad_sum L hmq (fun layer => Fintype.card layer.Coord)
    (Fintype.card_eq_zero_iff.mpr ⟨fun i => i.elim⟩)

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators

namespace RankPreparationLayer

variable {I J : Type} (L : RankPreparationLayer I J)

noncomputable def euclideanEquiv : euclideanSubspace L.space ≃ₗ[ℝ] L.space :=
  (euclideanSubspaceArrayEquiv L.space).toLinearEquiv.trans
    (LinearEquiv.piUnique ℝ (fun _ : Unit => L.space))

theorem euclidean_finrank : finrank ℝ (euclideanSubspace L.space) = L.rank :=
  L.euclideanEquiv.finrank_eq

theorem rank_add_orthogonal_finrank :
    L.rank + finrank ℝ (euclideanSubspace L.space)ᗮ = Fintype.card L.Coord := by
  rw [← L.euclidean_finrank, Submodule.finrank_add_finrank_orthogonal, finrank_euclideanSpace]

theorem lattice_full {d H R : ℕ} (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)) :=
  jointRationalSpaceLattice_full L.basis L.rows hH hR hL.2.2.1 hL.2.2.2

theorem exists_uniform_chart {d H R : ℕ} (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R)
    {p : ℝ} (hC : (Fintype.card L.Coord : ℝ) ≤ p) :
    ∃ b : Basis (Fin (finrank ℝ (euclideanSubspace L.space)ᗮ)) ℝ (euclideanSubspace L.space)ᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace L.space) ∧
      (∀ z, ‖normalizedOrthogonalChart (euclideanSubspace L.space) b z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ z, ‖(normalizedOrthogonalChart (euclideanSubspace L.space) b).symm z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      0 ≤ mixedDensityCovolumeRatio (euclideanSubspace L.space) b ∧
      mixedDensityCovolumeRatio (euclideanSubspace L.space) b ≤ Real.exp (allocatedUniformChartLog p) := by
  let := L.lattice_full hL hH hR
  exact exists_uniform_projected_chart (euclideanSubspace L.space) hC

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s)

theorem PreparedHeights.lattice_full {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (i : Fin s) :
    IsZLattice ℝ (latticeSection (standardEuclideanLattice (L i).Coord)
      (euclideanSubspace (L i).space)) :=
  (L i).lattice_full (hL i) (preparationHeight_pos hp _) hR

theorem PreparedHeights.coefficientTorus_compact {K : Type*} [Fintype K]
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R) :
    CompactSpace (CoefficientTorus (K := K) (fun i => (L i).space)) := by
  let := fun i => hL.lattice_full L hp hR i
  exact coefficientTorus_compact_of_lattice (fun i => (L i).space)

theorem PreparedHeights.exists_uniform_charts {p c : ℝ} {R : ℕ}
    (hL : L.PreparedHeights p R) (hp : 0 ≤ p) (hR : 1 ≤ R)
    (hC : ∀ i, (Fintype.card (L i).Coord : ℝ) ≤ c) :
    ∃ b : ∀ i, Basis (Fin (finrank ℝ (euclideanSubspace (L i).space)ᗮ)) ℝ
        (euclideanSubspace (L i).space)ᗮ,
      (∀ i, span ℤ (Set.range (b i)) = projectedIntegerLattice (euclideanSubspace (L i).space)) ∧
      (∀ i z, ‖normalizedOrthogonalChart (euclideanSubspace (L i).space) (b i) z‖ ≤
        Real.exp (allocatedUniformChartLog c) * ‖z‖) ∧
      (∀ i z, ‖(normalizedOrthogonalChart (euclideanSubspace (L i).space) (b i)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog c) * ‖z‖) ∧
      (∀ i, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L i).space) (b i) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L i).space) (b i) ≤
          Real.exp (allocatedUniformChartLog c)) := by
  let := fun i => hL.lattice_full L hp hR i
  exact exists_allocated_uniform_charts (fun i => (L i).space) hC

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule

variable {X J E : Type} [Fintype E] (L : RankPreparationLayer X J)
variable [IsZLattice ℝ
  (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))]

noncomputable def integralCoordinateBasis
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    Basis E ℝ L.space :=
  (bW.ofZLatticeBasis ℝ _).map L.euclideanEquiv

theorem integralCoordinateBasis_card
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    Fintype.card E = L.rank :=
  (Module.finrank_eq_card_basis (L.integralCoordinateBasis bW)).symm

omit [Fintype E] in
theorem integralCoordinateBasis_integer
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)))
    (i : L.Coord) (e : E) :
    ∃ z : ℤ, (L.integralCoordinateBasis bW e).val i = (z : ℝ) := by
  have h := (mem_standardEuclideanLattice L.Coord (bW e).val.val).mp (bW e).property i
  obtain ⟨z, hz⟩ := h
  refine ⟨z, ?_⟩
  change ((bW.ofZLatticeBasis ℝ _) e).val i = (z : ℝ)
  rw [Basis.ofZLatticeBasis_apply]
  exact hz.symm

noncomputable def integralCoordinateMatrix
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))) :
    L.Coord → E → ℤ :=
  fun i e => Classical.choose (L.integralCoordinateBasis_integer bW i e)

omit [Fintype E] in
theorem integralCoordinateMatrix_cast [Fintype E]
    (bW : Basis E ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)))
    (i : L.Coord) (e : E) :
    (L.integralCoordinateBasis bW e).val i = (L.integralCoordinateMatrix bW i e : ℝ) :=
  Classical.choose_spec (L.integralCoordinateBasis_integer bW i e)

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox

variable {X J : Type} (L : RankPreparationLayer X J)

noncomputable def shortIntegralBasisNormBound (H R : ℕ) : ℝ :=
  (L.rank : ℝ) * L.rank.factorial * minkowskiSecondConstant L.rank *
    ((Fintype.card L.Coord : ℝ) *
      (jointSpaceGeneratorHeight (Fintype.card L.Coord) (Fintype.card L.Column)
        (Fintype.card L.Row) H R : ℝ) ^ (Fintype.card L.Coord * Fintype.card L.Coord))

theorem exists_short_integral_basis {d H R : ℕ}
    (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R) :
    ∃ bW : Basis (Fin L.rank) ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)),
      ∀ a, ‖(bW a).val‖ ≤ L.shortIntegralBasisNormBound H R := by
  let := L.lattice_full hL hH hR
  obtain ⟨P, hP, hspace⟩ := exists_jointRationalSpace_generators
    L.basis L.rows hH hR hL.2.2.1 hL.2.2.2
  obtain ⟨v, hvspan, hvmem, hvnorm⟩ :=
    exists_bounded_integral_span_of_rational_range P L.space hspace hP
  let o : OrthonormalBasis (Fin L.rank) ℝ (euclideanSubspace L.space) :=
    (stdOrthonormalBasis ℝ (euclideanSubspace L.space)).reindex
      (finCongr L.euclidean_finrank)
  obtain ⟨b, hbspan, _hbprod, hbnorm⟩ := exists_short_euclidean_lattice_basis
    (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))
    o v hvspan hvmem hvnorm
  refine ⟨integerBasisOfReal _ b hbspan, ?_⟩
  intro a
  rw [integerBasisOfReal_apply]
  exact hbnorm a

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3

open Module Submodule

theorem basisAxisScale_jointRationalSpace_le_exp
    {J C V K : Type*} [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) {H R : ℕ}
    (hH : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ v j, RationalHeightLE (A v j) R)
    (b : Basis K ℝ (euclideanSubspace (VectorPolynomial.jointRationalSpace B A))ᗮ)
    (hb : span ℤ (Set.range b) =
      projectedIntegerLattice (euclideanSubspace (VectorPolynomial.jointRationalSpace B A)))
    {p : ℝ} (hp : 0 ≤ p)
    (hJ : (Fintype.card J : ℝ) ≤ p) (hC : (Fintype.card C : ℝ) ≤ p)
    (hV : (Fintype.card V : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p)
    (i : K) :
    (basisAxisScale b i : ℝ) ≤ Real.exp ((p+2)^28) := by
  obtain ⟨Q, hQ, hQker⟩ :=
    VectorPolynomial.exists_jointRationalSpace_defining_matrix B A hH hB hA
  have hscale := basisAxisScale_le_of_rational_kernel Q _ hQker hQ b hb i
  have hrow : (Fintype.card (J ⊕ V) : ℝ) ≤ 2*p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith only [hJ, hV]
  have hcol : (Fintype.card J : ℝ) ≤ 2*p := by linarith only [hJ, hp]
  have hheight :
      ((max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R : ℕ) : ℝ) ≤
        Real.exp ((2*p+2)^10) := by
    apply (jointSpaceDefiningHeight_le_exp _ _ H R hp hJ hC hHp hRp).trans
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_left₀ (show 0 ≤ p+2 by positivity) (show p+2 ≤ 2*p+2 by linarith only [hp]) 10
  have hceil := rationalKernelSeparationConstant_ceil_le_exp_power Q
    (show 0 ≤ 2*p by positivity) 10 (by decide) hrow hcol hheight hQ
  have hpower : (2*p+2)^14 ≤ (p+2)^28 := by
    calc
      _ ≤ ((p+2)^2)^14 := pow_le_pow_left₀ (show 0 ≤ 2*p+2 by positivity)
        (show 2*p+2 ≤ (p+2)^2 by nlinarith only [hp, sq_nonneg p]) 14
      _ = _ := by rw [← pow_mul]
  calc
    _ ≤ (⌈rationalKernelAxisBound Q
        (max (imageDefiningHeight (Fintype.card C) (Fintype.card J) H) R)⌉₊ : ℝ) :=
      Nat.cast_le.mpr hscale
    _ ≤ Real.exp ((2*p+2)^14) := hceil
    _ ≤ _ := Real.exp_le_exp.mpr hpower

namespace RankPreparationLayer

theorem basisAxisScale_le_exp {X J : Type} (L : RankPreparationLayer X J)
    {degree H R : ℕ} (hL : L.Valid degree H R) (hH : 1 ≤ H)
    {K : Type*} (b : Basis K ℝ (euclideanSubspace L.space)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace L.space))
    {p : ℝ} (hp : 0 ≤ p)
    (hCoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hColumn : (Fintype.card L.Column : ℝ) ≤ p)
    (hRow : (Fintype.card L.Row : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p)
    (i : K) :
    (basisAxisScale b i : ℝ) ≤ Real.exp ((p+2)^28) :=
  basisAxisScale_jointRationalSpace_le_exp L.basis L.rows hH hL.2.2.1 hL.2.2.2
    b hb hp hCoord hColumn hRow hHp hRp i

end RankPreparationLayer

end Erdos3

end

end OAI

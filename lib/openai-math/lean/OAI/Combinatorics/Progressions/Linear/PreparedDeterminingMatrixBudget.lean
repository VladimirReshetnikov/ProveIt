import OAI.Combinatorics.Progressions.Estimates.PreparedCenteredDeterminingSlots

namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

theorem determiningMatrix_row_abs_sum (r : L.PreparedCoordinate) :
    (∑ a : L.DeterminingIndex E, |(L.determiningMatrix bW r a : ℝ)|) =
      ∑ a : E r.1, |((L r.1).integralCoordinateBasis (bW r.1) a).val r.2| := by
  classical
  rw [Fintype.sum_sigma]
  have heq (u : Fin m) :
      (∑ a : E u, |(L.determiningMatrix bW r ⟨u, a⟩ : ℝ)|) =
      if h : u = r.1 then
        ∑ a : E r.1, |((L r.1).integralCoordinateBasis (bW r.1) a).val r.2|
      else 0 := by
    by_cases h : u = r.1
    · subst u
      simp only [determiningMatrix, ↓reduceDIte,
        (L r.1).integralCoordinateMatrix_cast (bW r.1)]
    · simp [determiningMatrix, h]
  simp_rw [heq]
  exact Fintype.sum_dite_eq' _ _

theorem sortedDeterminingMatrix_row_abs_sum {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) =
      ∑ a : E (e i).1, |((L (e i).1).integralCoordinateBasis (bW (e i).1) a).val (e i).2| := by
  change (∑ a, |(L.determiningMatrix bW (e i) (sortedLayerCoordinateEquiv E a) : ℝ)|) = _
  rw [sum_sortedLayerCoordinateEquiv E (fun a => |(L.determiningMatrix bW (e i) a : ℝ)|)]
  exact L.determiningMatrix_row_abs_sum bW (e i)

theorem sortedDeterminingMatrix_row_abs_sum_le {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {B : ℝ}
    (hB : ∀ a : E (e i).1,
      |((L (e i).1).integralCoordinateBasis (bW (e i).1) a).val (e i).2| ≤ B) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤ (L (e i).1).rank * B := by
  rw [L.sortedDeterminingMatrix_row_abs_sum bW e i]
  calc
    _ ≤ ∑ _a : E (e i).1, B := Finset.sum_le_sum (fun a _ => hB a)
    _ = (L (e i).1).rank * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        (L (e i).1).integralCoordinateBasis_card (bW (e i).1)]

theorem sortedDeterminingMatrix_row_abs_sum_le_of_basis_norm {n : ℕ}
    (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) {B : ℝ}
    (hB : ∀ a : E (e i).1, ‖(bW (e i).1 a).val‖ ≤ B) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤ (L (e i).1).rank * B := by
  apply L.sortedDeterminingMatrix_row_abs_sum_le bW e i
  intro a
  change |(((bW (e i).1).ofZLatticeBasis ℝ _) a).val (e i).2| ≤ B
  rw [Basis.ofZLatticeBasis_apply]
  have hcoord := PiLp.norm_apply_le (bW (e i).1 a).val.val (e i).2
  rw [Real.norm_eq_abs] at hcoord
  exact hcoord.trans (hB a)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox
open scoped BigOperators

namespace RankPreparationLayer

variable {X J : Type} (L : RankPreparationLayer X J)

theorem rank_le_coord_card : L.rank ≤ Fintype.card L.Coord := by
  have h := L.rank_add_orthogonal_finrank
  omega

attribute [local irreducible] rank

theorem shortIntegralBasisNormBound_le_exp {H R : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hcoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hcols : (Fintype.card L.Column : ℝ) ≤ p)
    (hrows : (Fintype.card L.Row : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    L.shortIntegralBasisNormBound H R ≤ Real.exp ((p + 2) ^ 124) := by
  have hrank : (L.rank : ℝ) ≤ p :=
    (Nat.cast_le.mpr L.rank_le_coord_card).trans hcoord
  have hgen := jointSpaceGeneratorHeight_le_exp
    (Fintype.card L.Coord) (Fintype.card L.Column) (Fintype.card L.Row) H R
    hp hcoord hcols hrows hH hR
  have hfront : (L.rank : ℝ) * L.rank.factorial * minkowskiSecondConstant L.rank ≤
      Real.exp (4 * (p + 1) ^ 2) := by
    calc
      _ ≤ projectedAxisNormBudget L.rank := by
        unfold projectedAxisNormBudget
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (show (L.rank : ℝ) ≤ L.rank + 1 by linarith) (Nat.cast_nonneg _))
          (minkowskiSecondConstant_nonneg L.rank)
      _ ≤ Real.exp (4 * ((L.rank : ℝ) + 1) ^ 2) := projectedAxisNormBudget_le_exp L.rank
      _ ≤ _ := Real.exp_le_exp.mpr (by gcongr)
  have hcoordexp : (Fintype.card L.Coord : ℝ) ≤ Real.exp p :=
    hcoord.trans (by linarith only [Real.add_one_le_exp p])
  have hpow :
      (jointSpaceGeneratorHeight (Fintype.card L.Coord) (Fintype.card L.Column)
        (Fintype.card L.Row) H R : ℝ) ^ (Fintype.card L.Coord * Fintype.card L.Coord) ≤
      Real.exp (p ^ 2 * (p + 2) ^ 120) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hgen _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_mul]
    calc
      (Fintype.card L.Coord : ℝ) * Fintype.card L.Coord * (p + 2) ^ 120 ≤
          (p * p) * (p + 2) ^ 120 := by gcongr
      _ = _ := by rw [pow_two]
  have hnorm : L.shortIntegralBasisNormBound H R ≤
      Real.exp (4 * (p + 1) ^ 2 + p + p ^ 2 * (p + 2) ^ 120) := by
    unfold shortIntegralBasisNormBound
    calc
      _ ≤ Real.exp (4 * (p + 1) ^ 2) *
          (Real.exp p * Real.exp (p ^ 2 * (p + 2) ^ 120)) := by
        apply mul_le_mul hfront (mul_le_mul hcoordexp hpow (by positivity)
          (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [Real.exp_add, Real.exp_add, mul_assoc]
  apply hnorm.trans (Real.exp_le_exp.mpr ?_)
  have hbase : 1 ≤ p + 2 := by linarith
  have hsmall : 4 * (p + 1) ^ 2 + p ≤ 5 * (p + 2) ^ 2 := by nlinarith
  have hcube : (5 : ℝ) ≤ (p + 2) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : (2 : ℝ) ≤ p + 2) 3
    norm_num at h
    linarith
  have hsmall' : 4 * (p + 1) ^ 2 + p ≤ (p + 2) ^ 5 := by
    apply hsmall.trans
    calc
      5 * (p + 2) ^ 2 ≤ (p + 2) ^ 3 * (p + 2) ^ 2 := by gcongr
      _ = _ := by rw [← pow_add]
  have hmain : p ^ 2 * (p + 2) ^ 120 ≤ (p + 2) ^ 122 := by
    calc
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 120 := by gcongr; linarith
      _ = _ := by rw [← pow_add]
  have hsmall122 := hsmall'.trans (pow_le_pow_right₀ hbase (by decide : 5 ≤ 122))
  calc
    _ ≤ (p + 2) ^ 122 + (p + 2) ^ 122 := add_le_add hsmall122 hmain
    _ = 2 * (p + 2) ^ 122 := (two_mul _).symm
    _ ≤ (p + 2) * (p + 2) ^ 122 := by gcongr; linarith
    _ = (p + 2) ^ 123 := (pow_succ' (p + 2) 122).symm
    _ ≤ (p + 2) ^ 124 := pow_le_pow_right₀ hbase (by decide)

theorem exists_bounded_integral_basis {d H R : ℕ} {p : ℝ}
    (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R)
    (hp : 0 ≤ p) (hcoord : (Fintype.card L.Coord : ℝ) ≤ p)
    (hcols : (Fintype.card L.Column : ℝ) ≤ p)
    (hrows : (Fintype.card L.Row : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hRp : (R : ℝ) ≤ Real.exp p) :
    ∃ bW : Basis (Fin L.rank) ℤ
      (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space)),
      ∀ a, ‖(bW a).val‖ ≤ Real.exp ((p + 2) ^ 124) := by
  obtain ⟨bW, hbW⟩ := L.exists_short_integral_basis hL hH hR
  exact ⟨bW, fun a => (hbW a).trans
    (L.shortIntegralBasisNormBound_le_exp hp hcoord hcols hrows hHp hRp)⟩

end RankPreparationLayer

def preparedIntegralBasisExponent (m : ℕ) : ℕ :=
  (budgetDepthExponent 38 m + 2) * 124

namespace RankPreparationFamily

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_bounded_integral_bases
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hcols : ∀ j, (Fintype.card (L j).Column : ℝ) ≤ p)
    (hrows : ∀ j, (Fintype.card (L j).Row : ℝ) ≤ p) :
    ∃ bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)),
      ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  let q := (p + 2) ^ budgetDepthExponent 38 m
  have hpq : p ≤ q := le_power_budget hp (preparationExponent_pos m)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hheight (j : Fin m) :
      (preparationHeight p (m - 1 - j.val) : ℝ) ≤ Real.exp q :=
    (Nat.cast_le.mpr (preparationHeight_mono hp (by omega : m - 1 - j.val ≤ m))).trans
      (preparationHeight_le_exp p m)
  have hRpq : (R : ℝ) ≤ Real.exp q := hRp.trans (Real.exp_le_exp.mpr hpq)
  have heach (j : Fin m) := (L j).exists_bounded_integral_basis
    (hL j) (preparationHeight_pos hp _) hR hq
    ((hcoord j).trans hpq) ((hcols j).trans hpq) ((hrows j).trans hpq)
    (hheight j) hRpq
  choose bW hbW using heach
  refine ⟨bW, fun j a => (hbW j a).trans (Real.exp_le_exp.mpr ?_)⟩
  exact shifted_power_budget_le hp (budgetDepthExponent 38 m) 124

theorem PreparedHeights.exists_bounded_integral_bases_of_sized
    {p : ℝ} {R D t T : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hsize : L.Sized D t) (ht : t ≤ T)
    (hcap : (preparationCoordinateCap m D T : ℝ) ≤ p) :
    ∃ bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)),
      ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) := by
  apply hL.exists_bounded_integral_bases L hp hR hRp
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).1).trans hcap
  · intro j
    exact (Nat.cast_le.mpr (preparationCoordinateCap_bounds hsize ht j).2.1).trans hcap
  · intro j
    have h := (preparationCoordinateCap_bounds hsize ht j).2.2
    exact (Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ _) h)).trans hcap

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space))]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (L j).Coord) (euclideanSubspace (L j).space)))

theorem sortedDeterminingMatrix_row_abs_sum_le_exp {p : ℝ}
    (hp : 0 ≤ p) (hcoord : ∀ j, (Fintype.card (L j).Coord : ℝ) ≤ p)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤ Real.exp ((p + 2) ^ preparedIntegralBasisExponent m))
    {n : ℕ} (e : Fin n ≃ L.PreparedCoordinate) (i : Fin n) :
    (∑ a, |(L.sortedDeterminingMatrix bW e i a : ℝ)|) ≤
      Real.exp ((p + 2) ^ (preparedIntegralBasisExponent m + 1)) := by
  have hrank : ((L (e i).1).rank : ℝ) ≤ p :=
    (Nat.cast_le.mpr (L (e i).1).rank_le_coord_card).trans (hcoord (e i).1)
  have hrankexp : ((L (e i).1).rank : ℝ) ≤ Real.exp p :=
    hrank.trans (by linarith only [Real.add_one_le_exp p])
  have hpower : p ≤ (p + 2) ^ preparedIntegralBasisExponent m :=
    le_power_budget hp (by unfold preparedIntegralBasisExponent; omega)
  calc
    _ ≤ (L (e i).1).rank * Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) :=
      L.sortedDeterminingMatrix_row_abs_sum_le_of_basis_norm bW e i (hbW (e i).1)
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ preparedIntegralBasisExponent m) :=
      mul_le_mul_of_nonneg_right hrankexp (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ preparedIntegralBasisExponent m) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      calc
        _ ≤ 2 * (p + 2) ^ preparedIntegralBasisExponent m := by linarith only [hpower]
        _ ≤ (p + 2) * (p + 2) ^ preparedIntegralBasisExponent m := by gcongr; linarith
        _ = _ := (pow_succ' (p + 2) (preparedIntegralBasisExponent m)).symm)

end Erdos3.RankPreparationFamily

end

end OAI

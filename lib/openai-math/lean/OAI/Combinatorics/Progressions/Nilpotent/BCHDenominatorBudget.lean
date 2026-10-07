import OAI.Combinatorics.Progressions.Geometry.LieCoordinateHeight
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
import OAI.Combinatorics.Progressions.Polynomial.RationalPolynomialGrid
import OAI.Combinatorics.Progressions.Sampling.ConjugationGridBudget

namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchCoordinateDenominator (e : Basis ι ℚ L) (s : ℕ) : ℕ :=
  polynomialFamilyDenominator (bchCoordinatePolynomial (lieStructureConstants e) s)

theorem bchCoordinateDenominator_pos (e : Basis ι ℚ L) (s : ℕ) :
    0 < bchCoordinateDenominator e s := polynomialFamilyDenominator_pos _

theorem lieBCH_mem_denominatorGrid (e : Basis ι ℚ L) (s q : ℕ) (a b : L)
    (ha : e.equivFun a ∈ denominatorGrid q) (hb : e.equivFun b ∈ denominatorGrid q) :
    e.equivFun (lieBCH s a b) ∈ denominatorGrid (bchCoordinateDenominator e s * q ^ s) := by
  have h := polynomial_family_rational_values_grid
    (bchCoordinatePolynomial (lieStructureConstants e) s) q s
    (bchCoordinatePolynomial_totalDegree _ s)
    (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2)
    (pairInput_mem_denominatorGrid (e.equivFun a) (e.equivFun b) q ha hb)
  have he : (fun k => MvPolynomial.eval
      (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2)
      (bchCoordinatePolynomial (lieStructureConstants e) s k)) = e.equivFun (lieBCH s a b) := by
    funext k
    have hi : (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2) =
        (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2) := by
      funext xi
      rcases xi with ⟨i, j⟩
      fin_cases i <;> rfl
    rw [hi]
    exact bchCoordinatePolynomial_eval e s a b k
  rw [he] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem lieCoordinateHeight_le_exp (d H n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (lieCoordinateHeight d H n : ℝ) ≤ Real.exp ((p + 2) ^ (3 * n + 2)) := by
  have hd2 : (d : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg d) hd 2
  have hpexp : Real.exp p ≤ Real.exp (p ^ 2 + 1) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p - 1)])
  have hsmall : (d : ℝ) ^ 2 + 2 ≤ Real.exp (p ^ 2 + 1) := by
    have h := Real.add_one_le_exp (p ^ 2 + 1)
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hbase : (d : ℝ) ^ 2 + H + 2 ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ 2 * Real.exp (p ^ 2 + 1) := by linarith [hH.trans hpexp]
      _ ≤ Real.exp 1 * Real.exp (p ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (p ^ 2 + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hexponent : ((2 * d ^ 2 + 2) ^ n : ℕ) ≤ (p + 2) ^ (3 * n) := by
    push_cast
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [pow_nonneg hp 3]
  unfold lieCoordinateHeight
  push_cast
  calc
    _ ≤ (Real.exp ((p + 2) ^ 2)) ^ ((2 * d ^ 2 + 2) ^ n) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((((2 * d ^ 2 + 2) ^ n : ℕ) : ℝ) * (p + 2) ^ 2) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (3 * n) * (p + 2) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexponent (by positivity))
    _ = _ := by rw [pow_add]

theorem bchCoordinateHeight_le_exp (s d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hc : (bchCoefficientHeight s : ℝ) ≤ Real.exp p)
    (hm : ((bchBracketSupport s).card : ℝ) ≤ p) :
    (bchCoordinateHeight s d H : ℝ) ≤ Real.exp ((p + 2) ^ (3 * s + 5)) := by
  have hlie := lieCoordinateHeight_le_exp d H s hp hd hH
  have hpbudget : p ≤ (p + 2) ^ (3 * s + 2) := le_power_budget hp (by omega)
  have hprod : ((bchCoefficientHeight s * lieCoordinateHeight d H s : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ (3 * s + 3)) := by
    push_cast
    calc
      _ ≤ Real.exp ((p + 2) ^ (3 * s + 2)) * Real.exp ((p + 2) ^ (3 * s + 2)) :=
        mul_le_mul (hc.trans (Real.exp_le_exp.mpr hpbudget)) hlie
          (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + 2) ^ (3 * s + 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show 3 * s + 3 = (3 * s + 2) + 1 by omega,
          pow_succ (p + 2) (3 * s + 2)]
        nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) (3 * s + 2)]
  have hcard : ((bchBracketSupport s).card : ℝ) ≤ (p + 2) ^ 1 := by
    rw [pow_one]
    linarith
  exact rational_sum_cost_le_exp (bchBracketSupport s).card
    (bchCoefficientHeight s * lieCoordinateHeight d H s) hp (3 * s + 3) 1 hprod hcard

theorem exists_bchCoordinateHeight_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (bchCoordinateHeight s d H : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let C := bchCoefficientHeight s + (bchBracketSupport s).card + 3 * s + 7
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro d H p hp hd hH
  let q : ℝ := p + bchCoefficientHeight s + (bchBracketSupport s).card
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) (bchCoefficientHeight s),
      Nat.cast_nonneg (α := ℝ) (bchBracketSupport s).card]
  have hq : 0 ≤ q := hp.trans hpq
  have hc : (bchCoefficientHeight s : ℝ) ≤ Real.exp q := by
    have h := Real.add_one_le_exp q
    dsimp [q]
    dsimp [q] at h
    linarith [Nat.cast_nonneg (α := ℝ) (bchBracketSupport s).card]
  have hm : ((bchBracketSupport s).card : ℝ) ≤ q := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) (bchCoefficientHeight s)]
  have hbound := bchCoordinateHeight_le_exp s d H hq (hd.trans hpq)
    (hH.trans (Real.exp_le_exp.mpr hpq)) hc hm
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  have hbase : q + 2 ≤ p + C := by
    dsimp [q, C]
    push_cast
    nlinarith
  calc
    (q + 2) ^ (3 * s + 5) ≤ (p + C) ^ (3 * s + 5) :=
      pow_le_pow_left₀ (by linarith) hbase _
    _ ≤ (p + C) ^ C := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)

theorem exists_bch_coordinate_polynomials_exp_height (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Module.Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∃ P : ι → MvPolynomial (Fin 2 × ι) ℚ,
        (∀ (a b : L) k,
          MvPolynomial.aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2) (P k) =
            e.repr (lieBCH s a b) k) ∧
        (∀ k, (P k).totalDegree ≤ s) ∧
        ∀ k m, (((P k).coeff m).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          (((P k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_bchCoordinateHeight_exp_budget s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hc
  refine ⟨bchCoordinatePolynomial (lieStructureConstants e) s,
    bchCoordinatePolynomial_eval e s, bchCoordinatePolynomial_totalDegree _ s, ?_⟩
  intro k m
  have hheight := bchCoordinatePolynomial_height (lieStructureConstants e) hc s k m
  have hbound := hbudget (Fintype.card ι) H p hp hd hH
  constructor
  · exact (Nat.cast_le.mpr hheight.1).trans hbound
  · exact (Nat.cast_le.mpr hheight.2).trans hbound

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bchCoordinateDenominator_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (bchCoordinateDenominator e s : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _, hc⟩ := exists_bchCoordinateHeight_exp_budget s
  let R : Polynomial ℕ :=
    (2 * Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c + Polynomial.C (s + 3)) ^ (s + 3)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hstructure
  let q : ℝ := 2 * p + (p + c) ^ c
  have hpower : 0 ≤ (p + c) ^ c := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hheight := hc (Fintype.card ι) H p hp hd hH
  have hcoeff : ∀ i α, (((bchCoordinatePolynomial (lieStructureConstants e) s i).coeff α).den : ℝ) ≤
      Real.exp q := by
    intro i α
    exact (Nat.cast_le.mpr (bchCoordinatePolynomial_height (lieStructureConstants e) hstructure s i α).2).trans
      (hheight.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith)))
  have hinputs : (Fintype.card (Fin 2 × ι) : ℝ) ≤ q := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [q]
    linarith
  have hD := polynomialFamilyDenominator_degree_budget (bchCoordinatePolynomial (lieStructureConstants e) s)
    s (bchCoordinatePolynomial_totalDegree _ s) hq (hd.trans hpq) hinputs hcoeff
  have hpoly : (q + (s + 3)) ^ (s + 3) ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact hD.trans (Real.exp_le_exp.mpr hpoly)

theorem exists_bch_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ q ∣ m ∧
        ∀ a b : L, e.equivFun a ∈ denominatorGrid q → e.equivFun b ∈ denominatorGrid q →
          e.equivFun (lieBCH s a b) ∈ denominatorGrid m := by
  obtain ⟨K, _, hK⟩ := exists_bchCoordinateDenominator_exp_budget s
  refine ⟨K + s + 5, by omega, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hstructure q hq hqp
  let D := bchCoordinateDenominator e s
  let m := q * D * q ^ s
  have hD : 0 < D := bchCoordinateDenominator_pos e s
  have hqm : q ∣ m := ⟨D * q ^ s, Nat.mul_assoc q D (q ^ s)⟩
  have hDm : D * q ^ s ∣ m := ⟨q,
    (Nat.mul_assoc q D (q ^ s)).trans (Nat.mul_comm q (D * q ^ s))⟩
  refine ⟨m, Nat.mul_pos (Nat.mul_pos hq hD) (pow_pos hq _), ?_, hqm, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using conjugation_grid_allowance_le_exp K s q D q hp hqp
      (hK e H p hp hd hH hstructure) hqp
  · intro a b ha hb
    exact denominatorGrid_subset_of_dvd hDm (lieBCH_mem_denominatorGrid e s q a b ha hb)

end Erdos3

end

end OAI

import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Dynamics.ConjugationDenominatorBudget
import OAI.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH

namespace OAI

section

namespace Erdos3

open Module MvPolynomial

theorem polynomial_period_cost_le_exp (K r s l D Q : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hD : (D : ℝ) ≤ Real.exp ((p + K) ^ K))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3))) :
    (((l * D * Q ^ s) * Q : ℕ) : ℝ) ≤
      Real.exp ((p + (K + r + s + 10)) ^ (K + r + s + 10)) := by
  let C := K + r + s + 10
  let t := p + C
  have ht : 3 ≤ t := by
    dsimp [t, C]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) s]
  have hC : 1 ≤ C := by dsimp [C]; omega
  have hpT : p ≤ t ^ (C - 1) := by
    apply (show p ≤ t by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) C; linarith).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) (show 1 ≤ C - 1 by dsimp [C]; omega)
  have hDT : (p + K) ^ K ≤ t ^ (C - 1) := by
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + K) (show p + K ≤ t by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) s]) K).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hQT : ((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3) ≤ t ^ (C - 1) := by
    have hs : (s : ℝ) + 1 ≤ t := by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) r]
    have hr : p + (r + 3) ≤ t := by
      dsimp [t, C]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) s]
    calc
      _ ≤ t * t ^ (r + 3) := mul_le_mul hs (pow_le_pow_left₀ (by positivity) hr _) (by positivity) (by linarith)
      _ = t ^ (r + 4) := (pow_succ' _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  have hQpow : (Q : ℝ) ^ (s + 1) ≤ Real.exp (((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) := by
    simpa only [← Real.exp_nat_mul, Nat.cast_add, Nat.cast_one] using
      pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ (s + 1)
  push_cast
  calc
    _ = (l : ℝ) * D * (Q : ℝ) ^ (s + 1) := by rw [pow_succ]; ring
    _ ≤ Real.exp p * Real.exp ((p + K) ^ K) *
        Real.exp (((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) :=
      mul_le_mul (mul_le_mul hl hD (by positivity) (by positivity)) hQpow (by positivity) (by positivity)
    _ = Real.exp (p + (p + K) ^ K + ((s : ℝ) + 1) * (p + (r + 3)) ^ (r + 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (t ^ C) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 3 * t ^ (C - 1) := by linarith
        _ ≤ t * t ^ (C - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hC]
    _ = _ := by simp [t, C]

theorem exists_polynomial_BCH_period_exp_bound (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ)
      (P : ι → MvPolynomial σ ℚ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i, (P i).totalDegree ≤ r) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp p) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ x y : σ → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
          (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
            QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + r + s + 10, by omega, ?_⟩
  intro ι σ L _ _ _ _ e hnil Γ l H P p hl hinner hdegree hp hd hn hH hlb hc hP
  refine ⟨polynomialBCHPeriod e s l P, polynomialBCHPeriod_pos e s l P hl, ?_, ?_⟩
  · simpa only [polynomialBCHPeriod, Nat.cast_add, Nat.cast_ofNat] using
      polynomial_period_cost_le_exp K r s l _ _ hp hlb (hden e H p hp hd hH hc)
        (polynomialFamilyDenominator_degree_budget P r hdegree hp hd hn hP)
  · intro x y hxy
    exact polynomialBCHMap_coset_eq e hnil Γ l r P hdegree hinner x y hxy

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial

theorem exists_factor_through_integer_reduction {σ α : Type*}
    (f : (σ → ℤ) → α) (M : ℕ)
    (hf : ∀ x y, (∀ i, (M : ℤ) ∣ x i - y i) → f x = f y) :
    ∃ F : (σ → ZMod M) → α, ∀ x, F (fun i => (x i : ZMod M)) = f x := by
  classical
  let lift : (σ → ZMod M) → σ → ℤ := fun x i => Classical.choose (ZMod.intCast_surjective (x i))
  have hlift (x : σ → ZMod M) (i : σ) : (lift x i : ZMod M) = x i :=
    Classical.choose_spec (ZMod.intCast_surjective (x i))
  refine ⟨fun x => f (lift x), ?_⟩
  intro x
  apply hf
  intro i
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (lift (fun j => (x j : ZMod M)) i) M).mp
  exact (hlift (fun j => (x j : ZMod M)) i).symm

theorem exists_polynomial_BCH_finite_quotient (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ)
      (P : ι → MvPolynomial σ ℚ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i, (P i).totalDegree ≤ r) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp p) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ F : (σ → ZMod M) → (NilpotentLieBCHGroup L s hnil ⧸ Γ),
          ∀ x : σ → ℤ, F (fun j => (x j : ZMod M)) = QuotientGroup.mk (polynomialBCHMap e hnil P x) := by
  obtain ⟨C, hC, hperiod⟩ := exists_polynomial_BCH_period_exp_bound s r
  refine ⟨C, hC, ?_⟩
  intro ι σ L _ _ _ _ e hnil Γ l H P p hl hinner hdegree hp hd hn hH hlb hc hP
  obtain ⟨M, hM, hMb, hcong⟩ := hperiod e hnil Γ l H P p hl hinner hdegree hp hd hn hH hlb hc hP
  exact ⟨M, hM, hMb, exists_factor_through_integer_reduction
    (fun x => (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ)) M hcong⟩

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial

theorem polynomialDenominator_dvd_power {σ : Type*} (P : MvPolynomial σ ℚ)
    (q N : ℕ) (hden : ∀ α, (P.coeff α).den ∣ q) (hcard : P.support.card ≤ N) :
    polynomialDenominator P ∣ q ^ N := by
  classical
  have h : polynomialDenominator P ∣ q ^ P.support.card := by
    unfold polynomialDenominator arrayDenominator
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun α : P.support => (P.coeff α.val).den)
        (fun _ : P.support => q) (fun α _ => hden α.val)
  exact h.trans (pow_dvd_pow q hcard)

theorem polynomialFamilyDenominator_dvd_power {ι σ : Type*} [Fintype ι]
    (P : ι → MvPolynomial σ ℚ) (q N : ℕ)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q) (hcard : ∀ i, (P i).support.card ≤ N) :
    polynomialFamilyDenominator P ∣ q ^ (N * Fintype.card ι) := by
  classical
  unfold polynomialFamilyDenominator
  simpa only [Finset.prod_const, Finset.card_univ, ← pow_mul] using
    Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun i => polynomialDenominator (P i))
      (fun _ : ι => q ^ N) (fun i _ => polynomialDenominator_dvd_power (P i) q N (hden i) (hcard i))

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def uniformPolynomialBCHPeriod (e : Basis ι ℚ L) (s r l q : ℕ) : ℕ :=
  let Q := q ^ (((r + 1) * (Fintype.card σ + 1) ^ r) * Fintype.card ι)
  (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * Q ^ s) * Q

theorem uniformPolynomialBCHPeriod_pos (e : Basis ι ℚ L) (s r l q : ℕ)
    (hl : 0 < l) (hq : 0 < q) : 0 < uniformPolynomialBCHPeriod (σ := σ) e s r l q := by
  unfold uniformPolynomialBCHPeriod
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl (polynomialFamilyDenominator_pos _))
    (pow_pos (pow_pos hq _) _)) (pow_pos hq _)

theorem polynomialBCHPeriod_dvd_uniform (e : Basis ι ℚ L) (s r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q) :
    polynomialBCHPeriod e s l P ∣ uniformPolynomialBCHPeriod (σ := σ) e s r l q := by
  have h := polynomialFamilyDenominator_dvd_power P q ((r + 1) * (Fintype.card σ + 1) ^ r)
    hden (fun i => polynomial_support_card_le (P i) (hdegree i))
  exact mul_dvd_mul (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd h s)) h

theorem polynomialBCHMap_uniform_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x) : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y) := by
  apply polynomialBCHMap_coset_eq e hnil Γ l r P hdegree hinner x y
  intro j
  exact (Int.natCast_dvd_natCast.mpr (polynomialBCHPeriod_dvd_uniform e s r l q P hdegree hden)).trans (hxy j)

theorem polynomialBCHMap_uniform_inverse_coset_eq (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ) (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    (QuotientGroup.mk (polynomialBCHMap e hnil P x)⁻¹ : _ ⧸ Γ) =
      QuotientGroup.mk (polynomialBCHMap e hnil P y)⁻¹ := by
  have hinv (z : σ → ℤ) : polynomialBCHMap e hnil (fun i => -(P i)) z =
      (polynomialBCHMap e hnil P z)⁻¹ := by
    apply NilpotentLieBCHGroup.ext
    change e.equivFun.symm (fun i => eval (fun j => (z j : ℚ)) (-(P i))) =
      -(e.equivFun.symm (fun i => eval (fun j => (z j : ℚ)) (P i)))
    simp only [map_neg, ← Pi.neg_def]
  have h := polynomialBCHMap_uniform_coset_eq e hnil Γ r l q (fun i => -(P i))
    (fun i => by simpa only [totalDegree_neg] using hdegree i)
    (fun i α => by simpa only [coeff_neg, Rat.neg_den] using hden i α)
    hinner x y hxy
  simpa only [hinv] using h

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial
open scoped TensorProduct

theorem exists_real_polynomial_BCH_finite_quotient (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ)
      (P : ι → MvPolynomial σ ℚ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      (∀ i, (P i).totalDegree ≤ r) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp p) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ F : (σ → ZMod M) →
          (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
            ⧸ Γ.map NilpotentLieBCHGroup.realificationHom),
          ∀ x : σ → ℤ, F (fun j => (x j : ZMod M)) =
            QuotientGroup.mk (realPolynomialBCHMap (e.baseChange ℝ) P (fun j => (x j : ℝ))) := by
  obtain ⟨C, hC, hperiod⟩ := exists_polynomial_BCH_period_exp_bound s r
  refine ⟨C, hC, ?_⟩
  intro ι σ L _ _ _ _ e hnil Γ l H P p hl hinner hdegree hp hd hn hH hlb hc hP
  obtain ⟨M, hM, hMb, hcong⟩ := hperiod e hnil Γ l H P p hl hinner hdegree hp hd hn hH hlb hc hP
  refine ⟨M, hM, hMb, exists_factor_through_integer_reduction
    (fun x : σ → ℤ =>
      (QuotientGroup.mk (realPolynomialBCHMap (e.baseChange ℝ) P (fun j => (x j : ℝ))) :
        _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom)) M ?_⟩
  intro x y hxy
  rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer]
  exact realification_coset_eq Γ _ _ (hcong x y hxy)

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial
open scoped TensorProduct

theorem uniformPolynomialBCHPeriod_le_exp {ι σ L : Type*} [Fintype ι] [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) (K s r l q : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hn : (Fintype.card σ : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p) (hq : (q : ℝ) ≤ Real.exp p)
    (hD : (polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) : ℝ) ≤
      Real.exp ((p + K) ^ K)) :
    (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℝ) ≤
      Real.exp ((p + (K + r + s + 10)) ^ (K + r + s + 10)) := by
  let N := ((r + 1) * (Fintype.card σ + 1) ^ r) * Fintype.card ι
  let Q := q ^ N
  let t : ℝ := p + (r + 3)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hdt : (Fintype.card ι : ℝ) ≤ t := hd.trans hpt
  have hnt : (Fintype.card σ : ℝ) + 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hrt : (r : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hlength : (N : ℝ) * p ≤ t ^ (r + 3) := by
    dsimp only [N]
    push_cast
    calc
      _ ≤ t * t ^ r * t * t := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hQ : (Q : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3)) := by
    dsimp only [Q]
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hq N).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hlength
  exact polynomial_period_cost_le_exp K r s l _ Q hp hl hD hQ

theorem exists_uniformPolynomialBCHPeriod_exp_bound (s r : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ L : Type*} [Fintype ι] [Fintype σ]
      [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (l H q : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨K, hK, hden⟩ := exists_conjugation_denominator_exp_bound s
  refine ⟨K + r + s + 10, by omega, ?_⟩
  intro ι σ L _ _ _ _ e l H q p hp hd hn hH hlb hqb hc
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    uniformPolynomialBCHPeriod_le_exp (σ := σ) e K s r l q hp hd hn hlb hqb
    (hden e H p hp hd hH hc)

theorem realPolynomialBCHMap_uniform_cosets {ι σ L : Type*} [Fintype ι] [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hP : ∀ i α, ((P i).coeff α).den ∣ q)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (x y : σ → ℤ)
    (hxy : ∀ j, (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℤ) ∣ x j - y j) :
    let f := fun z : σ → ℤ => realPolynomialBCHMap
      (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ) P
      (fun j => (z j : ℝ))
    ((QuotientGroup.mk (f x) : _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
      QuotientGroup.mk (f y)) ∧
    ((QuotientGroup.mk (f x)⁻¹ : _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
      QuotientGroup.mk (f y)⁻¹) := by
  dsimp only
  constructor
  · rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer]
    exact realification_coset_eq Γ _ _
      (polynomialBCHMap_uniform_coset_eq e hnil Γ r l q P hdegree hP hinner x y hxy)
  · rw [realPolynomialBCHMap_integer, realPolynomialBCHMap_integer,
      ← map_inv, ← map_inv]
    exact realification_coset_eq Γ _ _
      (polynomialBCHMap_uniform_inverse_coset_eq e hnil Γ r l q P hdegree hP hinner x y hxy)

end Erdos3

end

end OAI

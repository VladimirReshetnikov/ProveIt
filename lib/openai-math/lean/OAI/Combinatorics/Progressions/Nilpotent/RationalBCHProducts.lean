import OAI.Combinatorics.Progressions.Lattices.ConjugatedLatticeGrids
import OAI.Combinatorics.Progressions.Sampling.RealGridRationalLift

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_grid_mul (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hmul : ∀ a b : NilpotentLieBCHGroup L s hnil,
      e.equivFun a.coord ∈ denominatorGrid l → e.equivFun b.coord ∈ denominatorGrid l →
      e.equivFun (a * b).coord ∈ denominatorGrid m)
    (a b : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (ha : (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l)
    (hb : (e.baseChange ℝ).equivFun b.coord ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (a * b).coord ∈ realDenominatorGrid m := by
  obtain ⟨aq, haq, heqa⟩ := (realification_grid_iff (hnil := hnil) e l hl a).mp ha
  obtain ⟨bq, hbq, heqb⟩ := (realification_grid_iff (hnil := hnil) e l hl b).mp hb
  rw [← heqa, ← heqb, ← map_mul, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  exact hmul aq bq haq hbq

theorem realification_grid_inv (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hinv : ∀ a : NilpotentLieBCHGroup L s hnil,
      e.equivFun a.coord ∈ denominatorGrid l → e.equivFun (a⁻¹).coord ∈ denominatorGrid m)
    (a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (ha : (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (a⁻¹).coord ∈ realDenominatorGrid m := by
  obtain ⟨aq, haq, heqa⟩ := (realification_grid_iff (hnil := hnil) e l hl a).mp ha
  rw [← heqa, ← map_inv, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  exact hinv aq haq

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_real_bch_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ a b : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun b.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (a * b).coord ∈ realDenominatorGrid m) ∧
        (∀ a : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun a.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (a⁻¹).coord ∈ realDenominatorGrid m) := by
  obtain ⟨C, hC, hbound⟩ := exists_bch_rational_closure s
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hmul⟩ := hbound e H p hp hd hH hc l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_, ?_⟩
  · exact NilpotentLieBCHGroup.realification_grid_mul (hnil := hnil) e l m hl
      (fun a b ha hb => hmul a.coord b.coord ha hb)
  · apply NilpotentLieBCHGroup.realification_grid_inv (hnil := hnil) e l m hl
    intro a ha
    change e.equivFun (-a.coord) ∈ denominatorGrid m
    rw [map_neg]
    exact denominatorGrid_subset_of_dvd hlm (denominatorGrid_neg l ha)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realDenominatorGrid_zero {ι : Type*} (l : ℕ) :
    (0 : ι → ℝ) ∈ realDenominatorGrid l := by
  exact ⟨0, by ext i; simp⟩

theorem realDenominatorGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m) :
    (realDenominatorGrid l : Set (ι → ℝ)) ⊆ realDenominatorGrid m := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := realDenominatorGrid_exists_rational l hl x hx
  exact (real_cast_mem_denominatorGrid_iff m y).mpr (denominatorGrid_subset_of_dvd hlm hy)

theorem exists_real_bch_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (lieStructureConstants e i j z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)),
          rs.length ≤ k →
          (∀ r ∈ rs, (e.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l) →
          (e.baseChange ℝ).equivFun rs.prod.coord ∈ realDenominatorGrid m := by
  induction k with
  | zero =>
    refine ⟨2, by omega, ?_⟩
    intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
    refine ⟨l, hl, hlp.trans (Real.exp_le_exp.mpr (le_power_budget hp (by omega))), dvd_refl l, ?_⟩
    intro rs hlen hrs
    have hrs0 : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simpa only [List.prod_nil, NilpotentLieBCHGroup.coord_one, map_zero] using
      (realDenominatorGrid_zero (ι := ι) l)
  | succ k ih =>
    obtain ⟨K, hK, hprod⟩ := ih
    obtain ⟨J, _, hmul⟩ := exists_real_bch_rational_closure s
    let R : Polynomial ℕ := ((Polynomial.X + Polynomial.C K) ^ K + Polynomial.C J) ^ J
    obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
    refine ⟨C, hC, ?_⟩
    intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
    obtain ⟨m₁, hm₁, hm₁p, hlm₁, hprod₁⟩ := hprod e H p hnil hp hd hH hc l hl hlp
    let q : ℝ := (p + K) ^ K
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hpq : p ≤ q := by
      apply (show p ≤ p + K from le_add_of_nonneg_right (Nat.cast_nonneg K)).trans
      have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
      simpa only [pow_one] using pow_le_pow_right₀
        (show (1 : ℝ) ≤ p + K by linarith) (show 1 ≤ K by omega)
    obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hmul₂, _⟩ := hmul e H q hnil hq (hd.trans hpq)
      (hH.trans (Real.exp_le_exp.mpr hpq)) hc m₁ hm₁ hm₁p
    have hpoly : (q + J) ^ J ≤ (p + C) ^ C := by
      simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
    refine ⟨m₂, hm₂, hm₂p.trans (Real.exp_le_exp.mpr hpoly), hlm₁.trans hm₁m₂, ?_⟩
    intro rs hlen hrs
    cases rs with
    | nil =>
      simpa only [List.prod_nil, NilpotentLieBCHGroup.coord_one, map_zero] using
        (realDenominatorGrid_zero (ι := ι) m₂)
    | cons r rs =>
      rw [List.prod_cons]
      apply hmul₂
      · exact realDenominatorGrid_subset_of_dvd hl hlm₁ (hrs r (List.mem_cons_self))
      · apply hprod₁ rs (Nat.le_of_succ_le_succ hlen)
        exact fun x hx => hrs x (List.mem_cons_of_mem r hx)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_bch_rational_product_bound (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (lieStructureConstants e i j z) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ rs : List (NilpotentLieBCHGroup L s hnil), rs.length ≤ k →
          (∀ r ∈ rs, e.equivFun r.coord ∈ denominatorGrid l) →
          e.equivFun rs.prod.coord ∈ denominatorGrid m := by
  have hrealExists := exists_real_bch_rational_product_bound s k
  obtain ⟨C, hC, hreal⟩ := hrealExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hp hd hH hc l hl hlp
  have hproductsExists := hreal e H p hnil hp hd hH hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hproductsExists
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro rs hlen hrs
  have hinputs : ∀ r ∈ rs.map (realificationHom (hnil := hnil)),
      (e.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid l := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
    exact hrs q hq
  have hout := hproducts (rs.map (realificationHom (hnil := hnil)))
    (by simpa only [List.length_map] using hlen) hinputs
  rw [← map_list_prod, realificationHom_coordinates, real_cast_mem_denominatorGrid_iff] at hout
  exact hout

end Erdos3

end

end OAI

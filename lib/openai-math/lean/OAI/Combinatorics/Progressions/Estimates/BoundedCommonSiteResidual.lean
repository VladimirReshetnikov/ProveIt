/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.CommonIntegerSiteResidual

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def complementaryPeriod {I : Type*} [Fintype I] (q : I → ℕ) (i : I) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, q j

theorem complementaryPeriod_pos {I : Type*} [Fintype I] (q : I → ℕ)
    (hq : ∀ i, 0 < q i) (i : I) : 0 < complementaryPeriod q i :=
  Finset.prod_pos (fun j _ => hq j)

theorem period_mul_complementary {I : Type*} [Fintype I] (q : I → ℕ) (i : I) :
    q i * complementaryPeriod q i = ∏ j, q j :=
  Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)

theorem complementaryPeriod_le_product {I : Type*} [Fintype I] (q : I → ℕ)
    (hq : ∀ i, 0 < q i) (i : I) : complementaryPeriod q i ≤ ∏ j, q j := by
  rw [← period_mul_complementary q i]
  exact Nat.le_mul_of_pos_left _ (hq i)

theorem subspaceArrayCharacter_common_period {I S J : Type*} [Fintype I] [Fintype S] [Fintype J]
    (q : I → ℕ) (hq : ∀ i, 0 < q i) (i : I)
    (U : Submodule ℝ (J → ℝ)) (b : Matrix S J ℤ) (x : S → U) :
    subspaceArrayCharacter U (fun s a => (complementaryPeriod q i : ℤ) * b s a)
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U) (((∏ j, q j : ℕ) : ℝ)⁻¹ • x)) =
    subspaceArrayCharacter U b
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U) ((q i : ℝ)⁻¹ • x)) := by
  rw [← period_mul_complementary q i]
  exact subspaceArrayCharacter_period_multiple U b (q i) (complementaryPeriod q i)
    (hq i) (complementaryPeriod_pos q hq i) x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_bounded_common_site_residual {J S : Type*} [Fintype J] [Fintype S]
    {I : J → Type*} [∀ j, Fintype (I j)] (E : ∀ j, Matrix S (I j) ℤ)
    (H : J → ℕ) (hH : ∀ j, 1 ≤ H j)
    (hE : ∀ j s i, RationalHeightLE (E j s i : ℚ) (H j)) :
    ∃ (d : ℕ) (T : ∀ j, Matrix (I j) S ℤ), 0 < d ∧
      (∀ j {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I j → W),
        matrixModuleAction (fun s i => (E j s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E j s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E j s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (∀ j, (Fintype.card (I j) : ℝ) ≤ P) →
        (Fintype.card S : ℝ) ≤ P → (∀ j, (H j : ℝ) ≤ Real.exp P) →
        (d : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) ∧
          ∀ j i s, |(T j i s : ℝ)| ≤ Real.exp (((Fintype.card J : ℝ) + 2) * (P + 2) ^ 36)) := by
  choose d T hd hT hbound using fun j => exists_bounded_integer_site_residual (E j) (hH j) (hE j)
  let D := ∏ j, d j
  refine ⟨D, fun j i s => (complementaryPeriod d j : ℤ) * T j i s,
    Finset.prod_pos (fun j _ => hd j), ?_, ?_⟩
  · intro j W _ _ x
    rw [matrixModuleAction_int_smul, map_smul, hT j, smul_smul]
    congr 1
    exact_mod_cast (by simpa only [Nat.mul_comm] using period_mul_complementary d j :
      complementaryPeriod d j * d j = D)
  · intro P hP hI hS hHP
    have hD : (D : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) := by
      calc
        (D : ℝ) = ∏ j, (d j : ℝ) := Nat.cast_prod _ _
        _ ≤ ∏ _j : J, Real.exp ((P + 2) ^ 36) :=
          Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _)
            (fun j _ => (hbound j hP (hI j) hS (hHP j)).1)
        _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    refine ⟨hD, ?_⟩
    intro j i s
    rw [Int.cast_mul, Int.cast_natCast, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (complementaryPeriod d j) : (0 : ℝ) ≤ complementaryPeriod d j)]
    have hc : (complementaryPeriod d j : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) :=
      (Nat.cast_le.mpr (complementaryPeriod_le_product d hd j)).trans hD
    calc
      _ ≤ Real.exp (Fintype.card J * (P + 2) ^ 36) * Real.exp (2 * (P + 2) ^ 36) :=
        mul_le_mul hc ((hbound j hP (hI j) hS (hHP j)).2 i s) (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

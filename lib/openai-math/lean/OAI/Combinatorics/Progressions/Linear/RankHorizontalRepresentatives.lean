import OAI.Combinatorics.Progressions.Estimates.NativeProductCoefficient

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem exists_rank_two_basis (d : Fin (s + 1)) (hd : 1 ≤ d.val) {p : ℝ}
    (hR : R.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (R.filtration.layer d.val 2))) ℚ (R.filtration.layer d.val 2),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  by_cases hs : 2 < s + 1
  · exact ⟨R.basis d ⟨2, hs⟩, hR.2 d ⟨2, hs⟩⟩
  · have hbot : R.filtration.layer d.val 2 = ⊥ := by
      apply bot_unique
      calc
        R.filtration.layer d.val 2 ≤ R.filtration.layer s (r + 1) :=
          R.filtration.lex_antitone (Or.inr ⟨by omega, by have hr := R.filtration.rank_le_degree; omega⟩)
        _ = ⊥ := R.filtration.terminal
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    let b := Module.finBasis ℚ (R.filtration.layer d.val 2)
    refine ⟨b, fun j k => ?_⟩
    have hb : (b j : L) = 0 := by
      have h := (b j).property
      simpa only [hbot, Submodule.mem_bot] using h
    rw [hb]
    simpa [rationalLogHeight] using (Nat.cast_nonneg n).trans hR.1.1

theorem exists_horizontal_ambient_basis (d : Fin (s + 1)) (hd : 1 ≤ d.val)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p) :
    ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ Real.exp ((p + 3) ^ 7) ∧
      ∃ m : ℕ, m ≤ n ∧ ∃ f : Basis (Fin m) ℚ (L ⧸ R.filtration.layer d.val 2),
        ∀ i j, RationalHeightLE (f.repr ((R.filtration.layer d.val 2).mkQ (D.basis j)) i) H := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  obtain ⟨b, hb⟩ := R.exists_rank_two_basis d hd hR
  have hdim : (finrank ℚ (R.filtration.layer d.val 2) : ℝ) ≤ p + 1 := by
    calc
      _ ≤ (finrank ℚ L : ℝ) := by exact_mod_cast Submodule.finrank_le (R.filtration.layer d.val 2)
      _ = n := by rw [finrank_eq_card_basis D.basis, Fintype.card_fin]
      _ ≤ p + 1 := hR.1.1.trans (by linarith)
  obtain ⟨H, hH, hHp, m, hm, f, hf⟩ := exists_submodule_quotient_basis_exp D.basis
    (R.filtration.layer d.val 2) (fun j => (b j : L))
    (span_submodule_basis (R.filtration.layer d.val 2) b) (one_le_ceil_exp p)
    (fun j k => rationalHeightLE_ceil_exp (hb j k)) (by linarith : 0 ≤ p + 1)
    (by simpa only [Fintype.card_fin] using hdim) (ceil_exp_le_exp_add_one hp)
  refine ⟨H, hH, ?_, m, ?_, f, hf⟩
  · convert hHp using 2
    ring
  · simpa only [Fintype.card_fin] using hm

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {D : RationalFilteredNilmanifold L s n} (R : D.DegreeRankStructure r)

theorem exists_controlled_horizontal_representatives
    {σ : Type*} (d : Fin (s + 1)) (hd : 1 ≤ d.val)
    {p : ℝ} (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    {t : ℕ} (ht : t ≤ n) (f : Basis (Fin t) ℚ (L ⧸ R.filtration.layer d.val 2))
    (hf : ∀ i j, rationalLogHeight (f.repr ((R.filtration.layer d.val 2).mkQ (D.basis j)) i) ≤ p)
    {l : ℕ} (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget ((p + 3) ^ 4)) ≤ T i) :
    let P : ℝ := (p + 3) ^ 4
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (P + ((P + 2) ^ 3 + (P + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 →
        ∀ (x y z : ℝ ⊗[ℚ] R.filtration.HigherHorizontal d.val) (a q : Fin t → ℝ),
        R.filtration.realHigherHorizontalCoordinates d.val f (x - y - z) = a + q →
        ‖a‖ ≤ Real.exp P / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : (R.filtration.layer d.val 1).baseChange ℝ,
          R.filtration.realHigherHorizontalCoordinates d.val f
            (R.filtration.realHorizontalMap d.val E) = a ∧
          R.filtration.realHigherHorizontalCoordinates d.val f
            (R.filtration.realHorizontalMap d.val Q) = q ∧
          x - y - R.filtration.realHorizontalMap d.val E -
            R.filtration.realHorizontalMap d.val Q = z ∧
          ‖(D.basis.baseChange ℝ).equivFun E.val‖ ≤
            Real.exp ((P + 2) ^ 3 + (P + 2) ^ 18 + P) / monomialScale T α ∧
          (D.basis.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid m := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := R.basis d ⟨1, by omega⟩
  let v : Fin (finrank ℚ (R.filtration.layer d.val 1)) → L := fun j => b j
  let K := ⌈Real.exp p⌉₊
  let H := max K ((n + 1) * (K * K) ^ n)
  let P : ℝ := (p + 3) ^ 4
  have hP : p + 1 ≤ P := by
    simpa only [P, show p + 1 + 2 = p + 3 by ring] using
      le_power_budget (p := p + 1) (by linarith) (by decide : 1 ≤ 4)
  have hpP : p ≤ P := (by linarith : p ≤ p + 1).trans hP
  have hn : (n : ℝ) ≤ p := hR.1.1
  have hvdim : finrank ℚ (R.filtration.layer d.val 1) ≤ n := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      Submodule.finrank_le (R.filtration.layer d.val 1)
  have hH : 1 ≤ H := (one_le_ceil_exp p).trans (Nat.le_max_left _ _)
  have hHP : (H : ℝ) ≤ Real.exp P := by
    change ((max K (replicatedFrequencyHeight n K) : ℕ) : ℝ) ≤ Real.exp P
    rw [Nat.cast_max]
    exact max_le ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hP))
      (replicatedFrequencyHeight_ceil_exp n hp hn)
  have hvH : ∀ j i, RationalHeightLE (D.basis.repr (v j) i) H := by
    intro j i
    exact (rationalHeightLE_ceil_exp (hR.2 d ⟨1, by omega⟩ j i)).mono (Nat.le_max_left _ _)
  have hfH : ∀ j i,
      RationalHeightLE (R.filtration.ambientHorizontalCoordinates d.val f (v j) i) H := by
    intro j i
    have h := linearMap_coordinate_height D.basis f (R.filtration.layer d.val 2).mkQ
      (fun j i => rationalHeightLE_ceil_exp (hf i j)) (v j)
      (fun i => rationalHeightLE_ceil_exp (hR.2 d ⟨1, by omega⟩ j i)) i
    exact (show RationalHeightLE
      (R.filtration.ambientHorizontalCoordinates d.val f (v j) i)
      ((n + 1) * (K * K) ^ n) from by
        simpa only [Fintype.card_fin, DegreeRankLieFiltration.ambientHorizontalCoordinates,
          LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_apply] using h).mono
        (Nat.le_max_right _ _)
  exact R.filtration.exists_controlled_horizontal_lifts d.val f D.basis v
    (span_submodule_basis _ b) hH hl hvH hfH (hp.trans hpP)
    (by simpa only [Fintype.card_fin] using hn.trans hpP)
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr ht).trans (hn.trans hpP))
    (by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hvdim).trans (hn.trans hpP))
    hHP (hlp.trans (Real.exp_le_exp.mpr hpP)) T hT

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI

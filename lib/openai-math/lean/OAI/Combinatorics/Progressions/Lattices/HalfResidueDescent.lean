import OAI.Combinatorics.Progressions.Estimates.DescentPartitionLengths
import OAI.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent

namespace OAI

section

namespace Erdos3

theorem exists_residue_descent_precision (C : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ ε δ : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧ δ⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧
        8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) = Δ / 2 := by
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ C + Polynomial.X + Polynomial.C 32
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget B
  refine ⟨K, hK, ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  let E := Real.exp ((p + 2) ^ C)
  let ε := Δ / 32
  let δ := Δ / (8 * E)
  have hE : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := Real.one_le_exp (pow_nonneg (by linarith) _)
  have hε : 0 < ε := div_pos hΔ (by norm_num)
  have hδ : 0 < δ := div_pos hΔ (mul_pos (by norm_num) hE)
  have htotal : (p + 2) ^ C + p + 32 ≤ (p + 2) ^ K := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hεinv : ε⁻¹ = 32 * Δ⁻¹ := by
    change (Δ / 32)⁻¹ = 32 * Δ⁻¹
    rw [inv_div, div_eq_mul_inv]
  have hδinv : δ⁻¹ = 8 * E * Δ⁻¹ := by
    change (Δ / (8 * E))⁻¹ = 8 * E * Δ⁻¹
    rw [inv_div, div_eq_mul_inv]
  have h32 : (32 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hεbound : ε⁻¹ ≤ Real.exp ((p + 2) ^ K) := by
    rw [hεinv]
    calc
      32 * Δ⁻¹ ≤ 32 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 32 * Real.exp p := mul_le_mul_of_nonneg_right h32 (Real.exp_nonneg _)
      _ = Real.exp (32 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) C])
  have hδbound : δ⁻¹ ≤ Real.exp ((p + 2) ^ K) := by
    rw [hδinv]
    calc
      8 * E * Δ⁻¹ ≤ 8 * E * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by positivity)
      _ ≤ Real.exp 8 * E * Real.exp p := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 hE.le) (Real.exp_nonneg _)
      _ = Real.exp (8 + (p + 2) ^ C + p) := by
        dsimp only [E]
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcancel : E * δ = Δ / 8 := by
    dsimp only [δ]
    field_simp
  refine ⟨ε, δ, hε, ?_, hδ, ?_, hεbound, hδbound, ?_⟩
  · dsimp only [ε]
    linarith
  · apply (div_le_one (mul_pos (by norm_num) hE)).mpr
    linarith
  · change 8 * ε + 2 * (E * δ) = Δ / 2
    rw [hcancel]
    dsimp only [ε]
    ring

end Erdos3

end

section

namespace Erdos3

theorem exists_residue_event_descent_precision (C : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ,
      0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ rho q ε δ : ℝ,
        p + 16 ≤ q ∧ verticalDecompositionBudget (p + 16) ≤ q ∧ q ≤ (p + 2) ^ K ∧
        0 < rho ∧ rho⁻¹ ≤ Real.exp (p + 16) ∧
        0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧ δ⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (p + 16) - q)) ≤ Δ / 2 ∧
        8 * ε + 2 * (Real.exp (((p + 16) + 2) ^ C) * δ) = Δ / 4 := by
  obtain ⟨C₀, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  obtain ⟨K₀, _, hprecision⟩ := exists_residue_descent_precision C
  let P : Polynomial ℕ := (Polynomial.X + 18) ^ K₀ +
    (Polynomial.X + Polynomial.C (16 + C₀)) ^ C₀ + Polynomial.X + 32
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨K, hK, ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  have hp16 : 0 ≤ p + 16 := by linarith
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hdouble : (Δ / 2)⁻¹ ≤ Real.exp (p + 16) := by
    rw [inv_div, div_eq_mul_inv]
    calc
      2 * Δ⁻¹ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, herror⟩ :=
    hprecision (p + 16) hp16 (Δ / 2) (by positivity) (by linarith) hdouble
  let rho := Δ / 16
  let q := verticalDecompositionBudget (p + 16) + p + 32
  have hfreq0 : 0 ≤ verticalDecompositionBudget (p + 16) :=
    verticalDecompositionBudget_nonneg hp16
  have hpoly : (p + 18) ^ K₀ + (p + (16 + C₀ : ℕ)) ^ C₀ + p + 32 ≤ (p + 2) ^ K := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq : verticalDecompositionBudget (p + 16) ≤ (p + (16 + C₀ : ℕ)) ^ C₀ := by
    simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hvertical (p + 16) hp16
  have hpow : ((p + 16) + 2) ^ K₀ ≤ (p + 2) ^ K := by
    have hother : 0 ≤ (p + (16 + C₀ : ℕ)) ^ C₀ := by positivity
    have heq : (p + 16) + 2 = p + 18 := by ring
    rw [heq]
    linarith
  have hq : q ≤ (p + 2) ^ K := by
    have hother : 0 ≤ (p + 18) ^ K₀ := by positivity
    dsimp only [q]
    linarith
  have hrho : rho⁻¹ ≤ Real.exp (p + 16) := by
    change (Δ / 16)⁻¹ ≤ Real.exp (p + 16)
    rw [inv_div, div_eq_mul_inv]
    calc
      16 * Δ⁻¹ ≤ 16 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right h16 (Real.exp_nonneg _)
      _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
  have hsmall : Real.exp (-p) ≤ Δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ hΔ (Real.exp_pos p)).mp hΔinv
  have h32 : (8 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have htail : Real.exp (-32 : ℝ) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h32
  have htailbound : Real.exp (verticalDecompositionBudget (p + 16) - q) ≤ Δ / 8 := by
    have heq : verticalDecompositionBudget (p + 16) - q = -p + (-32) := by
      dsimp only [q]
      ring
    rw [heq, Real.exp_add]
    calc
      Real.exp (-p) * Real.exp (-32) ≤ Δ * (1 / 8) :=
        mul_le_mul hsmall htail (Real.exp_nonneg _) hΔ.le
      _ = _ := by ring
  refine ⟨rho, q, ε, δ, ?_, ?_, hq, by dsimp only [rho]; positivity, hrho,
    hε, hεhalf, hδ, hδone, hεbound.trans (Real.exp_le_exp.mpr hpow),
    hδbound.trans (Real.exp_le_exp.mpr hpow), ?_, ?_⟩
  · dsimp only [q]
    linarith
  · dsimp only [q]
    linarith
  · dsimp only [rho]
    linarith
  · linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residue_descent_size_bounds {σ : Type*} [Fintype σ]
    (N : σ → ℕ) (M P : ℕ) (J : σ → ℕ) (E Q ε δ : ℝ)
    (hE : 1 ≤ E) (hQ : Q ≤ E) (hM : (M : ℝ) ≤ E) (hP : (P : ℝ) ≤ E)
    (hJ : ∀ i, (J i : ℝ) ≤ E) (hcard : (Fintype.card σ : ℝ) ≤ E)
    (hε : 0 < ε) (hδ : 0 < δ) (hεinv : ε⁻¹ ≤ E) (hδinv : δ⁻¹ ≤ E)
    (hN : ∀ i, 8 * E ^ 6 ≤ (N i : ℝ)) :
    (∀ i, ((M * J i : ℕ) : ℝ) * (Q + 1) ≤ (N i : ℝ)) ∧
    (∀ i, 8 ≤ δ * (N i : ℝ)) ∧
    (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 := by
  have hE0 : 0 < E := by linarith
  have hsize0 : 0 < 8 * E ^ 6 := by positivity
  have hN0 : ∀ i, 0 < (N i : ℝ) := fun i => hsize0.trans_le (hN i)
  have hεlower : E⁻¹ ≤ ε := (inv_le_comm₀ hε hE0).mp hεinv
  have hδlower : E⁻¹ ≤ δ := (inv_le_comm₀ hδ hE0).mp hδinv
  have hδmul : 1 ≤ δ * E :=
    (div_le_iff₀ hE0).mp (by simpa only [one_div] using hδlower)
  have hE16 : E ≤ E ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hE (by norm_num : 1 ≤ 6)
  have hE36 : E ^ 3 ≤ E ^ 6 := pow_le_pow_right₀ hE (by norm_num : 3 ≤ 6)
  have hpair : ∀ i, ((M * J i : ℕ) : ℝ) ≤ E ^ 2 := by
    intro i
    simpa only [Nat.cast_mul, pow_two] using
      mul_le_mul hM (hJ i) (Nat.cast_nonneg (J i)) hE0.le
  have hlcm : Nat.lcm M (M * P) = M * P :=
    Nat.lcm_eq_right_iff_dvd.mpr (Nat.dvd_mul_right M P)
  have htriple : ∀ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) ≤ E ^ 3 := by
    intro i
    rw [hlcm, Nat.cast_mul, Nat.cast_mul]
    calc
      (M : ℝ) * P * J i ≤ (E * E) * E :=
        mul_le_mul (mul_le_mul hM hP (Nat.cast_nonneg P) hE0.le)
          (hJ i) (Nat.cast_nonneg (J i)) (by positivity)
      _ = E ^ 3 := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro i
    calc
      ((M * J i : ℕ) : ℝ) * (Q + 1) ≤ ((M * J i : ℕ) : ℝ) * (E + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hQ (le_refl 1)) (Nat.cast_nonneg _)
      _ ≤ E ^ 2 * (E + 1) := mul_le_mul_of_nonneg_right (hpair i) (by positivity)
      _ ≤ E ^ 2 * (2 * E) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 * E ^ 3 := by ring
      _ ≤ 8 * E ^ 6 := by nlinarith [pow_nonneg hE0.le 6]
      _ ≤ (N i : ℝ) := hN i
  · intro i
    have hn : 8 * E ≤ (N i : ℝ) :=
      (mul_le_mul_of_nonneg_left hE16 (by norm_num)).trans (hN i)
    calc
      8 ≤ δ * (8 * E) := by nlinarith
      _ ≤ δ * (N i : ℝ) := mul_le_mul_of_nonneg_left hn hδ.le
  · have hterm : ∀ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ) ≤
        E ^ 3 / (8 * E ^ 6) := by
      intro i
      exact (div_le_div_of_nonneg_right (htriple i) (hN0 i).le).trans
        (div_le_div_of_nonneg_left (by positivity) hsize0 (hN i))
    calc
      (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤
          ∑ _ : σ, E ^ 3 / (8 * E ^ 6) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Fintype.card σ : ℝ) * (E ^ 3 / (8 * E ^ 6)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ E * (E ^ 3 / (8 * E ^ 6)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = E⁻¹ * E⁻¹ / 8 := by field_simp
      _ ≤ δ * ε / 8 := div_le_div_of_nonneg_right
        (mul_le_mul hδlower hεlower (by positivity) hδ.le) (by norm_num)

end Erdos3

end

section

namespace Erdos3

theorem exists_separated_residue_precision :
    ∃ Kevent : ℕ, 2 ≤ Kevent ∧ ∀ C : ℕ, ∃ Kfreeze : ℕ, 2 ≤ Kfreeze ∧
      ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ rho q : ℝ,
        p + 16 ≤ q ∧ verticalDecompositionBudget (p + 16) ≤ q ∧ q ≤ (p + 2) ^ Kevent ∧
        0 < rho ∧ rho⁻¹ ≤ Real.exp (p + 16) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (p + 16) - q)) ≤ Δ / 2 ∧
        ∀ work : ℝ, p + 16 ≤ work → ∃ ε δ : ℝ,
          0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
          ε⁻¹ ≤ Real.exp ((work + 2) ^ Kfreeze) ∧ δ⁻¹ ≤ Real.exp ((work + 2) ^ Kfreeze) ∧
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) = Δ / 4 := by
  obtain ⟨Kevent, hKevent, hevent⟩ := exists_residue_event_descent_precision 0
  refine ⟨Kevent, hKevent, ?_⟩
  intro C
  obtain ⟨Kfreeze, hKfreeze, hfreeze⟩ := exists_residue_descent_precision C
  refine ⟨Kfreeze, hKfreeze, ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  obtain ⟨rho, q, _, _, hpq, hfreq, hq, hrho, hrhop, _, _, _, _, _, _, hprojection, _⟩ :=
    hevent p hp Δ hΔ hΔone hΔinv
  refine ⟨rho, q, hpq, hfreq, hq, hrho, hrhop, hprojection, ?_⟩
  intro work hwork
  have h16 : (2 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hdouble : (Δ / 2)⁻¹ ≤ Real.exp work := by
    rw [inv_div, div_eq_mul_inv]
    calc
      2 * Δ⁻¹ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right h16 (Real.exp_nonneg _)
      _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp work := Real.exp_le_exp.mpr hwork
  obtain ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, herror⟩ :=
    hfreeze work (by linarith) (Δ / 2) (by positivity) (by linarith) hdouble
  exact ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, by linarith⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_child_residue_descent (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) (w : σ → ℕ),
      (∀ i, 0 < w i) → ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) {e n : ℕ}
        (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
        (Q : RationalFilteredNilmanifold
          ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
        (_hEF : E.filtration = D.filtration.gradedRefiltration W)
        (_hQF : Q.filtration = E.filtration.quotientTop)
        (b : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
        ∀ cost : ℝ, 0 ≤ cost → SingleRefilteredRecoveryFamily D W E Q p q C cost →
        let H := D.filtration.gradedRefiltrationSubalgebra W
        let N := H ⧸ E.filtration.layerIdeal (s + 1)
        let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
        let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
        let := realification_moduleTopology_t2 Q.basis
        let T := Q.raiseStep (Nat.le_succ s)
        ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
          (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
          (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (B : ℕ) (hB : 0 < B)
            (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
            (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
            let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
            V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
            ∃ child : V.filtration.realification.PolynomialOrbit w,
              DegreeLE w s child.log ∧
              FixedResidueDescent D W V w b child p q P hP C a (cost + 4) := by
  obtain ⟨C, hC, hfreezing⟩ := Niltest.exists_auxiliary_frozen_discrepancy (s + 1) a
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ _ d D w hw p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hfreeze⟩ := hfreezing D w hw p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro W e n E Q hEF hQF b hb hb0 cost hcost hfamily H N _ _ _ T
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, hdegree, hrealize⟩ :=
    SingleRefilteredRecoveryFamily.exists_fixed_child D W E Q hEF hQF w hw b hb hb0 hcost hfamily
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hVF, hVL, hV,
    child, hdegree, ?_⟩
  change FixedResidueDescent D W V w b child p q P hP C a (cost + 4)
  intro S hS hunit hinvariant slow rational κ hκ hprod hgrid A hA hslow M hM lo length width
    hwidth hwidthN u v J hJ hv hcop δ ε hδ hε hsize hphysical hsmall cells c₀ c₁ F G
  obtain ⟨k, hk₀, hk₁, l₀, r₀, hl₀, hr₀, hgap⟩ :=
    hfreeze S hS hunit slow b rational κ hκ hprod hgrid A hA hslow
      M hM lo length width hwidth hwidthN u v J hJ hv hcop δ ε hδ hε hsize hphysical hsmall
  have hℓ : (S.lipBound : ℝ) ≤ Real.exp p := by
    linarith [S.observable_budget hS, S.normBound.coe_nonneg]
  have hreal := hrealize l₀ r₀ hl₀ hr₀ S.observable S.lipBound hℓ S.lipschitz hunit hinvariant
  obtain ⟨U, hU, hunitU, hcostU, hgapU⟩ := hreal.transfer_discrepancy
    (partitionCell c₀ k) (partitionCell c₁ k)
    (fun x => commonStrideIndex u M (fun i => (x i).val))
    (fun x => commonStrideIndex u M (fun i => (x i).val)) hgap
  exact ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, hgapU⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem FixedResidueDescent.half_discrepancy
    {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {W : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    {V : RationalFilteredNilmanifold K t e} {w : σ → ℕ}
    {b : (D.filtration.realification.adaptedPolynomialFiltration w).Group}
    {child : V.filtration.realification.PolynomialOrbit w}
    {p cost : ℝ} {q P C a : ℕ} {hP : 0 < P}
    (hdesc : FixedResidueDescent D W V w b child p q P hP C a cost)
    (S : D.Niltest w) (hS : S.ComplexityLE p) (hunit : S.UnitIntervalValued)
    (hinvariant : ∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
      ∀ x, S.observable (z • x) = S.observable x)
    (E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨S.orbit.log, S.orbit.property⟩⟩)
    (hgrid : D.filtration.PolynomialRationalGrid D.basis w q R)
    (A : σ → ℝ) (hA : ∀ i, 0 < A i)
    (hE : D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E)
    (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N : σ → ℕ) (u v : σ → ℤ) (J : σ → ℕ)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hcop : ∀ i, (M * (M * P)).Coprime (J i)) (Δ ε δ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : ε < 1 / 2)
    (hprecision : 8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) ≤ Δ / 2)
    (hlarge : ∀ i, 8 ≤ δ * (N i : ℝ))
    (hphysical : ∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
      (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i)
    (hcount : (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8)
    (hgap : Δ ≤
      ‖(𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
          residueBoxStrideValue S.eval u M x) -
        (𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v,
          residueBoxStrideValue S.eval u M x)‖) :
    ∃ (H : σ → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i),
      (∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ)) ∧
      (∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4) ∧
      let Q := comparableBoxPartitions N H hH hHN
      let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u
      let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
        (fun _ => Nat.mul_pos hM hP) u v hv
      ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
        0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
        ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
          Δ / 2 ≤
            ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue U.eval u M x) -
              (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue U.eval u M x)‖ := by
  have hsize : ∀ i, (N i : ℝ) ≤ 2 * (M : ℝ) * A i := by
    intro i
    linarith [(hphysical i).1, (hphysical i).2]
  obtain ⟨H, hH, hHN, hlo, hhi, hfreeze, hcounts⟩ := exists_descent_partition_lengths N M A δ hδ hδone
    hsize hlarge (fun i => ((Nat.lcm M (M * P) * J i : ℕ) : ℝ))
    (fun _ => Nat.cast_nonneg _) ε hcount
  refine ⟨H, hH, hHN, hlo, hhi, ?_⟩
  intro Q c₀ c₁
  obtain ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, hchild⟩ := hdesc S hS hunit hinvariant
    E R κ hκ hprod hgrid A hA hE M hM lo N H hH hHN u v J hJ hv hcop
    δ ε hδ.le hε hfreeze hphysical hcounts
  refine ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, ?_⟩
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI

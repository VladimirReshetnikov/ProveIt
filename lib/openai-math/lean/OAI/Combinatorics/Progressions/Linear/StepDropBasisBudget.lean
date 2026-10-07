import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3

open Module

theorem stepDropBracketHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (stepDropBracketHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hh : (H : ℝ) * H ≤ Real.exp (2 * p) := by
    rw [show 2 * p = p + p by ring, Real.exp_add]
    exact mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) hh (n ^ 2)
  rw [← Real.exp_nat_mul] at hpow
  have hinner : (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H : ℕ) ≤
      Real.exp ((n : ℝ) ^ 2 + n ^ 2 * (2 * p) + p) := by
    push_cast
    rw [Real.exp_add, Real.exp_add]
    apply mul_le_mul _ hH (Nat.cast_nonneg H) (by positivity)
    exact mul_le_mul (Real.add_one_le_exp ((n : ℝ) ^ 2))
      (by simpa only [Nat.cast_pow] using hpow) (by positivity) (Real.exp_nonneg _)
  have hout := pow_le_pow_left₀
    (Nat.cast_nonneg (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H)) hinner n
  rw [← Real.exp_nat_mul] at hout
  have htotal : (stepDropBracketHeight n H : ℝ) ≤
      Real.exp ((n : ℝ) + n * (n ^ 2 + n ^ 2 * (2 * p) + p)) := by
    unfold stepDropBracketHeight
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hout (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  calc
    (n : ℝ) + n * (n ^ 2 + n ^ 2 * (2 * p) + p) ≤
        p + p * (p ^ 2 + p ^ 2 * (2 * p) + p) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 8 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 79 * p + 32 := by positivity
      nlinarith

theorem exists_stepDrop_basis_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]
    (b : Basis μ ℚ L) (w : μ → ℕ) (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ} (_hH : 1 ≤ H)
    (_hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (_hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (_hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (_heK : ∀ i j, RationalHeightLE (b.repr (eK j : L) i) H)
    (_hstructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hν : (Fintype.card ν : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p),
    ∃ e : Basis (Fin (Module.finrank ℚ (stepDropSubmodule b w U V K)))
      ℚ (stepDropSubmodule b w U V K), ∀ i j,
      (((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
      (((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + 2) ^ 5 + 2) ^ 9)
  refine ⟨C, hC, ?_⟩
  intro L μ υ χ κ ν _ _ _ _ _ _ _ b w U V K fU fK fV eK H hH hU hK hV heK hstructure
    p hp hμ hυ hχ hκ hν hHp
  let q := (p + 2) ^ 5
  let J := max H (stepDropBracketHeight (Fintype.card μ) H)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hp2 : p ≤ p + 2 := by linarith
    apply hp2.trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 1 ≤ 5)
  have hrows : (Fintype.card (StepDropRow υ χ κ ν) : ℝ) ≤ q := by
    simp only [StepDropRow, Fintype.card_sum, Fintype.card_prod, Nat.cast_add, Nat.cast_mul]
    have hprod : (Fintype.card κ : ℝ) * Fintype.card ν ≤ p * p :=
      mul_le_mul hκ hν (Nat.cast_nonneg _) hp
    have hpoly : p ^ 2 + 3 * p ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 10 * p ^ 4 + 40 * p ^ 3 + 79 * p ^ 2 + 77 * p + 32 := by positivity
      nlinarith
    dsimp [q]
    nlinarith
  have hJ : 1 ≤ J := hH.trans (Nat.le_max_left _ _)
  have hJq : (J : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHp.trans (Real.exp_le_exp.mpr hpq))
      (stepDropBracketHeight_le_exp (Fintype.card μ) H hp hμ hHp)
  obtain ⟨e, he⟩ := exists_stepDrop_basis_exp_height b w U V K fU fK fV eK hJ
    (fun i j => (hU i j).mono (Nat.le_max_left _ _))
    (fun i j => (hK i j).mono (Nat.le_max_left _ _))
    (fun i j => (hV i j).mono (Nat.le_max_left _ _))
    (fun i j z => (stepDrop_bracket_height b V K fV eK hV heK hstructure i j z).mono (Nat.le_max_right _ _))
    hq (hμ.trans hpq) hrows hJq
  have hcap : (q + 2) ^ 9 ≤ (p + C) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨e, fun i j => ⟨(he i j).1.trans (Real.exp_le_exp.mpr hcap),
    (he i j).2.trans (Real.exp_le_exp.mpr hcap)⟩⟩

end Erdos3

end

end OAI

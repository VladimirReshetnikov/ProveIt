import OAI.Combinatorics.Progressions.Estimates.NativeTwoSitePartition
import OAI.Combinatorics.Progressions.Lattices.IntegerOrbitTranslation

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_anchored_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (E : ∀ i, Bool → RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i b, (E i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ι → ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i b, (E i b).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
        (Fintype.card ((Fin n × ZMod q) × Fin m) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : ((Fin n × ZMod q) × Fin m) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (letI : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((E i false).integerOrbitPoint (g i false) ((x.val : ℤ) + c i))
               ((E i false).integerOrbitPoint (g i false) ((y.val : ℤ) + c i)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((E i true).integerOrbitPoint (g i true) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((E i true).integerOrbitPoint (g i true) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_two_site_partition s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((2 * X + 2 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d E g c q N _ _ p ρ hs hp hι hE hq hρ hρinv
  let D := fun k : ι × Bool => E k.1 k.2
  let G : ∀ k : ι × Bool, (D k).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun | (i, false) => (g i false).translate (fun _ => Nat.zero_lt_one) (fun _ => c i)
        | (i, true) => g i true
  let r := 2 * p + 2
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcard : (Fintype.card (ι × Bool) : ℝ) ≤ r := by
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hinv : 1 / ρ ≤ Real.exp ((r + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨n, m, hn, hm, hcount, A, hA, hsum, hres, hcircle, hexception, hobs, hmove⟩ :=
    hpartition D G q N hs hr hcard (fun k => (hE k.1 k.2).mono (E k.1 k.2) hpr)
      (hq.trans (Real.exp_le_exp.mpr hpr)) hρ hinv
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, m, hn, hm, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
  constructor
  · intro j x y hx hy i
    have h := hobs j x y hx hy (i, false) 0 (by norm_num)
    simpa only [D, G, zero_mul, add_zero, integerOrbitPoint_translate] using h
  · intro h b j k x y hx hy hxy hyy i
    exact hmove h b j k x y hx hy hxy hyy (i, true)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

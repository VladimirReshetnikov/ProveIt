import OAI.Combinatorics.Progressions.Dynamics.CyclicAlternativePathRecovery
import OAI.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_two_site_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
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
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_shifted_residue_partition s a
  obtain ⟨R, _, hrefine⟩ := exists_interval_refined_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, U, hU, hUsum, hres, hobs⟩ :=
    hpartition D g q N hs hp hι hD hq hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hinv : 1 / ρ ≤ Real.exp ((t + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨m, hm, hcount, A, hA, hsum, hsupport, hcircle, hexception, _⟩ :=
    hrefine U hs ht
      (by simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul] using
        hnb.trans (Real.exp_le_exp.mpr hBt))
      (fun j => (hU j).mono le_rfl hBt) hUsum hρ hinv
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, m, hn, hm, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum,
    fun j x hx => hres j.1 x (hsupport j x hx), hcircle, hexception, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  have hdiam j x y (hx : 0 < A j x) (hy : 0 < A j y) (i : ι) (k : ℤ) (hk : |k| ≤ 1) :
      dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + k * N))
        ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + k * N)) ≤ ρ :=
    hobs j.1 x y (hsupport j x hx) (hsupport j y hy) i k hk
  refine ⟨hdiam, ?_⟩
  intro h b j k x y hx hy hxy hyy i
  exact positive_cell_ordinary_shift_recovery A A ((D i).integerOrbitPoint (g i)) hρ
    (fun j x => ((hA j).unit_interval x).1) hcircle
    (fun j x y hx hy t ht => hdiam j x y hx hy i t ht) h b j k x y hx hy hxy hyy

end Erdos3.RationalFilteredNilmanifold

end

end OAI

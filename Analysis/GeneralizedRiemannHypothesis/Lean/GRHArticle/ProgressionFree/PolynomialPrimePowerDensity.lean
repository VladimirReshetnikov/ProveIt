import GRHArticle.ProgressionFree.PolynomialPrimePowerLayers
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# How one prime changes the density of a monic family

Adjoining any prescribed set of powers of a monic irreducible multiplies
the degree-layer density by its local weight series.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- Normalized exact-degree count of a monic family. -/
noncomputable def monicFamilyProportion (B : Set F[X]) (n : ℕ) : ℝ :=
  ((monicFamilyLayer B n).card : ℝ) / (Fintype.card F : ℝ)^n

theorem monicFamilyProportion_mem_unitInterval (B : Set F[X]) (n : ℕ) :
    monicFamilyProportion B n ∈ Set.Icc 0 1 := by
  refine ⟨by unfold monicFamilyProportion; positivity, (div_le_one (by positivity)).mpr ?_⟩
  exact_mod_cast card_monicFamilyLayer_le B n

/-- The contribution of an allowed set of local prime multiplicities. -/
noncomputable def primeExponentWeight (w : ℝ) (D : Set ℕ) : ℝ :=
  ∑' e : ℕ, D.indicator (w ^ ·) e

/-- A degree-layer limit passes to the full prime-power extension. -/
theorem tendsto_monicFamilyProportion_extendByPrimePowers {P : F[X]} (hP : P.Monic)
    (hi : Irreducible P) (D : Set ℕ) {B : Set F[X]} (hB : ∀ g ∈ B, g.Monic ∧ ¬P ∣ g)
    {c : ℝ} (hlim : Tendsto (monicFamilyProportion B) atTop (𝓝 c)) :
    Tendsto (monicFamilyProportion (extendByPrimePowers P D B)) atTop
      (𝓝 (c * primeExponentWeight ((Fintype.card F : ℝ)⁻¹^P.natDegree) D)) := by
  let q : ℝ := Fintype.card F
  let d := P.natDegree
  let w := q⁻¹^d
  have hd : 0 < d := hi.natDegree_pos
  have hq : 1 < q := by dsimp [q]; exact_mod_cast Fintype.one_lt_card
  have hq₀ : 0 < q := by linarith
  have hw₀ : 0 ≤ w := by dsimp [w]; positivity
  have hw₁ : w < 1 := pow_lt_one₀ (inv_nonneg.mpr hq₀.le)
    (inv_lt_one_of_one_lt₀ hq) hd.ne'
  let v (e : ℕ) := D.indicator (w ^ ·) e
  have hv (e : ℕ) : 0 ≤ v e ∧ v e ≤ w^e := by
    by_cases h : e ∈ D <;> simp [v, Set.indicator, h, pow_nonneg hw₀]
  let a (n e : ℕ) := if e*d ≤ n then monicFamilyProportion B (n-e*d)*v e else 0
  have hp (e : ℕ) : Tendsto (a · e) atTop (𝓝 (c*v e)) := by
    refine ((hlim.comp (tendsto_sub_atTop_nat (e*d))).mul tendsto_const_nhds).congr' ?_
    filter_upwards [eventually_ge_atTop (e*d)] with n hn
    exact (if_pos hn).symm
  have hb (n e : ℕ) : ‖a n e‖ ≤ w^e := by
    by_cases h : e*d ≤ n
    · have hu := monicFamilyProportion_mem_unitInterval B (n-e*d)
      simp only [a, if_pos h, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu.1 (hv e).1)]
      exact (mul_le_of_le_one_left (hv e).1 hu.2).trans (hv e).2
    · simpa only [a, if_neg h, norm_zero] using pow_nonneg hw₀ e
  have ha := tendsto_tsum_of_dominated_convergence (summable_geometric_of_lt_one hw₀ hw₁)
    hp (Eventually.of_forall hb)
  have hfinite (n : ℕ) : (∑' e, a n e) = monicFamilyProportion (extendByPrimePowers P D B) n := by
    let E := (Finset.range (n+1)).filter (fun e ↦ e ∈ D ∧ e*d ≤ n)
    rw [tsum_eq_sum (s := E)]
    · unfold monicFamilyProportion
      rw [card_monicFamilyLayer_extendByPrimePowers hP hi D hB, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨_,heD,hen⟩ := Finset.mem_filter.mp he
      simp only [a, if_pos hen, monicFamilyProportion, v, Set.indicator_of_mem heD]
      change (_ / q^(n-e*d)) * (q⁻¹^d)^e = _ / q^n
      have heq : q^n = q^(n-e*d)*q^(e*d) :=
        (congrArg (q ^ ·) (show n = (n-e*d)+(e*d) by omega)).trans (pow_add _ _ _)
      rw [heq, ← pow_mul, Nat.mul_comm d e, inv_pow]
      field_simp
      rfl
    · intro e he
      by_cases hen : e*d ≤ n
      · have he' := Nat.le_mul_of_pos_right e hd
        have heD : e ∉ D := fun h ↦ he (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), h, hen⟩)
        simp [a, hen, v, heD]
      · simp [a, hen]
  simpa only [hfinite, tsum_mul_left, primeExponentWeight, v, w, d, q] using ha

end GRHArticle.ProgressionFree

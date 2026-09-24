import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Zeros of real exponential polynomials

A finite sum `G(x) = Σⱼ Aⱼ(x) e^{Bⱼ(x)}` with real polynomials `Aⱼ, Bⱼ` either vanishes
identically or has no arbitrarily large real zeros (the dominant-term argument of Jones, Sato,
Wada and Wiens, 1976, proof of Theorem 4.4).

Group the terms whose exponents differ from an eventually largest exponent `B₀` by a constant:
their sum is `e^{B₀(x)} R(x)` for a real polynomial `R`. Every other exponent differs from `B₀`
by a nonconstant polynomial with negative leading coefficient, so after division by `e^{B₀}`
those terms tend to zero. If `R ≠ 0` then `|R|` stays away from zero and `G` has no large zeros;
if `R = 0` the group contributes nothing and induction on the number of terms applies.
-/

namespace Diophantine

open Polynomial Filter Asymptotics Topology

/-- The sign of a real polynomial is eventually constant. -/
theorem eventually_nonneg_or_nonpos (D : ℝ[X]) :
    (∀ᶠ x in atTop, 0 ≤ D.eval x) ∨ (∀ᶠ x in atTop, D.eval x ≤ 0) := by
  by_cases hd : 0 < D.degree
  · rcases le_total 0 D.leadingCoeff with h | h
    · exact Or.inl ((D.tendsto_atTop_of_leadingCoeff_nonneg hd h).eventually_ge_atTop 0)
    · exact Or.inr ((D.tendsto_atBot_of_leadingCoeff_nonpos hd h).eventually_le_atBot 0)
  · have hc := eq_C_of_degree_le_zero (not_lt.1 hd)
    rcases le_total 0 (D.coeff 0) with h | h
    · exact Or.inl (Eventually.of_forall fun x => by rw [hc, eval_C]; exact h)
    · exact Or.inr (Eventually.of_forall fun x => by rw [hc, eval_C]; exact h)

/-- A nonconstant real polynomial with negative leading coefficient is eventually below a
negative multiple of the identity. -/
theorem eventually_le_neg_mul (D : ℝ[X]) (hd : 0 < D.degree) (hl : D.leadingCoeff < 0) :
    ∃ ε > 0, ∀ᶠ x in atTop, D.eval x ≤ -(ε * x) := by
  set a := D.leadingCoeff with ha
  refine ⟨-a / 2, by linarith, ?_⟩
  have hn : 1 ≤ D.natDegree := natDegree_pos_iff_degree_pos.2 hd
  rcases eq_or_lt_of_le hn with h1 | h2
  · -- linear case
    have hD := eq_X_add_C_of_natDegree_le_one (show D.natDegree ≤ 1 by omega)
    have h1a : D.coeff 1 = a := by rw [ha, leadingCoeff, ← h1]
    set c := D.coeff 0
    filter_upwards [eventually_ge_atTop (2 * |c| / (-a))] with x hx
    have hev : D.eval x = a * x + c := by
      conv_lhs => rw [hD]
      simp [h1a]
    rw [hev]
    have hpos : 0 < -a := by linarith
    have hx' : 2 * |c| ≤ -a * x := by
      have := (div_le_iff₀ hpos).1 hx
      linarith
    have := le_abs_self c
    nlinarith
  · -- degree at least two
    have hlt : (C (-a / 2) * X : ℝ[X]).degree < D.degree := by
      calc (C (-a / 2) * X : ℝ[X]).degree ≤ 1 := degree_C_mul_X_le _
        _ < D.degree := by
            rw [degree_eq_natDegree (ne_zero_of_degree_gt hd)]
            exact_mod_cast h2
    set E := D + C (-a / 2) * X with hE
    have hEd : 0 < E.degree := by rw [hE, degree_add_eq_left_of_degree_lt hlt]; exact hd
    have hEl : E.leadingCoeff ≤ 0 := by
      rw [hE, leadingCoeff_add_of_degree_lt' hlt]; exact hl.le
    filter_upwards [(E.tendsto_atBot_of_leadingCoeff_nonpos hEd hEl).eventually_le_atBot 0]
      with x hx
    simp only [hE, eval_add, eval_mul, eval_C, eval_X] at hx
    linarith

/-- A polynomial times the exponential of a polynomial with negative leading coefficient tends
to zero. -/
theorem tendsto_mul_exp_zero (A D : ℝ[X]) (hd : 0 < D.degree) (hl : D.leadingCoeff < 0) :
    Tendsto (fun x => A.eval x * Real.exp (D.eval x)) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hD⟩ := eventually_le_neg_mul D hd hl
  set k := A.natDegree
  have hA : A.eval =O[atTop] (fun x : ℝ => x ^ k) := by
    have := A.isBigO_atTop_of_degree_le (X ^ k : ℝ[X]) (by rw [degree_X_pow]; exact degree_le_natDegree)
    simpa using this
  have hexp : (fun x => Real.exp (D.eval x)) =O[atTop] (fun x => Real.exp (-(ε * x))) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hD] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _), one_mul]
    exact Real.exp_le_exp.2 hx
  have hlim : Tendsto (fun x : ℝ => x ^ k * Real.exp (-(ε * x))) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop hε)
    have h2 := h1.const_mul ((ε ^ k)⁻¹)
    rw [mul_zero] at h2
    refine h2.congr' (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, id]
    rw [mul_pow]
    field_simp
  exact (hA.mul hexp).trans_tendsto hlim

/-- A finite nonempty family has an eventually largest exponent. -/
theorem exists_eventually_max {ι : Type*} (B : ι → ℝ[X]) (s : Finset ι) (hs : s.Nonempty) :
    ∃ j₀ ∈ s, ∀ j ∈ s, ∀ᶠ x in atTop, (B j).eval x ≤ (B j₀).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert i s hi ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨i, by simp, fun j hj => ?_⟩
      have : j = i := by simpa using hj
      subst this
      exact Eventually.of_forall fun _ => le_rfl
    · obtain ⟨j₀, hj₀, hmax⟩ := ih hne
      rcases eventually_nonneg_or_nonpos (B j₀ - B i) with h | h
      · refine ⟨j₀, Finset.mem_insert_of_mem hj₀, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · filter_upwards [h] with x hx; simp only [eval_sub] at hx; linarith
        · exact hmax j hj
      · refine ⟨i, Finset.mem_insert_self _ _, fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact Eventually.of_forall fun _ => le_rfl
        · filter_upwards [h, hmax j hj] with x hx hj'
          simp only [eval_sub] at hx; linarith

/-- The exponential polynomial `Σⱼ Aⱼ(x) e^{Bⱼ(x)}`. -/
noncomputable def expPoly {ι : Type*} (s : Finset ι) (A B : ι → ℝ[X]) (x : ℝ) : ℝ :=
  ∑ j ∈ s, (A j).eval x * Real.exp ((B j).eval x)

/-- **A real exponential polynomial with arbitrarily large zeros vanishes identically.** -/
theorem expPoly_eq_zero_of_frequently {ι : Type*} (A B : ι → ℝ[X]) :
    ∀ (s : Finset ι), (∀ N : ℝ, ∃ x ≥ N, expPoly s A B x = 0) → ∀ x, expPoly s A B x = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hz
  rcases s.eq_empty_or_nonempty with rfl | hne
  · intro x; simp [expPoly]
  obtain ⟨j₀, hj₀, hmax⟩ := exists_eventually_max B s hne
  set S := s.filter (fun j => (B j - B j₀).degree ≤ 0) with hS
  set R : ℝ[X] := ∑ j ∈ S, C (Real.exp ((B j - B j₀).coeff 0)) * A j with hR
  have hsplit : ∀ x, expPoly s A B x =
      R.eval x * Real.exp ((B j₀).eval x) + expPoly (s.filter fun j => ¬ (B j - B j₀).degree ≤ 0) A B x := by
    intro x
    unfold expPoly
    rw [← Finset.sum_filter_add_sum_filter_not s (fun j => (B j - B j₀).degree ≤ 0)]
    congr 1
    rw [hR, eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hc := eq_C_of_degree_le_zero (Finset.mem_filter.1 hj).2
    have hB : (B j).eval x = (B j₀).eval x + (B j - B j₀).coeff 0 := by
      have := congrArg (eval x) hc
      simp only [eval_sub, eval_C] at this
      linarith
    rw [hB, eval_mul, eval_C, Real.exp_add]
    ring
  by_cases hR0 : R = 0
  · -- the grouped terms cancel
    have hrest : ∀ x, expPoly s A B x = expPoly (s.filter fun j => ¬ (B j - B j₀).degree ≤ 0) A B x :=
      fun x => by rw [hsplit, hR0, eval_zero, zero_mul, zero_add]
    have hsub : s.filter (fun j => ¬ (B j - B j₀).degree ≤ 0) ⊂ s := by
      refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨j₀, hj₀, ?_⟩
      simp
    intro x
    rw [hrest]
    exact ih _ hsub (fun N => by
      obtain ⟨y, hy, hy0⟩ := hz N
      exact ⟨y, hy, by rw [← hrest]; exact hy0⟩) x
  · -- the grouped terms dominate
    exfalso
    obtain ⟨m, hm, hRm⟩ : ∃ m > 0, ∀ᶠ x in atTop, m ≤ |R.eval x| := by
      by_cases hd : 0 < R.degree
      · exact ⟨1, one_pos, (R.abs_tendsto_atTop hd).eventually_ge_atTop 1⟩
      · have hc := eq_C_of_degree_le_zero (not_lt.1 hd)
        have hc0 : R.coeff 0 ≠ 0 := fun h => hR0 (by rw [hc, h, C_0])
        exact ⟨|R.coeff 0|, abs_pos.2 hc0, Eventually.of_forall fun x => by rw [hc]; simp⟩
    have hterm : ∀ j ∈ s.filter (fun j => ¬ (B j - B j₀).degree ≤ 0),
        Tendsto (fun x => (A j).eval x * Real.exp ((B j - B j₀).eval x)) atTop (𝓝 0) := by
      intro j hj
      have hj' := Finset.mem_filter.1 hj
      have hd : 0 < (B j - B j₀).degree := not_le.1 hj'.2
      have hl : (B j - B j₀).leadingCoeff < 0 := by
        rcases lt_or_ge (B j - B j₀).leadingCoeff 0 with h | h
        · exact h
        · exfalso
          have htop := (B j - B j₀).tendsto_atTop_of_leadingCoeff_nonneg hd h
          have hev := (htop.eventually_gt_atTop 0).and (hmax j hj'.1)
          obtain ⟨x, hx1, hx2⟩ := hev.exists
          simp only [eval_sub] at hx1
          linarith
      exact tendsto_mul_exp_zero (A j) _ hd hl
    have hsmall : Tendsto (fun x => ∑ j ∈ s.filter (fun j => ¬ (B j - B j₀).degree ≤ 0),
        (A j).eval x * Real.exp ((B j - B j₀).eval x)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum _ hterm
    have hev := hRm.and ((hsmall.eventually (Metric.ball_mem_nhds 0 (half_pos hm))))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    obtain ⟨x, hx, hx0⟩ := hz N
    obtain ⟨h1, h2⟩ := hN x hx
    rw [dist_zero_right, Real.norm_eq_abs] at h2
    have hkey : expPoly s A B x = Real.exp ((B j₀).eval x) * (R.eval x + ∑ j ∈
        s.filter (fun j => ¬ (B j - B j₀).degree ≤ 0),
        (A j).eval x * Real.exp ((B j - B j₀).eval x)) := by
      rw [hsplit, mul_add, Finset.mul_sum]
      unfold expPoly
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [eval_sub, Real.exp_sub]
        field_simp
    rw [hkey] at hx0
    have hne := mul_ne_zero (Real.exp_pos ((B j₀).eval x)).ne' (show R.eval x + _ ≠ 0 from fun h => by
      have : |R.eval x| ≤ |∑ j ∈ s.filter (fun j => ¬ (B j - B j₀).degree ≤ 0),
          (A j).eval x * Real.exp ((B j - B j₀).eval x)| := by
        rw [eq_neg_of_add_eq_zero_left h, abs_neg]
      linarith)
    exact hne hx0

end Diophantine
